"""Run generator witnesses: Python programs that print a witness.

A witness with `format: generator` is a Python program, kept here as the
witness file, that prints a witness in one of its family's formats (`output`)
to standard output. The checker runs it, checks that what it printed has the
SHA-256 given as `output_sha256`, and then checks the output with the family's
checker, as if it were a witness file in that format. Output with a different
hash is still checked, with a warning. This allows witnesses
far larger than the size limit, when a short program can produce them.

The generator's output is checked, so its correctness doesn't have to be
trusted. Running it does: a maintainer reads a generator before running it to
verify it, as for a Lean proof, and it runs in a sandbox with no network, able
to write only to its own temporary directory, and with limits on its time and
output.
"""

import hashlib
import os
import pathlib
import resource
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Mapping

from .errors import CertificateError
from .witness import MAX_UNCOMPRESSED_BYTES


# Most CPU and wall-clock seconds a generator can take, and most bytes it can
# print (the same as for a decompressed witness file)
GENERATOR_SECONDS = 3600
GENERATOR_OUTPUT_BYTES = MAX_UNCOMPRESSED_BYTES

# Fields of a generator witness, which don't pass on to the generated witness
GENERATOR_FIELDS = ["format", "file", "output", "output_sha256"]

# macOS sandbox profile: no network, and writes only to the working directory
MACOS_PROFILE = """\
(version 1)
(allow default)
(deny network*)
(deny file-write*)
(allow file-write* (subpath "{work}") (literal "/dev/null"))
"""


def sandbox_command(work: pathlib.Path, command: list[str]) -> list[str]:
    """Wrap a command to run in a sandbox with no network, which can write only
    to the directory work: sandbox-exec on macOS, or bubblewrap on Linux."""
    if sys.platform == "darwin" and shutil.which("sandbox-exec"):
        return ["sandbox-exec", "-p", MACOS_PROFILE.format(work=work), *command]
    if sys.platform.startswith("linux") and shutil.which("bwrap"):
        return [
            "bwrap", "--ro-bind", "/", "/", "--dev", "/dev", "--proc", "/proc", "--bind", str(work), str(work),
            "--unshare-all", "--die-with-parent", "--new-session", "--chdir", str(work), *command,
        ]
    raise CertificateError(
        "Running a generator needs a sandbox: sandbox-exec on macOS, or bubblewrap (bwrap) on Linux"
    )


def limit_resources() -> None:
    """In the generator's process: limit its CPU time and the size of the files
    it writes, including its output."""
    resource.setrlimit(resource.RLIMIT_CPU, (GENERATOR_SECONDS, GENERATOR_SECONDS))
    resource.setrlimit(resource.RLIMIT_FSIZE, (GENERATOR_OUTPUT_BYTES + 1, GENERATOR_OUTPUT_BYTES + 1))


def run_generator(cert: Mapping[str, Any]) -> tuple[bytes, list[str]]:
    """Run a certificate's generator in a sandbox, and return what it printed,
    with a warning if that doesn't have the SHA-256 the certificate gives.

    A different output doesn't make the certificate fail: whatever the
    generator prints is checked, so if it passes, it proves the bound. But it
    means something differs from where the hash was computed, such as the
    version of Python or a package, so the witness checked isn't exactly the
    one submitted."""
    witness = cert["witness"]
    source = pathlib.Path(cert["path"]).parent / witness["file"]
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp).resolve()
        work = tmp / "work"
        work.mkdir()
        shutil.copy(source, work / "generator.py")
        output_path, errors_path = tmp / "output", tmp / "errors"
        # -s: no user site-packages; -P: don't put the script's directory on
        # the path; -B: don't write bytecode. The environment is only what's
        # given here, with hash randomization off so that iteration order over
        # sets of strings is the same on every run.
        command = [sys.executable, "-s", "-P", "-B", "generator.py"]
        env = {"PATH": os.defpath, "LC_ALL": "C", "PYTHONHASHSEED": "0", "HOME": str(work), "TMPDIR": str(work)}
        with open(output_path, "wb") as output, open(errors_path, "wb") as errors:
            try:
                result = subprocess.run(
                    sandbox_command(work, command), stdin=subprocess.DEVNULL, stdout=output, stderr=errors,
                    cwd=work, env=env, timeout=GENERATOR_SECONDS, preexec_fn=limit_resources,
                )
            except subprocess.TimeoutExpired:
                raise CertificateError(f"{cert['id']}: the generator took more than {GENERATOR_SECONDS} seconds")
        size = output_path.stat().st_size
        if size > GENERATOR_OUTPUT_BYTES:
            raise CertificateError(f"{cert['id']}: the generator printed more than {GENERATOR_OUTPUT_BYTES} bytes")
        if result.returncode != 0:
            message = errors_path.read_bytes()[-2000:].decode(errors="replace").strip()
            raise CertificateError(f"{cert['id']}: the generator failed (exit status {result.returncode}):\n{message}")
        data = output_path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    warnings = []
    if digest != witness["output_sha256"]:
        warnings.append(
            f"the generator's output has SHA-256 {digest}, not the output_sha256 given, {witness['output_sha256']}, "
            "so it printed something different from what was submitted"
        )
    return data, warnings


def generated_certificate(cert: Mapping[str, Any]) -> tuple[dict[str, Any], list[str]]:
    """A certificate with a generator witness, with the witness replaced by the
    generator's output, in the format the generator says it prints, and any
    warnings from running it. Other fields of the witness, such as symmetries,
    pass on to the output."""
    witness = cert["witness"]
    data, warnings = run_generator(cert)
    generated = {key: value for key, value in witness.items() if key not in GENERATOR_FIELDS}
    generated |= {"format": witness["output"], "generated": data}
    return {**cert, "witness": generated}, warnings
