"""Run generator witnesses: Python programs that print a witness.

A witness with `format: generator` is a Python program, kept here as the
witness file, that prints a witness in one of its family's formats (`output`)
to standard output. The checker runs it, checks that what it printed has the
SHA-256 given as `output_sha256`, and then checks the output with the family's
checker, as if it were a witness file in that format. Output with a different
hash is still checked, with a warning. This allows witnesses far larger than
the size limit, when a short program can produce them. Most checkers read the
output all at once, up to the limit for a decompressed witness file; a checker
that reads it as a stream, line by line, can read any amount.

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
import select
import shutil
import subprocess
import sys
import tempfile
import time
from typing import Any, Iterator, Mapping

from .errors import CertificateError
from .witness import MAX_UNCOMPRESSED_BYTES


# Most CPU seconds a generator can take, and most seconds the checker waits for
# its output. Most bytes it can print for a checker that reads its output all
# at once (the same as for a decompressed witness file), and most bytes it can
# write to any file. A checker that reads its output as a stream can read any
# amount.
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


class GeneratorOutput:
    """A certificate's generator, running in a sandbox, and what it prints.

    Use it as a context manager, which stops the generator on leaving. Read
    the output either all at once with read(), up to GENERATOR_OUTPUT_BYTES,
    or once as a stream of lines, with no limit on its size.
    Then call finish(), which checks that the generator succeeded, and returns
    a warning if its output doesn't have the SHA-256 the certificate gives.

    A different output doesn't make the certificate fail: whatever the
    generator prints is checked, so if it passes, it proves the bound. But it
    means something differs from where the hash was computed, such as the
    version of Python or a package, so the witness checked isn't exactly the
    one submitted.

    The generator has GENERATOR_SECONDS of CPU time, and the checker waits at
    most that long in all for its output, however long the checker itself
    takes to check what it reads."""

    def __init__(self, cert: Mapping[str, Any]):
        self.cert = cert
        self.read_started = False
        self.complete = False
        self.hash = hashlib.sha256()
        self.waited = 0.0
        self.data: bytes | None = None

    def __enter__(self) -> "GeneratorOutput":
        witness = self.cert["witness"]
        source = pathlib.Path(self.cert["path"]).parent / witness["file"]
        self.tmp = tempfile.TemporaryDirectory()
        tmp = pathlib.Path(self.tmp.name).resolve()
        work = tmp / "work"
        work.mkdir()
        shutil.copy(source, work / "generator.py")
        self.errors = open(tmp / "errors", "w+b")
        # -s: no user site-packages; -P: don't put the script's directory on
        # the path; -B: don't write bytecode. The environment is only what's
        # given here, with hash randomization off so that iteration order over
        # sets of strings is the same on every run.
        command = [sys.executable, "-s", "-P", "-B", "generator.py"]
        env = {"PATH": os.defpath, "LC_ALL": "C", "PYTHONHASHSEED": "0", "HOME": str(work), "TMPDIR": str(work)}
        self.process = subprocess.Popen(
            sandbox_command(work, command), stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=self.errors,
            cwd=work, env=env, preexec_fn=limit_resources,
        )
        return self

    def __exit__(self, *exc: Any) -> None:
        if self.process.poll() is None:
            self.process.kill()
        self.process.wait()
        self.process.stdout.close()
        self.errors.close()
        self.tmp.cleanup()

    def chunks(self) -> Iterator[bytes]:
        """The output, in chunks as the generator prints it."""
        if self.read_started:
            raise CertificateError(f"{self.cert['id']}: the generator's output can only be read once")
        self.read_started = True
        return self._remaining_chunks()

    def _remaining_chunks(self) -> Iterator[bytes]:
        fd = self.process.stdout.fileno()
        while True:
            remaining = GENERATOR_SECONDS - self.waited
            started = time.monotonic()
            ready, _, _ = select.select([fd], [], [], max(remaining, 0))
            chunk = os.read(fd, 1 << 20) if ready else None
            self.waited += time.monotonic() - started
            if chunk is None:
                raise CertificateError(f"{self.cert['id']}: the generator took more than {GENERATOR_SECONDS} seconds")
            if not chunk:
                self.complete = True
                return
            self.hash.update(chunk)
            yield chunk

    def lines(self) -> Iterator[str]:
        """The output, line by line, without line endings."""
        rest = b""
        for chunk in self.chunks():
            *lines, rest = (rest + chunk).split(b"\n")
            yield from self._decode(lines)
        if rest:
            yield from self._decode([rest])

    def _decode(self, lines: list[bytes]) -> list[str]:
        try:
            return [line.decode("ascii") for line in lines]
        except UnicodeDecodeError:
            raise CertificateError(f"{self.cert['id']}: the generator's output isn't ASCII text")

    def read(self) -> bytes:
        """All of the output, up to GENERATOR_OUTPUT_BYTES. It's kept, so it
        can be read more than once this way."""
        if self.data is not None:
            return self.data
        data = bytearray()
        for chunk in self.chunks():
            data += chunk
            if len(data) > GENERATOR_OUTPUT_BYTES:
                raise CertificateError(
                    f"{self.cert['id']}: the generator printed more than {GENERATOR_OUTPUT_BYTES} bytes, "
                    "which is more than this family's checker can read at once"
                )
        self.data = bytes(data)
        return self.data

    def finish(self) -> list[str]:
        """Read whatever is left of the output, check that the generator
        succeeded, and return any warnings."""
        for _ in self._remaining_chunks() if self.read_started else self.chunks():
            pass
        try:
            status = self.process.wait(timeout=max(GENERATOR_SECONDS - self.waited, 0))
        except subprocess.TimeoutExpired:
            raise CertificateError(f"{self.cert['id']}: the generator took more than {GENERATOR_SECONDS} seconds")
        if status != 0:
            raise CertificateError(self.failure(status))
        return self.warnings()

    def failure(self, status: int) -> str:
        """A message saying that the generator failed, with the end of what it
        printed to standard error."""
        self.errors.seek(0, os.SEEK_END)
        self.errors.seek(max(self.errors.tell() - 2000, 0))
        message = self.errors.read().decode(errors="replace").strip()
        return f"{self.cert['id']}: the generator failed (exit status {status}):\n{message}"

    def failed(self) -> str | None:
        """If all the output has been read and the generator failed, a message
        saying so, which explains a check of its output failing."""
        if not self.complete:
            return None
        try:
            status = self.process.wait(timeout=10)
        except subprocess.TimeoutExpired:
            return None
        return self.failure(status) if status != 0 else None

    def warnings(self) -> list[str]:
        """A warning if the generator printed something other than what was
        submitted, once all its output has been read."""
        expected = self.cert["witness"]["output_sha256"]
        if self.complete and self.hash.hexdigest() != expected:
            return [
                f"the generator's output has SHA-256 {self.hash.hexdigest()}, not the output_sha256 given, "
                f"{expected}, so it printed something different from what was submitted"
            ]
        return []


def generated_witness(cert: Mapping[str, Any], output: GeneratorOutput) -> dict[str, Any]:
    """A certificate with a generator witness, with the witness replaced by the
    generator's output, in the format the generator says it prints. Other
    fields of the witness, such as symmetries, pass on to the output."""
    witness = cert["witness"]
    generated = {key: value for key, value in witness.items() if key not in GENERATOR_FIELDS}
    generated |= {"format": witness["output"], "generated": output}
    return {**cert, "witness": generated}
