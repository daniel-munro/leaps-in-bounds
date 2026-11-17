"""Check Lean proofs against the families' formal statements."""

import json
import pathlib
import subprocess
import tempfile
from typing import Any, Mapping

from .families import get_family


FORMAL_DIR = pathlib.Path("formal")
CHECK_LEAN_SCRIPT = pathlib.Path("scripts/check_lean.lean")


def check_lean(certs: list[Mapping[str, Any]], build: bool = True) -> dict[str, str]:
    """Check that each certificate's named theorem proves the expected
    statement using only allowed axioms. Returns an error message for each
    certificate that fails.

    Builds the proof modules first unless build is False, in which case they
    must already be compiled. Building runs the submission's code, so CI
    builds them in a separate job.

    The comparison is done by scripts/check_lean.lean, which builds the
    expected statement directly rather than elaborating it alongside the
    submitted proof, and replays the proofs through the kernel.
    """
    errors = {}
    entries = []
    for cert in certs:
        if "url" in cert["lean"]:
            errors[cert["id"]] = "the Lean proof is linked from elsewhere, so it can't be checked here"
            continue
        module = cert["lean"]["module"]
        if not module.startswith("LeapsInBounds.Proofs."):
            errors[cert["id"]] = "Lean proofs must live under LeapsInBounds.Proofs"
            continue
        family, params = get_family(cert["constant"])
        statement, args = family.lean_statement(params, cert["bound"], cert["value"])
        entries.append({
            "id": cert["id"],
            "statementModule": family.lean_module,
            "statement": statement,
            "args": args,
            "proofModule": module,
            "theorem": cert["lean"]["theorem"],
        })
    modules = sorted({entry["proofModule"] for entry in entries})
    if not modules:
        return errors
    if build:
        result = subprocess.run(["lake", "build", *modules], cwd=FORMAL_DIR, capture_output=True, text=True)
        if result.returncode != 0:
            output = result.stdout + result.stderr
            return errors | {entry["id"]: f"lake build failed:\n{output}" for entry in entries}
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as file:
        json.dump(entries, file)
        input_path = pathlib.Path(file.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(CHECK_LEAN_SCRIPT.resolve()), str(input_path)],
            cwd=FORMAL_DIR, capture_output=True, text=True,
        )
    finally:
        input_path.unlink()
    try:
        failures = json.loads(result.stdout) if result.returncode == 0 else None
    except json.JSONDecodeError:
        failures = None
    if failures is None:
        output = result.stdout + result.stderr
        return errors | {entry["id"]: f"Lean check failed:\n{output}" for entry in entries}
    for entry in entries:
        if entry["id"] in failures:
            statement = " ".join([entry["statement"], *map(lean_arg, entry["args"])])
            errors[entry["id"]] = f"Theorem {entry['theorem']} does not prove `{statement}`: {failures[entry['id']]}"
    return errors


def lean_arg(arg: int | list[list[int]]) -> str:
    """Write a statement argument as Lean source, for messages."""
    if isinstance(arg, int):
        return str(arg)
    return "[" + ", ".join(f"({c}, {m})" for c, m in arg) + "]"
