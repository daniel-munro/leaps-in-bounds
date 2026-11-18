"""Load and check the records of how thoroughly each family has been covered,
and report where more work is likely to pay off.

Two files record this, both edited by hand:

- literature/coverage.yml: for each family, when its literature was last
  reviewed, which surveys, tables and databases were read through, whether its
  history is complete from them, and known gaps.
- certificates/blocked.yml: current bounds that can't be certified yet, and
  why, so the same dead ends aren't tried again.

process_data.py loads both through load_coverage() and load_blocked(), which
raise ValueError on anything malformed, so the build checks them. Run this
script after building the data (sh scripts/build.sh check) for a report of
each family's coverage, most in need of work first:

    python scripts/coverage.py
    python scripts/coverage.py --family ramsey   # also list its uncertified bounds
"""

import argparse
import datetime
import json
import pathlib
import re
from typing import Any, Mapping

import yaml

ROOT = pathlib.Path(__file__).resolve().parent.parent
COVERAGE_PATH = ROOT / "literature" / "coverage.yml"
BLOCKED_PATH = ROOT / "certificates" / "blocked.yml"

HISTORY_STATUSES = {"complete", "partial"}
BLOCKED_REASONS = {
    "unpublished": "the construction or proof isn't public, or couldn't be found",
    "too-large": "the evidence is over the size limit even compressed, with no stable link to attest",
    "needs-format": "the family's checker can't read this kind of witness or value yet",
    "too-slow": "checking it here takes too long, and no one has attested it",
    "out-of-reach": "a Lean proof would need formalization or computation beyond what's practical",
}
DATE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def _date(value: Any, where: str) -> str:
    # YAML reads unquoted dates as datetime.date; accept either form.
    if isinstance(value, datetime.date):
        value = value.isoformat()
    if not isinstance(value, str) or not DATE.match(value):
        raise ValueError(f"{where}: dates must be YYYY-MM-DD, got {value!r}")
    return value


def _string_list(value: Any, where: str) -> list[str]:
    if value is None:
        return []
    if not isinstance(value, list) or not all(isinstance(v, str) for v in value):
        raise ValueError(f"{where}: must be a list of strings")
    return value


def load_coverage(families: Mapping[str, Any], sources: Mapping[str, Any]) -> dict[str, dict[str, Any]]:
    """Load literature/coverage.yml, checking it against the families and sources.

    Returns {family: {"status", "reviewed", "sources", "gaps", "notes"}}, for
    the families that have been reviewed. Families not in the file haven't
    been reviewed.
    """
    if not COVERAGE_PATH.exists():
        return {}
    data = yaml.safe_load(COVERAGE_PATH.read_text()) or {}
    if not isinstance(data, dict):
        raise ValueError(f"{COVERAGE_PATH.name}: must map family IDs to entries")
    allowed = {"status", "reviewed", "sources", "gaps", "notes"}
    coverage = {}
    for family, entry in data.items():
        where = f"{COVERAGE_PATH.name}: {family}"
        if family not in families:
            raise ValueError(f"{where}: unknown family")
        if not isinstance(entry, dict):
            raise ValueError(f"{where}: must be a mapping")
        if extra := set(entry) - allowed:
            raise ValueError(f"{where}: unknown fields {sorted(extra)}")
        if entry.get("status") not in HISTORY_STATUSES:
            raise ValueError(f"{where}: status must be one of {sorted(HISTORY_STATUSES)}")
        read = _string_list(entry.get("sources"), f"{where}: sources")
        if unknown := [s for s in read if s not in sources]:
            raise ValueError(f"{where}: sources not in literature/sources.yml: {unknown}")
        if entry["status"] == "complete" and not read:
            raise ValueError(f"{where}: a complete history must list the sources it was reviewed from")
        notes = entry.get("notes")
        if notes is not None and not isinstance(notes, str):
            raise ValueError(f"{where}: notes must be a string")
        coverage[family] = {
            "status": entry["status"],
            "reviewed": _date(entry.get("reviewed"), where),
            "sources": read,
            "gaps": _string_list(entry.get("gaps"), f"{where}: gaps"),
            "notes": notes,
        }
    return coverage


def load_blocked(constants: Mapping[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    """Load certificates/blocked.yml, checking it against the constants.

    Returns {(constant, side): {"reason", "checked", "detail"}}. An entry can
    list several constants that are blocked for the same reason.
    """
    if not BLOCKED_PATH.exists():
        return {}
    data = yaml.safe_load(BLOCKED_PATH.read_text()) or []
    if not isinstance(data, list):
        raise ValueError(f"{BLOCKED_PATH.name}: must be a list of entries")
    allowed = {"constants", "bound", "reason", "checked", "detail"}
    blocked = {}
    for i, entry in enumerate(data, 1):
        where = f"{BLOCKED_PATH.name}: entry {i}"
        if not isinstance(entry, dict):
            raise ValueError(f"{where}: must be a mapping")
        if extra := set(entry) - allowed:
            raise ValueError(f"{where}: unknown fields {sorted(extra)}")
        ids = _string_list(entry.get("constants"), f"{where}: constants")
        if not ids:
            raise ValueError(f"{where}: constants is required")
        if unknown := [c for c in ids if c not in constants]:
            raise ValueError(f"{where}: unknown constants {unknown}")
        if entry.get("bound") not in ("lower", "upper"):
            raise ValueError(f"{where}: bound must be lower or upper")
        if entry.get("reason") not in BLOCKED_REASONS:
            raise ValueError(f"{where}: reason must be one of {sorted(BLOCKED_REASONS)}")
        if not isinstance(entry.get("detail"), str) or not entry["detail"].strip():
            raise ValueError(f"{where}: detail is required: say what was checked and what's missing")
        record = {
            "reason": entry["reason"],
            "checked": _date(entry.get("checked"), where),
            "detail": entry["detail"].strip(),
        }
        for constant in ids:
            key = (constant, entry["bound"])
            if key in blocked:
                raise ValueError(f"{where}: {constant} {entry['bound']} bound is already listed")
            blocked[key] = record
    return blocked


def blocked_record(
    blocked: Mapping[tuple[str, str], Mapping[str, Any]], constant: str, side: str, bound_date: str | None
) -> dict[str, Any] | None:
    """The blocked entry for a current bound, marked stale if the bound
    improved after it was checked, since a newer bound may come with a
    witness."""
    record = blocked.get((constant, side))
    if record is None:
        return None
    stale = bound_date is not None and bound_date[:10] > record["checked"]
    return {**record, "stale": stale}


# Report


def load_built(name: str) -> Any:
    path = ROOT / "data" / f"{name}.json"
    if not path.exists():
        raise SystemExit(f"{path.relative_to(ROOT)} not found: run sh scripts/build.sh check first")
    return json.loads(path.read_text())


def report(family_filter: str | None) -> None:
    families = load_built("families")
    unverified = load_built("unverified_bounds")
    history = load_built("history")
    constants = load_built("constants")
    sources = yaml.safe_load((ROOT / "literature" / "sources.yml").read_text())
    coverage = load_coverage(families, sources)
    today = datetime.date.today()

    literature_rows: dict[str, int] = {}
    for event in history:
        if event["discovery_kind"] == "source":
            family = constants[event["constant"]]["family"]
            literature_rows[family] = literature_rows.get(family, 0) + 1

    rows = []
    for family, info in families.items():
        if family_filter and family != family_filter:
            continue
        mine = [u for u in unverified if u["family"] == family]
        blocked = [u for u in mine if u.get("blocked") and not u["blocked"]["stale"]]
        stale = [u for u in mine if u.get("blocked") and u["blocked"]["stale"]]
        entry = coverage.get(family)
        age = (today - datetime.date.fromisoformat(entry["reviewed"])).days if entry else None
        rows.append({
            "family": family,
            "constants": info["stats"]["total_constants"],
            "history": entry["status"] if entry else "not reviewed",
            "reviewed": entry["reviewed"] if entry else "",
            "age": age,
            "gaps": len(entry["gaps"]) if entry else 0,
            "literature_rows": literature_rows.get(family, 0),
            "uncertified": len(mine),
            "blocked": len(blocked),
            "stale": len(stale),
            "witness": sum(1 for u in mine if u["certify_with"] == "witness" and u not in blocked),
            "lean": sum(1 for u in mine if u["certify_with"] == "lean" and u not in blocked),
            "items": mine,
        })

    # Most in need of work first: never reviewed, then partial, then by how long ago.
    rank = {"not reviewed": 0, "partial": 1, "complete": 2}
    rows.sort(key=lambda r: (rank[r["history"]], -(r["age"] or 0), -r["witness"]))

    header = f"{'family':42} {'consts':>6} {'history':>12} {'reviewed':>10} {'gaps':>4} {'lit':>5}   {'uncert':>6} {'blocked':>7} {'stale':>5} {'witness':>7} {'lean':>5}"
    print(header)
    print("-" * len(header))
    for r in rows:
        print(
            f"{r['family']:42} {r['constants']:>6} {r['history']:>12} {r['reviewed']:>10} {r['gaps']:>4} "
            f"{r['literature_rows']:>5}   {r['uncertified']:>6} {r['blocked']:>7} {r['stale']:>5} {r['witness']:>7} {r['lean']:>5}"
        )
    print()
    print("history: literature review status from literature/coverage.yml; lit: literature rows in its history")
    print("uncert: current bounds without a verified certificate; blocked: listed in certificates/blocked.yml")
    print("stale: blocked, but the bound improved since it was checked")
    print("witness, lean: uncertified and not blocked, by what could certify them (witnesses are usually more tractable)")

    if family_filter:
        for r in rows:
            entry = coverage.get(r["family"])
            if entry:
                print(f"\nLiterature reviewed {entry['reviewed']} from: {', '.join(entry['sources'])}")
                for gap in entry["gaps"]:
                    print(f"  gap: {gap}")
            print("\nUncertified current bounds:")
            for u in r["items"]:
                status = ""
                if u.get("blocked"):
                    b = u["blocked"]
                    status = f"  [{'stale: ' if b['stale'] else ''}{b['reason']}, checked {b['checked']}]"
                print(f"  {u['constant']} {u['bound']} {u['value']['latex']} ({u['certify_with']}, {u['evidence']}){status}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--family", help="report on one family, listing its uncertified bounds")
    report(parser.parse_args().family)
