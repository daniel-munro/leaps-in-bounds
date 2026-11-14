"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Check each constant's updates from the literature for consistency.
4. Attach certificates, then merge them with the updates into each
   constant's history: the bounds discovered over time, each with the record
   of its discovery (a source or a certificate) and its best evidence
   (a verified or attested certificate, or the literature). The current
   bounds are the latest in the history. List the current bounds that aren't
   verified yet, all certificates with their role in the history, and the
   whole history.
6. Process images for constants.
7. Add statistics to each constant group.
8. List who added sources and constant groups, to credit them.
"""

import itertools
import pathlib
import yaml
import csv
from typing import Any, Mapping
from certificates import (
    FAMILIES,
    GITHUB_USERNAME,
    certificate_status,
    is_better,
    load_certificates,
    load_manifest,
)
from utils import Value, QuotedString, process_constant_images


def quoted_string_representer(dumper: yaml.Dumper, data: QuotedString) -> Any:
    return dumper.represent_scalar('tag:yaml.org,2002:str', data, style="'")

# Register the representer
yaml.add_representer(QuotedString, quoted_string_representer)


def load_updates(
    updates_dir: str | pathlib.Path,
    sources: Mapping[str, Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Load updates from a directory of CSV files.

    Args:
        updates_dir: Directory containing CSV files with updates.
        sources: Dictionary of sources.

    Returns:
        List of updates sorted chronologically.
    """
    updates = []
    
    # Get all .csv files in updates directory
    updates_dir = pathlib.Path(updates_dir)
    csv_files = list(updates_dir.glob("*.csv"))
    
    for csv_file in csv_files:
        with open(csv_file, "r", newline='') as file:
            reader = csv.DictReader(file)
            for row in reader:
                update = {
                    k: v if v != '' else None 
                    for k, v in row.items()
                }
                
                # Validate and convert bounds to type and value
                has_lower = update.get('lower_bound') is not None
                has_upper = update.get('upper_bound') is not None
                
                if has_lower == has_upper:
                    raise ValueError(f"Update must have exactly one bound set: {update}")
                
                if has_lower:
                    update['type'] = 'lower_bound'
                    update['value'] = Value(update['lower_bound'])
                else:
                    update['type'] = 'upper_bound'
                    update['value'] = Value(update['upper_bound'])
                
                del update['lower_bound']
                del update['upper_bound']
                
                if update.get('primary_source'):
                    primary_source = sources[update["primary_source"]]
                    update["date"] = primary_source.get("date")
                else:
                    update["date"] = None
                    
                field_order = [
                    "constant",
                    "type",
                    "value",
                    "date",
                    "primary_source",
                    "secondary_source"
                ]
                update = {k: update.get(k) for k in field_order}
                updates.append(update)
                
    # List non-dated updates first, as it seems more likely for more recent updates to have known dates
    # (Multiple updates for the same bound ought to always be dated though.)
    updates.sort(key=lambda x: (x["date"] is not None, x["date"]))
    return updates


def get_constants(groups: Mapping[str, Mapping[str, Any]]) -> dict[str, dict[str, Any]]:
    """Generate constants from constant groups.

    Args:
        groups: Dictionary of constant groups.

    Returns:
        Dictionary of constants.
    """
    constants = {}
    for group_id, group in groups.items():
        # Handle single-constant groups (empty parameters list)
        if not group.get("parameters"):
            constant = {
                "name": group["name"],
                "description": group["description"],
                "group": group_id,
            }
            constants[group_id] = constant
            continue

        param_values = []
        for values in group["parameter_values"]:
            # Some items in values list are numbers, others are length-2 lists
            # giving inclusive ranges. Iterate through all combinations.
            if any(isinstance(v, list) for v in values):
                value_ranges = []
                for v in values:
                    if isinstance(v, list):
                        value_ranges.append(range(v[0], v[1] + 1))
                    else:
                        value_ranges.append([v])
                for values in itertools.product(*value_ranges):
                    param_values.append(values)
            else:
                param_values.append(values)
        for values in param_values:
            params = {p: v for p, v in zip(group["parameters"], values)}
            constant = {}
            id = group["id_template"].format(**params)
            constant["name"] = group["name_template"].format(**params)
            constant["description"] = group["description_template"].format(**params)
            constant["group"] = group_id
            constants[id] = constant
    return constants


def assign_updates_and_values(
    constants: dict[str, dict[str, Any]],
    updates: list[dict[str, Any]],
) -> None:
    """Assign updates and values to constants.

    Args:
        constants: Dictionary of constants.
        updates: List of updates in chronological order to process.
    """
    for constant in constants.values():
        constant["exact_value"] = None
        constant["lower_bound"] = None
        constant["upper_bound"] = None
        constant["updates"] = []
        constant["update_records"] = []
        
    for update in updates:
        constant = constants[update["constant"]]
        if constant["exact_value"] is not None:
            print(f"Invalid update for constant with exact value: {update}")
            raise AssertionError("Constant already has an exact value")
            
        update_copy = update.copy()
        del update_copy["constant"]
        update_copy["value"] = update_copy["value"].to_dict()
        constant["updates"].append(update_copy)
        constant["update_records"].append(update)
        
        bound_type = update["type"]
        bound_value = update["value"]
        
        # Create or update the bound and check if it's an improvement
        # Allow equal decimal approximations in case improvement is beyond the precision limit
        # (or an update like <=0.5 -> <0.5)
        if bound_type == "lower_bound":
            if constant["lower_bound"] is not None:
                if bound_value.less_than(constant["lower_bound"]):
                    raise AssertionError(f"Lower bound is not an improvement")
            constant["lower_bound"] = bound_value
        else:  # upper_bound
            if constant["upper_bound"] is not None:
                if constant["upper_bound"].less_than(bound_value):
                    raise AssertionError(f"Upper bound is not an improvement")
            constant["upper_bound"] = bound_value
        
        # Check if bounds are now equal, indicating an exact value
        if (constant["lower_bound"] and constant["upper_bound"] and 
            constant["lower_bound"].latex == constant["upper_bound"].latex):
            constant["exact_value"] = constant["lower_bound"]
            
        # Check if bounds are inconsistent
        if (constant["lower_bound"] and constant["upper_bound"] and 
            constant["upper_bound"].less_than(constant["lower_bound"])):
            raise AssertionError(f"Lower bound exceeds upper bound")


def attach_certificates(
    constants: dict[str, dict[str, Any]],
    certificates: Mapping[str, Mapping[str, Any]],
    manifest: Mapping[str, Mapping[str, Any]],
) -> None:
    """Attach certificates to constants, with their status.

    A certificate is verified if the manifest records that a trusted verifier
    checked its evidence, and attested if it cites someone else's published
    checker instead (see scripts/check_certificates.py, which runs in CI).
    Certificates that are neither, awaiting verification, are left out.

    Args:
        constants: Dictionary of constants.
        certificates: Dictionary of certificates.
        manifest: Manifest of verified certificates.
    """
    for constant in constants.values():
        constant["certifiable"] = constant["group"] in FAMILIES
        constant["certificates"] = []

    left_out = 0
    for cert in sorted(certificates.values(), key=lambda c: (c["date"], c["id"])):
        if cert["constant"] not in constants:
            raise ValueError(f"Certificate {cert['id']} is for unknown constant {cert['constant']}")
        status = certificate_status(cert, manifest)
        if status not in ("verified", "attested"):
            left_out += 1
            continue
        fields = ["id", "bound", "value", "kind", "submitted_by", "date", "source", "notes", "path", "attestation"]
        summary = {k: cert[k] for k in fields if k in cert}
        summary["status"] = status
        summary["approx"] = cert["approx"]
        if cert["kind"] == "lean":
            summary["theorem"] = cert["lean"]["theorem"]
        constants[cert["constant"]]["certificates"].append(summary)

    if left_out:
        print(f"Leaving out {left_out} certificates awaiting verification")


# How strong each kind of evidence is: checked here, checked elsewhere with a
# published checker, or a source's word for it.
EVIDENCE_RANK = {"verified": 3, "attested": 2, "literature": 1}


def rounded(approx: int | float) -> int | float:
    """Round a certificate's value like literature values: integers exactly,
    other values to 7 significant digits."""
    if float(approx).is_integer():
        return int(approx)
    return float(f"{approx:.7g}")


def at_least_as_strong(side: str, a: float | None, b: float | None) -> bool:
    """Whether bound value a is at least as strong as b (False if either is unknown)."""
    if a is None or b is None:
        return False
    return a >= b if side == "lower" else a <= b


def bound_events(
    side: str,
    updates: list[Mapping[str, Any]],
    certificates: list[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """Merge one side's literature updates and certificates into the bounds
    discovered over time, each with its discovery and best evidence.

    A record (an update citing a source, or a certificate) is a discovery when
    it improves on every earlier record. Ties in date go to the source, and
    undated updates come first. A literature update that doesn't improve on
    an earlier certificate isn't a discovery. Updates that only match an
    earlier literature bound to the precision of the decimal approximation
    still count, as before, since the literature was checked on its own.

    The best evidence for a bound comes from the strongest record at that
    value or a stronger one, since evidence for a stronger bound proves the
    weaker one too: a verified certificate, then an attested one, then the
    literature. Ties go to a certificate for exactly that value, then the
    earliest.
    """
    records = [("source", u, u["value"].decimal_approx, u["date"]) for u in updates]
    records += [("certificate", c, rounded(c["approx"]), c["date"]) for c in certificates]
    records.sort(key=lambda r: (r[3] is not None, r[3] or "", r[0] != "source"))

    events = []
    best_approx, best_kind = None, None
    for kind, record, approx, date in records:
        if events and best_approx is not None and approx is not None:
            if kind == "source" and best_kind == "source":
                improves = at_least_as_strong(side, approx, best_approx)
            else:
                improves = is_better(side, approx, best_approx)
        else:
            # Incomparable values: trust the literature's order
            improves = kind == "source" or not events
        if not improves:
            continue
        if kind == "source":
            value = record["value"]
            discovery = {
                "kind": "source",
                "id": record["primary_source"],
                "via": record["secondary_source"],
                "date": date,
            }
        else:
            value = Value(str(record["value"]))
            discovery = {
                "kind": "certificate",
                "id": record["id"],
                "via": None,
                "date": date,
                "submitted_by": record["submitted_by"],
            }
        events.append({"type": f"{side}_bound", "value": value, "date": date, "discovery": discovery})
        best_approx, best_kind = approx, kind

    for event in events:
        approx = event["value"].decimal_approx
        candidates = [
            c for c in certificates
            if at_least_as_strong(side, rounded(c["approx"]), approx)
        ]
        candidates.sort(key=lambda c: (
            -EVIDENCE_RANK[c["status"]],
            Value(str(c["value"])).latex != event["value"].latex,
            c["date"],
            c["id"],
        ))
        if candidates:
            cert = candidates[0]
            evidence = {
                "tier": cert["status"],
                "kind": cert["kind"],
                "certificate": cert["id"],
                "source": None,
                "value": Value(str(cert["value"])) if str(cert["value"]) != event["value"].latex else None,
                "date": cert["date"],
            }
        else:
            discovery = event["discovery"]
            evidence = {
                "tier": "literature",
                "kind": None,
                "certificate": None,
                "source": discovery["id"] or discovery["via"],
                "value": None,
                "date": discovery["date"],
            }
        event["evidence"] = evidence
    return events


def build_histories(constants: dict[str, dict[str, Any]]) -> None:
    """Give each constant its history of bounds, merging the literature and
    certificates, and set its current bounds, their evidence, and its exact
    value from it.

    Call after assign_updates_and_values and attach_certificates. Sets, for
    each side, {side}_bound (the latest bound), {side}_bound_evidence (its
    best evidence) and verified_{side}_bound with verified_{side}_certificate
    (the strongest verified certificate, which may be weaker).
    """
    for constant in constants.values():
        history = []
        for side in ["lower", "upper"]:
            updates = [u for u in constant["update_records"] if u["type"] == f"{side}_bound"]
            certs = [c for c in constant["certificates"] if c["bound"] == side]
            events = bound_events(side, updates, certs)
            history += events
            last = events[-1] if events else None
            constant[f"{side}_bound"] = last["value"] if last else None
            constant[f"{side}_bound_evidence"] = last["evidence"]["tier"] if last else None
            cert = None
            for c in certs:  # In date order, so ties go to the earliest
                if c["status"] == "verified" and (cert is None or is_better(side, c["approx"], cert["approx"])):
                    cert = c
            constant[f"verified_{side}_bound"] = Value(str(cert["value"])) if cert else None
            constant[f"verified_{side}_certificate"] = cert["id"] if cert else None
        history.sort(key=lambda e: (e["date"] is not None, e["date"] or ""))
        constant["history"] = history
        lower, upper = constant["lower_bound"], constant["upper_bound"]
        constant["exact_value"] = lower if lower is not None and upper is not None and (
            lower.latex == upper.latex
            or lower.decimal_approx is not None and lower.decimal_approx == upper.decimal_approx
        ) else None
        del constant["update_records"]


def find_unverified_bounds(constants: Mapping[str, Mapping[str, Any]]) -> list[dict[str, Any]]:
    """List the current bounds whose best evidence isn't verified yet, for
    constants in families that accept certificates.

    Each entry gives the bound, its discovery and best evidence, the
    strongest verified bound if any, and whether a witness can certify it or
    it needs a Lean proof. Call after build_histories, before the values are
    written out.
    """
    unverified = []
    for constant_id, constant in constants.items():
        if not constant["certifiable"]:
            continue
        family = FAMILIES[constant["group"]]
        for side in ["lower", "upper"]:
            events = [e for e in constant["history"] if e["type"] == f"{side}_bound"]
            if not events or events[-1]["evidence"]["tier"] == "verified":
                continue
            event = events[-1]
            if event["value"].decimal_approx is None:
                continue
            verified = constant[f"verified_{side}_bound"]
            unverified.append({
                "constant": constant_id,
                "group": constant["group"],
                "bound": side,
                "value": event["value"].to_dict(),
                "date": event["date"],
                "discovery_kind": event["discovery"]["kind"],
                "discovery": event["discovery"]["id"],
                "via": event["discovery"]["via"],
                "evidence": event["evidence"]["tier"],
                "evidence_certificate": event["evidence"]["certificate"],
                "verified": verified.to_dict() if verified is not None else None,
                "verified_certificate": constant[f"verified_{side}_certificate"],
                "certify_with": "witness" if family.witness_bound == side else "lean",
            })
    return unverified


def list_certificates(constants: Mapping[str, Mapping[str, Any]]) -> list[dict[str, Any]]:
    """List all certificates, newest first, with the role each plays in its
    constant's history: "discovery" when it established a new bound,
    "evidence" when it's the best evidence for a bound discovered earlier,
    "superseded" when other certificates are better evidence for every bound
    it proves, or "weaker" when it's weaker than every recorded bound.
    "current" says whether it's the best evidence for the current bound.
    Call after build_histories, before the values are written out.
    """
    rows = []
    for constant_id, constant in constants.items():
        for cert in constant["certificates"]:
            side = cert["bound"]
            events = [e for e in constant["history"] if e["type"] == f"{side}_bound"]
            discovered = next((e for e in events if e["discovery"]["kind"] == "certificate"
                               and e["discovery"]["id"] == cert["id"]), None)
            supported = [e for e in events if e["evidence"]["certificate"] == cert["id"]]
            if discovered is not None:
                role, event = "discovery", discovered
            elif supported:
                role, event = "evidence", supported[-1]
            elif any(at_least_as_strong(side, rounded(cert["approx"]), e["value"].decimal_approx) for e in events):
                role, event = "superseded", None
            else:
                role, event = "weaker", None
            cert["role"] = role
            rows.append({
                "id": cert["id"],
                "constant": constant_id,
                "group": constant["group"],
                "bound": side,
                "value": Value(str(cert["value"])).to_dict(),
                "kind": cert["kind"],
                "submitted_by": cert["submitted_by"],
                "date": cert["date"],
                "status": cert["status"],
                "role": role,
                "current": bool(events) and events[-1]["evidence"]["certificate"] == cert["id"],
                "event_date": event["date"] if event else None,
                "event_discovery": event["discovery"]["id"] if event else None,
                "attested_by": cert["attestation"]["by"] if "attestation" in cert else None,
                "checker": cert["attestation"]["checker"] if "attestation" in cert else None,
                "source": cert.get("source"),
                "path": cert["path"],
            })
    rows.sort(key=lambda row: row["id"])
    rows.sort(key=lambda row: row["date"], reverse=True)
    return rows


def list_history(constants: Mapping[str, Mapping[str, Any]]) -> list[dict[str, Any]]:
    """Flatten every constant's history into one list of bounds in
    chronological order, for download and the visualizations. Call after
    build_histories, before the values are written out."""
    rows = []
    for constant_id, constant in constants.items():
        for event in constant["history"]:
            discovery, evidence = event["discovery"], event["evidence"]
            rows.append({
                "constant": constant_id,
                "type": event["type"],
                "value": event["value"].to_dict(),
                "date": event["date"],
                "discovery_kind": discovery["kind"],
                "discovery": discovery["id"],
                "via": discovery["via"],
                "evidence": evidence["tier"],
                "evidence_kind": evidence["kind"],
                "evidence_certificate": evidence["certificate"],
                "evidence_source": evidence["source"],
            })
    rows.sort(key=lambda row: (row["date"] is not None, row["date"] or ""))
    return rows


def calculate_group_stats(
    group_id: str,
    constants: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Calculate statistics for a constant group.

    Args:
        group_id: ID of the constant group.
        constants: Dictionary of all constants.

    Returns:
        Dictionary containing group statistics.
    """
    stats = {
        "total_constants": 0,
        "exact_values": 0,
        "bounded": 0,
        "half_bounded": 0,
        "unbounded": 0,
        "total_updates": 0,
        "updates_with_sources": 0,
        "verified_bounds": 0,
        "attested_bounds": 0,
        "literature_bounds": 0,
    }
    
    # Find constants belonging to this group
    group_constants = {
        id: const for id, const in constants.items()
        if const["group"] == group_id
    }
    
    stats["total_constants"] = len(group_constants)
    
    # Analyze constant values
    for const in group_constants.values():
        if const["exact_value"] is not None:
            stats["exact_values"] += 1
        elif const["lower_bound"] is not None and const["upper_bound"] is not None:
            stats["bounded"] += 1
        elif const["lower_bound"] is not None or const["upper_bound"] is not None:
            stats["half_bounded"] += 1
        else:
            stats["unbounded"] += 1
            
        # Count updates and their sources
        stats["total_updates"] += len(const["updates"])
        stats["updates_with_sources"] += sum(
            1 for update in const["updates"] 
            if update.get("primary_source") is not None
        )
        # Count current bounds by their best evidence
        for side in ["lower", "upper"]:
            tier = const[f"{side}_bound_evidence"]
            if tier is not None:
                stats[f"{tier}_bounds"] += 1
    
    # Calculate percentages
    if stats["total_updates"] > 0:
        stats["source_coverage"] = round(
            stats["updates_with_sources"] / stats["total_updates"] * 100, 2
        )
    else:
        stats["source_coverage"] = 0.00
        
    return stats


def list_literature_contributors(
    groups: Mapping[str, Mapping[str, Any]],
    sources: Mapping[str, Mapping[str, Any]],
    updates: list[Mapping[str, Any]],
) -> list[dict[str, Any]]:
    """List the GitHub accounts credited with `added_by` on sources and
    constant groups, with the groups and sources each added and the number
    of updates citing their sources as the primary source. Most first.
    """
    contributors: dict[str, dict[str, Any]] = {}

    def credit(kind: str, item_id: str, item: Mapping[str, Any]) -> dict[str, Any] | None:
        username = item.get("added_by")
        if username is None:
            return None
        if not isinstance(username, str) or not GITHUB_USERNAME.fullmatch(username):
            raise ValueError(f"{kind} {item_id}: added_by must be a GitHub username")
        return contributors.setdefault(
            username, {"contributor": username, "groups": [], "sources": [], "updates": 0}
        )

    for group_id, group in groups.items():
        contributor = credit("Constant group", group_id, group)
        if contributor is not None:
            contributor["groups"].append(group_id)
    for source_id, source in sources.items():
        contributor = credit("Source", source_id, source)
        if contributor is not None:
            contributor["sources"].append(source_id)
    for update in updates:
        source = sources.get(update["primary_source"]) if update["primary_source"] else None
        if source is not None and source.get("added_by") in contributors:
            contributors[source["added_by"]]["updates"] += 1
    return sorted(
        contributors.values(),
        key=lambda c: (-len(c["groups"]), -c["updates"], -len(c["sources"]), c["contributor"].lower()),
    )


def write_constants(constants: dict[str, dict[str, Any]], filename: str) -> None:
    """Write processed constants info to a YAML file."""
    value_fields = ["exact_value", "lower_bound", "upper_bound", "verified_lower_bound", "verified_upper_bound"]
    for constant in constants.values():
        for field in value_fields:
            if constant[field] is not None:
                constant[field] = constant[field].to_dict()
        for cert in constant["certificates"]:
            del cert["approx"]
        for event in constant["history"]:
            event["value"] = event["value"].to_dict()
            if event["evidence"]["value"] is not None:
                event["evidence"]["value"] = event["evidence"]["value"].to_dict()
    with open(filename, "w") as file:
        yaml.dump(constants, file, sort_keys=False)


def write_groups(groups: dict[str, dict[str, Any]], filename: str) -> None:
    """Write processed constant groups info to a YAML file, with compact lists."""
    # Set compact list representer
    def compact_lists_representer(dumper, data):
        return dumper.represent_sequence('tag:yaml.org,2002:seq', data, flow_style=True)
    yaml.add_representer(list, compact_lists_representer)
    # Write groups with compact lists
    with open(filename, "w") as file:
        yaml.dump(groups, file, sort_keys=False)
    # Restore default list representer
    default_representer = yaml.representer.SafeRepresenter.represent_list
    yaml.add_representer(list, default_representer)


def main() -> None:
    with open("source_data/constant_groups.yml", "r") as file:
        groups = yaml.safe_load(file)

    with open("_data/sources.yml", "r") as file:
        sources = yaml.safe_load(file)

    # Load source data for constants (for image metadata)
    with open('source_data/constants.yml', 'r') as file:
        constants_metadata = yaml.safe_load(file) or {}

    updates = load_updates("source_data/updates", sources)

    constants = get_constants(groups)
    assign_updates_and_values(constants, updates)

    # Cache images and update constants with image metadata
    process_constant_images(constants_metadata)
    for constant_id, data in constants_metadata.items():
        if data:
            for field in data:
                constants[constant_id][field] = data[field]

    certificates = load_certificates()
    attach_certificates(constants, certificates, load_manifest())
    build_histories(constants)
    with open("_data/unverified_bounds.yml", "w") as file:
        yaml.dump(find_unverified_bounds(constants), file, sort_keys=False)
    with open("_data/certificates.yml", "w") as file:
        yaml.dump(list_certificates(constants), file, sort_keys=False)
    with open("_data/history.yml", "w") as file:
        yaml.dump(list_history(constants), file, sort_keys=False)

    with open("_data/literature_contributors.yml", "w") as file:
        yaml.dump(list_literature_contributors(groups, sources, updates), file, sort_keys=False)

    # Save combined updates for download
    for update in updates:
        update["value"] = update["value"].to_dict()
    with open("_data/updates.yml", "w") as file:
        yaml.dump(updates, file, sort_keys=False)

    # Save constants for download
    write_constants(constants, "_data/constants.yml")

    # Add category to each group
    with open("source_data/categories.yml", "r") as file:
        categories = yaml.safe_load(file)
    for category in categories:
        for group_id in category["groups"]:
            groups[group_id]["category"] = f"{category['msc']} {category['name']}"

    # Add statistics to each group
    for group_id, group in groups.items():
        group["stats"] = calculate_group_stats(group_id, constants)

    write_groups(groups, "_data/constant_groups.yml")


if __name__ == "__main__":
    main()
