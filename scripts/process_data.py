"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Save all updates to _data/updates.yml.
4. Find most recent updates for each constant's bounds or exact value.
5. Save constants to _data/constants.yml.
6. Add statistics to each constant group.
7. Save constant groups to _data/constant_groups.yml.
"""

from collections import defaultdict
import itertools
import pathlib
import yaml

def load_updates(updates_dir: str, sources: dict) -> list[dict]:
    """Load updates from a directory of YAML files.

    Args:
        updates_dir: Directory containing YAML files with updates.
        sources: Dictionary of sources.

    Returns:
        List of updates sorted chronologically.
    """
    updates = []
    
    # Get all .yml and .yaml files in updates directory
    updates_dir = pathlib.Path(updates_dir)
    yaml_files = list(updates_dir.glob("*.yml")) + list(updates_dir.glob("*.yaml"))
    
    for yaml_file in yaml_files:
        with open(yaml_file, "r") as file:
            updates_by_source = yaml.safe_load(file)
        if updates_by_source is None:
            continue
            
        for source_id, source_updates in updates_by_source.items():
            for update in source_updates:
                if source_id != "none":
                    update["secondary_source"] = source_id
                if "primary_source" in update:
                    primary_source = sources[update["primary_source"]]
                    if "date" in primary_source:
                        update["date"] = primary_source["date"]
                    else:
                        update["date"] = None
                else:
                    update["date"] = None
                updates.append(update)
                
    # List non-dated updates first, as it seems more likely for more recent updates to have known dates
    # (Multiple updates for the same bound ought to always be dated though.)
    updates.sort(key=lambda x: (x["date"] is not None, x["date"]))
    return updates

def get_constants(groups: dict) -> dict:
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
                "description": group["description"]
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
            constants[id] = constant
    return constants

def assign_updates_and_values(constants: dict, updates: list[dict]):
    """Assign updates and values to constants.

    Args:
        constants: Dictionary of constants.
        updates: List of updates in chronological order to process.
    """
    for constant in constants.values():
        constant["updates"] = []
        constant["value"] = None
        constant["lower_bound"] = None
        constant["upper_bound"] = None
    for update in updates:
        assert not ("lower_bound" in update and "upper_bound" in update), "Update cannot have both bounds"
        assert "lower_bound" in update or "upper_bound" in update, "Update must have one bound"
        bound_type = "lower_bound" if "lower_bound" in update else "upper_bound"
        bound_value = update[bound_type]
        assert bound_value is not None
        constant = constants[update["constant"]]
        assert constant["value"] is None, "Constant already has an exact value"
        update_copy = update.copy()
        del update_copy["constant"]
        constant["updates"].append(update_copy)
        assert constant[bound_type] != bound_value, "Duplicate update"
        constant[bound_type] = bound_value
        if constant["lower_bound"] == constant["upper_bound"]:
            constant["value"] = constant["lower_bound"]

def calculate_group_stats(group_id: str, constants: dict) -> dict:
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
    }
    
    # Find constants belonging to this group
    group_constants = {
        id: const for id, const in constants.items() 
        if id.startswith(group_id)
    }
    
    stats["total_constants"] = len(group_constants)
    
    # Analyze constant values
    for const in group_constants.values():
        if const["value"] is not None:
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
            if "primary_source" in update
        )
    
    # Calculate percentages
    if stats["total_updates"] > 0:
        stats["source_coverage"] = round(
            stats["updates_with_sources"] / stats["total_updates"] * 100, 2
        )
    else:
        stats["source_coverage"] = 0.00
        
    return stats

def write_groups(groups: dict, filename: str):
    """Write processed constant groups info to file, with compact lists."""
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

with open("source_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

updates = load_updates("source_data/updates", sources)

# Save combined updates for download
with open("_data/updates.yml", "w") as file:
    yaml.dump(updates, file, sort_keys=False)

constants = get_constants(groups)
assign_updates_and_values(constants, updates)

with open("_data/constants.yml", "w") as file:
    yaml.dump(constants, file, sort_keys=False)

# Add statistics to each group
for group_id, group in groups.items():
    group["stats"] = calculate_group_stats(group_id, constants)

write_groups(groups, "_data/constant_groups.yml")
