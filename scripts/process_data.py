"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Find most recent updates for each constant's bounds or exact value.
4. Process images for constants.
5. Add statistics to each constant group.
"""

import itertools
import pathlib
import yaml
import csv
from utils import Value, QuotedString, process_constant_images


def quoted_string_representer(dumper, data):
    return dumper.represent_scalar('tag:yaml.org,2002:str', data, style="'")

# Register the representer
yaml.add_representer(QuotedString, quoted_string_representer)


def load_updates(updates_dir: str, sources: dict) -> list[dict]:
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
        constant["exact_value"] = None
        constant["lower_bound"] = None
        constant["upper_bound"] = None
        constant["updates"] = []
        
    for update in updates:
        constant = constants[update["constant"]]
        if constant["exact_value"] is not None:
            print(f"Invalid update for constant with exact value: {update}")
            raise AssertionError("Constant already has an exact value")
            
        update_copy = update.copy()
        del update_copy["constant"]
        update_copy["value"] = update_copy["value"].to_dict()
        constant["updates"].append(update_copy)
        
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
    
    # Calculate percentages
    if stats["total_updates"] > 0:
        stats["source_coverage"] = round(
            stats["updates_with_sources"] / stats["total_updates"] * 100, 2
        )
    else:
        stats["source_coverage"] = 0.00
        
    return stats


def write_constants(constants: dict, filename: str):
    """Write processed constants info to file."""
    for constant in constants.values():
        if constant["exact_value"] is not None:
            constant["exact_value"] = constant["exact_value"].to_dict()
        if constant["lower_bound"] is not None:
            constant["lower_bound"] = constant["lower_bound"].to_dict()
        if constant["upper_bound"] is not None:
            constant["upper_bound"] = constant["upper_bound"].to_dict()
    with open(filename, "w") as file:
        yaml.dump(constants, file, sort_keys=False)


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

# Save combined updates for download
for update in updates:
    update["value"] = update["value"].to_dict()
with open("_data/updates.yml", "w") as file:
    yaml.dump(updates, file, sort_keys=False)

# Save constants for download
write_constants(constants, "_data/constants.yml")

# Add statistics to each group
for group_id, group in groups.items():
    group["stats"] = calculate_group_stats(group_id, constants)

write_groups(groups, "_data/constant_groups.yml")
