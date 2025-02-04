"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Find most recent updates for each constant's bounds or exact value.
4. Save constants to _data/constants.yml.
"""

from collections import defaultdict
import itertools
import pathlib
import yaml

def load_updates(updates_dir: str, sources: dict) -> list[dict]:
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
                update["secondary_source"] = source_id
                if "primary_source" in update:
                    update["date"] = sources[update["primary_source"]]["date"]
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
    for group in groups.values():
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

with open("_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

updates = load_updates("source_data/updates", sources)
constants = get_constants(groups)
assign_updates_and_values(constants, updates)

with open("_data/constants.yml", "w") as file:
    yaml.dump(constants, file, sort_keys=False)
