"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Find most recent updates for each constant's bounds or exact value.
4. Save constants to _data/constants.yml.
"""

from collections import defaultdict
import itertools
import yaml

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
        assert update["type"] in ["lower_bound", "upper_bound"]
        assert update["value"] is not None
        constant = constants[update["constant"]]
        assert constant["value"] is None, "Constant already has an exact value"
        del update["constant"]
        constant["updates"].append(update)
        assert constant[update["type"]] != update["value"], "Duplicate update"
        constant[update["type"]] = update["value"]
        if constant["lower_bound"] == constant["upper_bound"]:
            constant["value"] = constant["lower_bound"]

with open("_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

with open("source_data/updates.yml", "r") as file:
    updates = yaml.safe_load(file)
for update in updates:
    if "primary_source" in update:
        update["date"] = sources[update["primary_source"]]["date"]
    else:
        update["date"] = None
# List non-dated updates first, as it seems more likely for more recent updates to have known dates
updates.sort(key=lambda x: (x["date"] is not None, x["date"]))

constants = get_constants(groups)
assign_updates_and_values(constants, updates)

with open("_data/constants.yml", "w") as file:
    yaml.dump(constants, file, sort_keys=False)
