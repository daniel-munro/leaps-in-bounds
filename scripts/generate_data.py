"""Read source data and use templates to generate the data files.

1. Generate list of constants from constant groups.
2. Use sources to assign dates to updates.
3. Find most recent updates for each constant's bounds or exact value.
4. Save constants to _data/constants.yml.
"""

from collections import defaultdict
import itertools
import yaml

def get_latest_updates(updates):
    """For each constant, find the most recent lower bound and upper bound or exact value
    
    Most recent should also be best, but values may be expressed as strings
    (e.g. involving log or roots), so easier to use the most recent value.
    """
    values = defaultdict(dict)
    for update in updates:
        constant = update["constant"]
        update_type = update["type"]
        update["date"] = sources[update["primary_source"]]["date"]
        if update_type in values[constant]:
            assert update_type != "exact" # Exact values should only be discovered once

            # Compare dates for bounds
            existing_date = values[constant][update_type]["date"]
            new_date = update["date"]
            
            # Convert YYYY-MM-DD to YYYY for comparison if needed
            existing_year = existing_date[:4]
            new_year = new_date[:4]
            
            # Replace only if new date is more recent
            if new_year > existing_year or new_date > existing_date:
                values[constant][update_type] = update

        else:
            values[constant][update_type] = update
    return values

def get_constants(groups):
    constants = {}
    for group in groups:
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

def assign_current_values(constants, latest_updates):
    for id, constant in constants.items():
        latest = latest_updates[id]
        for type in ["lower_bound", "upper_bound", "exact"]:
            field = "value" if type == "exact" else type
            if type in latest:
                constant[field] = latest[type]["value"]
            else:
                constant[field] = None

with open("_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

with open("_data/updates.yml", "r") as file:
    updates = yaml.safe_load(file)

constants = get_constants(groups)
latest_updates = get_latest_updates(updates)
assign_current_values(constants, latest_updates)

with open("_data/constants.yml", "w") as file:
    yaml.dump(constants, file, sort_keys=False)

# for group in groups:
#     del group["id_template"]
#     del group["name_template"]
#     del group["description_template"]

# with open("_data/constant_groups.yml", "w") as file:
#     yaml.dump(groups, file, sort_keys=False)
