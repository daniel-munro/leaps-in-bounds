"""Read raw data and use templates to generate the data files."""

import itertools
import yaml

with open("raw_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

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
        id = group["id"].format(**params)
        constant["name"] = group["name"].format(**params)
        constant["description"] = group["description"].format(**params)
        constants[id] = constant

with open("_data/constants.yml", "w") as file:
    yaml.dump(constants, file, sort_keys=False)
