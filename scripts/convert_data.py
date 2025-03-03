"""Convert YAML data to other formats for download."""

import json
import pandas as pd
import yaml

def flatten_value_dict(data_dict, field_name):
    """Flatten a value dictionary into separate fields for CSV export."""
    for subfield in ['latex', 'decimal_approx', 'alt_display']:
        if data_dict[field_name] is not None and subfield in data_dict[field_name]:
            data_dict[f"{field_name}_{subfield}"] = data_dict[field_name][subfield]
        else:
            data_dict[f"{field_name}_{subfield}"] = None
    del data_dict[field_name]

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

with open("_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

with open("_data/updates.yml", "r") as file:
    updates = yaml.safe_load(file)

# Remove extraneous fields
for constant in constants.values():
    if 'image' in constant:
        del constant['image']
for group in groups.values():
    if 'display_rows' in group:
        del group['display_rows']
    if 'display_columns' in group:
        del group['display_columns']
    if 'parameter_values' in group:
        del group['parameter_values']
    if 'representative_image' in group:
        del group['representative_image']

# Export nested data structures to YAML
with open("data/constants.yml", "w") as f:
    yaml.dump(constants, f, sort_keys=False)

with open("data/constant_groups.yml", "w") as f:
    yaml.dump(groups, f, sort_keys=False)

with open("data/sources.yml", "w") as f:
    yaml.dump(sources, f, sort_keys=False)

with open("data/updates.yml", "w") as f:
    yaml.dump(updates, f, sort_keys=False)

# Export nested data structures to JSON
with open("data/constants.json", "w") as f:
    json.dump(constants, f, indent=2)

with open("data/constant_groups.json", "w") as f:
    json.dump(groups, f, indent=2)

with open("data/sources.json", "w") as f:
    json.dump(sources, f, indent=2)

with open("data/updates.json", "w") as f:
    json.dump(updates, f, indent=2)

# Convert constants to CSV and TSV
constants_list = []
for constant_id, constant_data in constants.items():
    constant_dict = {'id': constant_id}
    for k, v in constant_data.items():
        if k not in ['updates', 'description']:
            constant_dict[k] = v
    
    # Flatten nested value dictionaries
    flatten_value_dict(constant_dict, 'exact_value')
    flatten_value_dict(constant_dict, 'lower_bound')
    flatten_value_dict(constant_dict, 'upper_bound')
            
    constants_list.append(constant_dict)

constants_df = pd.DataFrame(constants_list)
constants_df.to_csv("data/constants.csv", index=False)
constants_df.to_csv("data/constants.tsv", sep="\t", index=False)

# Convert constant groups to CSV and TSV
groups_list = []
for group_id, group_data in groups.items():
    group_dict = {'id': group_id}
    for k, v in group_data.items():
        if k == 'stats':
            for stat_k, stat_v in v.items():
                group_dict[f'stats_{stat_k}'] = stat_v
        elif k == 'external_ids':
            for id_k, id_v in v.items():
                group_dict[f'id_{id_k}'] = id_v
        else:
            group_dict[k] = v
    groups_list.append(group_dict)
groups_df = pd.DataFrame(groups_list)
groups_df.to_csv("data/constant_groups.csv", index=False)
groups_df.to_csv("data/constant_groups.tsv", sep="\t", index=False)

# Convert sources to CSV and TSV
sources_list = []
for source_id, source_data in sources.items():
    source_dict = {'id': source_id}
    source_dict.update(source_data)
    sources_list.append(source_dict)
sources_df = pd.DataFrame(sources_list)
sources_df.to_csv("data/sources.csv", index=False)
sources_df.to_csv("data/sources.tsv", sep="\t", index=False)

# Convert updates to CSV and TSV
updates_list = []
for update in updates:
    update_dict = update.copy()
    flatten_value_dict(update_dict, 'value')
    updates_list.append(update_dict)
    
updates_df = pd.DataFrame(updates_list)
updates_df.to_csv("data/updates.csv", index=False)
updates_df.to_csv("data/updates.tsv", sep="\t", index=False)
