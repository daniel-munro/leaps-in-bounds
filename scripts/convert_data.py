"""Convert YAML data to other formats for download."""

import json
import pandas as pd
import yaml
from typing import Any, MutableMapping

def flatten_value_dict(data_dict: MutableMapping[str, Any], field_name: str) -> None:
    """Flatten a value dictionary into separate fields for CSV export."""
    for subfield in ['latex', 'decimal_approx', 'alt_display']:
        if data_dict[field_name] is not None and subfield in data_dict[field_name]:
            data_dict[f"{field_name}_{subfield}"] = data_dict[field_name][subfield]
        else:
            data_dict[f"{field_name}_{subfield}"] = None
    del data_dict[field_name]

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

with open("_data/families.yml", "r") as file:
    families = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

with open("_data/updates.yml", "r") as file:
    updates = yaml.safe_load(file)

with open("_data/unverified_bounds.yml", "r") as file:
    unverified = yaml.safe_load(file)

with open("_data/certificates.yml", "r") as file:
    certificates = yaml.safe_load(file)

with open("_data/history.yml", "r") as file:
    history = yaml.safe_load(file)

# Remove extraneous fields
for constant in constants.values():
    if 'image' in constant:
        del constant['image']
for family in families.values():
    if 'display_rows' in family:
        del family['display_rows']
    if 'display_columns' in family:
        del family['display_columns']
    if 'parameter_values' in family:
        del family['parameter_values']
    if 'representative_image' in family:
        del family['representative_image']

# Export nested data structures to YAML
with open("data/constants.yml", "w") as f:
    yaml.dump(constants, f, sort_keys=False)

with open("data/families.yml", "w") as f:
    yaml.dump(families, f, sort_keys=False)

with open("data/sources.yml", "w") as f:
    yaml.dump(sources, f, sort_keys=False)

with open("data/updates.yml", "w") as f:
    yaml.dump(updates, f, sort_keys=False)

with open("data/unverified_bounds.yml", "w") as f:
    yaml.dump(unverified, f, sort_keys=False)

with open("data/certificates.yml", "w") as f:
    yaml.dump(certificates, f, sort_keys=False)

with open("data/history.yml", "w") as f:
    yaml.dump(history, f, sort_keys=False)

# Export nested data structures to JSON
with open("data/constants.json", "w") as f:
    json.dump(constants, f, indent=2)

with open("data/families.json", "w") as f:
    json.dump(families, f, indent=2)

with open("data/sources.json", "w") as f:
    json.dump(sources, f, indent=2)

with open("data/updates.json", "w") as f:
    json.dump(updates, f, indent=2)

with open("data/unverified_bounds.json", "w") as f:
    json.dump(unverified, f, indent=2)

with open("data/certificates.json", "w") as f:
    json.dump(certificates, f, indent=2)

with open("data/history.json", "w") as f:
    json.dump(history, f, indent=2)

# Convert constants to CSV and TSV
constants_list = []
for constant_id, constant_data in constants.items():
    constant_dict = {'id': constant_id}
    for k, v in constant_data.items():
        if k not in ['updates', 'history', 'description', 'certificates']:
            constant_dict[k] = v
    
    # Flatten nested value dictionaries
    flatten_value_dict(constant_dict, 'exact_value')
    flatten_value_dict(constant_dict, 'lower_bound')
    flatten_value_dict(constant_dict, 'upper_bound')
    flatten_value_dict(constant_dict, 'verified_lower_bound')
    flatten_value_dict(constant_dict, 'verified_upper_bound')
            
    constants_list.append(constant_dict)

constants_df = pd.DataFrame(constants_list)
constants_df.to_csv("data/constants.csv", index=False)
constants_df.to_csv("data/constants.tsv", sep="\t", index=False)

# Convert families to CSV and TSV
families_list = []
for family_id, family_data in families.items():
    family_dict = {'id': family_id}
    for k, v in family_data.items():
        if k == 'stats':
            for stat_k, stat_v in v.items():
                family_dict[f'stats_{stat_k}'] = stat_v
        elif k == 'external_ids':
            for id_k, id_v in v.items():
                family_dict[f'id_{id_k}'] = id_v
        else:
            family_dict[k] = v
    families_list.append(family_dict)
families_df = pd.DataFrame(families_list)
families_df.to_csv("data/families.csv", index=False)
families_df.to_csv("data/families.tsv", sep="\t", index=False)

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

# Convert unverified bounds to CSV and TSV
unverified_list = []
for row in unverified:
    row_dict = row.copy()
    flatten_value_dict(row_dict, 'value')
    flatten_value_dict(row_dict, 'verified')
    unverified_list.append(row_dict)

unverified_df = pd.DataFrame(unverified_list)
unverified_df.to_csv("data/unverified_bounds.csv", index=False)
unverified_df.to_csv("data/unverified_bounds.tsv", sep="\t", index=False)

# Convert certificates to CSV and TSV
certificates_list = []
for row in certificates:
    row_dict = row.copy()
    flatten_value_dict(row_dict, 'value')
    certificates_list.append(row_dict)

certificates_df = pd.DataFrame(certificates_list)
certificates_df.to_csv("data/certificates.csv", index=False)
certificates_df.to_csv("data/certificates.tsv", sep="\t", index=False)

# Convert the history of bounds to CSV and TSV
history_list = []
for row in history:
    row_dict = row.copy()
    flatten_value_dict(row_dict, 'value')
    history_list.append(row_dict)

history_df = pd.DataFrame(history_list)
history_df.to_csv("data/history.csv", index=False)
history_df.to_csv("data/history.tsv", sep="\t", index=False)
