"""Convert YAML data to other formats for download."""

import pandas as pd
import yaml

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

with open("_data/constant_groups.yml", "r") as file:
    groups = yaml.safe_load(file)

with open("_data/sources.yml", "r") as file:
    sources = yaml.safe_load(file)

with open("_data/updates.yml", "r") as file:
    updates = yaml.safe_load(file)

# Convert constants to CSV and TSV
constants_list = []
for constant_id, constant_data in constants.items():
    constant_dict = {'id': constant_id}
    for k, v in constant_data.items():
        if k not in ['updates', 'description']:
            constant_dict[k] = v
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
updates_df = pd.DataFrame(updates)
updates_df.to_csv("data/updates.csv", index=False)
updates_df.to_csv("data/updates.tsv", sep="\t", index=False)
