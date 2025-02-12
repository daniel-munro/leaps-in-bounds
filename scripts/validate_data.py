"""Check for issues with the data."""

import yaml

# Create custom loader to check for duplicates
class DuplicateKeyCheckLoader(yaml.SafeLoader):
    def construct_mapping(self, node, deep=False):
        mapping = {}
        for key_node, value_node in node.value:
            key = self.construct_object(key_node)
            if key in mapping:
                raise ValueError(f"Duplicate key found in YAML: {key}")
            mapping[key] = self.construct_object(value_node)
        return mapping

with open('_data/sources.yml') as f:
    sources = yaml.load(f, Loader=DuplicateKeyCheckLoader)

# Check for missing dates and strings
missing_dates = [id for id, source in sources.items() if 'date' not in source]
missing_strings = [id for id, source in sources.items() if 'string' not in source]

if missing_dates:
    print(f"Warning: {len(missing_dates)} sources are missing dates")
if missing_strings:
    print(f"Warning: {len(missing_strings)} sources are missing string representations")
