"""Check for issues with the data."""

import yaml

# Load sources
with open('_data/sources.yml') as f:
    sources = yaml.safe_load(f)

# Check for missing dates and strings
missing_dates = [id for id, source in sources.items() if 'date' not in source]
missing_strings = [id for id, source in sources.items() if 'string' not in source]

if missing_dates:
    print(f"Warning: {len(missing_dates)} sources are missing dates")
if missing_strings:
    print(f"Warning: {len(missing_strings)} sources are missing string representations")
