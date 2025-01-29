"""Generate templates for the pages for constants etc."""

import os
import yaml

with open("_data/constants.yml", "r") as file:
    constants = yaml.safe_load(file)

os.makedirs("pages/constants", exist_ok=True)

for id, constant in constants.items():
    fname = f"pages/constants/{id}.md"
    with open(fname, "w") as file:
        file.write("---\n")
        file.write("layout: constant\n")
        file.write(f"title: {constant['name']}\n")
        file.write(f"permalink: /constants/{id}/\n")
        file.write(f"id: {id}\n")
        file.write("---\n")
