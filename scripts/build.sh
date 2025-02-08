set -e

mkdir -p _data
cp -i source_data/sources.yml _data/
python scripts/process_data.py
python scripts/generate_pages.py

# Copy and convert data for download
mkdir -p data
cp _data/constants.yml data/
cp _data/constant_groups.yml data/
cp _data/sources.yml data/
cp _data/updates.yml data/
python scripts/convert_data.py

bundle exec jekyll build
