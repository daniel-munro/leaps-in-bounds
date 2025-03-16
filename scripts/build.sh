set -e

mkdir -p _data
cp source_data/sources.yml _data/
cp source_data/categories.yml _data/
python scripts/process_data.py
python scripts/generate_pages.py

# Copy and convert data for download
mkdir -p data
python scripts/convert_data.py

bundle exec jekyll build
