# Process data, check it, and build the site.
# Usage: sh scripts/build.sh [serve|check]
# With check, the data is processed and checked but the site isn't built.
set -e

mkdir -p _data
cp source_data/sources.yml _data/
cp source_data/categories.yml _data/
python scripts/process_data.py
python scripts/generate_pages.py

# Copy and convert data for download
mkdir -p data
python scripts/convert_data.py

python scripts/validate_data.py
python scripts/check_certificates.py --allow-pending
python scripts/check_notes.py

if [ "$1" = "check" ]; then
    exit 0
elif [ "$1" = "serve" ]; then
    bundle exec jekyll serve
else
    bundle exec jekyll build
fi
