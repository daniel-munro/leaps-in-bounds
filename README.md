# Leaps in Bounds

### Repository of progress on mathematical unknowns

This is a collaborative effort to compile data on historical progress on solved and unsolved mathematical constants. The focus is on quantitative updates, such as the lower and upper bounds on their values.

This site provides browsing, visualizations, and access to the structured data for other uses.

[leapsinbounds.org](https://leapsinbounds.org)

## Data Organization

There are three data layers that feed the site, each with a different purpose:

- `source_data/`: The hand-edited source of truth. This is where new constants, groups, sources, categories, and updates are authored. Updates live in `source_data/updates/*.csv` and are merged during processing.
- `_data/`: The processed, Jekyll-consumable dataset. `scripts/build.sh` copies `source_data/sources.yml` and `source_data/categories.yml` here, then `scripts/process_data.py` generates `_data/constants.yml`, `_data/constant_groups.yml`, and `_data/updates.yml` by expanding groups into constants, assigning dates, computing stats, and attaching images/metadata. Jekyll reads `_data/` directly for rendering.
- `data/`: The public export layer for downloads. `scripts/convert_data.py` converts `_data/` into YAML/JSON/CSV/TSV in `data/` and flattens nested fields for tabular formats.

In short: edit `source_data/` → run the build/test scripts → `_data/` powers the site → `data/` powers downloads.

## Verified Bounds

Alongside bounds from the literature, constants can have verified bounds backed by a certificate that is checked automatically: an explicit construction checked by a program, or a formal proof in Lean.

- `certificates/`: One YAML file per certificate. See [certificates/README.md](certificates/README.md) for the format and how to submit one.
- `formal/`: Lean project with the trusted formal statements of each bound (`LeapsInBounds/Statements/`) and submitted proofs (`LeapsInBounds/Proofs/`).
- `scripts/check_certificates.py`: Verifies all certificates. CI runs it on pull requests (with Lean proofs only when certificates, proofs, or scripts change), compiling submitted proofs in a separate job from the check.

So far, certificates are accepted for Ramsey numbers, van der Waerden numbers, cages, the degree-diameter problem, minimal superpermutations, and kissing numbers.

## Development Setup

Some data is preprocessed using Python scripts. If you don't need to modify the data, you can skip the Python setup (steps 1 and 2).

1. Create and activate a virtual environment:

```bash
python -m venv .venv
source .venv/bin/activate # On Windows, use: .venv\Scripts\activate
```

2. Install Python dependencies:

```bash
pip install -r requirements.txt
```

3. Install Ruby and Jekyll dependencies:

```bash
gem install bundler
bundle install
```

4. Run `bundle exec jekyll serve` to build and serve the site locally. Or, to process and check the data and then build and serve the site in one go, run the build script with `serve` (without it, the site is built but not served):

```bash
sh scripts/build.sh serve
```

## Contributing

Contributions are welcome!

- For technical problems and suggestions, open an issue on GitHub.
- To contribute data, post in the GitHub Discussions or email [Daniel Munro](https://danmun.ro).

## Related Projects

- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
