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

Alongside bounds from the literature, constants can have verified bounds backed by a certificate whose evidence has been checked here: an explicit construction checked by a program, or a formal proof in Lean. Evidence too slow to check here can be attested instead, by someone who checked it with a checker they published.

- `certificates/`: One YAML file per certificate. See [certificates/README.md](certificates/README.md) for the format and how to submit one.
- `formal/`: Lean project with the trusted formal statements of each bound (`LeapsInBounds/Statements/`) and submitted proofs (`LeapsInBounds/Proofs/`).
- `notes/`: Working notes on searches for verified bounds, one scratchpad per constant group, so people and agents can build on earlier attempts instead of repeating them. See [notes/README.md](notes/README.md).
- `certificates/verified.yml`: The manifest of verified certificates, recording a hash of the evidence that was checked, the commit of the checkers, who ran them and when.
- `scripts/verify_certificates.py`: Runs the checkers on certificates' evidence and records those that pass in the manifest. A maintainer runs it before merging new certificates.
- `scripts/check_certificates.py`: Checks that every certificate is well formed, consistent with the others and the literature, and verified or attested. CI runs it on pull requests, without running the checkers.

So far, certificates are accepted for Ramsey numbers, van der Waerden numbers, cages, the degree-diameter problem, minimal superpermutations, kissing numbers, packing unit squares in a square, packing unit circles in an equilateral triangle, Schur and weak Schur numbers, optimal Golomb rulers, arrangements of lines in the plane, snakes and coils in the hypercube, cap sets, the no-three-in-line problem, and isosceles sets.

## Images

A constant's image, set in `source_data/constants.yml`, is either downloaded from a `source_url` (and cached in `assets/images/constants/`) or `generated` by `scripts/generate_images.py`, which draws constructions in a consistent style as SVG in `assets/images/generated/`. The generator checks each construction (against a certificate's witness, or the constant's value) before drawing it. It isn't part of the build, so new images can be reviewed first:

```bash
python scripts/generate_images.py --sheet /tmp/image-review.html  # all families, plus a page comparing them to the current images
```

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

Contributions are welcome, from people and AI agents alike. Pull requests are the preferred way to contribute:

- **Bounds from the literature:** add updates and their sources in `source_data/` (see [Data Organization](#data-organization)), and run the build script to check them.
- **Verified bounds:** submit a certificate, either a construction checked by a program or a proof in Lean. See [how to submit one](certificates/README.md), and the [unverified bounds](https://leapsinbounds.org/unverified/) for bounds from the literature that don't have one yet.

For more open-ended contributions, such as suggesting a new group of constants or sharing data you're not sure how to add, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). For technical problems and suggestions, [open an issue](https://github.com/daniel-munro/leaps-in-bounds/issues).

To have an AI agent contribute a verified bound, give it this prompt:

```
Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md and follow it to submit a verified bound to Leaps in Bounds.
```

## Related Projects

- [Big O Speedrun](https://bigospeedrun.com) - Leaderboards of recent progress on bounds for algorithm running times and other constants, with Lean-verified submissions.
- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
