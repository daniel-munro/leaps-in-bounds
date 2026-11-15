# Leaps in Bounds

### Repository of progress on mathematical unknowns

This is a collaborative effort to compile data on historical progress on solved and unsolved mathematical constants. The focus is on quantitative updates, such as the lower and upper bounds on their values.

This site provides browsing, visualizations, and access to the structured data for other uses.

[leapsinbounds.org](https://leapsinbounds.org)

## Data Organization

The hand-edited data is in three directories, one for what is tracked and two for the records of bounds on it:

- `constants/`: The families of constants tracked (`families.yml`), the MSC2020 category each is listed under (`categories.yml`), and optional metadata for individual constants such as images (`constants.yml`). See [constants/README.md](constants/README.md) for how to add constants.
- `literature/`: Bounds from the literature, one CSV file per family in `literature/bounds/`, and the sources they cite (`sources.yml`). See [literature/README.md](literature/README.md) for how to add them.
- `certificates/`: Bounds with evidence checked here (see [Discovery and Evidence](#discovery-and-evidence) below).

The build turns these into two generated layers, neither of which is committed:

- `_data/`: The processed, Jekyll-consumable dataset. `scripts/build.sh` copies `literature/sources.yml` and `constants/categories.yml` here, then `scripts/process_data.py` generates `_data/constants.yml`, `_data/families.yml`, `_data/updates.yml`, `_data/history.yml`, `_data/discoveries.yml`, and `_data/contributors.yml` by expanding families into constants, assigning dates, merging bounds from the literature and certificates into each constant's history, computing stats, and attaching images/metadata. Jekyll reads `_data/` directly for rendering.
- `data/`: The public export layer for downloads. `scripts/convert_data.py` converts `_data/` into YAML/JSON/CSV/TSV in `data/` and flattens nested fields for tabular formats.

In short: edit `constants/`, `literature/` or `certificates/` → run the build/test scripts → `_data/` powers the site → `data/` powers downloads.

## Discovery and Evidence

Each constant has a history of bounds, each improving on the ones before. Two things are recorded for each bound:

- **Discovery:** the first record of it, with its date and who it's credited to. That's a source from the literature (a row in `literature/bounds/` citing it), or a certificate submitted here when no earlier record has a bound as strong.
- **Best evidence:** the strongest support for it, which can improve over time. A certificate whose evidence has been checked here is **verified**: an explicit construction checked by a program, or a formal proof in Lean. Evidence too slow to check here, or too large to keep here, can be **attested** instead, by someone who checked it with a checker they published: a large witness linked from elsewhere, say, or a Lean proof built on its own library. Without a certificate, the evidence is the literature. A certificate for a stronger bound is evidence for the weaker ones too.

Sources and certificates are independent records, matched by the bound they give: `scripts/process_data.py` uses the earlier record as the discovery and the strongest as the evidence.

The certificates and the tools around them:

- `certificates/`: One YAML file per certificate. See [certificates/README.md](certificates/README.md) for the format and how to submit one.
- `formal/`: Lean project with the trusted formal statements of each bound (`LeapsInBounds/Statements/`) and submitted proofs (`LeapsInBounds/Proofs/`).
- `notes/`: Working notes on searches for certificates, one scratchpad per family, so people and agents can build on earlier attempts instead of repeating them. See [notes/README.md](notes/README.md).
- `certificates/verified.yml`: The manifest of verified certificates, recording a hash of the evidence that was checked, the commit of the checkers, who ran them and when.
- `scripts/verify_certificates.py`: Runs the checkers on certificates' evidence and records those that pass in the manifest. A maintainer runs it before merging new certificates.
- `scripts/check_certificates.py`: Checks that every certificate is well formed, consistent with the others and the literature, and verified or attested. CI runs it on pull requests, without running the checkers.

So far, certificates are accepted for Ramsey numbers, van der Waerden numbers, cages, the degree-diameter problem, minimal superpermutations, kissing numbers, packing unit squares in a square, packing unit circles in an equilateral triangle, Schur and weak Schur numbers, multicolor Ramsey numbers for triangles, optimal Golomb rulers, arrangements of lines in the plane, snakes and coils in the hypercube, cap sets, the no-three-in-line problem, isosceles sets, the size and depth of sorting networks, the rectilinear crossing number of complete graphs, and the chromatic number of Euclidean space.

## Images

A constant's image, set in `constants/constants.yml`, is either downloaded from a `source_url` (and cached in `assets/images/constants/`) or `generated` by `scripts/generate_images.py`, which draws constructions in a consistent style as SVG in `assets/images/generated/`. The generator checks each construction (against a certificate's witness, or the constant's value) before drawing it. It isn't part of the build, so new images can be reviewed first:

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

- **Bounds from the literature:** add published bounds, their sources, and earlier steps in their history, or new constants and families of constants. See how to add [bounds](literature/README.md) and [constants](constants/README.md).
- **Certificates:** submit evidence that a program can check, either a construction or a proof in Lean, for a new bound or one discovered earlier. See [how to submit one](certificates/README.md), and the [unverified bounds](https://leapsinbounds.org/unverified/) for current bounds that don't have a verified one yet.

For more open-ended contributions, such as asking whether a family of constants fits or sharing data you're not sure how to add, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). For technical problems and suggestions, [open an issue](https://github.com/daniel-munro/leaps-in-bounds/issues).

Contributions are credited to the GitHub account that made them on the [contributions page](https://leapsinbounds.org/contributions/#contributors).

To have an AI agent contribute, give it one of these prompts:

```
Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/certificates/README.md and follow it to submit a verified bound to Leaps in Bounds.
```

```
Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/literature/README.md and follow it to add missing bounds from the literature to Leaps in Bounds, for <family or topic>.
```

## Related Projects

- [Big O Speedrun](https://bigospeedrun.com) - Leaderboards of recent progress on bounds for algorithm running times and other constants, with Lean-verified submissions.
- [Optimization Constants in Mathematics](https://github.com/teorth/optimizationproblems) - A curated collection of optimization constants in mathematics, often arising from solving a variational problem, or finding the best constant in a functional inequality.
