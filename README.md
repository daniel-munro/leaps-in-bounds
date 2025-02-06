# Leaps in Bounds

### Repository of progress on mathematical unknowns

This is a collaborative effort to compile data on historical progress on solved and unsolved mathematical constants. The focus is on quantitative updates, such as the lower and upper bounds on their values.

This site provides browsing, visualizations, and access to the structured data for other uses.

[leapsinbounds.org](https://leapsinbounds.org)

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

4. Run `bundle exec jekyll serve` to build and serve the site locally. Or, to run the data preprocessing and build and serve the site in one go, run the test script:

```bash
sh scripts/test.sh
```

## Contributing

Contributions are welcome!

- For technical problems and suggestions, open an issue on GitHub.
- To contribute data, post in the GitHub Discussions or email [Daniel Munro](https://danmun.ro).
