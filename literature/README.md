# Contributing bounds from the literature

This directory holds the bounds on each constant that come from the literature, and the sources they cite. This guide is for people and AI agents adding to it, by pull request: a published improvement to a bound, or earlier steps in a constant's history that are missing.

To add constants or families of constants for these bounds to be on, see [constants/README.md](../constants/README.md). To submit a bound that you've found yourself, or a construction or proof checked here, see [certificates/README.md](../certificates/README.md). Sources and certificates are both records of a bound, and the site matches them by the bound they give: the earlier record is its discovery, and a certificate checked here is its best evidence. So a published bound goes here even if a certificate already has it, and a certificate for it can follow.

Contributions are credited on the [contributions page](https://leapsinbounds.org/contributions/#contributors) to the GitHub account given in `added_by` (see [Credit](#credit)).

## Layout

| File | What it holds |
| --- | --- |
| `bounds/<family>.csv` | One row per bound in a constant's history, one file per family (or several small families, as in `other.csv`). |
| `sources.yml` | Every source cited by a bound, keyed by an ID. |

## Adding bounds

Each row of a bounds file records one bound from one source:

```csv
constant,lower_bound,upper_bound,source,via
weak-schur-6,646,,ageron-et-al-2021,
weak-schur-7,1740,,rafilipojaona-2017,ageron-et-al-2021
weak-schur-7,2146,,rowley-2020,ageron-et-al-2021
```

- `constant`: the constant's ID, as generated from its family's `id_template`, such as `ramsey-5-15` or `kissing-number-17`.
- `lower_bound` or `upper_bound`: exactly one of the two, never both. An exact value is two rows, a lower and an upper bound that are equal, usually from the same source.
- `source`: the source where the bound first appeared, which dates it. Use `trivial` for bounds that the `via` source calls trivial or easy, and leave it empty only if the original really can't be found.
- `via`: optional, a survey, table, or database where the bound is collected, such as Radziszowski's survey for Ramsey numbers or an OEIS entry. Cite one if that's where you learned of the bound.

Rows are sorted by the date of their source when processed, so their order in the file doesn't matter. But each bound must be an improvement on the earlier ones from the literature for the same side, and the lower bound can never exceed the upper bound: the build fails otherwise. This is a useful check that the dates are right. A bound that a certificate gave first is fine to add too: the site counts the certificate as its discovery, and the source as a later record.

**Add the whole history you can find, not just the current record.** The site is about progress over time, so each step that improved a bound is worth a row: who first proved $R(4,6) \ge 35$, and who raised it to 36. Steps that only matched an earlier bound don't need a row.

### Values

Values are LaTeX, without the surrounding `$`. Integers are written as is. Other forms in use:

- Exact expressions, such as `4\sqrt{3}` or `\frac{7+\sqrt{7}}{2}`. The build computes a decimal approximation for comparing bounds.
- Approximations prefixed with `{\approx}`, such as `{\approx}9.6348`, when the source only gives a decimal value. Give as many digits as the source does.
- Very large numbers in Knuth's up-arrow notation, such as `2\uparrow\uparrow 2\uparrow\uparrow 10`. These aren't compared numerically.

## Adding sources

Each source in `sources.yml` has an ID used in the bounds files:

```yaml
rowley-2020:
  string: "F. Rowley, New lower bounds for weak Schur partitions, Integers 21 (2021) #A59, arXiv:2011.11292."
  date: "2020-11-23"
  url: "https://arxiv.org/abs/2011.11292"
  added_by: octocat
```

- ID: lowercase, usually `<first author>-<year>`, with a suffix such as `-b` or a topic if that's taken. Databases and tables are named for what they are, such as `oeis-a072842-weak-schur`.
- `string`: the citation as it should be shown: authors, title, venue, and identifiers such as an arXiv number.
- `date`: when the bound was first made public, `YYYY-MM-DD`, or `YYYY-MM` or `YYYY` if that's all that's known. This is usually the date of the first preprint, not the journal publication, since that's when the result was announced. For a web page or database that changes, use the date it was retrieved, and say so in `string`.
- `url` and/or `doi`: a link to the source. Prefer arXiv or another open version when there is one, and a DOI as `https://doi.org/...`.
- `notes`: optional, for anything a reader should know, such as that the bound is a corollary not stated in the paper, or that it was later found to be wrong.
- `added_by`: optional, the GitHub username to credit for adding this source (see [Credit](#credit)).

Check whether a source is already there before adding it, by its arXiv number or DOI.

A bound found by computer and posted only in a repository or on Zenodo, rather than in a paper, is still a source if it's public and dated. If it comes with a witness that can be checked here, also consider submitting it as a [certificate](../certificates/README.md), which the site then shows as its verified evidence.

## Credit

Contributions to the literature data are credited on the [contributions page](https://leapsinbounds.org/contributions/#contributors) by the `added_by` field on sources and families (see [constants/README.md](../constants/README.md)): the GitHub account that added them, which is usually whoever opens the pull request. When a maintainer adds sources that a contributor pointed to, such as the sources for the earlier bounds behind a certificate, they're credited to the contributor. It credits the work of finding and recording the data, not the mathematics, which is credited to the sources themselves. When adding many bounds from one survey, the sources you add are what's credited, so it's worth adding the original sources rather than citing only the survey.

## Checking

Run the build script to process and check the data:

```bash
sh scripts/build.sh check   # without building the site, so Ruby isn't needed
sh scripts/build.sh         # also builds the site
```

It fails on rows for unknown constants or sources, rows with both or neither bound, bounds that aren't improvements, and lower bounds above upper bounds. It warns about sources without dates. CI runs the same checks on pull requests, and a preview of the site is linked on the pull request.

In the pull request, say where each bound comes from, and note anything you weren't sure about, such as a date that could be the preprint's or the journal's. A maintainer will check the sources before merging.

## For AI agents

To have an AI agent contribute bounds from the literature, give it a prompt such as:

```
Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/literature/README.md and follow it to add missing bounds from the literature to Leaps in Bounds, for <family or topic>.
```

Agents should cite only sources they have read, at least in the part that states the bound, and give each bound's source, page or theorem in the pull request so that it can be checked. Don't infer a bound that no source states, as a corollary of others, without saying so in the source's `notes`.
