# Contributing bounds from the literature

This directory holds the hand-edited data behind the site: constant groups, sources, and the history of bounds on each constant. This guide is for people and AI agents adding to it, by pull request. It covers two kinds of contribution:

- **Bounds from the literature:** a published improvement to a bound, or earlier steps in a constant's history that are missing.
- **New constants:** extending a group to more parameters, or adding a new group of constants.

To submit a bound that you've found yourself, or a construction or proof checked here, see [certificates/README.md](../certificates/README.md) instead. Sources and certificates are both records of a bound, and the site matches them by the bound they give: the earlier record is its discovery, and a certificate checked here is its best evidence. So a published bound goes here even if a certificate already has it, and a certificate for it can follow.

Contributions are credited on the [contributors page](https://leapsinbounds.org/contributors/) to the GitHub account given in `added_by` (see [Credit](#credit)).

## Layout

| File | What it holds |
| --- | --- |
| `updates/<group>.csv` | One row per bound in a constant's history, one file per constant group (or several small groups, as in `other.csv`). |
| `sources.yml` | Every source cited by an update, keyed by an ID. |
| `constant_groups.yml` | Each group of constants: its description, parameters, and how its table is drawn. |
| `categories.yml` | Which MSC2020 category each group is listed under. Every group must be in one. |
| `constants.yml` | Optional metadata for individual constants, such as an image. |

## Adding bounds

Each row of an updates file records one bound from one source:

```csv
constant,lower_bound,upper_bound,primary_source,secondary_source
weak-schur-6,646,,ageron-et-al-2021,
weak-schur-7,1740,,rafilipojaona-2017,ageron-et-al-2021
weak-schur-7,2146,,rowley-2020,ageron-et-al-2021
```

- `constant`: the constant's ID, as generated from its group's `id_template`, such as `ramsey-5-15` or `kissing-number-17`.
- `lower_bound` or `upper_bound`: exactly one of the two, never both. An exact value is two rows, a lower and an upper bound that are equal, usually from the same source.
- `primary_source`: the source where the bound first appeared, which dates it. Use `trivial` for bounds that a secondary source calls trivial or easy, and leave it empty only if the original really can't be found.
- `secondary_source`: optional, a survey, table, or database where the bound is collected, such as Radziszowski's survey for Ramsey numbers or an OEIS entry. Cite one if that's where you learned of the bound.

Rows are sorted by the date of their primary source when processed, so their order in the file doesn't matter. But each bound must be an improvement on the earlier ones from the literature for the same side, and the lower bound can never exceed the upper bound: the build fails otherwise. This is a useful check that the dates are right. A bound that a certificate gave first is fine to add too: the site counts the certificate as its discovery, and the source as a later record.

**Add the whole history you can find, not just the current record.** The site is about progress over time, so each step that improved a bound is worth a row: who first proved $R(4,6) \ge 35$, and who raised it to 36. Steps that only matched an earlier bound don't need a row.

### Values

Values are LaTeX, without the surrounding `$`. Integers are written as is. Other forms in use:

- Exact expressions, such as `4\sqrt{3}` or `\frac{7+\sqrt{7}}{2}`. The build computes a decimal approximation for comparing bounds.
- Approximations prefixed with `{\approx}`, such as `{\approx}9.6348`, when the source only gives a decimal value. Give as many digits as the source does.
- Very large numbers in Knuth's up-arrow notation, such as `2\uparrow\uparrow 2\uparrow\uparrow 10`. These aren't compared numerically.

## Adding sources

Each source in `sources.yml` has an ID used in the updates files:

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

## Adding constants

To cover more constants in an existing group, such as more Ramsey numbers or higher dimensions, extend its `parameter_values` in `constant_groups.yml`, then add their updates. Each entry of `parameter_values` lists one value per parameter, where a value can be a number or an inclusive range `[first, last]`, and the constants are all combinations:

```yaml
parameters: [k, g]
parameter_values: [[[3, 20], [3, 16]]]   # k from 3 to 20, g from 3 to 16
```

Constants with no bounds yet are shown as blank cells, which can be useful in a grid, but it's best to add bounds for the new constants in the same pull request.

### New groups

A good new group is a family of specific constants whose bounds have been improved over time, with sources for those improvements. Families under active work, where new bounds keep appearing, are especially welcome, such as problems that have recently seen bounds from computer searches. Constants that are just functions with a known closed form aren't a good fit, nor are general asymptotic bounds, which the site doesn't show yet.

If you're not sure a family fits, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions) first. Otherwise, open a pull request that adds:

1. The group in `constant_groups.yml`:

   ```yaml
   weak-schur:
     name: "Weak Schur numbers"
     description: "The weak Schur number $WS(k)$ is the largest number $n$ such that ..."
     external_ids:
       oeis: A072842
       wikipedia_en: Schur_number
     display_type: sequence
     id_template: "weak-schur-{k}"
     name_template: "Weak Schur number $WS({k})$"
     description_template: "The largest number $n$ such that the integers $1$ to $n$ can be colored with ${k}$ colors ..."
     parameters: [k]
     parameter_values: [[[1, 9]]]
     research_status: initial
     added_by: octocat
   ```

   - `description`: defines the constants precisely, in LaTeX between `$`s. The templates fill in `{k}` and so on for each constant; write a literal brace as `{{` or `}}`.
   - `external_ids`: any of `wikipedia_en`, `wikidata`, `mathworld`, `metamath`, `msc`, `planetmath`, and `oeis`.
   - `display_type`: `sequence` for one parameter, `grid` for two, with `display_rows` and `display_columns` listing the values to show, or `single` for a group of one constant with no parameters, which then has no templates or `parameter_values`.
   - `research_status`: `initial` if the data is incomplete, `sourced` if every current bound has a source, or `thorough` if the history of every bound has been searched for as far as it goes.
   - `representative_image`: optional, the ID of a constant whose image represents the group.
   - `added_by`: optional, the GitHub username to credit for adding the group.

2. The group in `categories.yml`, under its MSC2020 category, adding the category if needed.

3. Its bounds in `updates/<group>.csv`, and their sources in `sources.yml`.

Images and support for certificates can come later. A new group's certificates need a checker in `scripts/certificates.py` and a formal statement in `formal/`, which a maintainer will usually add, though proposals are welcome.

## Credit

Contributions to the literature data are credited on the [contributors page](https://leapsinbounds.org/contributors/) by the `added_by` field on sources and constant groups: the GitHub account that added them, which is usually whoever opens the pull request. When a maintainer adds sources that a contributor pointed to, such as the sources for the earlier bounds behind a certificate, they're credited to the contributor. It credits the work of finding and recording the data, not the mathematics, which is credited to the sources themselves. When adding many bounds from one survey, the sources you add are what's credited, so it's worth adding the primary sources rather than citing only the survey.

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
Read https://github.com/daniel-munro/leaps-in-bounds/blob/main/source_data/README.md and follow it to add missing bounds from the literature to Leaps in Bounds, for <group or topic>.
```

Agents should cite only sources they have read, at least in the part that states the bound, and give each bound's source, page or theorem in the pull request so that it can be checked. Don't infer a bound that no source states, as a corollary of others, without saying so in the source's `notes`.
