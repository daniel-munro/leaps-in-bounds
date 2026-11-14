# Adding constants

This directory defines which constants the site tracks. Constants come in families: a family is a set of related constants indexed by one or more parameters, such as the Ramsey numbers $R(k, l)$ or the kissing numbers in each dimension, and is listed on the site as one table. A family can also be a single constant with no parameters.

This guide is for people and AI agents adding to it, by pull request: extending a family to more parameters, or adding a new family. The bounds on each constant are recorded separately, in [`literature/`](../literature/README.md) for bounds from published sources and in [`certificates/`](../certificates/README.md) for bounds checked here.

## Layout

| File | What it holds |
| --- | --- |
| `families.yml` | Each family of constants: its description, parameters, and how its table is drawn. |
| `categories.yml` | Which MSC2020 category each family is listed under. Every family must be in one. |
| `constants.yml` | Optional metadata for individual constants, such as an image. |

## Extending a family

To cover more constants in an existing family, such as more Ramsey numbers or higher dimensions, extend its `parameter_values` in `families.yml`, then add their bounds in [`literature/`](../literature/README.md). Each entry of `parameter_values` lists one value per parameter, where a value can be a number or an inclusive range `[first, last]`, and the constants are all combinations:

```yaml
parameters: [k, g]
parameter_values: [[[3, 20], [3, 16]]]   # k from 3 to 20, g from 3 to 16
```

Constants with no bounds yet are shown as blank cells, which can be useful in a grid, but it's best to add bounds for the new constants in the same pull request.

## New families

A good new family is a set of specific constants whose bounds have been improved over time, with sources for those improvements. Families under active work, where new bounds keep appearing, are especially welcome, such as problems that have recently seen bounds from computer searches. Constants that are just functions with a known closed form aren't a good fit, nor are general asymptotic bounds, which the site doesn't show yet.

If you're not sure a family fits, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions) first. Otherwise, open a pull request that adds:

1. The family in `families.yml`:

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
     added_by: octocat
   ```

   - `description`: defines the constants precisely, in LaTeX between `$`s. The templates fill in `{k}` and so on for each constant; write a literal brace as `{{` or `}}`.
   - `external_ids`: any of `wikipedia_en`, `wikidata`, `mathworld`, `metamath`, `msc`, `planetmath`, and `oeis`.
   - `display_type`: `sequence` for one parameter, `grid` for two, with `display_rows` and `display_columns` listing the values to show, or `single` for a family of one constant with no parameters, which then has no templates or `parameter_values`.
   - `representative_image`: optional, the ID of a constant whose image represents the family.
   - `added_by`: optional, the GitHub username to credit for adding the family (see [Credit](../literature/README.md#credit)).

2. The family in `categories.yml`, under its MSC2020 category, adding the category if needed.

3. Its bounds in [`literature/bounds/<family>.csv`](../literature/README.md), and their sources in `literature/sources.yml`.

Images and support for certificates can come later. A new family's certificates need a checker in `scripts/certificates.py` and a formal statement in `formal/`, which a maintainer will usually add, though proposals are welcome.

## Images

A constant's image is set in `constants.yml`, either downloaded from a `source_url` or `generated` by `scripts/generate_images.py`. See [Images](../README.md#images) in the main README.

## Checking

Run the build script to process and check the data:

```bash
sh scripts/build.sh check   # without building the site, so Ruby isn't needed
```
