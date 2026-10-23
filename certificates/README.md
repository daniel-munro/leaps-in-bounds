# Certificates

A certificate claims a lower or upper bound on one constant and comes with evidence that a program can check, so the bound doesn't depend on trusting a paper or a secondary source. The site shows the strongest certificate on each side as the constant's **verified** bound, alongside the bounds from the literature.

Anyone, including an AI agent, can submit a certificate by opening a pull request that adds a file here. CI checks every certificate, and a new certificate must be strictly stronger than the existing ones for the same bound.

This is a pilot. Only the Ramsey numbers (`ramsey-{r}-{s}`) accept certificates so far.

## File format

One YAML file per certificate, in `certificates/<group>/`. The file name (without `.yml`) is the certificate ID and must be unique. By convention it's `<constant>-<lower|upper>-<value>.yml`.

```yaml
constant: ramsey-4-4      # constant ID, as on the site
bound: lower              # lower or upper
value: 18                 # the bound: R(4,4) >= 18
kind: witness             # witness or lean
witness:                  # for kind: witness (see the family's rules below)
  format: graph6
  data: 'PzlXWmJpZDeJEJbDgp\EJsWk'   # or `file: name.g6` for large witnesses
submitted_by: Your Name   # person or agent to credit
date: 2026-10-22          # submission date
source: greenwood-gleason-1955   # optional: key in source_data/sources.yml for where the construction comes from
notes: Paley graph of order 17.  # optional
```

For a Lean proof:

```yaml
kind: lean
lean:
  module: LeapsInBounds.Proofs.Ramsey33       # file in formal/, under LeapsInBounds/Proofs/
  theorem: LeapsInBounds.Proofs.Ramsey33.upper
```

## Kinds of evidence

### witness

An explicit construction, checked by a verifier for the constant's family in [`scripts/certificates.py`](../scripts/certificates.py). Witnesses suit bounds that come from a construction, which is how most new lower bounds on extremal quantities are found.

### lean

A theorem in the [`formal/`](../formal) Lean project whose type is exactly the family's formal statement of the bound, as defined in `formal/LeapsInBounds/Statements/`. The checker compiles the proof and checks that it depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorry`, new axioms and `native_decide`.

The statement files are trusted: they define what every certificate means. Submissions should only add files under `formal/LeapsInBounds/Proofs/`. CI flags any pull request that changes the statements or the checking scripts.

## Families

### Ramsey numbers: `ramsey-{r}-{s}`

Formal statements are in [`formal/LeapsInBounds/Statements/Ramsey.lean`](../formal/LeapsInBounds/Statements/Ramsey.lean):

- `LowerBound r s n` means `R(r,s) >= n`: some graph on `n - 1` vertices has no clique of size `r` and no independent set of size `s`.
- `UpperBound r s n` means `R(r,s) <= n`: every graph on `n` vertices has a clique of size `r` or an independent set of size `s`.

The same file proves that a lower bound never exceeds an upper bound, as a sanity check on the definitions.

Witnesses can certify lower bounds only. A witness for `R(r,s) >= n` is a graph on `n - 1` vertices in [graph6](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) format, with no `r`-clique and no independent set of size `s`.

## Checking locally

```bash
python scripts/check_certificates.py                # witnesses only
```

To also check Lean proofs, install [elan](https://github.com/leanprover/elan), then:

```bash
cd formal && lake exe cache get && lake build && cd ..
python scripts/check_certificates.py --lean
```

Add `--improves certificates/ramsey/<file>.yml` to check that a new certificate beats the existing ones, as CI does.

## Known gaps

- The Lean check elaborates the expected statement in the same environment as the submitted proof, so a malicious submission could in principle use macros or notation to change what the statement means. Pull requests that touch Lean still need human review until the check compares the proof's type against the statement compiled separately, in a clean environment.
- Compiling Lean runs code from the submission. CI runs with a read-only token and no secrets for this reason.
- Values are integers for now. Families with real-valued constants will need exact or interval-arithmetic witnesses.
