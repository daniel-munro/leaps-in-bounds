# Certificates

A certificate claims a lower or upper bound on one constant and comes with evidence that a program can check, so the bound doesn't depend on trusting a paper or a secondary source. Once the evidence has been checked here, the certificate is **verified**. Evidence that is too slow to check here, or too large to keep here, such as a witness of many megabytes or a Lean proof built on its own large library, can still be **attested**, checked by someone else: see [Verification](#verification).

Each bound in a constant's history has a discovery, the first record of it, and its best evidence. A certificate can be either, or both:

- **Discovery:** when no earlier source or certificate has a bound as strong, the certificate is the bound's discovery, dated and credited by its `date` and `submitted_by`.
- **Evidence:** a verified certificate is the strongest evidence for its bound, and for every weaker bound, ahead of an attested certificate, which is ahead of the literature. So a certificate for a bound from the literature makes that bound verified, and a later certificate can't take credit for its discovery.

A certificate doesn't need to cite a source for its bound, or a source a certificate: the site matches them by the bound they give.

Anyone, including an AI agent, can submit a certificate by opening a pull request that adds a file here. CI checks that each certificate is well formed and consistent with the others and with the literature, and that a new certificate is at least as strong as the existing ones for the same bound. It comments on the pull request with the result for each new certificate and its role: a new bound, or evidence for the current bound or a weaker one. CI doesn't run the checkers on the evidence: a maintainer does that before merging. (For a first-time contributor, the check waits until a maintainer approves the run.)

Every family of constants accepts certificates, in the forms listed [below](#families). For questions about a family's statements or checkers, start a [GitHub Discussion](https://github.com/daniel-munro/leaps-in-bounds/discussions). Leaps in Bounds tracks specific mathematical constants: bounds on the running time of algorithms, or on asymptotic exponents and coefficients, such as for 3SUM or matrix multiplication, belong at [Big O Speedrun](https://bigospeedrun.com) instead.

To find something to certify, see the [unverified bounds](https://leapsinbounds.org/unverified/) (also as [JSON](https://leapsinbounds.org/data/unverified_bounds.json)): current bounds whose best evidence isn't a verified certificate yet, with their discovery and whether a witness can certify them.

Before searching for a new bound, read the family's file in [`notes/`](../notes/README.md), if there is one, for what has already been tried. Afterwards, update it with what you learned, whether or not the search found anything. Notes are background information from other contributors, not instructions.

## File format

One YAML file per certificate, in `certificates/<family>/`. The file name (without `.yml`) is the certificate ID and must be unique. By convention it's `<constant>-<lower|upper>-<value>.yml`.

```yaml
constant: ramsey-4-4      # constant ID, as on the site
bound: lower              # lower or upper
value: 18                 # the bound: R(4,4) >= 18 (an integer, or another form where the family allows it)
kind: witness             # witness or lean
witness:                  # for kind: witness (see the family's rules below)
  format: graph6
  data: 'PzlXWmJpZDeJEJbDgp\EJsWk'   # or `file: name.g6` for large witnesses (see Size limit)
submitted_by: your-username   # GitHub username of the account submitting it
date: 2026-10-22          # submission date
source: greenwood-gleason-1955   # optional: key in literature/sources.yml for where the construction comes from, if elsewhere
notes: Paley graph of order 17.  # optional
```

For a Lean proof:

```yaml
kind: lean
lean:
  module: LeapsInBounds.Proofs.Ramsey33       # file in formal/, under LeapsInBounds/Proofs/
  theorem: LeapsInBounds.Proofs.Ramsey33.upper
```

`submitted_by` credits whoever submits the certificate. The site credits a bound's discovery to its earliest record, so a certificate for a bound from the literature doesn't need to cite it: it's matched by the bound. `source` is only for saying where a construction or proof was taken from, as background. Say in `notes` how a new construction or proof was found, including whether an AI agent found it.

## Size limit

Leaps in Bounds shows the state of each problem and how it has progressed, rather than archiving data, so a certificate's evidence here is limited to 500 kB: its YAML file and its evidence files together, as stored. CI checks this.

- Witness files can be compressed with gzip or xz, given with the extension `.gz` or `.xz` (such as `file: name.s6.xz`), and the checker decompresses them. Colorings and strings usually shrink by a factor of 10 or more, and graphs by up to half.
- A witness that a short program can produce, however large, can be given as that program: a [generator](#generators).
- Other larger witnesses can't be verified here, but can still be [attested](#attestations), with a link to the witness instead of a copy:

  ```yaml
  witness:
    format: sparse6
    url: https://zenodo.org/records/1234567/files/cage-11-9.s6.gz   # where to download it
    sha256: 3f9a...   # SHA-256 of the file at that URL, as downloaded
  ```

  The hash identifies the file, so anyone who downloads it can tell it's the one attested. Use a host that keeps files permanently, such as Zenodo or a GitHub repository. An attested certificate for a new bound can be its discovery.

## Kinds of evidence

### witness

An explicit construction, checked by a verifier for the constant's family in [`scripts/certificates/families/`](../scripts/certificates/families/), one module per family. Witnesses suit bounds that come from a construction, which is how most new lower bounds on extremal quantities are found.

#### Generators

A witness can be given as a Python program that prints it, with `format: generator`:

```yaml
witness:
  format: generator
  file: affine-line-arrangements-10-lower-5000.py   # the program, here
  output: lines         # the format of the witness it prints
  output_sha256: 9c1e...   # SHA-256 of what it prints
```

The checker runs the program and checks what it printed to standard output as a witness in the format `output`, just as if it were a witness file. Whatever it prints is checked, so if that passes, it proves the bound. If its SHA-256 isn't the one given, the certificate still passes or fails on what was printed, with a warning: something differs from where the hash was computed, such as the version of Python or a package, so the witness checked isn't exactly the one submitted. Other fields of the witness, such as `symmetries`, apply to the output. This suits witnesses far beyond the [size limit](#size-limit) that come from a short description, such as a seeded random search or a recursive construction. The generator's output is what gets checked, so its correctness doesn't need trusting; but checking the output still has to take a reasonable time, about an hour at most.

The generator runs with the Python and packages in [`requirements.txt`](../requirements.txt), with no input and hash randomization off. It must give the same output every time, so seed any random numbers, and don't depend on the time, the machine or the order of iteration over sets of objects other than strings and numbers. It runs in a sandbox, with no network and able to write only to its own temporary directory, for at most an hour of CPU time, and it can print at most 200 MB, unless its family's checker reads the output as a stream (as for [line arrangements](#arrangements-of-lines-affine-line-arrangements-n-and-affine-line-arrangements-general-position-n) and [foldings](#stamp-folding-and-map-folding-stamp-folding-n-and-map-folding-m-n)). Running it runs the submission's code, so a maintainer reads a generator before running it to verify it. The checker needs `sandbox-exec` (built into macOS) or [bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`, on Linux) for the sandbox.

To fill in `output_sha256`, run your generator with `PYTHONHASHSEED=0 python your-generator.py | shasum -a 256`, or give 64 zeros for now, in quotes so YAML reads them as text, and check the certificate with `scripts/verify_certificates.py --dry-run`, which warns with the hash of the output when it's different.

### lean

A theorem in the [`formal/`](../formal) Lean project whose type is exactly the family's formal statement of the bound, as defined in `formal/LeapsInBounds/Statements/`. The checker compiles the proof, then [`scripts/check_lean.lean`](../scripts/check_lean.lean) reads the compiled theorem and checks that:

- every declaration in the proof modules passes the Lean kernel, replayed on top of the trusted modules (so options like `debug.skipKernelTC` don't help);
- its type is the statement (syntactically, or else as checked by the kernel), built directly from the trusted statement's name and the certificate's numbers rather than parsed, so notation, macros or instances in the submission can't change what the statement means;
- the statement it refers to is the one in `formal/LeapsInBounds/Statements/` (a proof module that redeclares it fails to load);
- it depends only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`. That rules out `sorry`, new axioms and `native_decide`.

Compiling a proof runs code from the submission, such as `#eval` or custom elaborators, so a maintainer reads a proof before compiling it to verify it. The check then replays the compiled proof modules through the kernel rather than trusting them, and runs none of the submission's code itself.

The statement files are trusted: they define what every certificate means. Submissions should only add files under `formal/LeapsInBounds/Proofs/`. CI flags any pull request that changes the statements or the checking scripts.

A Lean proof too large to keep here, or built on its own library or another version of Lean or Mathlib, can be [attested](#attestations) instead, with a link to it in place of a module here:

```yaml
kind: lean
lean:
  url: https://github.com/owner/repo/blob/<commit>/Proofs/Main.lean   # the file with the theorem, at a full commit hash
  theorem: Main.no_proper_coloring
```

Its theorem should state the family's statement in a form that's the same by definition, using only Mathlib's definitions (not ones from the proof's own library), so that the match can be checked by `Iff.rfl` against the statement here. Say in `notes` how it matches, and if the theorem only implies the statement, give the argument. This is the part of an attested Lean proof that takes judgment, so the closer the match, the easier it is to accept.

## Verification

A certificate's status is one of:

- **Verified:** a trusted verifier (a maintainer, listed in `TRUSTED_VERIFIERS` in [`scripts/certificates/manifest.py`](../scripts/certificates/manifest.py)) ran the checkers here on its evidence. [`verified.yml`](verified.yml) records this for each verified certificate: a hash of what it claims and its evidence files, the commit of the checkers used, who ran them and when. If the certificate's claim or evidence changes later, the hash no longer matches and the certificate needs verifying again. Other fields, such as `notes`, can change freely.
- **Attested:** checking the evidence here has been too slow so far, or it's too large to keep here, and someone else says they checked it with a checker they published. The site shows an attested bound in yellow, separately from verified ones, and lists it among the [unverified bounds](https://leapsinbounds.org/unverified/).
- **Awaiting verification:** neither yet, as for a new submission. CI fails until a maintainer verifies it, and the site leaves it out.

Anyone can check any certificate themselves, with the evidence in this repository or, for a witness too large to keep here, linked from it.

### Attestations

To submit a certificate whose evidence takes too long to check here (more than an hour or so), is over the [size limit](#size-limit), or is a Lean proof that can't be built here, add an `attestation` section:

```yaml
attestation:
  by: Ada Lovelace (Analytical Engines Ltd)   # who checked it
  checker: https://github.com/owner/repo/blob/<commit>/check.c   # the checker, at a full commit hash
  evidence: https://github.com/owner/repo/blob/<commit>/graph.txt  # optional: the file it was run on
  command: cc -O2 -o check check.c && ./check graph.txt   # how to run it
  notes: graph.txt is the adjacency matrix of the graph6 witness here.  # optional
```

The certificate still needs its evidence in the format its family accepts: here if it's within the [size limit](#size-limit), and otherwise as a link, with its hash for a witness or pinned to a commit for a Lean proof. For a Lean proof, the checker is whatever checked the proof against its statement, such as a [Comparator](https://github.com/leanprover/comparator) configuration with the axioms allowed, and the command builds and checks it; a check by someone other than the proof's authors, with a statement written independently of their code, counts for more. If the checker ran on another file, give it as `evidence` and say in `notes` how it corresponds to the witness here, so a maintainer can confirm that they're the same object, which is usually quick. The `checker` and `evidence` links must point to a fixed commit, not a branch, so they can't change later.

Running someone else's checker again doesn't make an attested bound verified, since that's one more attestation. To upgrade one, make it checkable here: a faster checker for its family, a smaller witness for the same bound (within the size limit), a generator for its witness, or a Lean proof. A new certificate equal to an attested one is accepted for this.

### For maintainers

Before merging a pull request with new certificates, check out its branch and run:

```bash
python scripts/verify_certificates.py --jobs 4
```

This checks every certificate awaiting verification, as well as any whose manifest entry differs from the base branch's, so entries a pull request adds itself are checked again rather than trusted. Attested certificates are only checked when named by ID. Certificates that pass get manifest entries; commit `certificates/verified.yml` to the branch. The checkers must be committed, so the recorded commit says exactly what checked the evidence, and the script warns when they differ from the base branch, as when a pull request adds a checker for a new family: review those changes first. `--all` re-checks every certificate except attested ones, as an audit.

## Colorings

Witnesses with `format: coloring` give one color per integer, in base 36: `0` to `9`, then `a` to `z` for colors 10 to 35 (so at most 36 colors). Whitespace and case are ignored.

## Graph witnesses

Families whose witnesses are graphs accept them in [graph6 or sparse6](https://users.cecs.anu.edu.au/~bdm/data/formats.txt) format (`format: graph6` or `format: sparse6`), with vertices numbered from 0. Use whichever is shorter: graph6 for dense graphs, sparse6 for sparse ones. By convention, witness files use the extensions `.g6` and `.s6`.

## Families

### Ramsey numbers: `ramsey-{r}-{s}`

Formal statements are in [`formal/LeapsInBounds/Statements/Ramsey.lean`](../formal/LeapsInBounds/Statements/Ramsey.lean):

- `LowerBound r s n` means `R(r,s) >= n`: some graph on `n - 1` vertices has no clique of size `r` and no independent set of size `s`.
- `UpperBound r s n` means `R(r,s) <= n`: every graph on `n` vertices has a clique of size `r` or an independent set of size `s`.

The same file proves that a lower bound never exceeds an upper bound, as a sanity check on the definitions.

Witnesses can certify lower bounds only. A witness for `R(r,s) >= n` is a graph on `n - 1` vertices with no `r`-clique and no independent set of size `s`.

### Van der Waerden numbers: `van-der-waerden-{r}-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/VanDerWaerden.lean`](../formal/LeapsInBounds/Statements/VanDerWaerden.lean):

- `LowerBound r k n` means `W(r,k) >= n`: some `r`-coloring of `n - 1` consecutive integers has no monochromatic arithmetic progression of length `k`.
- `UpperBound r k n` means `W(r,k) <= n`: every `r`-coloring of `n` consecutive integers has one.

Witnesses can certify lower bounds only. A witness for `W(r,k) >= n` uses `format: coloring`: a string of `n - 1` colors from `0` to `r - 1`, the colors of consecutive integers, with no monochromatic arithmetic progression of length `k`. See [Colorings](#colorings).

### Cages: `cage-{k}-{g}`

Formal statements are in [`formal/LeapsInBounds/Statements/Cage.lean`](../formal/LeapsInBounds/Statements/Cage.lean):

- `LowerBound k g n` means `n(k,g) >= n`: no graph on fewer than `n` vertices is `k`-regular with girth `g`.
- `UpperBound k g n` means `n(k,g) <= n`: some graph on `n` vertices is `k`-regular with girth `g`.

Witnesses can certify upper bounds only. A witness for `n(k,g) <= n` is a `k`-regular graph of girth exactly `g` on `n` vertices.

### Degree-diameter problem: `degree-diameter-{d}-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/DegreeDiameter.lean`](../formal/LeapsInBounds/Statements/DegreeDiameter.lean):

- `LowerBound d k n` means `N(d,k) >= n`: some graph on `n` vertices has maximum degree at most `d` and diameter at most `k`.
- `UpperBound d k n` means `N(d,k) <= n`: every such graph has at most `n` vertices.

Witnesses can certify lower bounds only. A witness for `N(d,k) >= n` is a graph on `n` vertices with maximum degree at most `d` and diameter at most `k`.

Graphs too large for sparse6 within the [size limit](#size-limit) can use `format: hamming-lines` if they have this structure. It's a binary file, by convention with the extension `.h4l`:

- The base graph has `F` fibers, each with 256 vertices `(x0, x1, x2, x3)`, coordinates from 0 to 3, so vertex `256 f + x0 + 4 x1 + 16 x2 + 64 x3`. Each fiber has 256 lines of 4 vertices: line `256 f + 64 a + i` varies coordinate `a` and fixes the other three, in increasing order, to the base-4 digits of `i`, least significant first. Each line has a partner line, the partners pairing up all `256 F` lines, and each line is joined completely to its partner (a `K_{4,4}`). There are no other edges.
- Then `C` clones are added as vertices `256 F` onwards, each joined to the neighbors of its source vertex in the base graph.
- The file is the 8 bytes `H4LINE01`, then `F` and `C` as 4-byte unsigned little-endian integers, then the partner of each line in order and the source of each clone, each as a `b`-bit number, where `b` is the number of bits in `256 F - 1`. These are written as one stream of bits, each number least significant bit first, packed into bytes from their least significant bit, with the last byte padded with 0 bits.

The checker reconstructs the graph and checks that it's simple, as well as its degrees and diameter.

### Minimal superpermutations: `minimal-superpermutation-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Superpermutation.lean`](../formal/LeapsInBounds/Statements/Superpermutation.lean):

- `LowerBound n m` means `L(n) >= m`: every string containing all permutations of `n` symbols has length at least `m`.
- `UpperBound n m` means `L(n) <= m`: some such string has length at most `m`.

Witnesses can certify upper bounds only. A witness for `L(n) <= m` uses `format: string`: a string of at most `m` symbols from `1` to `n` that contains every permutation of those symbols as a contiguous substring. Symbols past `9` are letters, `a` for 10 and so on (so `n <= 35`). Whitespace and case are ignored.

### Kissing numbers: `kissing-number-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/KissingNumber.lean`](../formal/LeapsInBounds/Statements/KissingNumber.lean):

- `LowerBound n k` means `τ(n) >= k`: some `k` unit vectors in `ℝⁿ` are at distance at least 1 from each other (so unit spheres centered at twice these vectors touch the unit sphere at the origin without overlapping).
- `UpperBound n k` means `τ(n) <= k`: every such set of unit vectors has at most `k` vectors.

Witnesses can certify lower bounds only. A witness for `τ(n) >= k` uses `format: vectors`: `k` integer vectors, one per line with whitespace-separated entries, all with the same squared norm `N`, spanning a space of dimension at most `n` (they can have more than `n` coordinates), with every inner product between two of them at most `N / 2`. Normalized, these are unit vectors at angles of at least 60°, which is the same condition.

Large symmetric configurations can be given as a few seed vectors and a list of `symmetries`: signed permutations of the coordinates, each written as a list `s` of the numbers `±1` to `±m` in some order, mapping `x` to the vector whose `i`-th entry is `sign(s[i]) * x[|s[i]|]`. The configuration is then every image of the seeds under repeated symmetries, and must have exactly `k` vectors. The symmetries don't need to be symmetries of anything in particular: the checker only uses them to generate the vectors. For example, the 240 roots of `E_8` (scaled by 2):

```yaml
witness:
  format: vectors
  data: |
    2 2 0 0 0 0 0 0
    1 1 1 1 1 1 1 1
  symmetries:
  - [2, 1, 3, 4, 5, 6, 7, 8]     # swap the first two coordinates
  - [2, 3, 4, 5, 6, 7, 8, 1]     # cycle the coordinates
  - [-1, -2, 3, 4, 5, 6, 7, 8]   # negate the first two coordinates
```

### Packing unit squares in a square: `square-packing-in-square-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/SquarePacking.lean`](../formal/LeapsInBounds/Statements/SquarePacking.lean). A unit square is the image of `[0, 1]²` under an isometry of the plane, and a packing of `n` of them in `[0, s]²` has pairwise disjoint interiors.

- `SqrtLowerBound n m` means `s(n) >= √m`: no packing of `n` unit squares fits in a square of side less than `√m`.
- `SqrtUpperBound n m` means `s(n) <= √m`: `n` unit squares can be packed in a square of side `√m`.

Values can be integers `k` (proving the statement with `m = k²`) or square roots written `'\sqrt{m}'`, with `m` not a perfect square. Only Lean proofs are accepted so far.

### Packing unit circles in an equilateral triangle: `circle-in-equilateral-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/CircleInTriangle.lean`](../formal/LeapsInBounds/Statements/CircleInTriangle.lean). A packing of `n` unit circles in the equilateral triangle with vertices `(0, 0)`, `(s, 0)` and `(s / 2, s√3 / 2)` places `n` closed unit disks inside it with pairwise disjoint interiors.

- `RadicalLowerBound n terms d` means `s(n) >= radical terms d`: no packing of `n` unit circles fits in an equilateral triangle of smaller side.
- `RadicalUpperBound n terms d` means `s(n) <= radical terms d`: `n` unit circles can be packed in an equilateral triangle of that side.

Values are sums of rational multiples of square roots, written in LaTeX as a sum of terms `a`, `a\sqrt{m}` or `\frac{a\sqrt{m}}{b}` (each with an optional sign, and `a` optional before a square root), such as `'4+2\sqrt{3}+\frac{4\sqrt{6}}{3}'`. In Lean, `radical terms d` (from [`Radical.lean`](../formal/LeapsInBounds/Statements/Radical.lean)) is the real number `(c₁ √m₁ + ⋯ + cₖ √mₖ) / d` for `terms = [(c₁, m₁), …, (cₖ, mₖ)]`. The checker rewrites the value with squarefree `mᵢ` in increasing order (`1` for the rational part), integer `cᵢ`, and `d` the least common denominator, so that value must be proved as `RadicalLowerBound n [(12, 1), (6, 3), (4, 6)] 3` or `RadicalUpperBound n [(12, 1), (6, 3), (4, 6)] 3`.

Witnesses can certify upper bounds only. A witness for `s(n) <= v` uses `format: points`: the `n` centers in the triangle above with `s = v`, one per line as `x, y`, with coordinates in the same form as values. The checker decides exactly, without rounding, that each center is at distance at least 1 from each side of the triangle and at least 2 from the other centers, so circles can touch each other and the sides. For example, 4 circles in a triangle of side `4√3`:

```yaml
witness:
  format: points
  data: |
    \sqrt{3}, 1
    3\sqrt{3}, 1
    2\sqrt{3}, 2
    2\sqrt{3}, 4
```

### Packing unit circles in a square: `circle-in-square-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/CircleInSquare.lean`](../formal/LeapsInBounds/Statements/CircleInSquare.lean). A packing of `n` unit circles in the square `[0, s]²` places `n` closed unit disks inside it with pairwise disjoint interiors.

- `RadicalLowerBound n terms d` means `s(n) >= radical terms d`: no packing of `n` unit circles fits in a square of smaller side.
- `RadicalUpperBound n terms d` means `s(n) <= radical terms d`: `n` unit circles can be packed in a square of that side.

Values are written as for [circle packing in a triangle](#packing-unit-circles-in-an-equilateral-triangle-circle-in-equilateral-n), and can also be decimals, such as `'6.747443'` (quoted, so that it's read as text).

Witnesses can certify upper bounds only. A witness for `s(n) <= v` uses `format: points`: the `n` centers, one per line as `x, y`, with coordinates in the same form as values. The checker decides exactly, without rounding, that each center lies in `[1, v - 1]²` and is at distance at least 2 from the other centers. Most optimal packings have sides that aren't sums of square roots; for these, a witness can round the centers to decimals and the side up, certifying a value just above the optimum.

### Schur numbers: `schur-{k}` and `weak-schur-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/Schur.lean`](../formal/LeapsInBounds/Statements/Schur.lean):

- `LowerBound k n` means `S(k) >= n`: some `k`-coloring of `1, …, n` has no monochromatic solution to `x + y = z` (with `x = y` allowed).
- `UpperBound k n` means `S(k) <= n`: every `k`-coloring of `1, …, n + 1` has one.
- `WeakLowerBound k n` and `WeakUpperBound k n` are the same for the weak Schur number `WS(k)`, counting only solutions with `x ≠ y`.

Witnesses can certify lower bounds only. A witness for `S(k) >= n` or `WS(k) >= n` uses `format: coloring`: a string of `n` colors from `0` to `k - 1`, the colors of `1, …, n`, with no monochromatic solution. See [Colorings](#colorings).

### Multicolor Ramsey numbers for triangles: `multicolor-ramsey-triangle-{k}`

Formal statements are in [`formal/LeapsInBounds/Statements/MulticolorRamsey.lean`](../formal/LeapsInBounds/Statements/MulticolorRamsey.lean), where an edge coloring of `K_n` is a function `c : Fin n → Fin n → Fin k`, with `c a b` the color of the edge between `a < b`:

- `LowerBound k n` means `R_k(3) >= n`: some coloring of the edges of `K_{n - 1}` with `k` colors has no monochromatic triangle.
- `UpperBound k n` means `R_k(3) <= n`: every coloring of the edges of `K_n` with `k` colors has one.

Witnesses can certify lower bounds only. A witness for `R_k(3) >= n` is a coloring of the edges of `K_{n - 1}`, with vertices `0` to `n - 2`, in one of two formats, with colors from `0` to `k - 1` (see [Colorings](#colorings)):

- `format: edge-coloring`: a string of `(n - 1)(n - 2) / 2` colors, those of the edges `(0, 1), (0, 2), …, (0, n - 2), (1, 2), …, (n - 3, n - 2)` in that order, with no monochromatic triangle.
- `format: coloring`: a string of `n - 2` colors, those of the differences `1, …, n - 2`, where the edge between `u` and `v` gets the color of `|u - v|`. A triangle `a < b < d` is monochromatic when `b - a`, `d - b` and their sum `d - a` have the same color, so this is a Schur coloring of `1, …, n - 2`, and a witness for `S(k) >= n - 2` is also one for `R_k(3) >= n`.

### Optimal Golomb rulers: `golomb-ruler-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Golomb.lean`](../formal/LeapsInBounds/Statements/Golomb.lean):

- `LowerBound n L` means `G(n) >= L`: every Golomb ruler with `n` marks has two marks at least `L` apart.
- `UpperBound n L` means `G(n) <= L`: some Golomb ruler with `n` marks has its marks in `0, …, L`.

Witnesses can certify upper bounds only. A witness for `G(n) <= L` uses `format: marks`: `n` distinct integers from `0` to `L`, separated by whitespace or commas, whose pairwise differences are all distinct. For example, `'0 1 4 9 11'` for `G(5) <= 11`.

### Sorting networks: `sorting-network-size-{n}` and `sorting-network-depth-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/SortingNetwork.lean`](../formal/LeapsInBounds/Statements/SortingNetwork.lean). A network is a list of comparators `(i, j)` on wires numbered from `0`, applied in order, each putting the smaller of the two values on wire `min(i, j)` and the larger on the other. It sorts if it leaves every input of `n` values in increasing order on wires `0, …, n - 1`. Its depth is the length of the longest chain of comparators, each sharing a wire with the one before it: the number of steps it takes when comparators on different wires act at the same time.

- `SizeLowerBound n L` means `S(n) >= L`: every sorting network on `n` inputs has at least `L` comparators.
- `SizeUpperBound n L` means `S(n) <= L`: some sorting network on `n` inputs has at most `L` comparators.
- `DepthLowerBound n L` and `DepthUpperBound n L` mean `D(n) >= L` and `D(n) <= L`, for the depth.

Witnesses can certify upper bounds only. A witness for `S(n) <= L` or `D(n) <= L` uses `format: comparators`: a sorting network on `n` wires, as its comparators `i,j` in order, separated by whitespace, with at most `L` comparators or depth at most `L`. Writing each step's comparators on one line is clearer, but not needed. For example, `'0,2 1,3 0,1 2,3 1,2'` for `S(4) <= 5` and `D(4) <= 3`. The checker uses the 0-1 principle, and checks only the inputs that the network's first comparators can output, so it's fastest when they make a full layer.

### Snake-in-the-box and coil-in-the-box: `snake-in-the-box-{n}` and `coil-in-the-box-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/SnakeInTheBox.lean`](../formal/LeapsInBounds/Statements/SnakeInTheBox.lean). The vertices of the hypercube `Q_n` are the binary vectors of length `n`, two of them adjacent if they differ in one coordinate. A snake is an induced path in `Q_n` (its vertices are adjacent only when consecutive), and a coil is an induced cycle. Lengths count edges.

- `LowerBound n L` means some snake in `Q_n` has length at least `L`.
- `UpperBound n L` means every snake in `Q_n` has length at most `L`.
- `CoilLowerBound n L` and `CoilUpperBound n L` are the same for coils.

Witnesses can certify lower bounds only. A witness for a snake or coil of length `L` uses `format: transitions`: its transition sequence, the `L` coordinates (from `0` to `n - 1`) that change along its edges in order, starting from the vertex `0`. Each coordinate is one character, in base 36 (`0` to `9`, then `a` to `z`, so `n <= 36`), and whitespace is ignored. A coil's transitions must lead back to `0`. For example, `'0120'` for a snake of length 4 in `Q_3` (`000`, `001`, `011`, `111`, `110`), or `'012012'` for a coil of length 6.

### Cap sets: `cap-set-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/CapSet.lean`](../formal/LeapsInBounds/Statements/CapSet.lean). A cap set is a set of points in `F_3^n` with no three on a line. Three distinct points `x`, `y`, `z` are on a line exactly when `x + y + z = 0`.

- `LowerBound n L` means `r(n) >= L`: some cap set in `F_3^n` has at least `L` points.
- `UpperBound n L` means `r(n) <= L`: every cap set in `F_3^n` has at most `L` points.

Witnesses can certify lower bounds only. A witness for `r(n) >= L` uses `format: points`: `L` distinct points, separated by whitespace, each written as its `n` coordinates, digits from `0` to `2` with nothing between them. For example, `'00 01 10 11'` for `r(2) >= 4`.

### No-three-in-line problem: `no-three-in-line-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/NoThreeInLine.lean`](../formal/LeapsInBounds/Statements/NoThreeInLine.lean). The points of the `n × n` grid are the pairs `(x, y)` of integers from `0` to `n - 1`.

- `LowerBound n L` means `D(n) >= L`: some `L` points of the grid have no three on a line.
- `UpperBound n L` means `D(n) <= L`: any points of the grid with no three on a line number at most `L`.

Witnesses can certify lower bounds only. A witness for `D(n) >= L` uses `format: points`: `L` distinct points, separated by whitespace, each written `x,y`. For example, `'0,0 0,1 1,0 1,1'` for `D(2) >= 4`.

### Isosceles sets: `isosceles-set-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/IsoscelesSet.lean`](../formal/LeapsInBounds/Statements/IsoscelesSet.lean). An isosceles set is a set of points any three of which form an isosceles triangle.

- `LowerBound n L` means `i(n) >= L`: some isosceles set in `R^n` has at least `L` points.
- `UpperBound n L` means `i(n) <= L`: every isosceles set in `R^n` has at most `L` points.

Witnesses can certify lower bounds only. A witness for `i(n) >= L` uses `format: points`: `L` distinct points, one per line, with coordinates separated by commas. Each coordinate is a sum of rational multiples of square roots, written in LaTeX as a sum of terms `a`, `a\sqrt{m}` or `\frac{a\sqrt{m}}{b}`, such as `\frac{1}{2}+\frac{\sqrt{5}}{2}`. The points can have more than `n` coordinates, as long as they span an affine subspace of dimension at most `n`, which the checker computes exactly. This allows simple coordinates for many constructions, such as the points `e_i + e_j` of `R^(n+1)`, which lie in a hyperplane. For example, the three lines `0`, `1` and `2` for `i(1) >= 3`.

### Arrangements of lines: `affine-line-arrangements-{n}` and `affine-line-arrangements-general-position-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/LineArrangement.lean`](../formal/LeapsInBounds/Statements/LineArrangement.lean). The combinatorial type of an arrangement of distinct lines in the plane is given by its covectors, the vectors of signs saying which side of each line a point is on, up to renumbering the lines and swapping their sides. This identifies mirror images.

- `LowerBound n N` means there are at least `N` types of arrangements of `n` lines: some `N` arrangements are pairwise of different types.
- `UpperBound n N` means there are at most `N`: among any `N + 1` arrangements, two have the same type.
- `GeneralLowerBound n N` and `GeneralUpperBound n N` are the same for arrangements in general position, with no two lines parallel and no three through a point.

OEIS A241600 counts arrangements up to rigid isotopy rather than combinatorial type. Isotopic arrangements have the same type, so a lower bound on the number of types is also a lower bound for A241600.

Witnesses can certify lower bounds only. A witness for `LowerBound n N` or `GeneralLowerBound n N` uses `format: lines`: arrangements of at least `N` types, one per row, each as `3n` integers `a b c`, one triple for each line `a x + b y = c`. Arrangements of the same type can repeat, so a [generator](#generators) can print random samples without removing repeats itself. The checker computes a canonical form of each arrangement's type, and counts the distinct forms by an 8-byte hash of each: two types sharing a hash would only be undercounted. For an arrangement in general position, the form comes from the order in which the other lines cross each line, which is fast: about 0.1 ms per arrangement of 10 lines, on each core. For others, it comes from the arrangement's covectors, computed exactly (at the vertices, on each edge, and on either side of each edge), which is about 100 times slower. The checker reads a generator's output as a stream, so it can print any amount, as long as checking it takes about an hour at most. For example, the two arrangements of 2 lines, parallel and crossing:

```yaml
witness:
  format: lines
  data: |
    1 0 0 1 0 1
    1 0 0 0 1 0
```

### Rectilinear crossing number: `rectilinear-crossing-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/RectilinearCrossing.lean`](../formal/LeapsInBounds/Statements/RectilinearCrossing.lean). A drawing of the complete graph `K_n` places its vertices at `n` points of the plane, no three on a line, and draws its edges as segments. Two edges cross if they share no vertex and their segments meet.

- `LowerBound n c` means `cr(K_n) >= c`: every such drawing has at least `c` crossings.
- `UpperBound n c` means `cr(K_n) <= c`: some such drawing has at most `c` crossings.

Witnesses can certify upper bounds only. A witness for `cr(K_n) <= c` uses `format: points`: `n` distinct points with integer coordinates, no three on a line, written `x,y` and separated by whitespace. The checker counts the crossings exactly: two edges cross exactly when their four ends are in convex position, so it counts the 4-point subsets with no point inside the triangle of the other three. For example, a triangle with two points inside, for `cr(K_5) <= 1`:

```yaml
witness:
  format: points
  data: '0,0 6,0 3,6 2,2 4,3'
```

### Chromatic number of Euclidean space: `chromatic-number-space-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/ChromaticNumberSpace.lean`](../formal/LeapsInBounds/Statements/ChromaticNumberSpace.lean). A coloring of `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`) with `k` colors is any function to `Fin k`, with no assumption such as measurability, and it's proper if no two points at distance 1 have the same color.

- `LowerBound n k` means `χ(ℝⁿ) >= k`: no coloring with `k - 1` colors is proper.
- `UpperBound n k` means `χ(ℝⁿ) <= k`: some coloring with `k` colors is proper.

The same file proves that a lower bound never exceeds an upper bound. Only Lean proofs are accepted so far, here or attested.

### Busy beaver functions: `busy-beaver-shift-{n}` and `busy-beaver-ones-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/BusyBeaver.lean`](../formal/LeapsInBounds/Statements/BusyBeaver.lean). An `n`-state, 2-symbol Turing machine starts on a blank tape, infinite in both directions, and in each state, for each symbol read, writes a symbol, moves left or right, and goes to a state or halts. The halting transition also writes and moves, and counts as a step.

- `ShiftLowerBound n N` means `BB(n) >= N`: some `n`-state machine halts after at least `N` steps.
- `ShiftUpperBound n N` means `BB(n) <= N`: every `n`-state machine that halts does so within `N` steps.
- `OnesLowerBound n N` and `OnesUpperBound n N` are the same for `Σ(n)`, the number of 1s on the tape when the machine halts.

Witnesses can certify lower bounds only. A witness uses `format: turing-machine`: the machine in the [standard text format](https://wiki.bbchallenge.org/wiki/Standard_TM_Text_Format), such as `1RB1LB_1LA1RZ` for `BB(2) >= 6` and `Σ(2) >= 4`. For each state `A`, `B`, … in turn, separated by `_`, it gives the transitions on reading 0 and 1, each as the symbol to write, the direction (`L` or `R`) and the next state. A next state after the first `n` letters, conventionally `Z` or `H`, halts, and an undefined transition `---` halts as `1RZ` does. The machine starts in state `A`. The checker simulates it, for at most 10⁹ steps, so it can check the 5-state champion (47,176,870 steps) but not the 6- and 7-state ones, which run for far too long to simulate: those need a proof of the machine's behavior, in Lean here or [attested](#attestations).

### Stamp folding and map folding: `stamp-folding-{n}` and `map-folding-{m}-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Folding.lean`](../formal/LeapsInBounds/Statements/Folding.lean). A folding of an `m × n` map, with its cells labeled, is counted by its final stack: the order of the cells from the bottom up. The creases between rows `i` and `i + 1` all end up on one edge of the stack, and those for the next `i` on the opposite edge, and the same for columns. Each crease joins the levels of its two cells, and a stack is a folding exactly when no two creases on the same edge cross: their intervals of levels are nested or disjoint. A strip of `n` stamps is the `1 × n` map.

- `LowerBound m n N` means there are at least `N` foldings of the `m × n` map.
- `UpperBound m n N` means there are at most `N`.
- `StampLowerBound n N` and `StampUpperBound n N` are the same for the strip of `n` stamps.

Witnesses can certify lower bounds only. A witness uses `format: stacks`: at least `N` distinct stacks, separated by whitespace, each a folding written as its cells from the bottom up, with the cells numbered from `0` row by row: one character each in base 36, or, for maps of more than 36 cells, two base-36 characters each (such as `000102...18` for 45 cells) or decimal numbers separated by commas (such as `0,1,2,...,44`). For example, `'012 021 102 120 201 210'` for the 6 foldings of 3 stamps. Stacks can repeat; the checker counts the distinct ones by an 8-byte hash of each, so two sharing a hash would only be undercounted. Since the witness lists the foldings, the [size limit](#size-limit) allows counts up to a few hundred thousand in a file: with the stacks sorted, xz compresses them to under a byte each. Larger counts can be given by a [generator](#generators), whose output the checker reads as a stream, so it can print any amount, as long as checking it takes about an hour at most. Checking takes about 2 µs per stack of 15 stamps, on each core, and about 35 µs per stack of a 7 × 18 map written with commas (15 µs with two characters per cell).

### Covering a disk with disks: `disk-covering-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/DiskCovering.lean`](../formal/LeapsInBounds/Statements/DiskCovering.lean):

- `RadicalLowerBound n terms d` means `r(n) >= radical terms d`: no `n` closed disks of smaller radius cover the closed unit disk.
- `RadicalUpperBound n terms d` means `r(n) <= radical terms d`: some `n` closed disks of that radius cover it.

Values are written as for [circle packing](#packing-unit-circles-in-an-equilateral-triangle-circle-in-equilateral-n), and can also be decimals, such as `'0.6094'` (quoted, so that it's read as text).

Witnesses can certify upper bounds only. A witness for `r(n) <= v` uses `format: points`: the `n` centers, one per line as `x, y`, with rational coordinates written as integers, decimals or `\frac{a}{b}`. The radius must have a rational square. The checker covers the square `[-1, 1]²` with smaller and smaller squares, until each one misses the unit disk or lies in one of the disks, all with exact rational arithmetic. This finishes when the disks cover the unit disk with some room to spare, but not when they cover it only just, as optimal coverings do at the points where three boundaries meet. So a witness can only certify a radius slightly above the optimum of its configuration: round the radius up, in the sixth or seventh decimal place.

### The de Bruijn–Newman constant: `debruijn-newman`

Formal statements are in [`formal/LeapsInBounds/Statements/DeBruijnNewman.lean`](../formal/LeapsInBounds/Statements/DeBruijnNewman.lean), in terms of the zeros of `H(t, z)`:

- `RadicalLowerBound terms d` means `Λ >= radical terms d`: for every `t` below it, `H(t, ·)` has a zero that isn't real.
- `RadicalUpperBound terms d` means `Λ <= radical terms d`: for every `t` at least it, every zero of `H(t, ·)` is real.

Values are written as for disk covering, such as `'0.2'` or `-50`. Only Lean proofs are accepted, here or attested.

### The Tammes problem: `tammes-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Tammes.lean`](../formal/LeapsInBounds/Statements/Tammes.lean), with angles in degrees:

- `RadicalLowerBound n terms d` means `T(n) >= radical terms d`: some `n` points on the unit sphere are each at least that many degrees apart.
- `RadicalUpperBound n terms d` means `T(n) <= radical terms d`: no `n` points on the unit sphere are each further apart.

Values are written as for disk covering, such as `'57.13670307'` or `90`.

Witnesses can certify lower bounds only, at a rational number of degrees. A witness for `T(n) >= a` uses `format: vectors`: `n` nonzero vectors in `ℝ³`, one per line as `x, y, z`, with rational coordinates written as integers, decimals or fractions `a/b`. They needn't have unit length: the points are the vectors scaled to it. The checker compares the cosine of the angle between each two vectors, exactly, with rational bounds on `cos(a°)` from interval arithmetic. That decides every pair unless the angle is exactly `a` and `cos(a°)` is irrational, which happens for an optimal configuration whose angle is the bound. So, except at `60`, `90`, `120` and `180` degrees, where `cos(a°)` is rational, round the angle down a little, in the eighth decimal place, say.

### The Heilbronn triangle problem: `heilbronn-square-{n}` and `heilbronn-triangle-{n}`

Formal statements are in [`formal/LeapsInBounds/Statements/Heilbronn.lean`](../formal/LeapsInBounds/Statements/Heilbronn.lean):

- `SquareRadicalLowerBound n terms d` means `H(n) >= radical terms d`: some `n` points in the unit square `[0, 1]²` have every three forming a triangle of at least that area. `SquareRadicalUpperBound n terms d` means no `n` points do better.
- `TriangleRadicalLowerBound n terms d` and `TriangleRadicalUpperBound n terms d` are the same for `Δ(n)`, with points in the triangle with vertices `(0, 0)`, `(1, 0)` and `(0, 1)`, and areas as a fraction of its area `1/2`. Any triangle can be mapped to this one by an affine map, which scales all areas by the same factor.

Values are written as for disk covering, such as `'0.02701991666'` or `'\frac{1}{27}'`.

Witnesses can certify lower bounds only. A witness uses `format: points`: `n` points, one per line as `x, y`, in the square or triangle above, with coordinates written as for circle packing: decimals, fractions `\frac{a}{b}` or sums of rational multiples of square roots. With rational coordinates every area is rational, so the checker compares each of the `n choose 3` areas with the bound exactly. Optimal configurations usually have irrational coordinates, so a configuration with decimal coordinates attains a value slightly off the optimum: give the exact least area of the coordinates as written, rounded down, such as to ten significant digits.

### The moving sofa constant: `moving-sofa`

Formal statements are in [`formal/LeapsInBounds/Statements/MovingSofa.lean`](../formal/LeapsInBounds/Statements/MovingSofa.lean):

- `RadicalLowerBound terms d` means the constant is at least `radical terms d`: some connected shape of at least that area moves around the corner of the hallway of width 1, by a continuous family of rotations and translations.
- `RadicalUpperBound terms d` means it's at most `radical terms d`: every such shape has at most that area.

Values are written as for disk covering, such as `'2.37'`. Only Lean proofs are accepted, here or attested.

### Lebesgue's universal covering problem: `lebesgue-universal-cover`

Formal statements are in [`formal/LeapsInBounds/Statements/LebesgueCover.lean`](../formal/LeapsInBounds/Statements/LebesgueCover.lean):

- `RadicalLowerBound terms d` means the constant is at least `radical terms d`: every convex set that contains a congruent copy (by an isometry of the plane, reflections included) of every set of diameter at most 1 has at least that area.
- `RadicalUpperBound terms d` means it's at most `radical terms d`: some such convex set has at most that area.

Values are written as for disk covering, such as `'0.8440935944'`. Only Lean proofs are accepted, here or attested.

## Checking locally

To run the checkers on certificates, give their IDs:

```bash
python scripts/verify_certificates.py --dry-run ramsey-4-4-lower-18
```

Lean proofs need [elan](https://github.com/leanprover/elan) and Mathlib (`cd formal && lake exe cache get`). To run CI's checks of structure and consistency, without the checkers:

```bash
python scripts/check_certificates.py --allow-pending --new certificates/<family>/<file>.yml
```

## Blocked bounds

[`blocked.yml`](blocked.yml) lists current bounds that can't be certified yet, and why, so that the same dead ends aren't tried again:

```yaml
- constants: [kissing-number-17, kissing-number-18]
  bound: lower
  reason: needs-format
  checked: 2026-10-30
  detail: The records use irrational coordinates, and witnesses must have integer coordinates.
```

The reason is one of:

- `unpublished`: the construction or proof isn't public, or couldn't be found in the paper, its ancillary files or the authors' repositories.
- `too-large`: the evidence is over the [size limit](#size-limit) even compressed, and there's no stable link to [attest](#attestations) it with.
- `needs-format`: the family's checker can't read this kind of witness or value yet (see [Known gaps](#known-gaps)). A change to the checker would unblock it, in a pull request of its own.
- `too-slow`: checking it here takes too long, and no one has attested it.
- `out-of-reach`: a Lean proof would need formalization or computation beyond what's practical for now.

The bounds are marked with their reason in [`unverified_bounds.json`](https://leapsinbounds.org/data/unverified_bounds.json). If a bound improves after it was `checked`, it's marked as stale, since the new bound may come with a witness. The build warns about entries for bounds that have since been verified, which can be removed. A search that fell short of a record isn't a blocked bound: record it in the [search notes](../notes/README.md) instead.

## Known gaps

- Values are integers, decimals or sums of rational multiples of square roots for now. Other real values, such as most known square packings and disk coverings, will need more general exact arithmetic (such as nested square roots or roots of polynomials). Disk covering witnesses are checked with rational arithmetic, so they can only certify radii slightly above an optimal covering's, not the optimum itself.
- Kissing number witnesses must have integer coordinates (up to scaling). Some record configurations, such as those in dimensions 17 to 21, need irrational coordinates, so they can't be submitted yet.
