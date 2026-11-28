# Draft compact-witness proposal: 113,000,001 ten-line arrangements

**Submission status: DRAFT; not an accepted Leaps in Bounds certificate.**

Proposed lower-bound certificate for both:
- `affine-line-arrangements-general-position-10 >= 113000001`
- `affine-line-arrangements-10 >= 113000001`

Contributors: **Sami Hani Badaoui** and **Sarah Ellen Mary Vaughan**. GitHub submission account: **bargainlandz-code**. Computational work was conducted with AI assistance.

## Mathematical claim

We have a locally verified family of 113,000,001 pairwise inequivalent arrangements of ten straight affine lines in general position. These are explicit *lower-bound constructions*, not a determination of the exact total number or a claim of confirmed historical world-record priority.

For each witness, use ten equations `-m_i x + y = t_i`, with strictly increasing integral slopes `m_0<...<m_9`. Put `m_0=t_0=0`. For the first 10,000,001 witnesses, slopes are `m_i=i`. Later witnesses are encoded as nine positive unsigned-byte slope increments and nine signed 32-bit integer intercepts (45 bytes per witness).

For `i≠j`, the crossing abscissa is exactly
`x_ij = (t_i - t_j)/(m_j-m_i)`.
A verifier checks all nine crossings along each line have distinct exact rational values, so all 45 pairwise intersections are ordinary and there is no triple concurrence.

For each line, record its permutation of the other nine line indices ordered by crossing position. Canonicalize the ten nine-permutations under the 20 possible cyclic choices of starting line-end at infinity and their two orientations, **including reflections**. The resulting ten Lehmer ranks occupy 190 bits. An equivalence of affine arrangements induces one of these 40 transforms, so two *distinct* canonical keys prove two *inequivalent* arrangements. The local hash tables compare the full three-word keys on collisions, not hash values alone.

## Recorded independently checked counts

| Component | Witnesses |
|---|---:|
| Original fixed-slope construction | 10,000,001 |
| Additional variable-slope stage one | 60,000,000 |
| Additional variable-slope stage two | 30,000,000 |
| Chamber-crossing stages | 10,000,000 |
| Final chamber-crossing stage | 3,000,000 |
| **Total** | **113,000,001** |

The independently written global C++ checker recorded:
`PASS: independently canonicalized 113000001 inequivalent ten-line arrangements including reflections`.

The independently written exact determinant geometry checker recorded:
`PASS: 3000000 new variable-slope arrangements; all 45 pairs intersect and all 120 line triples are nonconcurrent for every arrangement`.

The original final-stage compressed 3,000,000-row binary witness SHA-256 was:
`c0895ab7a23324cc275e21dfeff42d2a24c69ba681fe91cd7d52203a165e12cd`.
The uncompressed final-stage SHA-256 was:
`626bfc7643cc2d1f8ae72f8418d1bb34378b7aafed3484247454e4319bfd2077`.

The locally preserved full dossier also records 109 distributed exact-rational cross-checks against the site's complete covector convention. These are *local computational checks*, not external attestation.

## Why a compact certificate format is needed

The site currently accepts a literal `witness.format: lines` file consisting of 30 integers for each arrangement. A 113-million-row witness is too large for the site's **500 kB repository evidence limit**. The additional 103 million binary witnesses alone occupy 4.635 GB before compression.

Following the site's accepted compact graph format precedent (degree-diameter PR #77) and Lean proof precedent (Golomb PR #70), we propose a new *deterministically generated* ten-line witness format, whose checker:

1. Reconstructs all five stages from committed source and fixed numerical seeds, without trusting a list of asserted distinctness values.
2. Rejects invalid general-position geometry using exact integer arithmetic.
3. Computes the full lossless canonical key under reflections and checks exact global distinctness across all 113,000,001 witnesses.
4. Verifies stage counts and known SHA-256s of reproduced outputs.
5. Runs the separately written independent canonical and geometry implementations as a secondary audit.

This would require trusted checker changes, a substantial memory/time budget and maintainer review. **The current repository's `format: lines` checker cannot accept this proposal unchanged.** A permanent externally hosted witness and attestation under the existing format is the fallback.

## Explicit limitations

- **This draft is not a finished valid YAML certificate.** Source scripts and the complete reproduction chain must be staged and independently rerun under the proposed checker before asking for merge.
- The compressed original witness parts are preserved privately, but a permanent public URL for the full site-format witness does **not** yet exist.
- No third-party referee has independently confirmed the 113-million count, and historical world-record priority is not established.

**No acceptance or verified-site status is claimed.**
