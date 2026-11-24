# Degree-diameter notes

## Initial lower bounds for d up to 20 and k up to 10 (2026-11)

Every constant from d = 4 to 20 and k = 3 to 10 without a verified lower bound got one from a random Cayley graph of a metacyclic group: Z_m ⋊ Z_s with product (a, b)(c, e) = (a + r^b c, b + e), where r^s ≡ 1 (mod m), and a random inverse-closed connection set of size at most d. The search was a small C program. Cayley graphs are vertex-transitive, so it needs only one BFS from the identity per candidate. For each order N it picks random (m, s, r) and random connection sets. Each certificate's notes give the group and connection set, so the graph can be rebuilt.

**Cap of 4000 vertices.** The checker in `scripts/certificates/families/degree_diameter.py` runs a bitset BFS from every vertex on Python big integers, which costs roughly n³/64 word operations. On a lightly loaded machine, n = 3000 takes about 8 s of CPU time and n = 4000 about 20 s. Bigger graphs fit easily within the 500 kB limit (sparse6 for n = 4000 and d = 20 is about 90 kB), so time is what limits them. With 112 certificates, 4000 vertices was the cap, so most of these constants have a bound of exactly 4000. That cap is far below the records (up to about 10¹¹). At n = 4000, a few thousand random tries usually found a graph at once. That worked for 97 of the 112, and for (6,6) and (13,4) with more tries.

**Constants below the cap**, from searching downward in N from min(4000, record) with a few thousand tries per order, plus a sparser second pass:

| (d,k) | found | record |
|---|---|---|
| (4,8) | 2943 | 3243 |
| (4,9), (5,7) | 3996 | 7884, 6000 |
| (5,6) | 1554 | 2836 |
| (7,5) | 2394 | 2810 |
| (8,5) | 3955 | 5334 |
| (10,4) | 2041 | 2556 |
| (11,4) | 2500 | 3645 |
| (12,4) | 3976 | 6156 |
| (17,3) | 1140 | 2210 |
| (18,3) | 1421 | 2210 |
| (19,3) | 1500 | 2783 |
| (20,3) | 1771 | 2796 |

At order exactly 4000, 10⁶ tries failed for (4,9), (5,7), (8,5) and (12,4), so those stayed just below the cap. For (5,6), 60000 tries at each order from 1600 to 2400 in steps of 16 found nothing. Metacyclic groups seem weak for degree 5 and diameter 6, or the search needs a better strategy than uniformly random generators. Diameter 3 with degree 17 to 20 is also well short of the records.

## Ideas

- A faster checker, such as numpy, or BFS from one vertex for a Cayley graph given by its group and generators, would lift the cap. Most of these constants would then go up to whatever the checker can handle.
- The small-k constants (k = 3 and 4 with d ≥ 10) and (5,6), (7,5) are the ones where better constructions matter, because the records are within reach of the cap. Options: other group families (semidirect products with non-cyclic kernels, as in Loz's and the Exoo tables), hill-climbing on the connection set instead of independent random tries, and known algebraic constructions for diameter 3, such as voltage graphs over Brown polarity graphs.
- Cartesian products of existing witnesses (degrees add and diameters add) and undirected Kautz graphs were much worse than random Cayley graphs here, so they weren't used.

## Published record graphs imported (2026-11-14)

An AI agent (Claude) converted adjacency lists from Francesc Comellas's table (https://web.mat.upc.edu/francesc.comellas/delta-d/, files under desc_g/adjacencies/) to sparse6 for records up to about 7000 vertices, matching the value in the literature data here. The checker is faster than estimated above: 6000 vertices took 63 s, 6804 vertices 37 s. The table sometimes has newer records than the literature data here, such as (7,3) 176, (5,5) 660 and (6,3) 126; those weren't imported, since a certificate would claim their discovery. Graphs given only inside SageMath scripts were read as text (sparse6 strings), not run. Not finished: (4,9) 7884, (9,5) 9020 and (14,4) 9720 (valid in a C check, but the Python check of 7884 was still running after 2 minutes when stopped for time). Missing or not tried: (7,3) 170, (7,4) 684 and (9,4) 1768 (404), (6,6) 8802 (the file holds an 8082-vertex graph), and (17..20,3).

## False twins and the hamming-lines format (2026-11-16)

Adding a false twin of a vertex (a new vertex joined to the same neighbors) keeps the diameter if it's at least 2, and raises by one the degree of each neighbor. So a graph of degree d and diameter k, with a set of S vertices whose neighborhoods are disjoint, gives N(d+1,k) >= n + S. Sami Hani Badaoui and Sarah Ellen Mary Vaughan used this on Dharunish Yugeswardeenoo's (16,5) graph on 159744 vertices, with S = 7936, for N(17,5) >= 167680. The same trick may lift other records by one degree; it only needs a large set of vertices pairwise at distance at least 3 in the record graph.

That graph is too big for sparse6 under the size limit, but it's made of 624 copies of the Hamming graph H(4,4) whose lines are matched in pairs, each pair joined as K_{4,4}, so the `hamming-lines` format stores only the matching and the clone sources (377 kB). See certificates/README.md. The degree-diameter checker now runs a numpy BFS from 512 vertices at a time, as bits of eight 64-bit words per vertex, instead of a Python big-integer BFS per vertex: the 167680-vertex graph takes about 2.5 minutes, and the 4000-vertex cap described above no longer applies.

## Literature review (2026-11-23)

The 2026 history for d <= 16 was rebuilt from the entry pages of Comellas' table (the "Former result" chains under each cell), the dated legend, and the authors' own deposits: Yugeswardeenoo's eight Zenodo records (October 25 to November 23), Rajiv's eight Zenodo papers, Mizuno's arXiv paper and GitHub repository (rmizuno42/ddp, whose results.json dates each graph), Bhakar's GitHub repository (f4t4nt/degree-diameter-graphs, commit dates), de Messieres' and Taghiyev's Zenodo records. Each step now has a day-level source, so same-month steps sort correctly. Things worth knowing for the next review:

- The table's (6,6) entry 8802 is a typo for 8082: the entry describes the incidence graph of H(5) (7812 vertices) plus 270 subdivision vertices, and the deposited file (Zenodo 23624117, deg6_diam6_n8082.txt) has 8082 lines. Gupta's (6,6) entry of September 8, 2026 is shown with order 2794, also a typo; its real order is unknown, so it isn't in the history.
- Entry pages for orders above about 20,000 lag the table (Comellas updates them monthly) and have no per-entry history for diameters 7 to 10. Intermediate steps there come only from dated deposits (Rajiv's papers, Yugeswardeenoo's and Taghiyev's Zenodo records, Bhakar's commits). Rajiv's tables also list "previous" values from the table, such as (8,7) 135621, (9,7) 286770, (11,7) 1031240, (7,9) 1223050 and (9,8) 1697688 (via the table, September 2026), whose finders weren't identified, so they're missing.
- Taghiyev's Zenodo record of November 10 (doi:10.5281/zenodo.24121859) has 19 records at diameters 7 to 10, but Comellas lists only (12,7) and (16,10). Yugeswardeenoo's record of November 23 has 8 more not yet in the table.
- Degrees 18 to 20 at diameter 3 had been missing the PolarStar graphs (Lakhotia et al., arXiv:2302.07217, 2023: 1830, 2128, 2394) and Isham-Lakhotia-Monroe-Petrini (arXiv:2608.27253, August 2026: 2340, 2470, 2600). These make Rajiv's July 2026 (18..20,3) graphs non-improvements, and (18,3) >= 2210 (from Rajiv's (17,3) graph by monotonicity) is no longer a step, so it was removed.
- Comellas' table now covers only degrees 3 to 16. For 17 to 20 the history is Loz-Pineda-Villavicencio 2010 (via the Combinatorics Wiki), PolarStar, Isham et al. and Rajiv's papers.
- Kerem Ozdemir's Zenodo record 23685374 (diameter-2 Cayley graphs for degrees 18 to 20 and more) improves only the Cayley table, not the general one.
- Second pass (same day), with the PDFs: Loz-Pineda-Villavicencio's Tables 1-9 match every d = 17-20 value here, including N(20,9) >= 12,951,451,931 (Table 8), so that value isn't a Wiki transcription error even though it equals Loz-Širáň's old (16,10) number. The paper is dated by its Advance Access (2009-11-04). Its (17,2) graph of order 274 is the EFH-Brown graph, now credited to Erdős-Fajtlowicz-Hoffman 1980. Bannai-Ito 1981 states the defect-1 nonexistence (for regular graphs) only in a closing remark, without a full proof; Jørgensen 1992, Conde-Gimbert 2009 and Miller-Pineda-Villavicencio 2009 confirm the upper bounds credited to them, now dated by their online or received dates.
