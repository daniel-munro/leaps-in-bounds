# Reproduction instructions: 113,000,001 ten-line arrangements

Status: **draft compact witness proposal**. The complete 113M witness data is held in the protected local research archives and is NOT hosted at a permanent public URL yet. The current Leaps in Bounds \`format: lines\` checker does not support the binary representation in this proposal.

## Components

| Count | Data |
|--:|--|
| 5,000,001 | \`LINE_ARRANGEMENTS_10_5000001_VERIFIED_2026-11-18.zip\`, a compressed 30-integer-per-row text witness |
| 5,000,000 | \`LINE_ARRANGEMENTS_10_PART2_5000000_CERTIFIED_2026-11-18.zip\`, a compressed text witness |
| 60,000,000 | \`new_60000000_exact_compact.bin.zst\`, 45 bytes per row |
| 30,000,000 | \`new_30000000_variable_gap31.bin.zst\`, 45 bytes per row |
| 1,000,000 | \`new_1000000_chamber_from100m.bin\`, 45 bytes per row |
| 9,000,000 | \`new_9000000_chamber_from101m.bin\`, 45 bytes per row |
| 3,000,000 | \`new_3000000_chamber_from110m.bin.zst\`, 45 bytes per row |

The 1,000,000 and 9,000,000 parts can be recovered by splitting the compressed/uncompressed 10,000,000-row stage at byte 45,000,000.

## Verify full construction with independent implementation

Extract/decompress the compact binary files, and create a stream of the original 10,000,001 text rows from the two ZIP archives. Then, from a directory containing the binary data:

\`\`\`sh
g++ -O3 -std=c++17 -Wall -Wextra independent_113m.cpp -o /tmp/verify_113m
g++ -O3 -std=c++17 -Wall -Wextra independent_geometry_bounds.cpp -o /tmp/verify_geometry

{ unzip -p LINE_ARRANGEMENTS_10_5000001_VERIFIED_2026-11-18.zip '*/lines-5000001.txt.xz' | xz -dc
  unzip -p LINE_ARRANGEMENTS_10_PART2_5000000_CERTIFIED_2026-11-18.zip '*PART2_ADDITIONAL*.txt.xz' | xz -dc
} | /tmp/verify_113m \
    10000001 \
    60000000 new_60000000_exact_compact.bin \
    30000000 new_30000000_variable_gap31.bin \
    1000000 new_1000000_chamber_from100m.bin \
    9000000 new_9000000_chamber_from101m.bin \
    3000000 new_3000000_chamber_from110m.bin

/tmp/verify_geometry new_3000000_chamber_from110m.bin 3000000 31 1000000000
\`\`\`

Expected output lines:

\`\`\`
PASS: independently canonicalized 113000001 inequivalent ten-line arrangements including reflections
PASS: 3000000 new variable-slope arrangements; all 45 pairs intersect and all 120 line triples are nonconcurrent for every arrangement
\`\`\`

The source archive SHA-256 manifest and local audit logs were checked on 18 November 2026. The three-million binary component has SHA-256:
- compressed: \`c0895ab7a23324cc275e21dfeff42d2a24c69ba681fe91cd7d52203a165e12cd\`
- uncompressed: \`626bfc7643cc2d1f8ae72f8418d1bb34378b7aafed3484247454e4319bfd2077\`

**Resource warning:** The full exact 190-bit signature table uses billions of bytes of RAM and may take substantially longer than the time budget of Leaps in Bounds' ordinary site checker. No site-integrated compact verifier, completed public full witness, or independent maintainer review is claimed yet.

## Further submission requirements

The maintainer would need to approve a new deterministic generated-witness format (similar in principle to the compact degree-diameter witness) or accept an externally hosted complete witness with an exact pinned hash and attestation. For the existing \`format: lines\` witness, each row needs ten \`-m_i 1 t_i\` triples. The public certificate must not pretend that the compact 45-byte records themselves are an accepted \`format: lines\` file.
