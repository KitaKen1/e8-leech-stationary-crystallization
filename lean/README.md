# Canonical proof and independent Comparator reference

`lake exe cache get && lake build FCSolution FCAudit` builds the proof bridge.
`Challenge` independently defines the target's mathematical environment and has
13 intentional theorem holes. The completed solution imports `E8Leech`, never
`Challenge` or `FCTargetDefinitions`. Compare using `comparator.json`.

The comparison target definitions and the dependency pins are frozen by
`comparator/pins.json`. Run `python3 comparator/check-inputs.py` to check the
source identities, all 13 statement headers, and the supplementary proof copy.
See `comparator/TARGET-CORRESPONDENCE.md` for semantic review and limitations.
