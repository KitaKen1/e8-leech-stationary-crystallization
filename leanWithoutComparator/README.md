# Supplementary copy of the same proof

The canonical project is [../lean/](../lean/). This folder contains the same proof
for browsing and building, with Comparator-only files removed. All 1,537 shared
Lean sources, the toolchain and dependency manifest are byte-identical.

```sh
lake exe cache get
lake build
```

The entry point is [FCSolution.lean](FCSolution.lean), importing the
[E8Leech.lean](E8Leech.lean) proof library. File correspondence and SHA-256 values
are in [shared-proof-sources.json](../lean/comparator/shared-proof-sources.json).
Original-manuscript review and full candidate CI remain unfinished;
see [the publication manifest](../PUBLICATION-MANIFEST.json).
