# Project S · P06 · Two-stage partition sorting

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

The Lean development covers marked-key and slot-rank bounds for ordinary gap words, as well as threshold-set contraction for arbitrary sequences of ordered blocks, including overlapping blocks. The block results include exact trajectory discrepancy and target footrule identities. The optimal two-stage complexity theorem over arbitrary predetermined ordered partitions awaits a dedicated Lean proof.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof guide](brief.md). OrderedBlockThreshold and BlockCancellation extend threshold accounting to ordered blocks.
