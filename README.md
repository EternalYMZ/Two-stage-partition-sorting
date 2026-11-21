# Project S · P06 · Two-stage partition sorting

Miaozhen Yu (俞缪臻) · [Project S directory](https://github.com/EternalYMZ/Optimal-mean-costs-of-three-pass-Shellsort/blob/main/PROJECT-S.md)

These supporting results concern the special case of ordinary gap words: threshold-set contraction under the same word, a bound for the change in slot ranks, and marked-key identities. The optimal two-stage theorem over arbitrary predetermined ordered partitions is awaiting a dedicated Lean proof.

## Check the Lean statements

With Git and elan installed, run from the repository root:

```sh
lake exe cache get
lake build
```

[Shellsort.lean](Shellsort.lean) imports the included modules and prints the selected statements and their axioms. Sources and dependency revisions are pinned. Supporting modules may also occur in other paper repositories.

## Proof guide

[Read the proof idea in Chinese](brief.md). OrderedBlockThreshold and BlockCancellation extend threshold accounting to ordered blocks.
