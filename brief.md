# Sorting a prescribed partition before a final insertion pass

For two chains, write down their colors in slot order and again in increasing key order. Sorting each chain matches the first occurrence of each color to its first target occurrence, then the second to the second, and so on. For AABB and ABAB only the second cut has a discrepancy, so one final shift suffices. In general let $q_r,X_r$ count the first color before cut $r$ in the two words, with chain lengths $a,b$. All keys of this color crossing any one cut move in the same direction. The surviving inversion count for the pair is exactly
$$\sum_{r=1}^{a+b-1}|X_r-q_r|.$$
Every final inversion belongs to one pair of chains. Under a uniform permutation $X_r$ is hypergeometric, while the layout fixes $q_r$.

For chain lengths $a_i$ put $s=\sum_i a_i^2/n$, the mean chain length seen by a uniformly chosen key. First-pass shifts have mean $n(s-1)/4$. Near the optimum, interchain fluctuations cost on the scale $n^2/\sqrt{s}$. Balancing the two gives $s$ of order $n^{2/3}$. Bounding the cut discrepancies for arbitrary predetermined partitions and attaining the bound with equally spaced chains gives the analytical leading term $3(\pi/1024)^{1/3}n^{5/3}$ for the separately minimized mean shifts and comparisons, using ordinary insertion at both stages.

Lean covers threshold contraction. Sorting an ordered block packs its marked slots into a prefix and preserves their number. Applying the same operation to the intersection of two markings gives a subset of both outputs of the original size of the intersection, so the one-sided difference cannot grow. This argument also applies to successive overlapping blocks. The leading-term theorem requires additional analysis.

[ThresholdContraction.lean](https://github.com/EternalYMZ/Two-stage-partition-sorting/blob/c367251171e3378458427db376408b9a2bdb7e4a/Shellsort/ThresholdContraction.lean) · [TaggedSetInfluence.lean](https://github.com/EternalYMZ/Two-stage-partition-sorting/blob/c367251171e3378458427db376408b9a2bdb7e4a/Shellsort/TaggedSetInfluence.lean)

[Ordered-block contraction](Shellsort/OrderedBlockThreshold.lean) · [Exact trace distance and target footrule](Shellsort/BlockCancellation.lean)
