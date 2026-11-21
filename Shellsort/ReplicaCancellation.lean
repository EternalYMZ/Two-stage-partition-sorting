import Shellsort.ThresholdGeometry
import Mathlib.Data.Nat.Dist

/-! Exact threshold disagreement between two real arrays after the same gap pass. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem gapSort_threshold_chain_subset {n : ℕ} (p q : RankPlacement n)
    (t u k r : ℕ)
    (hc : chainLowerCount (thresholdSet p t) k r ≤ chainLowerCount (thresholdSet q u) k r) :
    (thresholdSet (gapSort p k) t).filter (fun i => i.val % k = r) ⊆
    (thresholdSet (gapSort q k) u).filter (fun i => i.val % k = r) := by
  intro i hi
  obtain ⟨ha, hr⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨?_, hr⟩
  rw [gapSort_threshold_commutes] at ha ⊢
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and, hr] at ha ⊢
  exact lt_of_lt_of_le ha hc

/-- The number of slots low only in the first output is the sum of the
positive parts of the input chain-count differences. -/
theorem gapSort_threshold_sdiff_eq {n : ℕ} (p q : RankPlacement n) (t u k : ℕ)
    (hk : 0 < k) :
    (thresholdSet (gapSort p k) t \ thresholdSet (gapSort q k) u).card =
      ∑ r ∈ Finset.range k, (chainLowerCount (thresholdSet p t) k r -
        chainLowerCount (thresholdSet q u) k r) := by
  let A := thresholdSet (gapSort p k) t
  let B := thresholdSet (gapSort q k) u
  change (A \ B).card = _
  rw [Finset.card_eq_sum_card_fiberwise (f := fun i : Fin n => i.val % k)
    (t := Finset.range k) (fun i _ => Finset.mem_range.mpr (Nat.mod_lt _ hk))]
  apply Finset.sum_congr rfl
  intro r _
  have hset : (A \ B).filter (fun i => i.val % k = r) =
      (A.filter (fun i => i.val % k = r)) \ (B.filter (fun i => i.val % k = r)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto
  rw [hset]
  rcases le_total (chainLowerCount (thresholdSet p t) k r)
      (chainLowerCount (thresholdSet q u) k r) with hp | hq
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr (gapSort_threshold_chain_subset p q t u k r hp),
      Finset.card_empty, Nat.sub_eq_zero_of_le hp]
  · rw [Finset.card_sdiff_of_subset (gapSort_threshold_chain_subset q p u t k r hq)]
    change chainLowerCount (thresholdSet (gapSort p k) t) k r -
      chainLowerCount (thresholdSet (gapSort q k) u) k r = _
    rw [gapSort_threshold_chain_count, gapSort_threshold_chain_count]

/-- Threshold Hamming distance after a genuine gap sort is exactly the
sum of absolute differences of the two pre-pass low-key counts by chain.
The placements may themselves be the outputs of arbitrary prior gap words. -/
theorem gapSort_threshold_hamming_eq {n : ℕ} (p q : RankPlacement n) (t u k : ℕ)
    (hk : 0 < k) :
    (symmDiff (thresholdSet (gapSort p k) t) (thresholdSet (gapSort q k) u)).card =
      ∑ r ∈ Finset.range k, Nat.dist (chainLowerCount (thresholdSet p t) k r)
        (chainLowerCount (thresholdSet q u) k r) := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  · rw [gapSort_threshold_sdiff_eq p q t u k hk, gapSort_threshold_sdiff_eq q p u t k hk,
      ← Finset.sum_add_distrib]
    rfl
  · apply Finset.disjoint_left.mpr
    intro i hp hq
    exact (Finset.mem_sdiff.mp hp).2 (Finset.mem_sdiff.mp hq).1

end Shellsort
end
