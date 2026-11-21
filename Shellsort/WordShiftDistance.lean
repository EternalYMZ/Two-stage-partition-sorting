import Shellsort.ChainInversionBound
import Shellsort.RankBandCost
import Mathlib.Order.Interval.Finset.Fin

noncomputable section
namespace Shellsort
open scoped BigOperators

private theorem finRank_sum {m : ℕ} (v : Fin m) :
    (∑ w : Fin m, if w < v then (1 : ℝ) else 0) = v.val := by
  have hset : Finset.univ.filter (fun w : Fin m => w < v) = Finset.Iio v := by
    ext x
    simp
  have hnat : (∑ w : Fin m, if w < v then (1 : ℕ) else 0) = v.val := by
    rw [← Finset.sum_filter, Finset.sum_const, hset, Fin.card_Iio]
    simp
  exact_mod_cast hnat

/-- A net change of rank is bounded by the number of pairs whose order flips.
Summing by key charges the two endpoints of each inversion. -/
theorem finPerm_footrule_le_twice_inversions {m : ℕ} (q : Equiv.Perm (Fin m)) :
    (∑ v : Fin m, |((q v).val : ℝ) - (v.val : ℝ)|) ≤
    2 * ∑ j : Fin m, ∑ i : Fin m, if i < j ∧ q j < q i then (1 : ℝ) else 0 := by
  let inv := fun i j : Fin m => if i < j ∧ q j < q i then (1 : ℝ) else 0
  have point (v : Fin m) : |((q v).val : ℝ) - (v.val : ℝ)| ≤
      ∑ w : Fin m, (inv w v + inv v w) := by
    have hq := Equiv.sum_comp q (fun w : Fin m => if w < q v then (1 : ℝ) else 0)
    rw [finRank_sum] at hq
    rw [← hq, ← finRank_sum v, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    by_cases hwv : w = v
    · subst w; simp [inv]
    · have hdiff : q w ≠ q v := fun h => hwv (q.injective h)
      rcases lt_or_gt_of_ne hwv with hw | hw <;>
        rcases lt_or_gt_of_ne hdiff with hq | hq <;>
        simp [inv, hw, hq, not_lt_of_gt hw, not_lt_of_gt hq]
  calc
    _ ≤ ∑ v : Fin m, ∑ w : Fin m, (inv w v + inv v w) :=
      Finset.sum_le_sum fun v _ => point v
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun v w => inv v w)]
      change _ = 2 * ∑ v : Fin m, ∑ w : Fin m, inv w v
      ring

/-- The actual normalized chain displacements required by a gap pass can be
paid for by its executed insertion shifts. -/
theorem chainFootrule_le_twice_gapInsertionCost {n : ℕ} (p : RankPlacement n)
    (k : ℕ) (hk : 0 < k) :
    chainFootrule p k ≤ 2 * (gapInsertionCost p k hk : ℝ) := by
  rw [chainFootrule_eq_sum_actualChainRank p k hk, gapInsertionCost, Nat.cast_sum,
    Finset.mul_sum]
  apply Finset.sum_le_sum
  intro s _
  let m := sourceTrialLength (n / k) (n % k) s.val
  let rank := actualChainRank p k hk s
  have hrank (v : Fin m) : rank v < m := by
    let z := gapSort p k (chainKeys p k hk s v)
    have hz : z.val = s.val + k * rank v := actualChainRank_sorted_position p k hk s v
    have hq := actual_chain_quotient_lt (n := n) hk z
    rw [hz, Nat.add_mul_div_left _ _ hk, Nat.div_eq_of_lt s.isLt, Nat.zero_add,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt] at hq
    exact hq
  let f := fun v : Fin m => (⟨rank v, hrank v⟩ : Fin m)
  have hf : Function.Injective f :=
    fun _ _ he => actualChainRank_injective p k hk s (congrArg Fin.val he)
  let q := Equiv.ofBijective f ((Finite.injective_iff_bijective).mp hf)
  have hlt (i j : Fin m) : q j < q i ↔ chainKeys p k hk s j < chainKeys p k hk s i :=
    actualChainRank_lt_iff p k hk s j i
  rw [insertionExecution_ofFn_count]
  push_cast
  have hval (v : Fin m) : (q v).val = actualChainRank p k hk s v := rfl
  simpa only [hlt, hval, Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using
    finPerm_footrule_le_twice_inversions q

/-- Every source gap is weighted by its physical length. -/
def wordShiftDistance {n : ℕ} (p : RankPlacement n) : List {k : ℕ // 0 < k} → ℝ
  | [] => 0
  | k :: ks => (k.val : ℝ) * (gapInsertionCost p k.val k.property : ℝ) +
      wordShiftDistance (gapSort p k.val) ks

theorem footrule_le_wordShiftDistance {n : ℕ} (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    footrule p ≤ footrule (sortWord p (ks.map Subtype.val)) + 2 * wordShiftDistance p ks := by
  induction ks generalizing p with
  | nil => simp [wordShiftDistance, sortWord]
  | cons k ks ih =>
    have hs := chainFootrule_le_twice_gapInsertionCost p k.val k.property
    have ht := footrule_triangle p (gapSort p k.val)
    rw [gapSort_transport_eq_mul_chainFootrule p k.val k.property] at ht
    have hstep := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg k.val : (0 : ℝ) ≤ k.val)
    have hi := ih (gapSort p k.val)
    simp only [wordShiftDistance, List.map_cons, sortWord]
    linarith
/-- State after the prefix consisting of initial gaps at least K. -/
def scaleCutState {n : ℕ} (p : RankPlacement n) (K : ℕ) :
    List {k : ℕ // 0 < k} → RankPlacement n
  | [] => p
  | k :: ks => if k.val < K then p else scaleCutState (gapSort p k.val) K ks

private theorem scaleCutState_small {n K : ℕ} (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) (hsmall : ∀ k ∈ ks, k.val < K) :
    scaleCutState p K ks = p := by
  cases ks with
  | nil => rfl
  | cons k ks => simp [scaleCutState, hsmall k (by simp)]

private theorem scaleCutState_step {n K : ℕ} (p : RankPlacement n)
    (k : {t : ℕ // 0 < t}) (ks : List {t : ℕ // 0 < t})
    (hlt : ∀ h ∈ ks, h.val < k.val) :
    footrule (scaleCutState p K (k :: ks)) ≤ footrule (scaleCutState (gapSort p k.val) K ks) +
      (if k.val < K then 2 * (k.val : ℝ) * (gapInsertionCost p k.val k.property : ℝ) else 0) := by
  by_cases h : k.val < K
  · simp only [scaleCutState, ite_eq_left h]
    rw [scaleCutState_small _ _ (fun x hx => (hlt x hx).trans h)]
    have ht := footrule_le_wordShiftDistance p [k]
    simpa [sortWord, wordShiftDistance, mul_assoc] using ht
  · simp [scaleCutState, h]

/-- Geometric accounting for one shift of span h, uniformly in scale count. -/
theorem dyadic_span_charge (h J : ℕ) :
    (∑ j ∈ Finset.range J,
      if h < (2 : ℕ)^j then (h : ℝ) / (2 : ℝ)^j else 0) ≤ 2 := by
  have bound (m : ℕ) :
      (∑ j ∈ Finset.range m, if h < (2 : ℕ)^j then (h : ℝ) / (2 : ℝ)^j else 0) +
        min 2 (2 * (h : ℝ) / (2 : ℝ)^m) ≤ 2 := by
    induction m with
    | zero => simp
    | succ m ih =>
      have hp : (0 : ℝ) < 2^m := by positivity
      have hh : (0 : ℝ) ≤ h := by positivity
      rw [Finset.sum_range_succ, pow_succ]
      by_cases hlt : h < (2 : ℕ)^m
      · have hr : (h : ℝ) < 2^m := by exact_mod_cast hlt
        have hm : 2 * (h : ℝ) / (2 : ℝ)^m ≤ 2 := (div_le_iff₀ hp).mpr (by linarith)
        have hz : 2 * (h : ℝ) / (2^m * 2 : ℝ) ≤ 2 :=
          (div_le_iff₀ (by positivity)).mpr (by linarith)
        rw [min_eq_right hm] at ih
        rw [ite_eq_left hlt, min_eq_right hz]
        convert ih using 1; ring
      · rw [ite_eq_right hlt, add_zero]
        apply le_trans _ ih
        apply add_le_add le_rfl
        apply min_le_min le_rfl
        apply div_le_div_of_nonneg_left (by positivity) hp
        linarith
  have hb := bound J
  have hm : 0 ≤ min 2 (2 * (h : ℝ) / 2^J) := le_min (by norm_num) (by positivity)
  linarith

/-- Joint transport across all dyadic cuts of one strictly decreasing true
execution. The global target residual is subtracted so unfinished words are
also covered. For a word ending in gap one this residual vanishes. -/
theorem dyadic_cut_transport {n : ℕ} (p : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) (J : ℕ)
    (hd : ks.Pairwise (fun a b => b.val < a.val)) :
    (∑ j ∈ Finset.range J,
      (footrule (scaleCutState p (2^j) ks) - footrule (sortWord p (ks.map Subtype.val))) /
        (2 : ℝ)^j) ≤ 4 * (ordinaryWordShifts p ks : ℝ) := by
  induction ks generalizing p with
  | nil => simp [scaleCutState, sortWord, ordinaryWordShifts]
  | cons k ks ih =>
    obtain ⟨head, tail⟩ := List.pairwise_cons.mp hd
    let q := gapSort p k.val
    let a : ℝ := gapInsertionCost p k.val k.property
    let res := footrule (sortWord q (ks.map Subtype.val))
    let f := fun j : ℕ => (footrule (scaleCutState q (2^j) ks) - res) / (2:ℝ)^j
    let w := fun j : ℕ => if k.val < (2:ℕ)^j then (k.val : ℝ) / (2:ℝ)^j else 0
    have hfin := ih q tail
    have hw := dyadic_span_charge k.val J
    have ha : 0 ≤ a := by positivity
    have each (j : ℕ) : (footrule (scaleCutState p (2^j) (k::ks)) - res) / (2:ℝ)^j
        ≤ f j + (2*a) * w j := by
      have h := scaleCutState_step (K := 2^j) p k ks head
      dsimp only [f, w]
      by_cases hc : k.val < (2:ℕ)^j
      · rw [ite_eq_left hc] at *
        calc
          _ ≤ (footrule (scaleCutState q (2^j) ks) + 2 * (k.val:ℝ) * a - res) / (2:ℝ)^j :=
            div_le_div_of_nonneg_right (by linarith only [h]) (by positivity)
          _ = _ := by ring
      · rw [ite_eq_right hc] at *
        simp only [add_zero, mul_zero] at *
        exact div_le_div_of_nonneg_right (sub_le_sub_right h res) (by positivity)
    have s := Finset.sum_le_sum (s := Finset.range J) (fun j _ => each j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at s
    have hh : (2*a) * (∑ j ∈ Finset.range J, w j) ≤ (2*a)*2 :=
      mul_le_mul_of_nonneg_left hw (by positivity)
    change (∑ j ∈ Finset.range J, f j) ≤ _ at hfin
    change (∑ j ∈ Finset.range J, (footrule (scaleCutState p (2^j) (k::ks)) - res) / (2:ℝ)^j) ≤ _
    rw [ordinaryWordShifts, Nat.cast_add]
    change _ ≤ 4 * (a + (ordinaryWordShifts q ks : ℝ))
    linarith

private theorem sortWord_finish_one {n : ℕ} (p : RankPlacement n) (ks : List ℕ) :
    sortWord p (ks ++ [1]) = Equiv.refl _ := by
  induction ks generalizing p with
  | nil => simp [sortWord, gapSort_one]
  | cons k ks ih => exact ih (gapSort p k)

/-- On a complete ordinary word any subfamily of dyadic cut scales may be
charged against the same successful-shift budget once, up to factor four. -/
theorem complete_dyadic_cut_budget {n : ℕ} (p : RankPlacement n)
    (pre : List {k : ℕ // 0 < k}) (S : Finset ℕ) (J : ℕ) (hS : S ⊆ Finset.range J)
    (hd : (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})]).Pairwise (fun a b => b.val < a.val)) :
    (∑ j ∈ S, footrule (scaleCutState p (2^j) (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})])) / (2 : ℝ)^j)
        ≤ 4 * (ordinaryWordShifts p (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})]) : ℝ) := by
  have h := dyadic_cut_transport p _ J hd
  have hz : footrule (Equiv.refl (Fin n)) = 0 := by simp [footrule, transport]
  simp only [List.map_append, List.map_cons, List.map_nil, sortWord_finish_one, hz, sub_zero] at h
  apply le_trans _ h
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro i _ _
  apply div_nonneg _ (by positivity)
  unfold footrule transport
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- One common scale works in the uniform average; the scale is chosen
outside the average and does not depend on the individual permutation. -/
theorem exists_uniform_dyadic_cut {n : ℕ} (pre : List {k : ℕ // 0 < k})
    (S : Finset ℕ) (J : ℕ) (hS : S ⊆ Finset.range J) (hne : S.Nonempty)
    (hd : (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})]).Pairwise (fun a b => b.val < a.val)) :
    ∃ j ∈ S, (S.card : ℝ) *
        uniformAverage (fun p : RankPlacement n =>
          footrule (scaleCutState p (2^j) (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})])) / (2 : ℝ)^j) ≤
        4 * uniformAverage (fun p : RankPlacement n =>
          (ordinaryWordShifts p (pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})]) : ℝ)) := by
  let ks := pre ++ [(⟨1, by decide⟩ : {k : ℕ // 0 < k})]
  let f := fun j (p : RankPlacement n) => footrule (scaleCutState p (2^j) ks) / (2 : ℝ)^j
  let m := fun p : RankPlacement n => (ordinaryWordShifts p ks : ℝ)
  have h : ∑ j ∈ S, uniformAverage (f j) ≤ 4 * uniformAverage m := by
    simp only [uniformAverage, ← Finset.sum_div]
    rw [Finset.sum_comm, ← mul_div_assoc, Finset.mul_sum]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Finset.sum_le_sum fun p _ => complete_dyadic_cut_budget p pre S J hS hd
  obtain ⟨j, hj, hmin⟩ := S.exists_min_image (fun i => uniformAverage (f i)) hne
  refine ⟨j, hj, ?_⟩
  change (S.card : ℝ) * uniformAverage (f j) ≤ 4 * uniformAverage m
  apply le_trans _ h
  simpa [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (s := S)
    (fun i hi => hmin i hi)

end Shellsort
end

