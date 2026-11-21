import Shellsort.CheckpointSensitivity
import Shellsort.GapMonotone
import Mathlib.Logic.Equiv.Fintype

/-! Every threshold layer contracts its directed set difference under a fixed gap
word. Applied to a transposition, only thresholds separating the exchanged ranks
can affect the footrule at the final checkpoint of that word. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

theorem lowerStep_subset_of_subset {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B)
    (k : ℕ) : lowerStep A k ⊆ lowerStep B k := by
  intro i hi
  have hc := Finset.card_le_card (Finset.filter_subset_filter (fun j : Fin n => j.val % k = i.val % k) h)
  simp only [lowerStep, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  exact lt_of_lt_of_le hi hc

theorem lowerWord_subset_of_subset {n : ℕ} {A B : Finset (Fin n)} (h : A ⊆ B)
    (ks : List ℕ) : lowerWord A ks ⊆ lowerWord B ks := by
  induction ks generalizing A B with
  | nil => exact h
  | cons k ks ih => exact ih (lowerStep_subset_of_subset h k)

private theorem threshold_realizes_finset {n : ℕ} (B : Finset (Fin n)) :
    ∃ p : RankPlacement n, thresholdSet p B.card = B := by
  classical
  let U := thresholdSet (Equiv.refl (Fin n)) B.card
  have hcard : U.card = B.card := by
    rw [thresholdSet_card, min_eq_right (by simpa using B.card_le_univ)]
  let e := Finset.equivOfCardEq hcard
  let p : RankPlacement n := e.extendSubtype
  refine ⟨p, ?_⟩
  ext i
  obtain ⟨x, rfl⟩ := p.surjective i
  rw [threshold_mem, p.symm_apply_apply]
  have hmem : x ∈ U ↔ x.val < B.card := by simp [U, threshold_mem]
  constructor
  · intro hx
    exact e.extendSubtype_mem x (hmem.mpr hx)
  · intro hx
    by_contra hn
    exact e.extendSubtype_not_mem x (fun hu => hn (hmem.mp hu)) hx

theorem lowerWord_preserves_card {n : ℕ} (A : Finset (Fin n)) (ks : List ℕ) :
    (lowerWord A ks).card = A.card := by
  obtain ⟨p, hp⟩ := threshold_realizes_finset A
  rw [← hp, ← sortWord_threshold_commutes, thresholdSet_card, thresholdSet_card]

/-- Directed Hamming loss contracts even for unequal initial numbers of low keys. -/
theorem lowerWord_sdiff_card_le {n : ℕ} (A B : Finset (Fin n)) (ks : List ℕ) :
    (lowerWord A ks \ lowerWord B ks).card ≤ (A \ B).card := by
  have hs : lowerWord (B ∩ A) ks ⊆ lowerWord B ks ∩ lowerWord A ks :=
    Finset.subset_inter
      (lowerWord_subset_of_subset Finset.inter_subset_left ks)
      (lowerWord_subset_of_subset Finset.inter_subset_right ks)
  have hc := Finset.card_le_card hs
  rw [lowerWord_preserves_card] at hc
  rw [Finset.card_sdiff, Finset.card_sdiff, lowerWord_preserves_card]
  omega

/-- A fixed region of physical slots may be an interval, chain, or arbitrary subset. -/
theorem lowerWord_region_card_le {n : ℕ} (A B R : Finset (Fin n)) (ks : List ℕ) :
    (lowerWord A ks ∩ R).card ≤ (lowerWord B ks ∩ R).card + (A \ B).card := by
  have hs : lowerWord A ks ∩ R ⊆ (lowerWord B ks ∩ R) ∪ (lowerWord A ks \ lowerWord B ks) := by
    intro i hi
    obtain ⟨hA,hR⟩ := Finset.mem_inter.mp hi
    by_cases hB : i ∈ lowerWord B ks
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hB,hR⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hA,hB⟩)
  exact (Finset.card_le_card hs).trans
    ((Finset.card_union_le ..).trans (Nat.add_le_add_left (lowerWord_sdiff_card_le A B ks) _))

theorem sortWord_rightCutCount_le_sdiff {n : ℕ} (p q : RankPlacement n)
    (ks : List ℕ) (t : Fin n) :
    rightCutCount (sortWord p ks) t ≤ rightCutCount (sortWord q ks) t +
      (thresholdSet p (t.val + 1) \ thresholdSet q (t.val + 1)).card := by
  have h := lowerWord_region_card_le (thresholdSet p (t.val + 1))
    (thresholdSet q (t.val + 1)) (Finset.Ioi t) ks
  rw [← sortWord_threshold_commutes, ← sortWord_threshold_commutes] at h
  have hregion (S : Finset (Fin n)) : S ∩ Finset.Ioi t = S.filter (fun i => t < i) := by
    ext i
    simp
  simpa only [rightCutCount, hregion] using h

/-- Rank transport compares the values stored at each physical slot. Its exact
layer formula uses one orientation of threshold difference and a factor of two. -/
theorem slotRankTransport_eq_threshold_sum {n : ℕ} (p q : RankPlacement n) :
    transport p.symm q.symm = 2 * ∑ t : Fin n,
      ((thresholdSet p (t.val+1) \ thresholdSet q (t.val+1)).card : ℝ) := by
  have hmetric : transport p.symm q.symm = footrule (p.trans q.symm) := by
    unfold transport footrule
    rw [← Equiv.sum_comp p (fun i : Fin n => |((p.symm i).val : ℝ) - ((q.symm i).val : ℝ)|)]
    apply Finset.sum_congr rfl
    intro x _
    simp [abs_sub_comm]
  rw [hmetric, footrule_eq_two_sum_rightCuts]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  have e : ((thresholdSet p (t.val+1) \ thresholdSet q (t.val+1)).map q.symm.toEmbedding) =
      (thresholdSet (p.trans q.symm) (t.val+1)).filter (fun i => t < i) := by
    ext i
    simp only [Finset.mem_map_equiv, Equiv.symm_symm, Finset.mem_sdiff, threshold_mem,
      Equiv.symm_apply_apply, Finset.mem_filter, Equiv.symm_trans_apply,
      Nat.lt_succ_iff, not_le, Fin.lt_def]
  exact_mod_cast (congrArg Finset.card e).symm.trans (Finset.card_map ..)

/-- On arrays indexed by physical slots, sorting each prescribed gap chain
contracts the sum of absolute rank differences between two inputs. -/
theorem sortWord_slotRankTransport_le {n : ℕ} (p q : RankPlacement n) (ks : List ℕ) :
    transport (sortWord p ks).symm (sortWord q ks).symm ≤ transport p.symm q.symm := by
  rw [slotRankTransport_eq_threshold_sum, slotRankTransport_eq_threshold_sum]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro t _
  rw [sortWord_threshold_commutes, sortWord_threshold_commutes]
  exact_mod_cast lowerWord_sdiff_card_le (thresholdSet p (t.val+1))
    (thresholdSet q (t.val+1)) ks

/-- The lower-key set gains a single slot only at cuts separating the ranks. -/
theorem relabelSwap_threshold_sdiff_le {n : ℕ} (p : RankPlacement n) (a b t : Fin n)
    (hab : a ≤ b) :
    (thresholdSet (relabelSwap p a b) (t.val+1) \ thresholdSet p (t.val+1)).card ≤
      if t ∈ Finset.Ico a b then 1 else 0 := by
  classical
  let D := thresholdSet (relabelSwap p a b) (t.val+1) \ thresholdSet p (t.val+1)
  have hslot : ∀ i ∈ D, i = p b ∧ a ≤ t ∧ t < b := by
    intro i hi
    obtain ⟨x,rfl⟩ := p.surjective i
    obtain ⟨h₁,h₂⟩ := Finset.mem_sdiff.mp hi
    have h₁' : (Equiv.swap a b x).val ≤ t.val := by
      simpa [threshold_mem, relabelSwap, Nat.lt_succ_iff] using h₁
    have h₂' : t.val < x.val := by
      simpa [threshold_mem, Nat.lt_succ_iff] using h₂
    by_cases ha : x = a
    · subst x
      simp only [Equiv.swap_apply_left] at h₁'
      exact False.elim ((not_lt_of_ge ((show a.val ≤ b.val from hab).trans h₁')) h₂')
    by_cases hb : x = b
    · subst x
      simp only [Equiv.swap_apply_right] at h₁'
      exact ⟨rfl,h₁',h₂'⟩
    · simp only [Equiv.swap_apply_of_ne_of_ne ha hb] at h₁'
      omega
  change D.card ≤ _
  split_ifs with ht
  · have hs : D ⊆ {p b} := fun i hi => Finset.mem_singleton.mpr (hslot i hi).1
    simpa using Finset.card_le_card hs
  · have hempty : D = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi => ht (Finset.mem_Ico.mpr (hslot i hi).2))
    simp [hempty]

private theorem swap_footrule_direction {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : a ≤ b) (ks : List ℕ) :
    footrule (sortWord (relabelSwap p a b) ks) ≤
      footrule (sortWord p ks) + 2 * ((b.val - a.val : ℕ) : ℝ) := by
  classical
  have hpoint (t : Fin n) :
      (rightCutCount (sortWord (relabelSwap p a b) ks) t : ℝ) ≤
      (rightCutCount (sortWord p ks) t : ℝ) + (if t ∈ Finset.Ico a b then 1 else 0 : ℝ) := by
    have h := (sortWord_rightCutCount_le_sdiff (relabelSwap p a b) p ks t).trans
      (Nat.add_le_add_left (relabelSwap_threshold_sdiff_le p a b t hab) _)
    split_ifs at * <;> exact_mod_cast h
  have h := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hpoint t)
  rw [Finset.sum_add_distrib] at h
  have hc : (∑ t : Fin n, (if t ∈ Finset.Ico a b then 1 else 0 : ℝ)) =
      ((b.val - a.val : ℕ) : ℝ) := by
    rw [← Finset.sum_filter]
    have heq : (Finset.univ.filter (fun t => t ∈ Finset.Ico a b)) = Finset.Ico a b := by
      ext t
      simp
    rw [heq, Finset.sum_const, nsmul_one, Fin.card_Ico]
  rw [hc] at h
  rw [footrule_eq_two_sum_rightCuts, footrule_eq_two_sum_rightCuts]
  linarith

/-- A transposition of ranks at distance d changes the actual checkpoint footrule
by at most 2d, uniformly in the number and sizes of the prescribed gaps. -/
theorem sortWord_footrule_relabelSwap_le {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : a ≤ b) (ks : List ℕ) :
    |footrule (sortWord (relabelSwap p a b) ks) - footrule (sortWord p ks)| ≤
      2 * ((b.val - a.val : ℕ) : ℝ) := by
  have hf := swap_footrule_direction p a b hab ks
  have hr := swap_footrule_direction (relabelSwap p a b) a b hab ks
  rw [relabelSwap_twice] at hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Shellsort
end
