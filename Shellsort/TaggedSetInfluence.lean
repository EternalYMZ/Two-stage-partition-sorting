import Shellsort.TagThreshold

/-! Finite count-change identities for marking one original key and measuring
membership in a fixed slot set E. These use the actual full gap word. -/
noncomputable section
namespace Shellsort

def markedCount {n : ℕ} (E B : Finset (Fin n)) : ℤ :=
  ((B.filter (fun i => i ∈ E)).card : ℤ)

def markedWordChange {n : ℕ} (E B : Finset (Fin n)) (ks : List ℕ) : ℤ :=
  markedCount E (lowerWord B ks) - markedCount E B

private theorem markedCount_insert {n : ℕ} (E B : Finset (Fin n)) (i : Fin n) (hi : i ∉ B) :
    markedCount E (insert i B) = markedCount E B + (if i ∈ E then 1 else 0) := by
  by_cases h : i ∈ E <;> simp [markedCount, Finset.filter_insert, h, hi]

/-- With only the lower labels and the marked source slot fixed, the final
slot of that rank is identical in every consistent full refinement. -/
theorem tag_finalSlot_of_same_labels {n : ℕ} (p q : RankPlacement n) (x y : Fin n)
    (ks : List ℕ) (hsrc : p x = q y) (hlow : thresholdSet p x.val = thresholdSet q y.val) :
    sortWord p ks x = sortWord q ks y := by
  have hp := lowerWord_tag_difference p x ks
  rw [hsrc, hlow, lowerWord_tag_difference q y ks] at hp
  simpa using hp.symm

/-- Exact signed discrete derivative of the output-minus-input count in E,
when changing the one tagged slot from a high to a low key. -/
theorem markedWordChange_toggle {n : ℕ} (p : RankPlacement n) (x : Fin n)
    (ks : List ℕ) (E : Finset (Fin n)) :
    markedWordChange E (insert (p x) (thresholdSet p x.val)) ks -
      markedWordChange E (thresholdSet p x.val) ks =
        (if sortWord p ks x ∈ E then (1 : ℤ) else 0) -
        (if p x ∈ E then (1 : ℤ) else 0) := by
  unfold markedWordChange
  rw [markedCount_insert _ _ _ (tag_not_in_threshold p x), ← thresholdSet_succ_tag,
    ← sortWord_threshold_commutes, ← sortWord_threshold_commutes, thresholdSet_succ_tag,
    markedCount_insert _ _ _ (tag_not_in_threshold (sortWord p ks) x)]
  ring

/-- The squared derivative pays exactly one if the tagged key changes sides
of E. This is the deterministic integrand in the Bernoulli variance bound. -/
theorem markedWordChange_toggle_sq {n : ℕ} (p : RankPlacement n) (x : Fin n)
    (ks : List ℕ) (E : Finset (Fin n)) :
    (markedWordChange E (insert (p x) (thresholdSet p x.val)) ks -
      markedWordChange E (thresholdSet p x.val) ks)^2 =
        (if (sortWord p ks x ∈ E) ↔ (p x ∈ E) then (0 : ℤ) else 1) := by
  rw [markedWordChange_toggle]
  by_cases h₁ : sortWord p ks x ∈ E <;> by_cases h₂ : p x ∈ E <;> norm_num [h₁, h₂]

end Shellsort
end
