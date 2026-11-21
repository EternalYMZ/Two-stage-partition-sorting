import Shellsort.WordShiftDistance

/-! Key-specific slot potentials for actual gap-insertion checkpoints. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- Per-key test functions are evaluated only at physical slots below n. -/
def slotPotential {n : ℕ} (U : Fin n → ℕ → ℝ) (p : RankPlacement n) : ℝ :=
  ∑ x : Fin n, U x (p x).val

/-- A bound on each adjacent edge in a physical k-chain. -/
def gapPotentialBound {n : ℕ} (U : Fin n → ℕ → ℝ) (k : ℕ) (w : ℝ) : Prop :=
  ∀ (x : Fin n) (i : ℕ), i+k < n → |U x i - U x (i+k)| ≤ w

private theorem alongChain {n k : ℕ} {w : ℝ} {U : Fin n → ℕ → ℝ}
    (h : gapPotentialBound U k w) (x : Fin n) (i d : ℕ) (hi : i+k*d < n) :
    |U x i - U x (i+k*d)| ≤ (d : ℝ)*w := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Nat.mul_succ, ← Nat.add_assoc] at hi ⊢
    have prev := ih (by omega)
    have step := h x (i+k*d) hi
    have tri := abs_sub_le (U x i) (U x (i+k*d)) (U x (i+k*d+k))
    push_cast
    linarith

private theorem withinChain {n k : ℕ} {w : ℝ} {U : Fin n → ℕ → ℝ}
    (h : gapPotentialBound U k w) (x : Fin n) (s a b : ℕ)
    (ha : s+k*a < n) (hb : s+k*b < n) :
    |U x (s+k*a) - U x (s+k*b)| ≤ |(a : ℝ)-(b : ℝ)| * w := by
  have ordered (i j : ℕ) (hij : i ≤ j) (hj : s+k*j < n) :
      |U x (s+k*i) - U x (s+k*j)| ≤ ((j : ℝ)-(i : ℝ))*w := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    rw [Nat.mul_add, ← Nat.add_assoc] at hj ⊢
    simpa using alongChain h x (s+k*i) d hj
  rcases le_total a b with hab | hba
  · have h : (a : ℝ) - (b : ℝ) ≤ 0 := sub_nonpos.mpr (by exact_mod_cast hab)
    rw [abs_of_nonpos h, neg_sub]
    exact ordered a b hab hb
  · have h : 0 ≤ (a : ℝ) - (b : ℝ) := sub_nonneg.mpr (by exact_mod_cast hba)
    rw [abs_sub_comm (U x _) _, abs_of_nonneg h]
    exact ordered b a hba ha

/-- The bound uses the true endpoint of each key in its own chain and the
actual insertion counter. The potentials may depend on the key. -/
theorem slotPotential_gap {n : ℕ} (p : RankPlacement n) (k : ℕ) (hk : 0 < k)
    (U : Fin n → ℕ → ℝ) (w : ℝ) (hw : 0 ≤ w) (hU : gapPotentialBound U k w) :
    |slotPotential U p - slotPotential U (gapSort p k)| ≤
      2*w*(gapInsertionCost p k hk : ℝ) := by
  let L := fun i : Fin n => chainLowerCount (thresholdSet p (p.symm i).val) k (i.val % k)
  have single (i : Fin n) :
      |U (p.symm i) i.val - U (p.symm i) (gapSort p k (p.symm i)).val| ≤
      |(L i : ℝ)-((i.val/k : ℕ) : ℝ)| * w := by
    have he := gapSort_tag_position p k hk (p.symm i)
    simp only [Equiv.apply_symm_apply] at he
    change (gapSort p k (p.symm i)).val = i.val%k+k*L i at he
    have hi := Nat.mod_add_div i.val k
    have h := withinChain hU (p.symm i) (i.val%k) (i.val/k) (L i)
      (by rw [hi]; exact i.isLt) (by rw [← he]; exact (gapSort p k (p.symm i)).isLt)
    simpa only [hi, ← he, abs_sub_comm ((i.val/k : ℕ) : ℝ) _] using h
  have reindex := p.symm.sum_comp (fun x => |U x (p x).val - U x (gapSort p k x).val|)
  simp only [Equiv.apply_symm_apply] at reindex
  unfold slotPotential
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ _ := Finset.abs_sum_le_sum_abs _ _
    _ = _ := reindex.symm
    _ ≤ ∑ i : Fin n, |(L i : ℝ)-((i.val/k : ℕ):ℝ)| * w :=
      Finset.sum_le_sum fun i _ => single i
    _ = chainFootrule p k * w := (Finset.sum_mul ..).symm
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right (chainFootrule_le_twice_gapInsertionCost p k hk) hw
      linarith

/-- Actual insertion shifts charged the selected price for each pass. -/
def weightedWordShifts {n : ℕ} (w : ℕ → ℝ) (p : RankPlacement n) :
    List {k : ℕ // 0 < k} → ℝ
  | [] => 0
  | k :: ks => w k.val * (gapInsertionCost p k.val k.property : ℝ) +
      weightedWordShifts w (gapSort p k.val) ks

theorem slotPotential_word {n : ℕ} (p : RankPlacement n) (ks : List {k : ℕ // 0 < k})
    (U : Fin n → ℕ → ℝ) (w : ℕ → ℝ)
    (hw : ∀ k ∈ ks, 0 ≤ w k.val)
    (hU : ∀ k ∈ ks, gapPotentialBound U k.val (w k.val)) :
    |slotPotential U p - slotPotential U (sortWord p (ks.map Subtype.val))| ≤
      2 * weightedWordShifts w p ks := by
  induction ks generalizing p with
  | nil => simp [sortWord, weightedWordShifts]
  | cons k ks ih =>
    have step := slotPotential_gap p k.val k.property U (w k.val) (hw _ (by simp))
      (hU _ (by simp))
    have rest := ih (gapSort p k.val) (fun a ha => hw a (by simp [ha]))
      (fun a ha => hU a (by simp [ha]))
    have tri := abs_sub_le (slotPotential U p) (slotPotential U (gapSort p k.val))
      (slotPotential U (sortWord (gapSort p k.val) (ks.map Subtype.val)))
    simp only [List.map_cons, sortWord, weightedWordShifts]
    linarith

/-- At a real checkpoint every key occurs once and each slot is occupied
once. These marginals allow a change of test functions between two words. -/
theorem slotPotential_checkpoint {n : ℕ} (p : RankPlacement n)
    (U V : Fin n → ℕ → ℝ) (row col : Fin n → ℝ)
    (feasible : ∀ x i : Fin n, U x i.val - V x i.val ≤ row x + col i) :
    slotPotential U p - slotPotential V p ≤ (∑ x, row x) + ∑ i, col i := by
  unfold slotPotential
  rw [← Finset.sum_sub_distrib, ← Equiv.sum_comp p col, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun x _ => feasible x (p x)

/-- A two-block lower certificate with independent gap prices in each block
and arbitrary row/slot prices at their shared checkpoint. -/
theorem slotPotential_twoBlock {n : ℕ} (p : RankPlacement n)
    (as bs : List {k : ℕ // 0 < k}) (U V : Fin n → ℕ → ℝ) (w v : ℕ → ℝ)
    (hw : ∀ k ∈ as, 0 ≤ w k.val) (hv : ∀ k ∈ bs, 0 ≤ v k.val)
    (hU : ∀ k ∈ as, gapPotentialBound U k.val (w k.val))
    (hV : ∀ k ∈ bs, gapPotentialBound V k.val (v k.val))
    (row col : Fin n → ℝ)
    (feasible : ∀ x i : Fin n, U x i.val - V x i.val ≤ row x + col i) :
    let mid := sortWord p (as.map Subtype.val)
    slotPotential U p - slotPotential V (sortWord mid (bs.map Subtype.val)) -
      ((∑ x, row x) + ∑ i, col i) ≤
      2*(weightedWordShifts w p as + weightedWordShifts v mid bs) := by
  dsimp only
  have a := (le_abs_self _).trans (slotPotential_word p as U w hw hU)
  have b := (le_abs_self _).trans (slotPotential_word (sortWord p (as.map Subtype.val)) bs V v hv hV)
  have c := slotPotential_checkpoint (sortWord p (as.map Subtype.val)) U V row col feasible
  linarith

end Shellsort
end
