import Shellsort.AdjacentRankCost
import Shellsort.WordShiftDistance
import Shellsort.WordSlotPotential

/-! Joint sensitivity of all executed pass counts and the order at the checkpoint. -/
noncomputable section
namespace Shellsort
open scoped BigOperators

/-- The variation between two executions counts the absolute change in each pass
separately. Differences of opposite signs cannot cancel. -/
def passShiftVariation {n : ℕ} (p q : RankPlacement n) : List {k : ℕ // 0 < k} → ℕ
  | [] => 0
  | k :: ks => Nat.dist (gapInsertionCost p k k.property) (gapInsertionCost q k k.property) +
      passShiftVariation (gapSort p k) (gapSort q k) ks

theorem passShiftVariation_output {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    passShiftVariation p q ks + (discordantSlots (sortWord p (ks.map Subtype.val))
      (sortWord q (ks.map Subtype.val))).card ≤ (discordantSlots p q).card := by
  induction ks generalizing p q with
  | nil => simp [passShiftVariation, sortWord]
  | cons k ks ih =>
    have step := ordinaryWordShifts_output_contraction p q [k]
    simp only [ordinaryWordShifts, add_zero, List.map_cons, List.map_nil, sortWord] at step
    have rest := ih (gapSort p k) (gapSort q k)
    simp only [passShiftVariation, List.map_cons, sortWord]
    omega

theorem sortWord_adjacent_outcomes {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (ks : List ℕ) :
    sortWord (relabelSwap p a b) ks = sortWord p ks ∨
      sortWord (relabelSwap p a b) ks = relabelSwap (sortWord p ks) a b := by
  induction ks generalizing p with
  | nil => exact Or.inr rfl
  | cons k ks ih =>
    simp only [sortWord]
    by_cases hm : (p a).val % k = (p b).val % k
    · exact Or.inl (congrArg (fun q => sortWord q ks) (adj_gapSort_of_meet p a b k hm))
    · rw [adj_gapSort_of_separate p a b hab k hm]
      exact ih (gapSort p k)

private theorem footrule_inverse {n : ℕ} (p : RankPlacement n) :
    footrule p.symm = footrule p := by
  unfold footrule transport
  simp only [Equiv.refl_apply]
  rw [← Equiv.sum_comp p (fun i : Fin n => |((p.symm i).val : ℝ) - (i.val : ℝ)|)]
  simp [abs_sub_comm]

/-- Measure the change of ranks at the *same physical slots*. -/
theorem slotRankTransport_le_discordant {n : ℕ} (p q : RankPlacement n) :
    transport p.symm q.symm ≤ 2 * ((discordantSlots p q).card : ℝ) := by
  classical
  let f := fun i j : Fin n =>
    if p.symm i < p.symm j ∧ q.symm j < q.symm i then (1 : ℝ) else 0
  have cnt : ((discordantSlots p q).card : ℝ) = ∑ j : Fin n, ∑ i : Fin n, f i j := by
    unfold discordantSlots
    rw [← Finset.sum_boole, Fintype.sum_prod_type, Finset.sum_comm]
  have counted : (∑ j : Fin n, ∑ i : Fin n, f (p i) (p j)) =
      ((discordantSlots p q).card : ℝ) := by
    calc
      _ = ∑ j : Fin n, ∑ i : Fin n, f i (p j) := Finset.sum_congr rfl
        (fun j _ => Equiv.sum_comp p (fun i => f i (p j)))
      _ = _ := (Equiv.sum_comp p (fun z => ∑ i, f i z)).trans cnt.symm
  have h := finPerm_footrule_le_twice_inversions (p.trans q.symm)
  unfold transport
  rw [← Equiv.sum_comp p (fun i : Fin n => |((p.symm i).val : ℝ) - ((q.symm i).val : ℝ)|),
    ← counted]
  calc
    _ = ∑ v : Fin n, |(((p.trans q.symm) v).val : ℝ) - v.val| := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [Equiv.symm_apply_apply, Equiv.trans_apply]
      apply abs_sub_comm
    _ ≤ _ := h
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      by_cases hh : i < j ∧ q.symm (p j) < q.symm (p i) <;> simp [f, hh]

theorem footrule_change_le_discordant {n : ℕ} (p q : RankPlacement n) :
    |footrule p - footrule q| ≤ 2 * ((discordantSlots p q).card : ℝ) := by
  have hp := footrule_triangle p.symm q.symm
  have hq := footrule_triangle q.symm p.symm
  rw [footrule_inverse, footrule_inverse] at hp hq
  rw [transport_symm q.symm p.symm] at hq
  have h := slotRankTransport_le_discordant p q
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem passShiftVariation_footrule {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    (passShiftVariation p q ks : ℝ) +
      |footrule (sortWord p (ks.map Subtype.val)) - footrule (sortWord q (ks.map Subtype.val))| / 2
      ≤ ((discordantSlots p q).card : ℝ) := by
  have h := passShiftVariation_output p q ks
  have h' := footrule_change_le_discordant (sortWord p (ks.map Subtype.val))
    (sortWord q (ks.map Subtype.val))
  have hr : (passShiftVariation p q ks : ℝ) +
      ((discordantSlots (sortWord p (ks.map Subtype.val))
        (sortWord q (ks.map Subtype.val))).card : ℝ) ≤ ((discordantSlots p q).card : ℝ) := by
    exact_mod_cast h
  linarith

/-- The initial Kendall budget of exchanging two arbitrary ranks, computed
exactly and independently of their physical separation. -/
theorem discordantSlots_rankSwap {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : a < b) :
    (discordantSlots p (relabelSwap p a b)).card = 2 * (b.val - a.val) - 1 := by
  classical
  let l := (Finset.Ioc a b).image (fun y => (p a, p y))
  let r := (Finset.Ioo a b).image (fun y => (p y, p b))
  have flip (x y : Fin n) :
      (x < y ∧ Equiv.swap a b y < Equiv.swap a b x) ↔
      (x = a ∧ a < y ∧ y ≤ b) ∨ (y = b ∧ a < x ∧ x < b) := by
    simp only [Equiv.swap_apply_def]
    split_ifs <;> simp_all only [Fin.lt_def, Fin.le_def, Fin.ext_iff] <;> grind
  have hu : discordantSlots p (relabelSwap p a b) = l ∪ r := by
    ext ⟨i, j⟩
    obtain ⟨x,rfl⟩ := p.surjective i
    obtain ⟨y,rfl⟩ := p.surjective j
    simp [discordantSlots, relabelSwap, flip, l, r, and_comm, and_assoc,
      eq_comm]
  have hd : Disjoint l r := by
    rw [Finset.disjoint_left]
    rintro _ hz hw
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x, hx, h⟩ := Finset.mem_image.mp hw
    have ha : x = a := p.injective (congrArg Prod.fst h)
    exact (Finset.mem_Ioo.mp hx).1.ne ha.symm
  have hl : l.card = b.val - a.val := (Finset.card_image_of_injective _
    (fun _ _ he => p.injective (congrArg Prod.snd he))).trans (Fin.card_Ioc a b)
  have hr : r.card = b.val - a.val - 1 := (Finset.card_image_of_injective _
    (fun _ _ he => p.injective (congrArg Prod.fst he))).trans (Fin.card_Ioo a b)
  rw [hu, Finset.card_union_of_disjoint hd, hl, hr]
  change a.val < b.val at hab
  omega

/-- Price of input sensitivity shared between all prefix pass counts and
the actual insertion cost of any one next pass (including the unit pass). -/
theorem passShiftVariation_nextPass {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) (g : ℕ) (hg : 0 < g) :
    passShiftVariation p q ks +
      Nat.dist (gapInsertionCost (sortWord p (ks.map Subtype.val)) g hg)
        (gapInsertionCost (sortWord q (ks.map Subtype.val)) g hg)
      ≤ (discordantSlots p q).card := by
  have bound := passShiftVariation_output p q ks
  have last := ordinaryWordShifts_output_contraction (sortWord p (ks.map Subtype.val))
    (sortWord q (ks.map Subtype.val)) [⟨g,hg⟩]
  simp only [ordinaryWordShifts, add_zero] at last
  omega

private theorem nat_dist_as_real (a b : ℕ) : |(a : ℝ) - b| = (Nat.dist a b : ℝ) := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr (by exact_mod_cast h))]
    simp [Nat.dist, Nat.sub_eq_zero_of_le h, Nat.cast_sub h]
  · rw [abs_of_nonneg (sub_nonneg.mpr (by exact_mod_cast h))]
    simp [Nat.dist, Nat.sub_eq_zero_of_le h, Nat.cast_sub h]

/-- This applies in particular when only long residue jumps receive unit price.
The price must be the same in the two executions. -/
theorem weightedWordShifts_change_le_variation {n : ℕ} (p q : RankPlacement n)
    (w : ℕ → ℝ) (ks : List {k : ℕ // 0 < k}) (hw : ∀ k ∈ ks, |w k.val| ≤ 1) :
    |weightedWordShifts w p ks - weightedWordShifts w q ks| ≤ passShiftVariation p q ks := by
  induction ks generalizing p q with
  | nil => simp [weightedWordShifts, passShiftVariation]
  | cons k ks ih =>
    have tail := ih (gapSort p k) (gapSort q k) (fun z h => hw z (List.mem_cons_of_mem _ h))
    let a := gapInsertionCost p k k.property
    let b := gapInsertionCost q k k.property
    have head : |w k.val * ((a : ℝ) - b)| ≤ (Nat.dist a b : ℝ) := by
      rw [abs_mul, ← nat_dist_as_real]
      exact mul_le_of_le_one_left (abs_nonneg _) (hw k (by simp))
    simp only [weightedWordShifts, passShiftVariation, Nat.cast_add]
    rw [add_sub_add_comm, ← mul_sub]
    exact (abs_add_le ..).trans (add_le_add head tail)

theorem weightedWordShifts_footrule_budget {n : ℕ} (p q : RankPlacement n)
    (w : ℕ → ℝ) (ks : List {k : ℕ // 0 < k}) (hw : ∀ k ∈ ks, |w k.val| ≤ 1) :
    |weightedWordShifts w p ks - weightedWordShifts w q ks| +
      |footrule (sortWord p (ks.map Subtype.val)) - footrule (sortWord q (ks.map Subtype.val))| / 2
      ≤ ((discordantSlots p q).card : ℝ) :=
  (add_le_add_left (weightedWordShifts_change_le_variation p q w ks hw) _).trans
    (passShiftVariation_footrule p q ks)

/-- A chain rank changes only when a pair of keys in that chain changes its
order. Count both ends to bound the change of the chain-normalized footrule. -/
theorem chainFootrule_change_le_discordant {n : ℕ} (p q : RankPlacement n) (k : ℕ) :
    |chainFootrule p k - chainFootrule q k| ≤ 2 * ((discordantSlots p q).card : ℝ) := by
  classical
  let cmp := fun (u : RankPlacement n) (i j : Fin n) =>
    if u.symm j < u.symm i ∧ j.val % k = i.val % k then (1 : ℝ) else 0
  let flip := fun i j : Fin n =>
    if p.symm i < p.symm j ∧ q.symm j < q.symm i then (1 : ℝ) else 0
  have rank (u : RankPlacement n) (i : Fin n) :
      (chainLowerCount (thresholdSet u (u.symm i).val) k (i.val % k) : ℝ)
        = ∑ j, cmp u i j := by
    unfold chainLowerCount thresholdSet
    simp only [Finset.filter_filter, ← Finset.sum_boole]
    rfl
  have pair (i j : Fin n) : |cmp p i j - cmp q i j| ≤ flip i j + flip j i := by
    by_cases he : i = j
    · subst j; simp [cmp, flip]
    have hp := p.symm.injective.ne he
    have hq := q.symm.injective.ne he
    rcases lt_or_gt_of_ne hp with hp | hp <;> rcases lt_or_gt_of_ne hq with hq | hq <;>
      by_cases hm : j.val % k = i.val % k <;>
      simp [cmp, flip, hm, hp, hq, not_lt_of_gt hp, not_lt_of_gt hq]
  have each (i : Fin n) :
      abs (abs ((∑ j, cmp p i j) - ((i.val / k : ℕ) : ℝ)) -
        abs ((∑ j, cmp q i j) - ((i.val / k : ℕ) : ℝ))) ≤ ∑ j, (flip i j + flip j i) := by
    apply (abs_abs_sub_abs_le_abs_sub _ _).trans
    rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun j _ => pair i j))
  have counted : ((discordantSlots p q).card : ℝ) = ∑ i : Fin n, ∑ j : Fin n, flip i j := by
    unfold discordantSlots
    rw [← Finset.sum_boole, Fintype.sum_prod_type]
  unfold chainFootrule
  simp_rw [rank]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply (Finset.sum_le_sum (fun i _ => each i)).trans_eq
  simp_rw [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => flip j i), counted]
  ring

theorem passShiftVariation_chainFootrule {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) (g : ℕ) :
    (passShiftVariation p q ks : ℝ) +
      |chainFootrule (sortWord p (ks.map Subtype.val)) g -
        chainFootrule (sortWord q (ks.map Subtype.val)) g| / 2
      ≤ ((discordantSlots p q).card : ℝ) := by
  have h : (passShiftVariation p q ks : ℝ) +
      ((discordantSlots (sortWord p (ks.map Subtype.val))
        (sortWord q (ks.map Subtype.val))).card : ℝ) ≤ ((discordantSlots p q).card : ℝ) := by
    exact_mod_cast passShiftVariation_output p q ks
  have h' := chainFootrule_change_le_discordant (sortWord p (ks.map Subtype.val))
    (sortWord q (ks.map Subtype.val)) g
  linarith

end Shellsort
