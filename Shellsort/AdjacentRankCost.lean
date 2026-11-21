import Shellsort.RankBandCost
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Nat.Dist

/-! Sensitivity of the operational shift counter under a transposition of
consecutive global ranks. The prefix before their first common chain
preserves the transposition, and the common-chain pass merges the states. -/
noncomputable section
namespace Shellsort

/-- Exchange two key labels while leaving the physical array slots in place. -/
def relabelSwap {n : ℕ} (p : RankPlacement n) (a b : Fin n) : RankPlacement n :=
  (Equiv.swap a b).trans p

@[simp] theorem relabelSwap_twice {n : ℕ} (p : RankPlacement n) (a b : Fin n) :
    relabelSwap (relabelSwap p a b) a b = p := by
  ext x
  simp [relabelSwap]

private theorem lost_order {n : ℕ} (a b x y : Fin n) (hab : b.val = a.val + 1)
    (hxy : x < y) (hlost : ¬ Equiv.swap a b x < Equiv.swap a b y) :
    x = a ∧ y = b := by
  simp only [Equiv.swap_apply_def] at hlost
  split_ifs at hlost <;> simp_all only [Fin.lt_def, Fin.ext_iff] <;> first | trivial | omega

private def paidPairs {n : ℕ} (p : RankPlacement n) (k : ℕ) :=
  (gapPositionPairs n k).filter (fun ij => p.symm ij.2 < p.symm ij.1)

private theorem paid_loss {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (k : ℕ) (ij : Fin n × Fin n)
    (h : ij ∈ paidPairs p k) (hl : ij ∉ paidPairs (relabelSwap p a b) k) :
    ij = (p b, p a) := by
  obtain ⟨hij,hin⟩ := Finset.mem_filter.mp h
  have hl' : ¬ Equiv.swap a b (p.symm ij.2) < Equiv.swap a b (p.symm ij.1) := by
    intro hh
    apply hl
    exact Finset.mem_filter.mpr ⟨hij, by simpa [relabelSwap] using hh⟩
  obtain ⟨hx,hy⟩ := lost_order a b _ _ hab hin hl'
  exact Prod.ext (by rw [← hy]; simp) (by rw [← hx]; simp)

theorem adj_gapInversions_le {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (k : ℕ) :
    gapInversions p k ≤ gapInversions (relabelSwap p a b) k + 1 := by
  have hs : paidPairs p k ⊆ insert (p b, p a) (paidPairs (relabelSwap p a b) k) := by
    intro ij hj
    by_cases hh : ij ∈ paidPairs (relabelSwap p a b) k
    · exact Finset.mem_insert_of_mem hh
    · exact Finset.mem_insert.mpr (Or.inl (paid_loss p a b hab k ij hj hh))
  exact (Finset.card_le_card hs).trans (Finset.card_insert_le ..)

private theorem adj_gapInversions_le_of_separate {n : ℕ} (p : RankPlacement n)
    (a b : Fin n) (hab : b.val = a.val + 1) (k : ℕ)
    (hsep : (p a).val % k ≠ (p b).val % k) :
    gapInversions p k ≤ gapInversions (relabelSwap p a b) k := by
  apply Finset.card_le_card
  intro ij hj
  by_contra hh
  obtain rfl := paid_loss p a b hab k ij hj hh
  have hmem := (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2.2
  exact hsep hmem.symm

theorem adj_gapInversions_eq_of_separate {n : ℕ} (p : RankPlacement n)
    (a b : Fin n) (hab : b.val = a.val + 1) (k : ℕ)
    (hsep : (p a).val % k ≠ (p b).val % k) :
    gapInversions p k = gapInversions (relabelSwap p a b) k := by
  apply Nat.le_antisymm (adj_gapInversions_le_of_separate p a b hab k hsep)
  have hs : ((relabelSwap p a b) a).val % k ≠ ((relabelSwap p a b) b).val % k := by
    simpa [relabelSwap] using Ne.symm hsep
  simpa using adj_gapInversions_le_of_separate (relabelSwap p a b) a b hab k hs

theorem adj_gapSort_of_meet {n : ℕ} (p : RankPlacement n) (a b : Fin n) (k : ℕ)
    (hm : (p a).val % k = (p b).val % k) :
    gapSort (relabelSwap p a b) k = gapSort p k := by
  have he (x : Fin n) : ((relabelSwap p a b) x).val % k = (p x).val % k := by
    by_cases h : x = a
    · subst x; simpa [relabelSwap] using hm.symm
    by_cases h' : x = b
    · subst x; simpa [relabelSwap] using hm
    · simp [relabelSwap, Equiv.swap_apply_of_ne_of_ne h h']
  apply gapSort_unique
  · intro x; rw [gapSort_preserves_residue, he]
  · intro x y h
    exact gapSort_sorted p k x y (by simpa only [gapSort_preserves_residue, he] using h)

theorem adj_gapSort_of_separate {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (k : ℕ) (hsep : (p a).val % k ≠ (p b).val % k) :
    gapSort (relabelSwap p a b) k = relabelSwap (gapSort p k) a b := by
  apply gapSort_unique
  · intro x
    exact gapSort_preserves_residue p k (Equiv.swap a b x)
  · intro x y h
    change (gapSort p k (Equiv.swap a b x) < gapSort p k (Equiv.swap a b y)) ↔ x < y
    change (p (Equiv.swap a b x)).val % k = (p (Equiv.swap a b y)).val % k at h
    rw [gapSort_sorted p k _ _ (by simpa only [gapSort_preserves_residue] using h)]
    constructor
    · intro hlt
      by_contra hn
      have H := lost_order a b _ _ hab hlt (by simpa using hn)
      have h' := h
      rw [H.1,H.2] at h'
      exact hsep h'
    · intro hlt
      by_contra hn
      obtain ⟨rfl,rfl⟩ := lost_order a b _ _ hab hlt hn
      exact hsep (by simpa using h.symm)

/-- Position pairs, oriented by the first array's key order, on which the two
arrays disagree. Each disagreement contributes exactly one ordered pair. -/
def discordantSlots {n : ℕ} (p q : RankPlacement n) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ij => p.symm ij.1 < p.symm ij.2 ∧ q.symm ij.2 < q.symm ij.1

private theorem exists_rank_descent {n : ℕ} (p q : RankPlacement n) (hpq : p ≠ q) :
    ∃ a b : Fin n, b.val = a.val + 1 ∧ q.symm (p b) < q.symm (p a) := by
  by_contra! h
  have mono : StrictMono (fun x => q.symm (p x)) := by
    cases n with
    | zero => intro x; exact Fin.elim0 x
    | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      exact lt_of_le_of_ne (h i.castSucc i.succ rfl) (by
        intro he
        have H := p.injective (q.symm.injective he)
        have := congrArg Fin.val H
        simp at this)
  apply hpq
  ext x
  have hx := congrFun mono.eq_id x
  have hx' : q.symm (p x) = x := hx
  simpa using congrArg (fun z => (q z).val) hx'

private theorem fewer_discordantSlots {n : ℕ} (p q : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (hr : q.symm (p b) < q.symm (p a)) :
    (discordantSlots (relabelSwap p a b) q).card < (discordantSlots p q).card := by
  have H : discordantSlots (relabelSwap p a b) q ⊆ discordantSlots p q := by
    intro ij hij
    obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hij).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, h2⟩
    by_contra hn
    change Equiv.swap a b (p.symm ij.1) < Equiv.swap a b (p.symm ij.2) at h1
    obtain ⟨hx,hy⟩ := lost_order a b _ _ hab h1 (by simpa using hn)
    have hi : ij.1 = p b := by
      have := congrArg (Equiv.swap a b) hx
      simpa using congrArg p this
    have hj : ij.2 = p a := by
      have := congrArg (Equiv.swap a b) hy
      simpa using congrArg p this
    rw [hi,hj] at h2
    exact (not_lt_of_gt hr) h2
  apply Finset.card_lt_card (Finset.ssubset_iff_of_subset H |>.mpr ?_)
  refine ⟨(p a,p b), ?_, ?_⟩
  · simp only [discordantSlots, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.symm_apply_apply]
    exact ⟨(show a.val < b.val by omega),hr⟩
  · intro hi
    have hx := (Finset.mem_filter.mp hi).2.1
    have hbad : b < a := by simpa [relabelSwap] using hx
    change b.val < a.val at hbad
    omega

theorem discordantSlots_self {n : ℕ} (p : RankPlacement n) :
    discordantSlots p p = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ij hi
  obtain ⟨h,h'⟩ := (Finset.mem_filter.mp hi).2
  exact (not_lt_of_gt h) h'

theorem discordantSlots_triangle {n : ℕ} (p q r : RankPlacement n) :
    (discordantSlots p r).card ≤ (discordantSlots p q).card + (discordantSlots q r).card := by
  apply le_trans _ (Finset.card_union_le ..)
  apply Finset.card_le_card
  intro ij hi
  obtain ⟨h,h'⟩ := (Finset.mem_filter.mp hi).2
  have hn : q.symm ij.1 ≠ q.symm ij.2 := by
    intro hq
    exact h.ne (congrArg p.symm (q.symm.injective hq))
  rcases lt_or_gt_of_ne hn with hq | hq
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, h'⟩)
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h, hq⟩)

private theorem discordantSlots_adjacent_le_one {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) :
    (discordantSlots p (relabelSwap p a b)).card ≤ 1 := by
  have H : discordantSlots p (relabelSwap p a b) ⊆ {(p a, p b)} := by
    intro ij hi
    obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hi).2
    change Equiv.swap a b (p.symm ij.2) < Equiv.swap a b (p.symm ij.1) at h2
    obtain ⟨hx,hy⟩ := lost_order a b _ _ hab h1 (not_lt_of_gt h2)
    apply Finset.mem_singleton.mpr
    exact Prod.ext (by rw [← hx]; simp) (by rw [← hy]; simp)
  simpa using Finset.card_le_card H

private theorem discordantSlots_swap_le {n : ℕ} (p q : RankPlacement n) :
    (discordantSlots p q).card ≤ (discordantSlots q p).card := by
  apply Finset.card_le_card_of_injOn (Equiv.prodComm (Fin n) (Fin n)) _
    (Equiv.prodComm (Fin n) (Fin n)).injective.injOn
  intro ij hi
  obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hi).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h2, h1⟩

theorem discordantSlots_card_comm {n : ℕ} (p q : RankPlacement n) :
    (discordantSlots p q).card = (discordantSlots q p).card :=
  Nat.le_antisymm (discordantSlots_swap_le p q) (discordantSlots_swap_le q p)

private theorem gain_when_aligned {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (k : ℕ) (hm : (p a).val % k = (p b).val % k)
    (hpos : p a < p b) :
    gapInversions (relabelSwap p a b) k = gapInversions p k + 1 := by
  have H : paidPairs p k ⊆ paidPairs (relabelSwap p a b) k := by
    intro ij hi
    by_contra hn
    obtain rfl := paid_loss p a b hab k ij hi hn
    exact (not_lt_of_gt hpos) ((Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).2.1)
  have hlt : Finset.card (paidPairs p k) < Finset.card (paidPairs (relabelSwap p a b) k) := by
    apply Finset.card_lt_card (Finset.ssubset_iff_of_subset H |>.mpr ?_)
    refine ⟨(p a,p b), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hpos,hm⟩,?_⟩
      simpa [relabelSwap] using (show a < b by change a.val < b.val; omega)
    · intro hi
      have hn : b < a := by simpa using (Finset.mem_filter.mp hi).2
      change b.val < a.val at hn
      omega
  change gapInversions p k < gapInversions (relabelSwap p a b) k at hlt
  have hu := adj_gapInversions_le (relabelSwap p a b) a b hab k
  rw [relabelSwap_twice] at hu
  omega

private theorem meet_gap_dist_one {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (k : ℕ) (hm : (p a).val % k = (p b).val % k) :
    Nat.dist (gapInversions p k) (gapInversions (relabelSwap p a b) k) = 1 := by
  by_cases h : p a < p b
  · have hh := gain_when_aligned p a b hab k hm h
    rw [hh]; unfold Nat.dist; omega
  · have hba : p b < p a := lt_of_le_of_ne (le_of_not_gt h)
      (fun he => by have := congrArg Fin.val (p.injective he); omega)
    have hh := gain_when_aligned (relabelSwap p a b) a b hab k
      (by simpa [relabelSwap] using hm.symm) (by simpa [relabelSwap] using hba)
    rw [relabelSwap_twice] at hh
    unfold Nat.dist
    omega

private theorem discordantSlots_adjacent_one {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) :
    (discordantSlots p (relabelSwap p a b)).card = 1 := by
  have hle := discordantSlots_adjacent_le_one p a b hab
  have hpos : (p a,p b) ∈ discordantSlots p (relabelSwap p a b) := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simpa [relabelSwap] using (show a < b ∧ a < b by
      change a.val < b.val ∧ a.val < b.val; omega)
  have hpositive := Finset.card_pos.mpr ⟨_,hpos⟩
  omega

/-- On a single adjacent-rank edge the joint bound is attained even for an
incomplete word. The changed order is charged either by the moves or by
the final array, but never twice. -/
theorem ordinaryWordShifts_adjacent_exact {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (ks : List {k : ℕ // 0 < k}) :
    Nat.dist (ordinaryWordShifts p ks) (ordinaryWordShifts (relabelSwap p a b) ks) +
      (discordantSlots (sortWord p (ks.map Subtype.val))
        (sortWord (relabelSwap p a b) (ks.map Subtype.val))).card = 1 := by
  induction ks generalizing p with
  | nil => simpa [ordinaryWordShifts, sortWord, Nat.dist] using discordantSlots_adjacent_one p a b hab
  | cons k ks ih =>
    simp only [ordinaryWordShifts, gapInsertionCost_eq_gapInversions, List.map_cons, sortWord]
    by_cases hm : (p a).val % k.val = (p b).val % k.val
    · rw [adj_gapSort_of_meet p a b k.val hm, discordantSlots_self]
      simp only [Finset.card_empty, Nat.add_zero]
      have h := meet_gap_dist_one p a b hab k.val hm
      unfold Nat.dist at *
      omega
    · rw [adj_gapSort_of_separate p a b hab k.val hm,
        adj_gapInversions_eq_of_separate p a b hab k.val hm]
      have h := ih (gapSort p k.val)
      unfold Nat.dist at *
      omega


/-- If an adjacent edit still distinguishes the checkpoints, its unit of
sensitivity is retained by the output rather than used by the accumulated cost. -/
theorem ordinaryWordShifts_adjacent_budget {n : ℕ} (p : RankPlacement n) (a b : Fin n)
    (hab : b.val = a.val + 1) (ks : List {k : ℕ // 0 < k}) :
    ordinaryWordShifts p ks +
      (discordantSlots (sortWord p (ks.map Subtype.val))
        (sortWord (relabelSwap p a b) (ks.map Subtype.val))).card ≤
      ordinaryWordShifts (relabelSwap p a b) ks + 1 := by
  have h := ordinaryWordShifts_adjacent_exact p a b hab ks
  unfold Nat.dist at h
  omega

/-- A common input-change budget for movement cost and remaining output
disagreement, including prefixes that stop before the array is sorted. -/
theorem ordinaryWordShifts_output_budget {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    ordinaryWordShifts p ks +
      (discordantSlots (sortWord p (ks.map Subtype.val)) (sortWord q (ks.map Subtype.val))).card ≤
    ordinaryWordShifts q ks + (discordantSlots p q).card := by
  by_cases hpq : p = q
  · subst p; simp [discordantSlots_self]
  · obtain ⟨a,b,hab,hr⟩ := exists_rank_descent p q hpq
    have hd := fewer_discordantSlots p q a b hab hr
    have h1 := ordinaryWordShifts_adjacent_budget p a b hab ks
    have hi := ordinaryWordShifts_output_budget (relabelSwap p a b) q ks
    have ht := discordantSlots_triangle (sortWord p (ks.map Subtype.val))
      (sortWord (relabelSwap p a b) (ks.map Subtype.val)) (sortWord q (ks.map Subtype.val))
    omega
termination_by (discordantSlots p q).card


/-- Symmetric version. The cost term is the absolute difference in numbers
of successful record shifts. -/
theorem ordinaryWordShifts_output_contraction {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    Nat.dist (ordinaryWordShifts p ks) (ordinaryWordShifts q ks) +
      (discordantSlots (sortWord p (ks.map Subtype.val)) (sortWord q (ks.map Subtype.val))).card ≤
    (discordantSlots p q).card := by
  have h1 := ordinaryWordShifts_output_budget p q ks
  have h2 := ordinaryWordShifts_output_budget q p ks
  rw [discordantSlots_card_comm q p,
      discordantSlots_card_comm (sortWord q _) (sortWord p _)] at h2
  unfold Nat.dist
  omega

/-- The complete finite-word ordinary insertion cost is one-Lipschitz for
Kendall distance on the initial physical position labels. -/
theorem ordinaryWordShifts_le_add_discordant {n : ℕ} (p q : RankPlacement n)
    (ks : List {k : ℕ // 0 < k}) :
    ordinaryWordShifts p ks ≤ ordinaryWordShifts q ks + (discordantSlots p q).card := by
  have h := ordinaryWordShifts_output_budget p q ks
  omega

/-- Potentially hidden order decisions under a nondecreasing labeling of
ranks. Each pair of ranks in the same bin occurs once. -/
def unresolvedRankPairs {n : ℕ} (color : Fin n → ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter fun ab => ab.1 < ab.2 ∧ color ab.1 = color ab.2

/-- Two rank refinements of one observed color array in physical slots. -/
def SameRankColors {n : ℕ} (color : Fin n → ℕ) (p q : RankPlacement n) : Prop :=
  ∀ i, color (p.symm i) = color (q.symm i)

theorem discordantSlots_le_unresolved {n : ℕ} (color : Fin n → ℕ) (hc : Monotone color)
    (p q : RankPlacement n) (hf : SameRankColors color p q) :
    (discordantSlots p q).card ≤ (unresolvedRankPairs color).card := by
  let e := Equiv.prodCongr p.symm p.symm
  apply Finset.card_le_card_of_injOn e _ e.injective.injOn
  intro ij hi
  obtain ⟨h1,h2⟩ := (Finset.mem_filter.mp hi).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,h1,le_antisymm (hc h1.le) ?_⟩
  change color (p.symm ij.2) ≤ color (p.symm ij.1)
  rw [hf ij.2, hf ij.1]
  exact hc h2.le

/-- A path-independent diameter bound for the actual cost conditional on
coarse ranks. The bound counts each unresolved pair once across all passes. -/
theorem ordinaryWordShifts_sameColors_le {n : ℕ} (color : Fin n → ℕ) (hc : Monotone color)
    (p q : RankPlacement n) (hf : SameRankColors color p q) (ks : List {k : ℕ // 0 < k}) :
    ordinaryWordShifts p ks ≤ ordinaryWordShifts q ks + (unresolvedRankPairs color).card :=
  (ordinaryWordShifts_le_add_discordant p q ks).trans
    (Nat.add_le_add_left (discordantSlots_le_unresolved color hc p q hf) _)

/-- Any word that beats another on a representative can lose at most twice
the fiber diameter on the true refinement. Both executions start at the
true input when their costs are compared. -/
theorem ordinaryWordShifts_representative_regret {n : ℕ}
    (color : Fin n → ℕ) (hc : Monotone color) (p q : RankPlacement n)
    (hf : SameRankColors color p q) (u v : List {k : ℕ // 0 < k})
    (hq : ordinaryWordShifts q u ≤ ordinaryWordShifts q v) :
    ordinaryWordShifts p u ≤ ordinaryWordShifts p v + 2 * (unresolvedRankPairs color).card := by
  have hu := ordinaryWordShifts_sameColors_le color hc p q hf u
  have hv := ordinaryWordShifts_sameColors_le color hc q p (fun i => (hf i).symm) v
  omega


theorem sortWord_eq_after_one {n : ℕ} (p q : RankPlacement n) (ks : List ℕ) (h : 1 ∈ ks) :
    sortWord p ks = sortWord q ks := by
  induction ks generalizing p q with
  | nil => simp at h
  | cons k ks ih =>
    rcases List.mem_cons.mp h with he | he
    · subst k; simp [sortWord, gapSort_one]
    · exact ih (gapSort p k) (gapSort q k) he

/-- Once a global sorting pass is present, an adjacent rank flip changes
the shift count by exactly one, for every input and either orientation. -/
theorem ordinaryWordShifts_adjacent_exact_of_one {n : ℕ} (p : RankPlacement n)
    (a b : Fin n) (hab : b.val = a.val + 1) (ks : List {k : ℕ // 0 < k})
    (h : 1 ∈ ks.map Subtype.val) :
    Nat.dist (ordinaryWordShifts p ks) (ordinaryWordShifts (relabelSwap p a b) ks) = 1 := by
  have hh := ordinaryWordShifts_adjacent_exact p a b hab ks
  rw [sortWord_eq_after_one p (relabelSwap p a b) _ h, discordantSlots_self] at hh
  simpa using hh


end Shellsort
end

