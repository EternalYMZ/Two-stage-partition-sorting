import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic

namespace Shellsort.OrderedBlockThreshold

/-- A block of distinct slots in visitation order. -/
abbrev Block (n : ℕ) := Σ m : ℕ, Fin m ↪ Fin n

def support {n m : ℕ} (s : Fin m ↪ Fin n) : Finset (Fin n) :=
  Finset.univ.map s

/-- Sort a binary threshold on one block: its low keys fill its prefix. -/
def pack {n m : ℕ} (s : Fin m ↪ Fin n) (A : Finset (Fin n)) : Finset (Fin n) :=
  (A \ support s) ∪
    (Finset.univ.filter (fun j : Fin m => j.val < (A ∩ support s).card)).map s

theorem pack_mono {n m : ℕ} (s : Fin m ↪ Fin n) {A B : Finset (Fin n)}
    (hab : A ⊆ B) : pack s A ⊆ pack s B := by
  unfold pack
  apply Finset.union_subset_union
  · intro i hi
    exact Finset.mem_sdiff.mpr ⟨hab (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩
  apply Finset.map_subset_map.mpr
  intro i hi
  have sub : A ∩ support s ⊆ B ∩ support s := Finset.inter_subset_inter hab (fun _ h => h)
  have count := Finset.card_le_card sub
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le count⟩

theorem pack_card {n m : ℕ} (s : Fin m ↪ Fin n) (A : Finset (Fin n)) :
    (pack s A).card = A.card := by
  have hs : (support s).card = m := by simp [support]
  have hc : (A ∩ support s).card ≤ m := calc
    (A ∩ support s).card ≤ (support s).card := Finset.card_le_card Finset.inter_subset_right
    _ = m := hs
  have dis : Disjoint (A \ support s)
      ((Finset.univ.filter (fun j : Fin m => j.val < (A ∩ support s).card)).map s) := by
    apply Finset.disjoint_left.mpr
    intro i ha hi
    rcases Finset.mem_map.mp hi with ⟨j,_,rfl⟩
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  rw [pack, Finset.card_union_of_disjoint dis, Finset.card_map, Fin.card_filter_val_lt,
    min_eq_right hc, Finset.card_sdiff_add_card_inter]

def run {n : ℕ} : List (Block n) → Finset (Fin n) → Finset (Fin n)
  | [], A => A
  | s :: ss, A => run ss (pack s.2 A)

theorem run_mono {n : ℕ} (word : List (Block n)) {A B : Finset (Fin n)}
    (hab : A ⊆ B) : run word A ⊆ run word B := by
  induction word generalizing A B with
  | nil => exact hab
  | cons s ss ih => exact ih (pack_mono _ hab)

theorem run_card {n : ℕ} (word : List (Block n)) (A : Finset (Fin n)) :
    (run word A).card = A.card := by
  induction word generalizing A with
  | nil => rfl
  | cons s ss ih => exact (ih _).trans (pack_card _ _)

/-- This permits different block sizes, different orders and overlapping blocks. -/
theorem directed_difference {n : ℕ} (word : List (Block n)) (A B : Finset (Fin n)) :
    (run word A \ run word B).card ≤ (A \ B).card := by
  have shared : run word (B ∩ A) ⊆ run word B ∩ run word A :=
    Finset.subset_inter (run_mono _ Finset.inter_subset_left) (run_mono _ Finset.inter_subset_right)
  have bound := Finset.card_le_card shared
  rw [run_card] at bound
  rw [Finset.card_sdiff,Finset.card_sdiff,run_card]
  omega

section Keys

variable {α : Type*} [LinearOrder α]

def low {n : ℕ} (x : Fin n → α) (t : α) := Finset.univ.filter (fun i => x i < t)

/-- The local sorting contract only fixes the resulting block and the untouched slots. -/
structure SortedBlock {m n : ℕ} (s : Fin m ↪ Fin n) (x y : Fin n → α) : Prop where
  sorted : Monotone (fun j => y (s j))
  reordered : ∃ π : Equiv.Perm (Fin m), ∀ j, y (s j) = x (s (π j))
  outside : ∀ i, i ∉ support s → y i = x i

private theorem slot_lt_iff {m : ℕ} {v : Fin m → α} (hv : Monotone v) (t : α) (j : Fin m) :
    v j < t ↔ j.val < (low v t).card := by
  constructor
  · intro hj
    have sub : Finset.Iic j ⊆ low v t := fun i h =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hv (Finset.mem_Iic.mp h)).trans_lt hj⟩
    have b := Finset.card_le_card sub
    rw [Fin.card_Iic] at b
    omega
  · intro hj
    by_contra hh
    have sub : low v t ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      by_contra! h
      exact hh ((hv h).trans_lt (Finset.mem_filter.mp hi).2)
    have b := Finset.card_le_card sub
    rw [Fin.card_Iio] at b
    omega

theorem threshold_of_sortedBlock {m n : ℕ} (s : Fin m ↪ Fin n)
    {x y : Fin n → α} (h : SortedBlock s x y) (t : α) :
    low y t = pack s (low x t) := by
  classical
  obtain ⟨π,hπ⟩ := h.reordered
  have eq1 : (low (fun j => y (s j)) t).map π.toEmbedding = low (fun j => x (s j)) t := by
    ext j
    simp only [Finset.mem_map, low, Finset.mem_filter, Finset.mem_univ, true_and,
      Equiv.toEmbedding_apply]
    constructor
    · rintro ⟨i,hi,rfl⟩; simpa [hπ] using hi
    · intro hj; exact ⟨π.symm j, by simpa [hπ] using hj, π.apply_symm_apply _⟩
  have eq2 : (low (fun j => x (s j)) t).map s = low x t ∩ support s := by
    ext i
    simp only [low, support, Finset.mem_inter, Finset.mem_map, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j,hj,rfl⟩; exact ⟨hj,j,rfl⟩
    · rintro ⟨hx,j,rfl⟩; exact ⟨j,hx,rfl⟩
  have same : (low (fun j => y (s j)) t).card = (low x t ∩ support s).card := by
    rw [← eq2, Finset.card_map, ← eq1, Finset.card_map]
  ext i
  by_cases he : i ∈ support s
  · obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp he
    have hj := slot_lt_iff h.sorted t j
    rw [same] at hj
    simp only [low,pack,Finset.mem_union,Finset.mem_sdiff,he,not_true_eq_false,and_false,
      false_or,Finset.mem_map',Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · intro hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj.mp hx⟩
    · intro hx
      exact hj.mpr (Finset.mem_filter.mp hx).2
  · have nohit : ¬∃ j, s j = i := fun ⟨j,hj⟩ => he (Finset.mem_map.mpr ⟨j,Finset.mem_univ _,hj⟩)
    simp only [low,pack,Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter,
      Finset.mem_univ,true_and,he,not_false_eq_true,and_true,Finset.mem_map,h.outside i he]
    exact ⟨Or.inl,fun h' => h'.elim id (fun ⟨j,_,hj⟩ => (nohit ⟨j,hj⟩).elim)⟩

inductive Follows {n : ℕ} : List (Block n) → (Fin n → α) → (Fin n → α) → Prop where
  | done (x) : Follows [] x x
  | next {s : Block n} {ss x y z} (sorted : SortedBlock s.2 x y)
      (later : Follows ss y z) : Follows (s :: ss) x z

theorem trace_threshold {n : ℕ} {word : List (Block n)} {x y : Fin n → α}
    (path : Follows word x y) (t : α) : low y t = run word (low x t) := by
  induction path with
  | done => rfl
  | next hb _ ih => rw [ih, threshold_of_sortedBlock _ hb t]; rfl

theorem trace_contraction {n : ℕ} {word : List (Block n)} {x y u v : Fin n → α}
    (firstPath : Follows word x y) (secondPath : Follows word u v) (t : α) :
    (low y t \ low v t).card ≤ (low x t \ low u t).card := by
  rw [trace_threshold firstPath t, trace_threshold secondPath t]
  exact directed_difference _ _ _

end Keys
end Shellsort.OrderedBlockThreshold

#print axioms Shellsort.OrderedBlockThreshold.directed_difference
#print axioms Shellsort.OrderedBlockThreshold.threshold_of_sortedBlock
#print axioms Shellsort.OrderedBlockThreshold.trace_contraction
