import Shellsort.OrderedBlockThreshold

namespace Shellsort.OrderedBlockThreshold

private def front {m n : ℕ} (s : Fin m ↪ Fin n) (k : ℕ) :=
  (Finset.univ.filter (fun j : Fin m => j.val < k)).map s

private theorem front_sub {m n : ℕ} (s : Fin m ↪ Fin n) (k : ℕ) :
    front s k ⊆ support s := Finset.map_subset_map.mpr (Finset.filter_subset _ _)

private theorem front_mono {m n k l : ℕ} (s : Fin m ↪ Fin n) (h : k ≤ l) :
    front s k ⊆ front s l := by
  apply Finset.map_subset_map.mpr
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.trans_le h⟩

private theorem front_card {m n : ℕ} (s : Fin m ↪ Fin n) (A : Finset (Fin n)) :
    (front s (A ∩ support s).card).card = (A ∩ support s).card := by
  have bound := Finset.card_le_card (show A ∩ support s ⊆ support s from Finset.inter_subset_right)
  simp [front, Fin.card_filter_val_lt, min_eq_right (show (A ∩ support s).card ≤ m by
    simpa [support] using bound)]

private theorem pieces {m n : ℕ} (s : Fin m ↪ Fin n) (A : Finset (Fin n)) :
    pack s A \ support s = A \ support s ∧
      pack s A ∩ support s = front s (A ∩ support s).card := by
  change ((A \ support s) ∪ front s (A ∩ support s).card) \ support s = A \ support s ∧
    ((A \ support s) ∪ front s (A ∩ support s).card) ∩ support s = front s (A ∩ support s).card
  have sub := front_sub s (A ∩ support s).card
  constructor <;> ext i <;> simp only [Finset.mem_union,Finset.mem_inter,Finset.mem_sdiff] <;>
    have hs : i ∈ front s (A ∩ support s).card → i ∈ support s := fun hi => sub hi <;> tauto

private theorem split_diff {n : ℕ} (A B S : Finset (Fin n)) :
    (A \ B).card = ((A \ S) \ (B \ S)).card + ((A ∩ S) \ (B ∩ S)).card := by
  have h₀ : ((A \ B) \ S) = (A \ S) \ (B \ S) := by
    ext i; simp only [Finset.mem_sdiff]; tauto
  have h₁ : (A \ B) ∩ S = (A ∩ S) \ (B ∩ S) := by
    ext i; simp only [Finset.mem_inter, Finset.mem_sdiff]; tauto
  rw [← h₀, ← h₁, Finset.card_sdiff_add_card_inter]

/-- One cancellation removes one mark of each orientation within this block. -/
def cancellations {m n : ℕ} (s : Fin m ↪ Fin n) (A B : Finset (Fin n)) : ℕ :=
  min (((A ∩ support s) \ (B ∩ support s)).card)
      (((B ∩ support s) \ (A ∩ support s)).card)

theorem one_block_exact {m n : ℕ} (s : Fin m ↪ Fin n) (A B : Finset (Fin n)) :
    (pack s A \ pack s B).card + cancellations s A B = (A \ B).card := by
  rw [split_diff (pack s A) (pack s B) (support s), split_diff A B (support s)]
  rw [(pieces s A).1,(pieces s B).1,(pieces s A).2,(pieces s B).2]
  unfold cancellations
  have ha := Finset.card_sdiff_add_card_inter (A ∩ support s) (B ∩ support s)
  have hb := Finset.card_sdiff_add_card_inter (B ∩ support s) (A ∩ support s)
  rw [Finset.inter_comm (B ∩ support s) (A ∩ support s)] at hb
  rcases le_total (A ∩ support s).card (B ∩ support s).card with h | h
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr (front_mono s h), Finset.card_empty]
    omega
  · rw [Finset.card_sdiff_of_subset (front_mono s h),front_card,front_card]
    omega

def totalLoss {n : ℕ} : List (Block n) → Finset (Fin n) → Finset (Fin n) → ℕ
  | [], _, _ => 0
  | s :: rest, A, B => cancellations s.2 A B + totalLoss rest (pack s.2 A) (pack s.2 B)

theorem word_exact {n : ℕ} (word : List (Block n)) (A B : Finset (Fin n)) :
    (run word A \ run word B).card + totalLoss word A B = (A \ B).card := by
  induction word generalizing A B with
  | nil => simp [run,totalLoss]
  | cons s rest ih =>
    have first := one_block_exact s.2 A B
    have later := ih (pack s.2 A) (pack s.2 B)
    simp only [run,totalLoss]
    omega

theorem loss_comm {n : ℕ} (word : List (Block n)) (A B : Finset (Fin n)) :
    totalLoss word A B = totalLoss word B A := by
  induction word generalizing A B with
  | nil => rfl
  | cons s ss ih => simp only [totalLoss, cancellations, min_comm]; rw [ih (pack s.2 A) (pack s.2 B)]

end Shellsort.OrderedBlockThreshold

namespace Shellsort.OrderedBlockThreshold

def rankDistance {n k : ℕ} (x u : Fin n → Fin k) : ℕ :=
  ∑ i, (((x i).val - (u i).val) + ((u i).val - (x i).val))

private theorem directed_cuts {n k : ℕ} (x u : Fin n → Fin k) :
    ∑ t : Fin k, ((low x t) \ (low u t)).card = ∑ i, ((u i).val - (x i).val) := by
  classical
  have cut (t : Fin k) : ((low x t) \ (low u t)).card =
      ∑ i : Fin n, if x i < t ∧ ¬u i < t then 1 else 0 := by
    rw [Finset.sum_boole]
    congr 1
    ext i
    simp [low, Finset.mem_sdiff]
  simp_rw [cut]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_boole]
  have seg : (Finset.univ.filter fun t : Fin k => x i < t ∧ ¬u i < t) =
      Finset.Iic (u i) \ Finset.Iic (x i) := by
    ext t
    simp [Finset.mem_sdiff, and_comm]
  rw [seg]
  rcases le_total (x i) (u i) with h | h
  · rw [Finset.card_sdiff_of_subset (Finset.Iic_subset_Iic.mpr h), Fin.card_Iic, Fin.card_Iic]
    simp
  · rw [Finset.sdiff_eq_empty_iff_subset.mpr (Finset.Iic_subset_Iic.mpr h)]
    simp [Nat.sub_eq_zero_of_le (show (u i).val ≤ (x i).val from h)]

theorem trace_distance_exact {n k : ℕ} {word : List (Block n)} {x y u v : Fin n → Fin k}
    (p : Follows word x y) (q : Follows word u v) :
    rankDistance y v + 2 * (∑ t, totalLoss word (low x t) (low u t)) = rankDistance x u := by
  have balance {a b c d : Fin n → Fin k} (first : Follows word a b)
      (second : Follows word c d) :
      (∑ i, ((d i).val - (b i).val)) + (∑ t, totalLoss word (low a t) (low c t)) =
        ∑ i, ((c i).val - (a i).val) := by
    rw [← directed_cuts, ← directed_cuts, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [trace_threshold first t, trace_threshold second t]
    exact word_exact _ _ _
  have h := balance p q
  have g := balance q p
  have flip : (∑ t, totalLoss word (low u t) (low x t)) =
      ∑ t, totalLoss word (low x t) (low u t) :=
    Finset.sum_congr rfl (fun t _ => loss_comm word _ _)
  rw [flip] at g
  unfold rankDistance
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  omega

theorem target_footrule_exact {n : ℕ} {word : List (Block n)} {x y : Fin n → Fin n}
    (p : Follows word x y) (ordered : ∀ s ∈ word, Monotone s.2) :
    rankDistance y id + 2 * (∑ t, totalLoss word (low x t) (low id t)) = rankDistance x id := by
  apply trace_distance_exact p
  clear p
  induction word with
  | nil => exact .done _
  | cons s rest ih =>
    apply Follows.next (y := id)
    · exact ⟨ordered s (by simp), ⟨Equiv.refl _, fun _ => rfl⟩, fun _ _ => rfl⟩
    · exact ih (by intro t ht; exact ordered t (List.mem_cons_of_mem _ ht))

end Shellsort.OrderedBlockThreshold
