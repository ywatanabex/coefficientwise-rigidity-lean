import CoefficientwiseRigidity.Slices

/-! The actual two-label set compression, its cardinalities and termination weight. -/
namespace CoefficientwiseRigidity.Compression
open Finset
open scoped Classical
noncomputable section
variable {α : Type*} {a b : α}

def shift (a b : α) (D : Finset α) : Finset α :=
  if b ∈ D ∧ a ∉ D then insert a (D.erase b) else D

def swapSet (a b : α) (D : Finset α) : Finset α := D.map (Equiv.swap a b).toEmbedding

def strip (a b : α) (D : Finset α) : Finset α := (D.erase a).erase b

theorem mem_swapSet (D : Finset α) (x : α) :
    x ∈ swapSet a b D ↔ Equiv.swap a b x ∈ D := by
  simp [swapSet,Finset.mem_map_equiv]

theorem swapSet_involutive (D : Finset α) : swapSet a b (swapSet a b D) = D := by
  ext x
  simp only [mem_swapSet,Equiv.swap_apply_self]

theorem card_swapSet (D : Finset α) : (swapSet a b D).card = D.card := Finset.card_map _

theorem card_shift (D : Finset α) : (shift a b D).card = D.card := by
  unfold shift
  split_ifs with h
  · rw [Finset.card_insert_of_not_mem (fun hm => h.2 (Finset.mem_of_mem_erase hm))]
    exact Finset.card_erase_add_one h.1
  · rfl

theorem mem_shift_left (hab : a ≠ b) (D : Finset α) :
    a ∈ shift a b D ↔ a ∈ D ∨ b ∈ D := by
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;> simp [shift,ha,hb,hab]

theorem mem_shift_right (hab : a ≠ b) (D : Finset α) :
    b ∈ shift a b D ↔ a ∈ D ∧ b ∈ D := by
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;> simp [shift,ha,hb,hab,Ne.symm hab]

theorem mem_shift_other (D : Finset α) {x : α} (hxa : x ≠ a) (hxb : x ≠ b) :
    x ∈ shift a b D ↔ x ∈ D := by
  unfold shift
  split_ifs <;> simp [hxa,hxb]

theorem strip_shift (D : Finset α) : strip a b (shift a b D) = strip a b D := by
  ext x
  simp only [strip,Finset.mem_erase]
  constructor
  · rintro ⟨hxb,hxa,hx⟩
    exact ⟨hxb,hxa,(mem_shift_other D hxa hxb).mp hx⟩
  · rintro ⟨hxb,hxa,hx⟩
    exact ⟨hxb,hxa,(mem_shift_other D hxa hxb).mpr hx⟩

theorem strip_swapSet (D : Finset α) : strip a b (swapSet a b D) = strip a b D := by
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp [strip,hxa,hxb,mem_swapSet,Equiv.swap_apply_of_ne_of_ne]

theorem shift_mono (hab : a ≠ b) {D E : Finset α} (hDE : D ⊆ E) :
    shift a b D ⊆ shift a b E := by
  intro x hx
  by_cases hxa : x = a
  · subst x
    rw [mem_shift_left hab] at hx ⊢
    exact hx.imp (fun h => hDE h) (fun h => hDE h)
  by_cases hxb : x = b
  · subst x
    rw [mem_shift_right hab] at hx ⊢
    exact ⟨hDE hx.1,hDE hx.2⟩
  · rw [mem_shift_other _ hxa hxb] at hx ⊢
    exact hDE hx

theorem shift_eq_swap_of_not_left_only (hab : a ≠ b) (D : Finset α)
    (h : ¬ (a ∈ D ∧ b ∉ D)) : shift a b D = swapSet a b D := by
  ext x
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D <;>
    by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [shift,mem_swapSet,Equiv.swap_apply_of_ne_of_ne]

/-- Nested rows all stay fixed, or all undergo the same transposition. -/
theorem nested_shift_common {I : Type*} (D : I → Finset α) (hab : a ≠ b)
    (hn : ∀ i j, D i ⊆ D j ∨ D j ⊆ D i) :
    (∀ i, shift a b (D i) = D i) ∨ (∀ i, shift a b (D i) = swapSet a b (D i)) := by
  by_cases hleft : ∃ i, a ∈ D i ∧ b ∉ D i
  · obtain ⟨i,hai,hbi⟩ := hleft
    left
    intro j
    have hnshift : ¬ (b ∈ D j ∧ a ∉ D j) := by
      rintro ⟨hbj,haj⟩
      rcases hn i j with hij | hji
      · exact haj (hij hai)
      · exact hbi (hji hbj)
    exact if_neg hnshift
  · right
    exact fun i => shift_eq_swap_of_not_left_only hab (D i) (fun h => hleft ⟨i,h⟩)

theorem card_strip_split (hab : a ≠ b) (D : Finset α) :
    D.card = (strip a b D).card + (if a ∈ D then 1 else 0) + (if b ∈ D then 1 else 0) := by
  have h1 := Finset.card_erase_add_one (s := D) (a := a)
  have h2 := Finset.card_erase_add_one (s := D.erase a) (a := b)
  by_cases ha : a ∈ D <;> by_cases hb : b ∈ D
  · have hb' : b ∈ D.erase a := Finset.mem_erase.mpr ⟨Ne.symm hab,hb⟩
    specialize h1 ha
    specialize h2 hb'
    simp only [strip,if_pos ha,if_pos hb]
    omega
  · simp [strip,ha,hb,Finset.erase_eq_of_not_mem (by simp [hb] : b ∉ D.erase a)]
    have := Finset.card_pos.mpr ⟨a,ha⟩
    omega
  · simp [strip,ha,hb,Finset.erase_eq_of_not_mem ha]
    have := Finset.card_pos.mpr ⟨b,hb⟩
    omega
  · simp [strip,ha,hb,Finset.erase_eq_of_not_mem ha,Finset.erase_eq_of_not_mem hb]

theorem inter_card_split (hab : a ≠ b) (Q D : Finset α) :
    (Q ∩ D).card = (strip a b Q ∩ strip a b D).card +
      (if a ∈ Q ∧ a ∈ D then 1 else 0) + (if b ∈ Q ∧ b ∈ D then 1 else 0) := by
  have he : strip a b (Q ∩ D) = strip a b Q ∩ strip a b D := by ext x; simp [strip]; tauto
  rw [card_strip_split hab (Q ∩ D),he]
  simp

theorem inter_shift_max (hab : a ≠ b) (Q D : Finset α) (ha : a ∈ Q) (hb : b ∉ Q) :
    (Q ∩ shift a b D).card = max (Q ∩ D).card (swapSet a b Q ∩ D).card := by
  rw [inter_card_split hab Q (shift a b D),inter_card_split hab Q D,
    inter_card_split hab (swapSet a b Q) D,strip_shift,strip_swapSet]
  simp only [mem_shift_left hab,mem_shift_right hab]
  by_cases haD : a ∈ D <;> by_cases hbD : b ∈ D <;>
    simp [ha,hb,haD,hbD,mem_swapSet,Equiv.swap_apply_left,Equiv.swap_apply_right]

theorem inter_shift_min (hab : a ≠ b) (Q D : Finset α) (ha : a ∉ Q) (hb : b ∈ Q) :
    (Q ∩ shift a b D).card = min (Q ∩ D).card (swapSet a b Q ∩ D).card := by
  rw [inter_card_split hab Q (shift a b D),inter_card_split hab Q D,
    inter_card_split hab (swapSet a b Q) D,strip_shift,strip_swapSet]
  simp only [mem_shift_left hab,mem_shift_right hab]
  by_cases haD : a ∈ D <;> by_cases hbD : b ∈ D <;>
    simp [ha,hb,haD,hbD,mem_swapSet,Equiv.swap_apply_left,Equiv.swap_apply_right]

theorem inter_shift_fixed (hab : a ≠ b) (Q D : Finset α) (hQ : a ∈ Q ↔ b ∈ Q) :
    (Q ∩ shift a b D).card = (Q ∩ D).card := by
  rw [inter_card_split hab Q (shift a b D),inter_card_split hab Q D,strip_shift]
  simp only [mem_shift_left hab,mem_shift_right hab]
  by_cases ha : a ∈ Q <;> by_cases hb : b ∈ Q <;>
    by_cases haD : a ∈ D <;> by_cases hbD : b ∈ D <;> simp_all

theorem swapSet_fixed (D : Finset α) (hD : a ∈ D ↔ b ∈ D) : swapSet a b D = D := by
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;>
    simp_all [mem_swapSet,Equiv.swap_apply_of_ne_of_ne]

theorem shift_weight_lt (w : α → ℕ) (hw : w a < w b) (D : Finset α)
    (hb : b ∈ D) (ha : a ∉ D) :
    (∑ x ∈ shift a b D, w x) < ∑ x ∈ D, w x := by
  have hs := Finset.sum_erase_add D w hb
  have hna : a ∉ D.erase b := fun h => ha (Finset.mem_of_mem_erase h)
  rw [shift,if_pos (show b ∈ D ∧ a ∉ D from ⟨hb,ha⟩),Finset.sum_insert hna]
  omega

end
end CoefficientwiseRigidity.Compression
