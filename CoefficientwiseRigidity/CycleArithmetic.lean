import CoefficientwiseRigidity.Targets

/-! Arithmetic helpers for the paper's unchanged induced-cycle definition. -/
namespace CoefficientwiseRigidity.Structure
open scoped Classical
variable {n : ℕ}

def cycleNext (i : Fin n) : Fin n :=
  if h : i.val + 1 < n then ⟨i.val + 1,h⟩ else ⟨0,by omega⟩

theorem cycleNext_val (i : Fin n) : (cycleNext i).val = (i.val + 1) % n := by
  unfold cycleNext
  split_ifs with h
  · exact (Nat.mod_eq_of_lt h).symm
  · have he : i.val + 1 = n := by omega
    simp [he]

theorem cycleAdjacent_linear (i j : Fin n) : CycleAdjacent i j ↔
    i.val + 1 = j.val ∨ j.val + 1 = i.val ∨
      (i.val + 1 = n ∧ j.val = 0) ∨ (j.val + 1 = n ∧ i.val = 0) := by
  unfold CycleAdjacent
  by_cases hi : i.val + 1 < n <;> by_cases hj : j.val + 1 < n
  · rw [Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj]
    omega
  · have hej : j.val + 1 = n := by omega
    rw [Nat.mod_eq_of_lt hi,hej,Nat.mod_self]
    omega
  · have hei : i.val + 1 = n := by omega
    rw [hei,Nat.mod_self,Nat.mod_eq_of_lt hj]
    omega
  · have hei : i.val + 1 = n := by omega
    have hej : j.val + 1 = n := by omega
    rw [hei,hej,Nat.mod_self]
    omega

theorem cycleAdjacent_next (i : Fin n) : CycleAdjacent i (cycleNext i) :=
  Or.inl (cycleNext_val i).symm

theorem cycleNext_ne (hn : 2 ≤ n) (i : Fin n) : cycleNext i ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  unfold cycleNext at hv
  split_ifs at hv <;> simp only [Fin.val_mk] at * <;> omega

theorem cycleNext_cases (i : Fin n) :
    ((cycleNext i).val = i.val + 1 ∧ i.val + 1 < n) ∨
      ((cycleNext i).val = 0 ∧ i.val + 1 = n) := by
  unfold cycleNext
  split_ifs with h
  · exact Or.inl ⟨rfl,h⟩
  · exact Or.inr ⟨rfl,by omega⟩

theorem cycleNext_two_ne (hn : 3 ≤ n) (i : Fin n) : cycleNext (cycleNext i) ≠ i := by
  intro h
  have hv := congrArg Fin.val h
  have h1 := cycleNext_cases i
  have h2 := cycleNext_cases (cycleNext i)
  omega

/-- A chordless cycle of length at least four has no common neighbour of the
ends of one edge. This prevents a primal edge witness from containing a third
cycle column. -/
theorem cycle_no_triangle (hn : 4 ≤ n) (i j : Fin n)
    (h1 : CycleAdjacent i j) (h2 : CycleAdjacent (cycleNext i) j) : False := by
  rw [cycleAdjacent_linear] at h1 h2
  have hi := i.isLt
  have hj := j.isLt
  have hs := cycleNext_cases i
  omega

/-- The index in an alternating row/column cycle. -/
def halfIndex (i : Fin (2 * n)) : Fin n := ⟨i.val / 2,by omega⟩

def alternatingCycle {R C : Type} (e : Fin n → R) (c : Fin n → C)
    (i : Fin (2 * n)) : R ⊕ C :=
  if i.val % 2 = 0 then Sum.inr (c (halfIndex i)) else Sum.inl (e (halfIndex i))

theorem alternatingCycle_injective {R C : Type} {e : Fin n → R} {c : Fin n → C}
    (he : Function.Injective e) (hc : Function.Injective c) :
    Function.Injective (alternatingCycle e c) := by
  intro i j h
  by_cases hi : i.val % 2 = 0
  · by_cases hj : j.val % 2 = 0
    · simp only [alternatingCycle,if_pos hi,if_pos hj,Sum.inr.injEq] at h
      have hv := congrArg Fin.val (hc h)
      change i.val / 2 = j.val / 2 at hv
      apply Fin.ext
      omega
    · simp [alternatingCycle,hi,hj] at h
  · by_cases hj : j.val % 2 = 0
    · simp [alternatingCycle,hi,hj] at h
    · simp only [alternatingCycle,if_neg hi,if_neg hj,Sum.inl.injEq] at h
      have hv := congrArg Fin.val (he h)
      change i.val / 2 = j.val / 2 at hv
      apply Fin.ext
      omega

/-- The wraparound edge is included; all arithmetic is on the original Fin(2n). -/
theorem alternatingCycle_adjacent (i j : Fin (2 * n)) :
    CycleAdjacent i j ↔
      (i.val % 2 = 0 ∧ j.val % 2 ≠ 0 ∧
        (halfIndex i = halfIndex j ∨ halfIndex i = cycleNext (halfIndex j))) ∨
      (i.val % 2 ≠ 0 ∧ j.val % 2 = 0 ∧
        (halfIndex j = halfIndex i ∨ halfIndex j = cycleNext (halfIndex i))) := by
  rw [cycleAdjacent_linear]
  have hi := i.isLt
  have hj := j.isLt
  have hs := cycleNext_cases (halfIndex i)
  have ht := cycleNext_cases (halfIndex j)
  simp only [Fin.ext_iff]
  change _ ↔ (i.val % 2 = 0 ∧ j.val % 2 ≠ 0 ∧
      (i.val / 2 = j.val / 2 ∨ i.val / 2 = (cycleNext (halfIndex j)).val)) ∨
    (i.val % 2 ≠ 0 ∧ j.val % 2 = 0 ∧
      (j.val / 2 = i.val / 2 ∨ j.val / 2 = (cycleNext (halfIndex i)).val))
  change ((cycleNext (halfIndex i)).val = i.val / 2 + 1 ∧ i.val / 2 + 1 < n) ∨
    ((cycleNext (halfIndex i)).val = 0 ∧ i.val / 2 + 1 = n) at hs
  change ((cycleNext (halfIndex j)).val = j.val / 2 + 1 ∧ j.val / 2 + 1 < n) ∨
    ((cycleNext (halfIndex j)).val = 0 ∧ j.val / 2 + 1 = n) at ht
  omega

end CoefficientwiseRigidity.Structure
