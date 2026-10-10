import CoefficientwiseRigidity.ChordalPaths

/-! Two induced paths with separated interiors form an actual induced cycle. -/
namespace CoefficientwiseRigidity.Structure
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {a b : V}

def InducedPath.Separated (p q : InducedPath G a b) : Prop :=
  ∀ (i : Fin (p.length + 1)) (j : Fin (q.length + 1)),
    0 < i.val → i.val < p.length → 0 < j.val → j.val < q.length →
      p.vertex i ≠ q.vertex j ∧ ¬ G.Adj (p.vertex i) (q.vertex j)

theorem InducedPath.Separated.mixed_ne {p q : InducedPath G a b} (h : p.Separated q)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj0 : 0 < j.val) (hjn : j.val < q.length) : p.vertex i ≠ q.vertex j := by
  intro he
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    have hh : q.vertex 0 = q.vertex j := q.first.trans ((hi ▸ p.first).symm.trans he)
    have := congrArg Fin.val (q.injective hh)
    simp only [Fin.val_zero] at this
    omega
  by_cases hin : i.val = p.length
  · have hi : i = ⟨p.length,by omega⟩ := Fin.ext hin
    have hh : q.vertex ⟨q.length,by omega⟩ = q.vertex j :=
      q.last.trans ((hi ▸ p.last).symm.trans he)
    have := congrArg Fin.val (q.injective hh)
    simp only [Fin.val_mk] at this
    omega
  · exact (h i j (by omega) (by have := i.isLt; omega) hj0 hjn).1 he

theorem InducedPath.Separated.mixed_adj {p q : InducedPath G a b} (h : p.Separated q)
    (hp : 0 < p.length)
    (i : Fin (p.length + 1)) (j : Fin (q.length + 1))
    (hj0 : 0 < j.val) (hjn : j.val < q.length) :
    G.Adj (p.vertex i) (q.vertex j) ↔
      (i.val = 0 ∧ j.val = 1) ∨ (i.val = p.length ∧ j.val + 1 = q.length) := by
  by_cases hi0 : i.val = 0
  · have hi : i = 0 := Fin.ext hi0
    have he : p.vertex i = q.vertex 0 := (hi ▸ p.first).trans q.first.symm
    rw [he,q.adj_iff]
    simp only [Fin.val_zero]
    omega
  by_cases hin : i.val = p.length
  · have hi : i = ⟨p.length,by omega⟩ := Fin.ext hin
    have he : p.vertex i = q.vertex ⟨q.length,by omega⟩ := (hi ▸ p.last).trans q.last.symm
    rw [he,q.adj_iff]
    simp only [Fin.val_mk]
    omega
  · have ha := (h i j (by omega) (by have := i.isLt; omega) hj0 hjn).2
    simp [ha,hi0,hin]

def InducedPath.cycleVertex (p q : InducedPath G a b) (i : Fin (p.length + q.length)) : V :=
  if h : i.val ≤ p.length then p.vertex ⟨i.val,by omega⟩
  else q.vertex ⟨p.length + q.length - i.val,by have := i.isLt; omega⟩

theorem InducedPath.cycle_injective (p q : InducedPath G a b) (h : p.Separated q) :
    Function.Injective (p.cycleVertex q) := by
  intro i j he
  have hi' := i.isLt
  have hj' := j.isLt
  by_cases hi : i.val ≤ p.length <;> by_cases hj : j.val ≤ p.length
  · simp only [InducedPath.cycleVertex,dif_pos hi,dif_pos hj] at he
    have hv := congrArg Fin.val (p.injective he)
    exact Fin.ext hv
  · simp only [InducedPath.cycleVertex,dif_pos hi,dif_neg hj] at he
    exact False.elim (h.mixed_ne _ _ (by dsimp; omega) (by dsimp; omega) he)
  · simp only [InducedPath.cycleVertex,dif_neg hi,dif_pos hj] at he
    exact False.elim (h.mixed_ne _ _ (by dsimp; omega) (by dsimp; omega) he.symm)
  · simp only [InducedPath.cycleVertex,dif_neg hi,dif_neg hj] at he
    have hv := congrArg Fin.val (q.injective he)
    simp only [Fin.val_mk] at hv
    exact Fin.ext (by omega)

theorem InducedPath.cycle_adj (p q : InducedPath G a b) (hp : 2 ≤ p.length)
    (hq : 2 ≤ q.length) (h : p.Separated q) (i j : Fin (p.length + q.length)) :
    G.Adj (p.cycleVertex q i) (p.cycleVertex q j) ↔ CycleAdjacent i j := by
  have hi' := i.isLt
  have hj' := j.isLt
  rw [cycleAdjacent_linear]
  by_cases hi : i.val ≤ p.length <;> by_cases hj : j.val ≤ p.length
  · simp only [InducedPath.cycleVertex,dif_pos hi,dif_pos hj,p.adj_iff,Fin.val_mk]
    omega
  · simp only [InducedPath.cycleVertex,dif_pos hi,dif_neg hj]
    rw [h.mixed_adj (by omega) _ _ (by dsimp; omega) (by dsimp; omega)]
    simp only [Fin.val_mk]
    omega
  · simp only [InducedPath.cycleVertex,dif_neg hi,dif_pos hj]
    rw [G.adj_comm,h.mixed_adj (by omega) _ _ (by dsimp; omega) (by dsimp; omega)]
    simp only [Fin.val_mk]
    omega
  · simp only [InducedPath.cycleVertex,dif_neg hi,dif_neg hj,q.adj_iff,Fin.val_mk]
    omega

/-- The witness uses the original arithmetic cycle predicate, including the
closing edge; no alternate cycle/chordality definition is substituted. -/
theorem InducedPath.not_separated_of_chordal (hg : ChordalGraph G)
    (p q : InducedPath G a b) (hne : a ≠ b) (hnadj : ¬ G.Adj a b) :
    ¬ p.Separated q := by
  intro h
  have hp := p.two_le_length hne hnadj
  have hq := q.two_le_length hne hnadj
  exact hg (p.length + q.length) (by omega)
    ⟨p.cycleVertex q,p.cycle_injective q h,p.cycle_adj q hp hq h⟩

end
end CoefficientwiseRigidity.Structure
