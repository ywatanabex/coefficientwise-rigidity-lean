import CoefficientwiseRigidity.HolonomyGauge
import CoefficientwiseRigidity.PaperReserve

/-! Coefficient form of the manuscript's polynomial lower bound, including zero ranks. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

theorem paperReserve_zero_of_not_feasible (b : Bipartition G) (hM : 2 ≤ M)
    (a : V → ℕ) (ha : ¬ Feasible G M a) : paperReserve G M a = 0 := by
  by_cases hp : Positive a
  · rw [paperReserve_eq_reserve G M a hp]
    apply Nat.eq_zero_of_not_pos
    intro hr
    have hf := (ordinary_pos_iff_feasible b (fun v => a v - 1)).mp hr
    apply ha
    constructor
    · intro v
      have := hp v
      have hfv : a v - 1 ≤ M - 2 := hf.1 v
      omega
    · intro u v he
      have := hp u
      have := hp v
      have hfe : a u - 1 + (a v - 1) ≤ M - 2 := hf.2 u v he
      omega
  · simp [paperReserve, hp]

/-- Every coefficient, with the shifted polynomial reserve rather than truncated ranks. -/
theorem coefficient_kappa_paperReserve (b : Bipartition G) (hM : 2 ≤ M)
    (X : Cover G M) (a : V → ℕ) (root : V) (hc : G.Connected)
    (he : ∃ u v, G.Adj u v) (hw : TreewidthAtMostTwo G) (hn : ¬ Flat X) :
    (coefficient X a : ℚ) + kappa M (holonomyGroup X root) * paperReserve G M a ≤
      ordinary G M a := by
  by_cases hf : Feasible G M a
  · by_cases hp : Positive a
    · rw [paperReserve_eq_reserve G M a hp]
      exact (mainBKappa b M hM X a root hc he hw hp hf hn).2.2.1
    · simp only [paperReserve, if_neg hp, Nat.cast_zero, mul_zero, add_zero]
      exact_mod_cast coefficient_le_of_treewidth b X a hw
  · rw [paperReserve_zero_of_not_feasible b hM a hf,
      coefficient_zero_of_not_feasible X a hf]
    simp

end
end CoefficientwiseRigidity
