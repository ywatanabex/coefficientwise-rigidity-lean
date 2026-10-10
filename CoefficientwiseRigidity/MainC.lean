import CoefficientwiseRigidity.HullFibres
import CoefficientwiseRigidity.HullQuantitative

/-! Completed inhabitants of all three Main C propositions and the combined original A–C target. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem paperMainC (b : Bipartition G) :
    MainCComparisonRigidity G ∧ MainCFibres G ∧ MainCQuantitative G :=
  ⟨paperMainCComparisonRigidity b, paperMainCFibres b, paperMainCQuantitative b⟩

/-- The original Targets.lean proposition; no target, premise, or graph class is replaced. -/
theorem paperMainTheorems : PaperMainTheorems := by
  intro n G hb
  obtain ⟨b⟩ := hb
  exact ⟨paperMainA b, mainBTwo b, mainBKappa b, mainBOdd b, paperMainC b⟩

end
end CoefficientwiseRigidity
