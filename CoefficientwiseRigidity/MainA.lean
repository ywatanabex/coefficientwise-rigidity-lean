import CoefficientwiseRigidity.ChordalRigidity
import CoefficientwiseRigidity.CoefficientBoundary

/-! Both structural branches of the unchanged Main A, on the exact positive active support. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

theorem coefficient_eq_iff_activeFlat_of_chordalBipartite (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (ha : Feasible G M a) (hg : ChordalBipartite (supportGraph G a)) :
    coefficient X a = ordinary G M a ↔ ActiveFlat X a := by
  let b' : Bipartition (supportGraph G a) :=
    ⟨fun v => b.side v.val,fun he => b.opposite he⟩
  have ha' : Feasible (supportGraph G a) M (fun v => a v.val) :=
    ⟨fun v => ha.1 v.val,fun u v he => ha.2 u.val v.val he⟩
  rw [coefficient_support_eq X a,ordinary_support_eq G M a,activeFlat_iff_support_flat]
  exact coefficient_eq_iff_flat_of_positive_chordalBipartite b' (supportCover X a)
    (fun v => a v.val) ha' (fun v => v.property) hg

theorem mainA_of_chordalBipartite (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : Feasible G M a) (hg : ChordalBipartite (supportGraph G a)) :
    coefficient X a ≤ ordinary G M a ∧
      (coefficient X a = ordinary G M a ↔ ActiveFlat X a) :=
  ⟨coefficient_le_of_active_chordalBipartite b X a hg,
    coefficient_eq_iff_activeFlat_of_chordalBipartite b X a ha hg⟩

/-- The original Main A proposition, with both structural alternatives and every boundary case. -/
theorem paperMainA (b : Bipartition G) : MainA G := by
  intro M _ X a ha hs
  rcases hs with hw | hg
  · exact mainA_of_treewidth b M X a ha hw
  · exact mainA_of_chordalBipartite b X a ha hg

end
end CoefficientwiseRigidity
