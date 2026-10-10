import CoefficientwiseRigidity.ChordalSimplicial
import CoefficientwiseRigidity.NestOrder

/-! Discharge hereditary alpha leaves from the original incidence hypothesis. -/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V] {U : Finset V} {H : Finset (Finset V)}

/-- B1 and B2 now construct the formerly missing alpha leaf. -/
theorem incidence_has_alpha (hg : ChordalBipartite (incidenceGraph U H))
    (hs : FamilySupported U H) (hn : U.Nonempty) : HasAlpha U H := by
  obtain ⟨u,hu⟩ := hn
  letI : Nonempty U := ⟨⟨u,hu⟩⟩
  obtain ⟨x,hx⟩ := (primal_chordal hg).exists_simplicial
  exact ⟨x.val,x.property,primal_simplicial_alpha hg hs x hx⟩

/-- Every nonempty subtrace has an alpha leaf. No leaf premise is assumed. -/
theorem incidence_hereditary_alpha (hg : ChordalBipartite (incidenceGraph U H)) :
    HereditaryAlpha U H := by
  intro W hW hn K hK
  exact incidence_has_alpha (incidence_chordal_subtrace hg hW hK)
    (fun E hE => trace_supported H W E (hK hE)) hn

/-- An actual root-last nest order from the unchanged incidence cycle condition. -/
theorem incidence_root_last_order (hg : ChordalBipartite (incidenceGraph U H))
    (hs : FamilySupported U H) {root : V} (hr : root ∈ U) :
    ∃ L : List V, NestOrder H L ∧ L.Nodup ∧ L.toFinset = U ∧ L.getLast? = some root :=
  exists_root_last_nest_order hs (incidence_hereditary_alpha hg) hr

theorem incidence_nest_order (hg : ChordalBipartite (incidenceGraph U H))
    (hs : FamilySupported U H) :
    ∃ L : List V, NestOrder H L ∧ L.Nodup ∧ L.toFinset = U :=
  exists_nest_order hs (incidence_hereditary_alpha hg)

end
end CoefficientwiseRigidity.Structure
