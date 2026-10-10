import CoefficientwiseRigidity.ChordalSeparators

/-! Vertex induction constructs simplicial vertices outside any proper clique. -/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V}

def SimplicialOn (G : SimpleGraph V) (U : Finset V) (x : V) : Prop :=
  ∀ y ∈ U, ∀ z ∈ U, G.Adj x y → G.Adj x z → y ≠ z → G.Adj y z

theorem componentIn_neighbor {U S : Finset V} {r v w : V}
    (hv : v ∈ componentIn G (U \ S) r) (hw : w ∈ U) (hvw : G.Adj v w) :
    w ∈ componentIn G (U \ S) r ∪ S := by
  by_cases hwS : w ∈ S
  · exact Finset.mem_union_right _ hwS
  · have hwT : w ∈ U \ S := Finset.mem_sdiff.mpr ⟨hw,hwS⟩
    exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨hwT,((Finset.mem_filter.mp hv).2).step hvw hwT⟩)

private theorem simplicial_outside_aux (n : ℕ) (hg : ChordalGraph G) :
    ∀ U : Finset V, U.card = n → ∀ K : Finset V, K ⊆ U → CliqueOn G K →
      (U \ K).Nonempty → ∃ v ∈ U, v ∉ K ∧ SimplicialOn G U v := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U hcard K hKU hK hnonempty
    by_cases hcomplete : CliqueOn G U
    · obtain ⟨v,hv⟩ := hnonempty
      exact ⟨v,(Finset.mem_sdiff.mp hv).1,(Finset.mem_sdiff.mp hv).2,
        fun y hy z hz _ _ hyz => hcomplete y hy z hz hyz⟩
    · have hn : ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ ¬ G.Adj x y := by
        by_contra hn
        apply hcomplete
        intro x hx y hy hxy
        by_contra hnadj
        exact hn ⟨x,hx,y,hy,hxy,hnadj⟩
      obtain ⟨x,hx,y,hy,hxy,hnadj⟩ := hn
      obtain ⟨S,hS⟩ := exists_minimalSeparator hx hy hxy hnadj
      have hsclique := hS.clique hg
      have side : ∃ r t, MinimalSeparator G U S r t ∧
          ∀ v ∈ componentIn G (U \ S) r, v ∉ K := by
        by_cases hxK : ∀ v ∈ componentIn G (U \ S) x, v ∉ K
        · exact ⟨x,y,hS,hxK⟩
        · push_neg at hxK
          obtain ⟨u,hu,huK⟩ := hxK
          refine ⟨y,x,hS.symm,?_⟩
          intro v hv hvK
          have hsep := componentIn_separated hS.1.2.2.2 hu hv
          exact hsep.2 (hK u huK v hvK hsep.1)
      obtain ⟨r,t,hrt,hside⟩ := side
      let C := componentIn G (U \ S) r
      let W := C ∪ S
      have hCU : C ⊆ U \ S := componentIn_subset
      have hWU : W ⊆ U := Finset.union_subset (hCU.trans Finset.sdiff_subset) hrt.1.1
      have htW : t ∉ W := by
        intro ht
        rcases Finset.mem_union.mp ht with ht | ht
        · exact hrt.1.2.2.2 (Finset.mem_filter.mp ht).2
        · exact (Finset.mem_sdiff.mp hrt.1.2.2.1).2 ht
      have hlt : W.card < n := by
        rw [← hcard]
        apply Finset.card_lt_card
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hWU,?_⟩
        intro he
        exact htW (he.symm ▸ (Finset.mem_sdiff.mp hrt.1.2.2.1).1)
      have hrC : r ∈ C := mem_componentIn_self hrt.1.2.1
      have hWS : (W \ S).Nonempty := ⟨r,Finset.mem_sdiff.mpr
        ⟨Finset.mem_union_left _ hrC,(Finset.mem_sdiff.mp hrt.1.2.1).2⟩⟩
      obtain ⟨v,hv,hvS,hvsimp⟩ := ih W.card hlt W rfl S
        Finset.subset_union_right hsclique hWS
      have hvC : v ∈ C := (Finset.mem_union.mp hv).resolve_right hvS
      refine ⟨v,hWU hv,hside v hvC,?_⟩
      intro a ha b hb hva hvb hab
      exact hvsimp a (componentIn_neighbor hvC ha hva)
        b (componentIn_neighbor hvC hb hvb) hva hvb hab

/-- Dirac's stronger induction invariant: a finite induced subgraph has a
simplicial vertex outside every proper clique, including the empty clique. -/
theorem ChordalGraph.simplicial_outside (hg : ChordalGraph G) (U K : Finset V)
    (hKU : K ⊆ U) (hK : CliqueOn G K) (hne : (U \ K).Nonempty) :
    ∃ v ∈ U, v ∉ K ∧ SimplicialOn G U v :=
  simplicial_outside_aux U.card hg U rfl K hKU hK hne

/-- Every nonempty finite chordal graph has an actual simplicial vertex. -/
theorem ChordalGraph.exists_simplicial [Fintype V] [Nonempty V] (hg : ChordalGraph G) :
    ∃ v, SimplicialVertex G v := by
  obtain ⟨v,_,_,hv⟩ := hg.simplicial_outside Finset.univ ∅ (by simp)
    (by simp [CliqueOn]) (by simp)
  exact ⟨v,fun y z hy hz hyz => hv y (Finset.mem_univ _) z (Finset.mem_univ _) hy hz hyz⟩

end
end CoefficientwiseRigidity.Structure
