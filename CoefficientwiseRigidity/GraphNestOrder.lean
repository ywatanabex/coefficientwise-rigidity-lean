import CoefficientwiseRigidity.ChordalNestOrder

/-! Original finite bipartite graphs supply actual root-last neighbourhood orders. -/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V}

def columnSet (b : Bipartition G) : Finset V := univ.filter (fun v => b.side v = false)

def rowNeighborhood (b : Bipartition G) (u : V) : Finset V :=
  (columnSet b).filter (fun v => G.Adj u v)

def neighborhoodFamily (b : Bipartition G) : Finset (Finset V) :=
  (univ.filter (fun u => b.side u = true)).image (rowNeighborhood b)

theorem neighborhoodFamily_supported (b : Bipartition G) :
    FamilySupported (columnSet b) (neighborhoodFamily b) := by
  intro E hE
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hE
  exact Finset.filter_subset _ _

/-- Distinct neighbourhood rows get distinct original representatives. Repeated
or empty rows cause no loss in the exact adjacency identity below. -/
def rowRepresentative (b : Bipartition G) (E : neighborhoodFamily b) : V :=
  Classical.choose (Finset.mem_image.mp E.property)

theorem rowRepresentative_side (b : Bipartition G) (E : neighborhoodFamily b) :
    b.side (rowRepresentative b E) = true :=
  (Finset.mem_filter.mp (Classical.choose_spec (Finset.mem_image.mp E.property)).1).2

theorem rowRepresentative_row (b : Bipartition G) (E : neighborhoodFamily b) :
    rowNeighborhood b (rowRepresentative b E) = E.val :=
  (Classical.choose_spec (Finset.mem_image.mp E.property)).2

def neighborhoodEmbedding (b : Bipartition G) :
    (neighborhoodFamily b ⊕ columnSet b) ↪ V where
  toFun := Sum.elim (rowRepresentative b) Subtype.val
  inj' := by
    intro a c hac
    have hcol (x : columnSet b) : b.side x.val = false := (Finset.mem_filter.mp x.property).2
    cases a with
    | inl E =>
      cases c with
      | inl F =>
        apply congrArg Sum.inl
        apply Subtype.ext
        rw [← rowRepresentative_row b E,← rowRepresentative_row b F]
        exact congrArg (rowNeighborhood b) hac
      | inr x =>
        have hh := congrArg b.side hac
        simp only [Sum.elim_inl,Sum.elim_inr,rowRepresentative_side,hcol] at hh
        cases hh
    | inr x =>
      cases c with
      | inl E =>
        have hh := congrArg b.side hac
        simp only [Sum.elim_inl,Sum.elim_inr,rowRepresentative_side,hcol] at hh
        cases hh
      | inr y => exact congrArg Sum.inr (Subtype.ext hac)

theorem neighborhoodEmbedding_graph (b : Bipartition G) :
    G.comap (neighborhoodEmbedding b) = incidenceGraph (columnSet b) (neighborhoodFamily b) := by
  ext a c
  have hcol (x : columnSet b) : b.side x.val = false := (Finset.mem_filter.mp x.property).2
  have hmem (E : neighborhoodFamily b) (x : columnSet b) :
      G.Adj (rowRepresentative b E) x.val ↔ x.val ∈ E.val := by
    rw [← rowRepresentative_row b E]
    simp only [rowNeighborhood,Finset.mem_filter,x.property,true_and]
  cases a with
  | inl E =>
    cases c with
    | inl F =>
      change G.Adj (rowRepresentative b E) (rowRepresentative b F) ↔ False
      simp only [iff_false]
      intro he
      exact b.opposite he (by rw [rowRepresentative_side,rowRepresentative_side])
    | inr x => exact hmem E x
  | inr x =>
    cases c with
    | inl E => exact (G.adj_comm _ _).trans (hmem E x)
    | inr y =>
      change G.Adj x.val y.val ↔ False
      simp only [iff_false]
      intro he
      exact b.opposite he (by rw [hcol,hcol])

theorem neighborhood_incidence_chordal (b : Bipartition G) (hg : ChordalBipartite G) :
    ChordalBipartite (incidenceGraph (columnSet b) (neighborhoodFamily b)) := by
  have h := chordalBipartite_comap hg (neighborhoodEmbedding b)
  rwa [neighborhoodEmbedding_graph] at h

/-- Every finite chordal-bipartite graph has a root-last order of its actual
right-neighbourhood family. The colouring and prescribed right root are explicit. -/
theorem graph_root_last_nest_order (b : Bipartition G) (hg : ChordalBipartite G)
    {root : V} (hr : b.side root = false) :
    ∃ L : List V, NestOrder (neighborhoodFamily b) L ∧ L.Nodup ∧
      L.toFinset = columnSet b ∧ L.getLast? = some root :=
  incidence_root_last_order (neighborhood_incidence_chordal b hg)
    (neighborhoodFamily_supported b) (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)

theorem graph_nest_order (b : Bipartition G) (hg : ChordalBipartite G) :
    ∃ L : List V, NestOrder (neighborhoodFamily b) L ∧ L.Nodup ∧ L.toFinset = columnSet b :=
  incidence_nest_order (neighborhood_incidence_chordal b hg) (neighborhoodFamily_supported b)

end
end CoefficientwiseRigidity.Structure
