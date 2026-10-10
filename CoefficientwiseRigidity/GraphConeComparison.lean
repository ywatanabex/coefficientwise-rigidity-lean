import CoefficientwiseRigidity.ConeElimination

/-! C3 for the original graph's neighbourhoods, with no supplied order certificate. -/
namespace CoefficientwiseRigidity.Intersections
open Finset Compression Structure
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

/-- Every original left vertex remains a separate row index, even if its
neighbourhood coincides with another row or is empty. -/
abbrev LeftRows (b : Bipartition G) := {u : V // b.side u = true}

def graphRows (b : Bipartition G) : LeftRows b → Finset V := fun u => rowNeighborhood b u.val

theorem family_graphRows (b : Bipartition G) : family (graphRows b) = neighborhoodFamily b := by
  ext E
  simp only [mem_family,neighborhoodFamily,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u.val,u.property,rfl⟩
  · rintro ⟨u,hu,hE⟩
    exact ⟨⟨u,hu⟩,hE⟩

theorem graphRows_supported (b : Bipartition G) : ∀ u, graphRows b u ⊆ columnSet b :=
  fun _ => Finset.filter_subset _ _

omit [Fintype V] in
theorem sumSet_of_list (q : V → ℕ) (U : Finset V) (L : List V)
    (hnd : L.Nodup) (he : L.toFinset = U)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U F Q = sumColumns q L F Q := by
  unfold sumSet
  exact sumColumns_perm q (he ▸ List.toFinset_toList hnd) F Q

/-- Unpinned full-cone comparison for arbitrary incidence gains on the actual
neighbourhoods of the original finite chordal-bipartite graph. -/
theorem graph_cone_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (LeftRows b → ℕ) → ℚ} (hF : ProductCone F) (Q : V → Finset (Fin M)) :
    sumSet q (columnSet b) (fun R => F (ranks (graphRows b) σ R)) Q ≤
      sumSet q (columnSet b) (fun R => F (ranks (graphRows b) (fun _ _ => Equiv.refl _) R)) Q := by
  obtain ⟨L,ho,hnd,he⟩ := graph_nest_order b hg
  rw [sumSet_of_list q _ L hnd he,sumSet_of_list q _ L hnd he]
  apply cone_comparison L [] (by simp) (graphRows b)
  · simpa only [List.append_nil,family_graphRows] using ho
  · simpa using hnd
  · simpa only [List.append_nil,he] using graphRows_supported b
  · exact hF

/-- A prescribed right set is retained throughout the sum. Its cardinality
need not be postulated: the same set is used in both models, including the bases. -/
theorem graph_root_cone_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (root : V) (hr : b.side root = false)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (LeftRows b → ℕ) → ℚ} (hF : ProductCone F) (Q : V → Finset (Fin M)) :
    sumSet q ((columnSet b).erase root) (fun R => F (ranks (graphRows b) σ R)) Q ≤
      sumSet q ((columnSet b).erase root) (fun R => F (ranks (graphRows b) (fun _ _ => Equiv.refl _) R)) Q := by
  obtain ⟨O,ho,hnd,he,hlast⟩ := graph_root_last_nest_order b hg hr
  obtain ⟨L,rfl⟩ := List.getLast?_eq_some_iff.mp hlast
  have hL := (List.nodup_append.mp hnd).1
  have hroot : root ∉ L := by
    intro hm
    exact (List.nodup_append.mp hnd).2.2 hm (by simp)
  have hset : L.toFinset = (columnSet b).erase root := by
    rw [← he]
    ext x
    simp only [Finset.mem_erase,List.mem_toFinset,List.mem_append,List.mem_singleton]
    constructor
    · intro hx
      exact ⟨fun h => hroot (h ▸ hx),Or.inl hx⟩
    · rintro ⟨hne,hx | hx⟩
      · exact hx
      · exact (hne hx).elim
  rw [sumSet_of_list q _ L hL hset,sumSet_of_list q _ L hL hset]
  apply cone_comparison L [root] (by simp) (graphRows b)
  · simpa only [family_graphRows] using ho
  · exact hnd
  · simpa only [he] using graphRows_supported b
  · exact hF

def finiteRanks {I : Type*} (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) : I → Fin (M + 1) := fun i => cardRank (row (J i) (σ i) Q)

omit [Fintype V] in
theorem finiteExtension_ranks {I : Type*} (F : (I → Fin (M + 1)) → ℚ)
    (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) :
    finiteExtension F (ranks J σ Q) = F (finiteRanks J σ Q) := by
  change (F fun i => clampRank M (row (J i) (σ i) Q).card) = F (fun i => cardRank (row (J i) (σ i) Q))
  simp only [clampRank_card]

theorem graph_finite_cone_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (LeftRows b → Fin (M + 1)) → ℚ} (hF : ProductCone F) (Q : V → Finset (Fin M)) :
    sumSet q (columnSet b) (fun R => F (finiteRanks (graphRows b) σ R)) Q ≤
      sumSet q (columnSet b) (fun R => F (finiteRanks (graphRows b) (fun _ _ => Equiv.refl _) R)) Q := by
  have hE : ProductCone (finiteExtension F) := hF.extend_finite
  simpa only [finiteExtension_ranks] using graph_cone_comparison b hg σ q hE Q

theorem graph_root_finite_cone_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (root : V) (hr : b.side root = false)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (LeftRows b → Fin (M + 1)) → ℚ} (hF : ProductCone F) (Q : V → Finset (Fin M)) :
    sumSet q ((columnSet b).erase root) (fun R => F (finiteRanks (graphRows b) σ R)) Q ≤
      sumSet q ((columnSet b).erase root) (fun R => F (finiteRanks (graphRows b) (fun _ _ => Equiv.refl _) R)) Q := by
  have hE : ProductCone (finiteExtension F) := hF.extend_finite
  simpa only [finiteExtension_ranks] using graph_root_cone_comparison b hg root hr σ q hE Q

end
end CoefficientwiseRigidity.Intersections
