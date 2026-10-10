import CoefficientwiseRigidity.GraphConeComparison
import CoefficientwiseRigidity.ColumnAssignments

/-! Actual cover transports and binomial completion counts for fixed columns. -/
namespace CoefficientwiseRigidity.Intersections
open Finset Compression Structure
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

def coverGains (b : Bipartition G) (X : Cover G M) : LeftRows b → V → Equiv.Perm (Fin M) :=
  fun u v => (X.transport u.val v).symm

theorem mem_cover_row (b : Bipartition G) (X : Cover G M) (u : LeftRows b)
    (Q : V → Finset (Fin M)) (x : Fin M) :
    x ∈ row (graphRows b u) (coverGains b X u) Q ↔
      ∀ v, G.Adj u.val v → X.transport u.val v x ∈ Q v := by
  rw [mem_row]
  constructor
  · intro h v he
    have hv : b.side v = false := by
      have hn := b.opposite he
      rw [u.property] at hn
      cases h : b.side v <;> simp_all
    have hh := h v (by simp [graphRows,rowNeighborhood,columnSet,hv,he])
    simpa [coverGains,Finset.mem_map_equiv] using hh
  · intro h v hv
    have he : G.Adj u.val v := (Finset.mem_filter.mp hv).2
    simpa [coverGains,Finset.mem_map_equiv] using h v he

def binomialCost {I : Type*} [Fintype I] (a : I → ℕ) (d : I → ℕ) : ℚ :=
  ∏ i, ((d i).choose (a i) : ℚ)

theorem binomialCost_cone {I : Type*} [Fintype I] (a : I → ℕ) : ProductCone (binomialCost a) := by
  unfold binomialCost
  refine ProductCone.prod (I := I) (A := ℕ) (fun i n => (n.choose (a i) : ℚ)) ?_ ?_
  · intro i n; exact Nat.cast_nonneg _
  · intro i n m h
    exact Nat.cast_le.mpr (Nat.choose_le_choose (a i) h)

/-- These are actual left subsets, independently chosen inside the gained
available sets, with every original left vertex represented once. -/
abbrev RowCompletions (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (Q : V → Finset (Fin M)) :=
  ∀ u : LeftRows b, {A : Finset (Fin M) // A ⊆ row (graphRows b u) (coverGains b X u) Q ∧ A.card = a u.val}

omit [Fintype V] in
theorem card_subset_rank (D : Finset (Fin M)) (k : ℕ) :
    Fintype.card {A : Finset (Fin M) // A ⊆ D ∧ A.card = k} = D.card.choose k := by
  rw [Fintype.card_subtype]
  have he : univ.filter (fun A : Finset (Fin M) => A ⊆ D ∧ A.card = k) = D.powersetCard k := by
    ext A
    simp [Finset.mem_powersetCard]
  rw [he,Finset.card_powersetCard]

theorem card_rowCompletions [DecidableEq V] (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (Q : V → Finset (Fin M)) :
    (Fintype.card (RowCompletions b X a Q) : ℚ) =
      binomialCost (fun u : LeftRows b => a u.val) (ranks (graphRows b) (coverGains b X) Q) := by
  simp only [RowCompletions,Fintype.card_pi,card_subset_rank,Nat.cast_prod,binomialCost,ranks]

theorem cover_binomial_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a q : V → ℕ) (Q : V → Finset (Fin M)) :
    sumSet q (columnSet b) (fun R => (Fintype.card (RowCompletions b X a R) : ℚ)) Q ≤
      sumSet q (columnSet b) (fun R => (Fintype.card (RowCompletions b (trivialCover G M) a R) : ℚ)) Q := by
  simp only [card_rowCompletions]
  exact graph_cone_comparison b hg (coverGains b X) q (binomialCost_cone _) Q

theorem cover_root_binomial_comparison (b : Bipartition G) (hg : ChordalBipartite G)
    (root : V) (hr : b.side root = false) (X : Cover G M) (a q : V → ℕ) (Q : V → Finset (Fin M)) :
    sumSet q ((columnSet b).erase root) (fun R => (Fintype.card (RowCompletions b X a R) : ℚ)) Q ≤
      sumSet q ((columnSet b).erase root) (fun R => (Fintype.card (RowCompletions b (trivialCover G M) a R) : ℚ)) Q := by
  simp only [card_rowCompletions]
  exact graph_root_cone_comparison b hg root hr (coverGains b X) q (binomialCost_cone _) Q

end
end CoefficientwiseRigidity.Intersections
