import CoefficientwiseRigidity.BipartiteAssignments

/-! Saturate one side using the maximum of the actual neighbour occupations. -/
namespace CoefficientwiseRigidity.Saturation
open Finset Structure Intersections
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

def capacity (b : Bipartition G) (M : ℕ) (a : V → ℕ) (u : V) : ℕ :=
  M - (rowNeighborhood b u).sup a

def occupation (b : Bipartition G) (M : ℕ) (a : V → ℕ) (v : V) : ℕ :=
  if b.side v = true then capacity b M a v else a v

theorem neighbor_mem (b : Bipartition G) {u v : V} (hu : b.side u = true)
    (he : G.Adj u v) : v ∈ rowNeighborhood b u := by
  have hv : b.side v = false := by
    have hn := b.opposite he
    rw [hu] at hn
    cases h : b.side v <;> simp_all
  simp [rowNeighborhood,columnSet,hv,he]

theorem rowNeighborhood_eq_neighbors (b : Bipartition G) {u : V}
    (hu : b.side u = true) : rowNeighborhood b u = univ.filter (G.Adj u) := by
  ext v
  constructor
  · intro hv; exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hv).2⟩
  · intro hv; exact neighbor_mem b hu (mem_filter.mp hv).2

theorem capacity_le (b : Bipartition G) (a : V → ℕ) (u : V) : capacity b M a u ≤ M :=
  Nat.sub_le _ _

theorem le_capacity (b : Bipartition G) {a : V → ℕ} (ha : Feasible G M a) (u : V) :
    a u ≤ capacity b M a u := by
  have hs : (rowNeighborhood b u).sup a ≤ M - a u := by
    apply Finset.sup_le
    intro v hv
    have he := (mem_filter.mp hv).2
    have hh := ha.2 u v he
    omega
  unfold capacity
  have hu := ha.1 u
  omega

theorem capacity_add_neighbor (b : Bipartition G) {a : V → ℕ}
    (ha : Feasible G M a) {u v : V} (hu : b.side u = true) (he : G.Adj u v) :
    capacity b M a u + a v ≤ M := by
  have hv := Finset.le_sup (f := a) (neighbor_mem b hu he)
  have hs : (rowNeighborhood b u).sup a ≤ M :=
    Finset.sup_le (fun v _ => ha.1 v)
  unfold capacity
  omega

theorem occupation_column (b : Bipartition G) (a : V → ℕ) {v : V}
    (hv : v ∈ columnSet b) : occupation b M a v = a v := by
  have h := (mem_filter.mp hv).2
  simp [occupation,h]

theorem occupation_feasible (b : Bipartition G) {a : V → ℕ} (ha : Feasible G M a) :
    Feasible G M (occupation b M a) := by
  constructor
  · intro v
    unfold occupation
    split_ifs
    · exact capacity_le b a v
    · exact ha.1 v
  · intro u v he
    have hn := b.opposite he
    cases hu : b.side u with
    | false =>
      have hv : b.side v = true := by cases h : b.side v <;> simp_all
      simpa [occupation,hu,hv,Nat.add_comm] using capacity_add_neighbor b ha hv (G.symm he)
    | true =>
      have hv : b.side v = false := by cases h : b.side v <;> simp_all
      simpa [occupation,hu,hv] using capacity_add_neighbor b ha hu he

theorem occupation_positive (b : Bipartition G) {a : V → ℕ}
    (ha : Feasible G M a) (hp : Positive a) : Positive (occupation b M a) := by
  intro v
  unfold occupation
  split_ifs
  · exact (hp v).trans_le (le_capacity b ha v)
  · exact hp v

theorem capacity_lt_of_neighbor (b : Bipartition G) {a : V → ℕ}
    (hp : Positive a) {u v : V} (hu : b.side u = true) (he : G.Adj u v) (hM : 0 < M) :
    capacity b M a u < M := by
  have hv := Finset.le_sup (f := a) (neighbor_mem b hu he)
  have hvp := hp v
  unfold capacity
  omega

theorem rank_le_capacity (b : Bipartition G) (a : V → ℕ) (ha : ∀ v, a v ≤ M)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (Q S : V → Finset (Fin M))
    (hs : ValidOn (columnRanks M a) (columnSet b) Q S) (u : LeftRows b) :
    ranks (graphRows b) σ S u ≤ capacity b M a u.val := by
  have hd : (row (graphRows b u) (σ u) S).card ≤ M := by
    simpa using Finset.card_le_univ (row (graphRows b u) (σ u) S)
  have hb : (rowNeighborhood b u.val).sup a ≤ M - (row (graphRows b u) (σ u) S).card := by
    apply Finset.sup_le
    intro v hv
    have hsub : row (graphRows b u) (σ u) S ⊆ (S v).map (σ u v).toEmbedding := by
      intro x hx
      exact (mem_row _ _ _ _).mp hx v hv
    have hc := Finset.card_le_card hsub
    rw [Finset.card_map,hs.1 v ((Finset.mem_filter.mp hv).1)] at hc
    change (row (graphRows b u) (σ u) S).card ≤ M - a v at hc
    have hav := ha v
    omega
  change (row (graphRows b u) (σ u) S).card ≤ M - (rowNeighborhood b u.val).sup a
  omega

end
end CoefficientwiseRigidity.Saturation
