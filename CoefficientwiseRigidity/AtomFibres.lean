import CoefficientwiseRigidity.ReplicaBags
import CoefficientwiseRigidity.ReplicaChordal
import CoefficientwiseRigidity.BoundaryPins

/-! Unconditional G1 for both original structural atom classes, on the original fibres. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

theorem atom_boundary_fibre_bound (b : Bipartition G) (hG : StructuralAtom G)
    (X : Cover G M) (a : V → ℕ) {S : Finset V} (hS : Replica.BoundaryShape G S)
    (c : Replica.BoundaryConfiguration X a S) :
    Fintype.card (Replica.BoundaryConfiguration X a S) *
      Fintype.card (Replica.Fibre X a S c) ≤ ordinary G M a := by
  apply Replica.fibre_bound_of_all_copies X a hS
  intro k
  rcases hG with hw | hg
  · exact coefficient_le_of_treewidth (Replica.bipartition b S (Fin k))
      (Replica.cover X S (Fin k)) _ (Replica.treewidth hw hS)
  · exact coefficient_le_of_chordalBipartite (Replica.cover X S (Fin k)) _
      (Replica.chordal hg hS)

theorem atom_root_fibre_bound (b : Bipartition G) (hG : StructuralAtom G)
    (X : Cover G M) (a : V → ℕ) (u : V) (A : Finset (Fin M)) (hA : A.card = a u) :
    M.choose (a u) * rootFibre X a u A ≤ ordinary G M a := by
  let c := (Replica.rootBoundaryEquiv X a u).symm ⟨A,hA⟩
  have h := atom_boundary_fibre_bound b hG X a (S := {u}) (Or.inr (Or.inl ⟨u,rfl⟩)) c
  rw [Replica.card_rootBoundary,Replica.card_rootBoundaryFibre] at h
  simpa [c] using h

theorem atom_edge_fibre_bound (b : Bipartition G) (hG : StructuralAtom G)
    (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (A B : Finset (Fin M)) (hA : A.card = a u) (hB : B.card = a v)
    (hd : Disjoint (A.map (X.transport u v).toEmbedding) B) :
    (M.choose (a u) * (M - a u).choose (a v)) * edgeFibre X a u v A B ≤ ordinary G M a := by
  let c := (Replica.edgeBoundaryEquiv X a u v huv).symm ⟨(A,B),hA,hB,hd⟩
  have h := atom_boundary_fibre_bound b hG X a (S := {u,v})
    (Or.inr (Or.inr ⟨u,v,rfl,huv⟩)) c
  rw [Replica.card_edgeBoundary X a u v huv,Replica.card_edgeBoundaryFibre X a u v huv] at h
  simpa [c] using h

/-- The exact fibre conclusions of Main C for a single structural atom, including all ranks. -/
theorem atom_fibres (b : Bipartition G) (hG : StructuralAtom G) (X : Cover G M) (a : V → ℕ) :
    (∀ u A, A.card = a u → M.choose (a u) * rootFibre X a u A ≤ ordinary G M a) ∧
    (∀ u v A B, G.Adj u v → A.card = a u → B.card = a v →
      Disjoint (A.map (X.transport u v).toEmbedding) B →
      (M.choose (a u) * (M - a u).choose (a v)) * edgeFibre X a u v A B ≤ ordinary G M a) :=
  ⟨atom_root_fibre_bound b hG X a,fun u v A B he => atom_edge_fibre_bound b hG X a u v he A B⟩

end
end CoefficientwiseRigidity
