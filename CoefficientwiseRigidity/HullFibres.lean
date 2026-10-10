import CoefficientwiseRigidity.HullComparison

/-! The unchanged Main C fibre inequalities on every finite legal-seam construction. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

omit [Fintype V] in
theorem SmallBoundary.of_shape {S : Finset V} (hs : Replica.BoundaryShape G S) :
    SmallBoundary G (fun v : (↑S : Set V) => v.val) := by
  rcases hs with hs | ⟨u, hs⟩ | ⟨u, v, hs, he⟩
  · exact Or.inl ⟨fun v => by have := v.property; simp [hs] at this⟩
  · refine Or.inr (Or.inl ⟨⟨u, by simp [hs]⟩, ?_⟩)
    intro v
    exact Subtype.ext (by simpa [hs] using v.property)
  · refine Or.inr (Or.inr ⟨⟨u, by simp [hs]⟩, ⟨v, by simp [hs]⟩, he, ?_⟩)
    intro w
    have hw : w.val = u ∨ w.val = v := by simpa [hs] using w.property
    exact hw.imp (fun h => Subtype.ext h) (fun h => Subtype.ext h)

theorem card_boundary_fibre_eq_pinned (X : Cover G M) (a : V → ℕ) (S : Finset V)
    (c : Replica.BoundaryConfiguration X a S) :
    Fintype.card (Replica.Fibre X a S c) = pinnedCount X a (fun v : (↑S : Set V) => v.val) c.val := by
  simp only [pinnedCount, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro C
  exact ⟨fun h v => congrFun (congrArg Subtype.val h) v, fun h => Subtype.ext (funext h)⟩

theorem BoundaryComparison.boundary_fibre_bound (b : Bipartition G)
    (X : Cover G M) (a : V → ℕ) (hc : BoundaryComparison X a)
    {S : Finset V} (hs : Replica.BoundaryShape G S) (c : Replica.BoundaryConfiguration X a S) :
    Fintype.card (Replica.BoundaryConfiguration X a S) * Fintype.card (Replica.Fibre X a S c) ≤
      ordinary G M a := by
  by_cases ha : Feasible G M a
  · let O : Configuration (trivialCover G M) a := ⟨nestedAssignment b M a, nestedAssignment_admissible b a ha⟩
    let c₀ := Replica.restriction (trivialCover G M) a S O
    have hp : PinAdmissible X a (fun v : (↑S : Set V) => v.val) c.val := by
      refine ⟨c.property.1, ?_⟩
      intro u v he
      exact (Gluing.coverEdgePin (restrictCover X S G le_rfl) (fun w => a w.val) u v he c).property.2.2
    have h := hc _ _ (SmallBoundary.of_shape hs) _ hp O
    change pinnedCount X a (fun v : (↑S : Set V) => v.val) c.val ≤
      pinnedCount (trivialCover G M) a (fun v : (↑S : Set V) => v.val) c₀.val at h
    rw [← card_boundary_fibre_eq_pinned, ← card_boundary_fibre_eq_pinned] at h
    calc
      _ ≤ Fintype.card (Replica.BoundaryConfiguration X a S) *
          Fintype.card (Replica.Fibre (trivialCover G M) a S c₀) := Nat.mul_le_mul_left _ h
      _ = ordinary G M a := by
        rw [Replica.boundary_card_eq X a hs]
        exact Replica.ordinary_boundary_normalization a hs c₀
  · have hz := coefficient_zero_of_not_feasible X a ha
    have hle : Fintype.card (Replica.Fibre X a S c) ≤ coefficient X a :=
      Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    rw [hz] at hle
    rw [Nat.eq_zero_of_le_zero hle, mul_zero]
    exact Nat.zero_le _

theorem BoundaryComparison.root_bound (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (hc : BoundaryComparison X a) (u : V) (A : Finset (Fin M)) (hA : A.card = a u) :
    M.choose (a u) * rootFibre X a u A ≤ ordinary G M a := by
  let c := (Replica.rootBoundaryEquiv X a u).symm ⟨A, hA⟩
  have h := hc.boundary_fibre_bound b X a (S := {u}) (Or.inr (Or.inl ⟨u, rfl⟩)) c
  rw [Replica.card_rootBoundary, Replica.card_rootBoundaryFibre] at h
  simpa [c] using h

theorem BoundaryComparison.edge_bound (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (hc : BoundaryComparison X a) (u v : V) (he : G.Adj u v)
    (A B : Finset (Fin M)) (hA : A.card = a u) (hB : B.card = a v)
    (hd : Disjoint (A.map (X.transport u v).toEmbedding) B) :
    (M.choose (a u) * (M - a u).choose (a v)) * edgeFibre X a u v A B ≤ ordinary G M a := by
  let c := (Replica.edgeBoundaryEquiv X a u v he).symm ⟨(A, B), hA, hB, hd⟩
  have h := hc.boundary_fibre_bound b X a (S := {u, v}) (Or.inr (Or.inr ⟨u, v, rfl, he⟩)) c
  rw [Replica.card_edgeBoundary X a u v he, Replica.card_edgeBoundaryFibre X a u v he] at h
  simpa [c] using h

/-- An inhabitant of the original, unchanged MainCFibres proposition. -/
theorem paperMainCFibres (b : Bipartition G) : MainCFibres G := by
  intro h M _ X a
  have hc := h.boundary_comparison_univ b X a
  exact ⟨hc.root_bound b X a, fun u v A B he => hc.edge_bound b X a u v he A B⟩

end
end CoefficientwiseRigidity
