import CoefficientwiseRigidity.AtomFibres
import CoefficientwiseRigidity.CoefficientInsertion

/-! Indexed empty, root and actual-edge pins, with literal configuration counts. -/
namespace CoefficientwiseRigidity
open scoped Classical BigOperators
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

/-- An index set consisting of no vertex, one vertex, or the endpoints of an actual edge. -/
def SmallBoundary {I : Type} (G : SimpleGraph V) (f : I → V) : Prop :=
  IsEmpty I ∨ (∃ i : I, ∀ j, j = i) ∨
    ∃ i j, G.Adj (f i) (f j) ∧ ∀ k, k = i ∨ k = j

def PinAdmissible {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) : Prop :=
  (∀ i, (A i).card = a (f i)) ∧
    ∀ i j, G.Adj (f i) (f j) → Disjoint ((A i).map (X.transport (f i) (f j)).toEmbedding) (A j)

def pinnedCount {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) : ℕ :=
  Fintype.card {C : Configuration X a // ∀ i, C.val (f i) = A i}

def BoundaryComparison (X : Cover G M) (a : V → ℕ) : Prop :=
  ∀ (I : Type) (f : I → V), SmallBoundary G f → ∀ A, PinAdmissible X a f A →
    ∀ O : Configuration (trivialCover G M) a,
      pinnedCount X a f A ≤ pinnedCount (trivialCover G M) a f (fun i => O.val (f i))

omit [Fintype V] [DecidableEq V] in
theorem configuration_pin_admissible {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (C : Configuration X a) : PinAdmissible X a f (fun i => C.val (f i)) := by
  refine ⟨fun i => C.property.1 _, ?_⟩
  intro i j h
  exact (Gluing.coverEdgePin X a (f i) (f j) h C).property.2.2

theorem pinnedCount_empty {I : Type} [IsEmpty I] (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) : pinnedCount X a f A = coefficient X a := by
  apply Fintype.card_congr
  exact { toFun := fun C => C.val
          invFun := fun C => ⟨C, fun i => isEmptyElim i⟩
          left_inv := fun C => Subtype.ext rfl
          right_inv := fun _ => rfl }

theorem pinnedCount_root {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) (i : I) (hi : ∀ j, j = i) :
    pinnedCount X a f A = rootFibre X a (f i) (A i) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro C
  exact ⟨fun h => h i, fun h j => by simpa [hi j] using h⟩

theorem pinnedCount_edge {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) (i j : I) (hij : ∀ k, k = i ∨ k = j) :
    pinnedCount X a f A = edgeFibre X a (f i) (f j) (A i) (A j) := by
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro C
  constructor
  · intro h; exact ⟨h i, h j⟩
  · rintro ⟨hi, hj⟩ k
    rcases hij k with rfl | rfl
    · exact hi
    · exact hj

theorem ordinary_pinned_constant {I : Type} (a : V → ℕ) (f : I → V)
    (hf : SmallBoundary G f) (A : I → Finset (Fin M))
    (hA : PinAdmissible (trivialCover G M) a f A)
    (O : Configuration (trivialCover G M) a) :
    pinnedCount (trivialCover G M) a f A =
      pinnedCount (trivialCover G M) a f (fun i => O.val (f i)) := by
  rcases hf with h | ⟨i, hi⟩ | ⟨i, j, he, hij⟩
  · letI := h
    rw [pinnedCount_empty, pinnedCount_empty]
  · rw [pinnedCount_root _ _ _ _ i hi, pinnedCount_root _ _ _ _ i hi]
    exact Gluing.ordinary_rootFibre_eq a _ _ _ ((hA.1 i).trans (O.property.1 _).symm)
  · rw [pinnedCount_edge _ _ _ _ i j hij, pinnedCount_edge _ _ _ _ i j hij]
    exact Gluing.ordinary_edgeFibre_eq a _ _ _ _ _ _
      ((hA.1 i).trans (O.property.1 _).symm) ((hA.1 j).trans (O.property.1 _).symm)
      (by simpa [trivialCover] using hA.2 i j he)
      (by simpa [trivialCover] using (configuration_pin_admissible _ a f O).2 i j he)

theorem atom_boundary_comparison (b : Bipartition G) (hg : StructuralAtom G)
    (X : Cover G M) (a : V → ℕ) : BoundaryComparison X a := by
  intro I f hf A hA O
  rcases hf with h | ⟨i, hi⟩ | ⟨i, j, he, hij⟩
  · letI := h
    rw [pinnedCount_empty, pinnedCount_empty]
    rcases hg with hw | hc
    · exact coefficient_le_of_treewidth b X a hw
    · exact coefficient_le_of_chordalBipartite X a hc
  · rw [pinnedCount_root _ _ _ _ i hi, pinnedCount_root _ _ _ _ i hi]
    have hb := atom_root_fibre_bound b hg X a (f i) (A i) (hA.1 i)
    rw [← Gluing.ordinary_root_normalization a (f i) (O.val (f i)) (O.property.1 _)] at hb
    exact (mul_le_mul_left (Nat.choose_pos ((feasible_of_admissible _ _ O.property).1 (f i)))).mp hb
  · rw [pinnedCount_edge _ _ _ _ i j hij, pinnedCount_edge _ _ _ _ i j hij]
    have ho := (configuration_pin_admissible _ a f O).2 i j he
    have hd : Disjoint (O.val (f i)) (O.val (f j)) := by simpa [trivialCover] using ho
    have hb := atom_edge_fibre_bound b hg X a (f i) (f j) he (A i) (A j)
      (hA.1 i) (hA.1 j) (hA.2 i j he)
    rw [← Gluing.ordinary_edge_normalization a (f i) (f j) he _ _
      (O.property.1 _) (O.property.1 _) hd] at hb
    have ha := feasible_of_admissible _ _ O.property
    have hp : 0 < M.choose (a (f i)) * (M - a (f i)).choose (a (f j)) :=
      Nat.mul_pos (Nat.choose_pos (ha.1 _)) (Nat.choose_pos (by have := ha.2 _ _ he; omega))
    exact (mul_le_mul_left hp).mp hb

theorem BoundaryComparison.coefficient_le (X : Cover G M) (a : V → ℕ)
    (h : BoundaryComparison X a) (O : Configuration (trivialCover G M) a) :
    coefficient X a ≤ ordinary G M a := by
  have he := h Empty Empty.elim (Or.inl inferInstance) Empty.elim
    ⟨fun i => isEmptyElim i, fun i => isEmptyElim i⟩ O
  simpa only [pinnedCount_empty] using he

/-- Insertion preserves every prescribed pin, even one with a larger boundary. -/
theorem pinnedCount_le_inserted {I : Type} (b : Bipartition G) (a : V → ℕ)
    (f : I → V) (O : Configuration (trivialCover G M) a) :
    pinnedCount (trivialCover G M) a f (fun i => O.val (f i)) ≤
      pinnedCount (trivialCover G (M + 2)) (fun v => a v + 1) f
        (fun i => (insertConfiguration b a O).val (f i)) := by
  let F : {C : Configuration (trivialCover G M) a // ∀ i, C.val (f i) = O.val (f i)} →
      {D : Configuration (trivialCover G (M + 2)) (fun v => a v + 1) //
        ∀ i, D.val (f i) = (insertConfiguration b a O).val (f i)} := fun C =>
    ⟨insertConfiguration b a C.val, by
      intro i
      change ((Kernel.liftSet (C.val.val (f i)) (b.side (f i))).map _) = _
      rw [C.property i]
      rfl⟩
  exact Fintype.card_le_of_injective F (fun C D he =>
    Subtype.ext (insertConfiguration_injective b a (congrArg Subtype.val he)))

end
end CoefficientwiseRigidity
