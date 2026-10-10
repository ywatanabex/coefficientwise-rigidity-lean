import CoefficientwiseRigidity.SeamDominationRight

/-! Boundary comparison along the original StructuralHull constructors. -/
namespace CoefficientwiseRigidity.Gluing
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

omit [Fintype V] in
theorem smallBoundary_child {I : Type} (f : I → (↑(U₁ ∪ U₂) : Set V))
    (hf : SmallBoundary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) f)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂) :
    (∃ h : ∀ i, (f i).val ∈ U₁,
      SmallBoundary (G₁.induce (↑U₁ : Set V)) (fun i => ⟨(f i).val, h i⟩)) ∨
    (∃ h : ∀ i, (f i).val ∈ U₂,
      SmallBoundary (G₂.induce (↑U₂ : Set V)) (fun i => ⟨(f i).val, h i⟩)) := by
  rcases hf with h | ⟨i, hi⟩ | ⟨i, j, he, hij⟩
  · letI := h
    exact Or.inl ⟨fun i => isEmptyElim i, Or.inl h⟩
  · rcases Finset.mem_union.mp (f i).property with h | h
    · exact Or.inl ⟨fun j => by simpa [hi j] using h, Or.inr (Or.inl ⟨i, hi⟩)⟩
    · exact Or.inr ⟨fun j => by simpa [hi j] using h, Or.inr (Or.inl ⟨i, hi⟩)⟩
  · rcases he with he | he
    · obtain ⟨hu, hv⟩ := hU₁ _ _ he
      refine Or.inl ⟨?_, Or.inr (Or.inr ⟨i, j, he, hij⟩)⟩
      intro k
      rcases hij k with rfl | rfl
      · exact hu
      · exact hv
    · obtain ⟨hu, hv⟩ := hU₂ _ _ he
      refine Or.inr ⟨?_, Or.inr (Or.inr ⟨i, j, he, hij⟩)⟩
      intro k
      rcases hij k with rfl | rfl
      · exact hu
      · exact hv

omit [Fintype V] in
theorem boundaryComparison_glue (X : Cover (G₁ ⊔ G₂) M) (a : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₁ : BoundaryComparison (restrictCover X U₁ G₁ le_sup_left) (fun v => a v.val))
    (h₂ : BoundaryComparison (restrictCover X U₂ G₂ le_sup_right) (fun v => a v.val)) :
    BoundaryComparison (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => a v.val) := by
  intro I f hf A hA O
  let O₁ := leftPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
  let O₂ := rightPart (trivialCover (G₁ ⊔ G₂) M) a U₁ U₂ O
  rcases smallBoundary_child f hf hU₁ hU₂ with ⟨h, hsmall⟩ | ⟨h, hsmall⟩
  · let g : I → (↑U₁ : Set V) := fun i => ⟨(f i).val, h i⟩
    have hpin : PinAdmissible (restrictCover X U₁ G₁ le_sup_left)
        (fun v => a v.val) g A :=
      ⟨hA.1, fun i j he => hA.2 i j (Or.inl he)⟩
    have hle := left_predicate_le X a hU₁ hU₂ hs h₂ O₂ (fun C => ∀ i, C.val (g i) = A i)
    have ho := ordinary_left_predicate_eq a hU₁ hU₂ hs O₂
      (fun C => ∀ i, C.val (g i) = O₁.val (g i))
    calc
      _ ≤ seamConstant a U₁ U₂ O₂ * pinnedCount (restrictCover X U₁ G₁ le_sup_left)
          (fun v => a v.val) g A := hle
      _ ≤ seamConstant a U₁ U₂ O₂ * pinnedCount (trivialCover (G₁.induce (↑U₁ : Set V)) M)
          (fun v => a v.val) g (fun i => O₁.val (g i)) := Nat.mul_le_mul_left _ (h₁ I g hsmall A hpin O₁)
      _ = _ := ho.symm
  · let g : I → (↑U₂ : Set V) := fun i => ⟨(f i).val, h i⟩
    have hpin : PinAdmissible (restrictCover X U₂ G₂ le_sup_right)
        (fun v => a v.val) g A :=
      ⟨hA.1, fun i j he => hA.2 i j (Or.inr he)⟩
    have hle := right_predicate_le X a hU₂ hU₁ hs h₁ O₁ (fun C => ∀ i, C.val (g i) = A i)
    have ho := ordinary_right_predicate_eq a hU₂ hU₁ hs O₁
      (fun C => ∀ i, C.val (g i) = O₂.val (g i))
    calc
      _ ≤ leftSeamConstant a U₁ U₂ O₁ * pinnedCount (restrictCover X U₂ G₂ le_sup_right)
          (fun v => a v.val) g A := hle
      _ ≤ leftSeamConstant a U₁ U₂ O₁ * pinnedCount (trivialCover (G₂.induce (↑U₂ : Set V)) M)
          (fun v => a v.val) g (fun i => O₂.val (g i)) := Nat.mul_le_mul_left _ (h₂ I g hsmall A hpin O₂)
      _ = _ := ho.symm

end
end CoefficientwiseRigidity.Gluing

namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {U : Finset V}

omit [Fintype V] in
theorem StructuralHull.boundary_comparison (h : StructuralHull U G) :
    ∀ (M : ℕ) (_b : Bipartition G) (X : Cover G M) (a : V → ℕ),
      BoundaryComparison (restrictCover X U G le_rfl) (fun v => a v.val) := by
  induction h with
  | atom U G _ hg =>
    intro M b X a
    exact atom_boundary_comparison ⟨fun v => b.side v.val, fun he => b.opposite he⟩ hg _ _
  | @glue U₁ U₂ G₁ G₂ h₁ h₂ hs ih₁ ih₂ =>
    intro M b X a
    exact Gluing.boundaryComparison_glue X a h₁.supported h₂.supported hs
      (ih₁ M ⟨b.side, fun he => b.opposite (Or.inl he)⟩ (Gluing.subCover X G₁ le_sup_left) a)
      (ih₂ M ⟨b.side, fun he => b.opposite (Or.inr he)⟩ (Gluing.subCover X G₂ le_sup_right) a)

/-- Removing the induced-universe wrapper also preserves every prescribed pin. -/
theorem pinnedCount_univ {M : ℕ} {I : Type} (X : Cover G M) (a : V → ℕ)
    (f : I → V) (A : I → Finset (Fin M)) :
    pinnedCount (restrictCover X Finset.univ G le_rfl) (fun v => a v.val)
      (fun i => ⟨f i, Finset.mem_univ _⟩) A = pinnedCount X a f A := by
  simp only [pinnedCount, ← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (Gluing.predicateEquiv (Gluing.univConfigurationEquiv X a)
    (fun C => ∀ i, C.val ⟨f i, Finset.mem_univ _⟩ = A i))).symm

theorem StructuralHull.boundary_comparison_univ (h : StructuralHull Finset.univ G)
    (b : Bipartition G) {M : ℕ} (X : Cover G M) (a : V → ℕ) : BoundaryComparison X a := by
  intro I f hf A hA O
  let f' : I → (↑(Finset.univ : Finset V) : Set V) := fun i => ⟨f i, Finset.mem_univ _⟩
  have hf' : SmallBoundary (G.induce (↑(Finset.univ : Finset V) : Set V)) f' := by
    rcases hf with hh | ⟨i, hi⟩ | ⟨i, j, he, hij⟩
    · exact Or.inl hh
    · exact Or.inr (Or.inl ⟨i, hi⟩)
    · exact Or.inr (Or.inr ⟨i, j, he, hij⟩)
  have hh := h.boundary_comparison M b X a I f' hf' A hA (Gluing.univConfigurationEquiv _ _ O)
  change pinnedCount (restrictCover X Finset.univ G le_rfl) (fun v => a v.val)
    (fun i => ⟨f i, Finset.mem_univ _⟩) A ≤
    pinnedCount (restrictCover (trivialCover G M) Finset.univ G le_rfl) (fun v => a v.val)
      (fun i => ⟨f i, Finset.mem_univ _⟩) (fun i => O.val (f i)) at hh
  simpa only [pinnedCount_univ] using hh

theorem StructuralHull.coefficient_le (h : StructuralHull Finset.univ G)
    (b : Bipartition G) {M : ℕ} (X : Cover G M) (a : V → ℕ) :
    coefficient X a ≤ ordinary G M a := by
  by_cases ha : Feasible G M a
  · let O : Configuration (trivialCover G M) a := ⟨nestedAssignment b M a, nestedAssignment_admissible b a ha⟩
    exact (h.boundary_comparison_univ b X a).coefficient_le X a O
  · rw [coefficient_zero_of_not_feasible X a ha]
    exact Nat.zero_le _

end
end CoefficientwiseRigidity
