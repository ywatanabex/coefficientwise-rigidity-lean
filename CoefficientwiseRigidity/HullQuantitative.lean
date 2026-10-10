import CoefficientwiseRigidity.SeamQuantitative
import CoefficientwiseRigidity.HullRigidity

/-! The designated WitnessHull leaf pays the original reserve all the way to the root. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {W U : Finset V} {H G : SimpleGraph V}

omit [Fintype V] in
theorem StructuralHull.piece_coefficient_le (h : StructuralHull U G)
    (b : Bipartition G) {M : ℕ} (X : Cover G M) (a : V → ℕ) :
    coefficient (restrictCover X U G le_rfl) (fun v => a v.val) ≤
      ordinary (G.induce (↑U : Set V)) M (fun v => a v.val) := by
  by_cases ha : Feasible (G.induce (↑U : Set V)) M (fun v => a v.val)
  · let b' : Bipartition (G.induce (↑U : Set V)) := ⟨fun v => b.side v.val, fun he => b.opposite he⟩
    let O : Configuration (trivialCover (G.induce (↑U : Set V)) M) (fun v => a v.val) :=
      ⟨nestedAssignment b' M (fun v => a v.val), nestedAssignment_admissible b' _ ha⟩
    exact (h.boundary_comparison M b X a).coefficient_le _ _ O
  · rw [coefficient_zero_of_not_feasible _ _ ha]
    exact Nat.zero_le _

omit [Fintype V] in
theorem WitnessHull.quantitative_succ {𝕜 : Type} [LinearOrderedField 𝕜] (h : WitnessHull W H U G) :
    ∀ (M : ℕ) (_b : Bipartition G) (X : Cover G (M + 2)) (q : V → ℕ) (k : 𝕜), 0 ≤ k →
    (coefficient (restrictCover X W H h.subgraph) (fun v => q v.val + 1) : 𝕜) +
      k * reserve (H.induce (↑W : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary (H.induce (↑W : Set V)) (M + 2) (fun v => q v.val + 1) →
    (coefficient (restrictCover X U G le_rfl) (fun v => q v.val + 1) : 𝕜) +
      k * reserve (G.induce (↑U : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary (G.induce (↑U : Set V)) (M + 2) (fun v => q v.val + 1) := by
  induction h with
  | here _ _ => intro M b X q k hk hh; exact hh
  | @left U₁ U₂ G₁ G₂ h₁ h₂ hs ih =>
    intro M b X q k hk hh
    let b₁ : Bipartition G₁ := ⟨b.side, fun he => b.opposite (Or.inl he)⟩
    let b₂ : Bipartition G₂ := ⟨b.side, fun he => b.opposite (Or.inr he)⟩
    exact Gluing.quantitative_glue_left_succ b X q h₁.toStructuralHull.supported h₂.supported hs
      (h₂.boundary_comparison (M + 2) b₂ (Gluing.subCover X G₂ le_sup_right) (fun v => q v + 1))
      ((StructuralHull.glue h₁.toStructuralHull h₂ hs).piece_coefficient_le b X (fun v => q v + 1))
      k hk (ih M b₁ (Gluing.subCover X G₁ le_sup_left) q k hk hh)
  | @right U₁ U₂ G₁ G₂ h₁ h₂ hs ih =>
    intro M b X q k hk hh
    let b₁ : Bipartition G₁ := ⟨b.side, fun he => b.opposite (Or.inl he)⟩
    let b₂ : Bipartition G₂ := ⟨b.side, fun he => b.opposite (Or.inr he)⟩
    exact Gluing.quantitative_glue_right_succ b X q h₁.supported h₂.toStructuralHull.supported hs
      (h₁.boundary_comparison (M + 2) b₁ (Gluing.subCover X G₁ le_sup_left) (fun v => q v + 1))
      ((StructuralHull.glue h₁ h₂.toStructuralHull hs).piece_coefficient_le b X (fun v => q v + 1))
      k hk (ih M b₂ (Gluing.subCover X G₂ le_sup_right) q k hk hh)

theorem ordinary_induce_univ (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) :
    ordinary (G.induce (↑(Finset.univ : Finset V) : Set V)) M (fun v => a v.val) = ordinary G M a :=
  coefficient_restrict_univ (trivialCover G M) a

theorem reserve_induce_univ (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) :
    reserve (G.induce (↑(Finset.univ : Finset V) : Set V)) M (fun v => a v.val) = reserve G M a :=
  ordinary_induce_univ G (M - 2) (fun v => a v - 1)

/-- An inhabitant of the original, unchanged MainCQuantitative proposition. -/
theorem paperMainCQuantitative (b : Bipartition G) : MainCQuantitative G := by
  intro M hM X a hp _ W H hle h k hk
  dsimp only
  intro hh
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 2 := ⟨M - 2, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : V → ℕ, a = fun v => q v + 1 :=
    ⟨fun v => a v - 1, by funext v; change a v = a v - 1 + 1; have := hp v; omega⟩
  have hq := h.quantitative_succ m b X q k hk.le hh
  rw [coefficient_restrict_univ X (fun v => q v + 1),
    reserve_induce_univ G (m + 2) (fun v => q v + 1),
    ordinary_induce_univ G (m + 2) (fun v => q v + 1)] at hq
  exact hq

end
end CoefficientwiseRigidity
