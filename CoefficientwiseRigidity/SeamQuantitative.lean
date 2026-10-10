import CoefficientwiseRigidity.SeamScalars

/-! Original-reserve propagation using a literal pinned insertion into the partner. -/
namespace CoefficientwiseRigidity.Gluing
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {𝕜 : Type} [LinearOrderedField 𝕜]
variable {G₁ G₂ : SimpleGraph V} {M : ℕ} {U₁ U₂ : Finset V}

theorem quantitative_of_factors (Z P R Z₁ P₁ R₁ c : ℕ) (k : 𝕜) (hk : 0 ≤ k)
    (hZ : Z ≤ c * Z₁) (hP : P = c * P₁) (hR : R ≤ c * R₁)
    (hbound : (Z₁ : 𝕜) + k * R₁ ≤ P₁) : (Z : 𝕜) + k * R ≤ P := by
  calc
    (Z : 𝕜) + k * R ≤ (c : 𝕜) * Z₁ + k * ((c : 𝕜) * R₁) :=
      add_le_add (by exact_mod_cast hZ)
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hR) hk)
    _ = (c : 𝕜) * ((Z₁ : 𝕜) + k * R₁) := by ring
    _ ≤ (c : 𝕜) * P₁ := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg c)
    _ = P := by exact_mod_cast hP.symm

omit [Fintype V] in
theorem quantitative_glue_left_succ (b : Bipartition (G₁ ⊔ G₂))
    (X : Cover (G₁ ⊔ G₂) (M + 2)) (q : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₂ : BoundaryComparison (restrictCover X U₂ G₂ le_sup_right) (fun v => q v.val + 1))
    (hscalar : coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => q v.val + 1) ≤
      ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1))
    (k : 𝕜) (hk : 0 ≤ k)
    (hbound : (coefficient (restrictCover X U₁ G₁ le_sup_left) (fun v => q v.val + 1) : 𝕜) +
      k * reserve (G₁.induce (↑U₁ : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary (G₁.induce (↑U₁ : Set V)) (M + 2) (fun v => q v.val + 1)) :
    (coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => q v.val + 1) : 𝕜) +
      k * reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) := by
  by_cases hz : reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) = 0
  · rw [hz, Nat.cast_zero, mul_zero, add_zero]
    exact_mod_cast hscalar
  · have hp : 0 < ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) M (fun v => q v.val) := by
      simpa only [reserve, Nat.add_sub_cancel] using Nat.pos_of_ne_zero hz
    obtain ⟨O⟩ := Fintype.card_pos_iff.mp hp
    let O₂ : RightConfiguration (trivialCover (G₁ ⊔ G₂) M) q U₂ :=
      rightPart (trivialCover (G₁ ⊔ G₂) M) q U₁ U₂ O
    let b₂ : Bipartition (G₂.induce (↑U₂ : Set V)) :=
      ⟨fun v => b.side v.val, fun he => b.opposite (Or.inr he)⟩
    let O₂' : RightConfiguration (trivialCover (G₁ ⊔ G₂) (M + 2)) (fun v => q v + 1) U₂ :=
      insertConfiguration b₂ (fun v => q v.val) O₂
    have hi : seamConstant q U₁ U₂ O₂ ≤ seamConstant (fun v => q v + 1) U₁ U₂ O₂' :=
      pinnedCount_le_inserted b₂ (fun v => q v.val) (rightIndex U₁ U₂) O₂
    have hr : reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) =
        seamConstant q U₁ U₂ O₂ * reserve (G₁.induce (↑U₁ : Set V)) (M + 2) (fun v => q v.val + 1) := by
      simpa only [reserve, Nat.add_sub_cancel] using ordinary_glue_left q hU₁ hU₂ hs O₂
    exact quantitative_of_factors _ _ _ _ _ _ _ k hk
      (coefficient_glue_le_left X (fun v => q v + 1) hU₁ hU₂ hs h₂ O₂')
      (ordinary_glue_left (fun v => q v + 1) hU₁ hU₂ hs O₂')
      (by rw [hr]; exact Nat.mul_le_mul_right _ hi) hbound

omit [Fintype V] in
theorem quantitative_glue_right_succ (b : Bipartition (G₁ ⊔ G₂))
    (X : Cover (G₁ ⊔ G₂) (M + 2)) (q : V → ℕ)
    (hU₁ : SupportedOn G₁ U₁) (hU₂ : SupportedOn G₂ U₂)
    (hs : LegalSeam U₁ U₂ G₁ G₂)
    (h₂ : BoundaryComparison (restrictCover X U₁ G₁ le_sup_left) (fun v => q v.val + 1))
    (hscalar : coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => q v.val + 1) ≤
      ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1))
    (k : 𝕜) (hk : 0 ≤ k)
    (hbound : (coefficient (restrictCover X U₂ G₂ le_sup_right) (fun v => q v.val + 1) : 𝕜) +
      k * reserve (G₂.induce (↑U₂ : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary (G₂.induce (↑U₂ : Set V)) (M + 2) (fun v => q v.val + 1)) :
    (coefficient (restrictCover X (U₁ ∪ U₂) (G₁ ⊔ G₂) le_rfl) (fun v => q v.val + 1) : 𝕜) +
      k * reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) ≤
        ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) := by
  by_cases hz : reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) = 0
  · rw [hz, Nat.cast_zero, mul_zero, add_zero]
    exact_mod_cast hscalar
  · have hp : 0 < ordinary ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) M (fun v => q v.val) := by
      simpa only [reserve, Nat.add_sub_cancel] using Nat.pos_of_ne_zero hz
    obtain ⟨O⟩ := Fintype.card_pos_iff.mp hp
    let O₂ : LeftConfiguration (trivialCover (G₁ ⊔ G₂) M) q U₁ :=
      leftPart (trivialCover (G₁ ⊔ G₂) M) q U₁ U₂ O
    let b₂ : Bipartition (G₁.induce (↑U₁ : Set V)) :=
      ⟨fun v => b.side v.val, fun he => b.opposite (Or.inl he)⟩
    let O₂' : LeftConfiguration (trivialCover (G₁ ⊔ G₂) (M + 2)) (fun v => q v + 1) U₁ :=
      insertConfiguration b₂ (fun v => q v.val) O₂
    have hi : leftSeamConstant q U₁ U₂ O₂ ≤ leftSeamConstant (fun v => q v + 1) U₁ U₂ O₂' :=
      pinnedCount_le_inserted b₂ (fun v => q v.val) (leftIndex U₁ U₂) O₂
    have hr : reserve ((G₁ ⊔ G₂).induce (↑(U₁ ∪ U₂) : Set V)) (M + 2) (fun v => q v.val + 1) =
        leftSeamConstant q U₁ U₂ O₂ * reserve (G₂.induce (↑U₂ : Set V)) (M + 2) (fun v => q v.val + 1) := by
      simpa only [reserve, Nat.add_sub_cancel] using ordinary_glue_right q hU₁ hU₂ hs O₂
    exact quantitative_of_factors _ _ _ _ _ _ _ k hk
      (coefficient_glue_le_right X (fun v => q v + 1) hU₁ hU₂ hs h₂ O₂')
      (ordinary_glue_right (fun v => q v + 1) hU₁ hU₂ hs O₂')
      (by rw [hr]; exact Nat.mul_le_mul_right _ hi) hbound

end
end CoefficientwiseRigidity.Gluing
