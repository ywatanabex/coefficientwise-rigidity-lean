import CoefficientwiseRigidity.HarmonicLifts
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! Actual slice spaces, harmonic kernels and their dimensions. -/
namespace CoefficientwiseRigidity.Spectral
open Finset Module
noncomputable section
variable {M : ℕ}

def levelSpace (M k : ℕ) : Submodule ℝ (Space M) where
  carrier := {f | OnLevel k f}
  zero_mem' := by intro A _; rfl
  add_mem' hf hg := by intro A hA; simp only [Pi.add_apply, hf A hA, hg A hA, add_zero]
  smul_mem' c f hf := by intro A hA; simp only [Pi.smul_apply, smul_eq_mul, hf A hA, mul_zero]

def levelEquiv (M k : ℕ) : levelSpace M k ≃ₗ[ℝ] (Kernel.Slice M k → ℝ) where
  toFun f A := f.val A.val
  invFun f := ⟨fun A => if hA : A.card = k then f ⟨A,hA⟩ else 0, by
    intro A hA
    simp only [dif_neg hA]⟩
  left_inv f := by
    apply Subtype.ext
    funext A
    by_cases hA : A.card = k
    · simp [hA]
    · simp [hA, f.property A hA]
  right_inv f := by funext A; simp [A.property]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finrank_levelSpace (M k : ℕ) : finrank ℝ (levelSpace M k) = M.choose k := by
  rw [(levelEquiv M k).finrank_eq, Module.finrank_fintype_fun_eq_card, Kernel.slice_card]

def upLevel (M k : ℕ) : levelSpace M k →ₗ[ℝ] levelSpace M (k + 1) where
  toFun f := ⟨up f.val, onLevel_up f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add up f.val g.val
  map_smul' c f := by apply Subtype.ext; exact map_smul up c f.val

def downLevel (M k : ℕ) : levelSpace M (k + 1) →ₗ[ℝ] levelSpace M k where
  toFun f := ⟨down f.val, onLevel_down f.property⟩
  map_add' f g := by apply Subtype.ext; exact map_add down f.val g.val
  map_smul' c f := by apply Subtype.ext; exact map_smul down c f.val

theorem downUp_injective {k : ℕ} (hk : 2 * k < M) :
    Function.Injective ((downLevel M k).comp (upLevel M k)) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hd : down (up f.val) = 0 := congrArg Subtype.val hf
  have hu : up f.val = 0 := by
    apply (counting_self_eq_zero_iff _).mp
    rw [counting_up, hd, counting_zero_right]
  apply Subtype.ext
  exact up_injective_onLevel hk f.property hu

theorem downLevel_surjective {k : ℕ} (hk : 2 * k < M) :
    Function.Surjective (downLevel M k) := by
  have h := LinearMap.surjective_of_injective (downUp_injective hk)
  intro f
  obtain ⟨g,hg⟩ := h f
  exact ⟨upLevel M k g, hg⟩

def harmonicSpace (M i : ℕ) : Submodule ℝ (Space M) :=
  levelSpace M i ⊓ LinearMap.ker down

theorem mem_harmonicSpace {i : ℕ} {f : Space M} : f ∈ harmonicSpace M i ↔ Harmonic i f := Iff.rfl

def harmonicKerEquiv (M k : ℕ) : LinearMap.ker (downLevel M k) ≃ₗ[ℝ] harmonicSpace M (k + 1) where
  toFun f := ⟨f.val.val, f.val.property, congrArg Subtype.val f.property⟩
  invFun f := ⟨⟨f.val, f.property.1⟩, Subtype.ext f.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem onLevel_zero_down {f : Space M} (hf : OnLevel 0 f) : down f = 0 := by
  ext A
  rw [down_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · rfl
  · apply hf
    rw [Finset.card_insert_of_not_mem hi]
    omega

theorem harmonicSpace_zero (M : ℕ) : harmonicSpace M 0 = levelSpace M 0 := by
  ext f
  constructor
  · exact And.left
  · intro hf
    exact ⟨hf, onLevel_zero_down hf⟩

theorem finrank_harmonicSpace_succ {k : ℕ} (hk : 2 * k < M) :
    finrank ℝ (harmonicSpace M (k + 1)) = M.choose (k + 1) - M.choose k := by
  have h := LinearMap.finrank_range_add_finrank_ker (downLevel M k)
  rw [LinearMap.range_eq_top.mpr (downLevel_surjective hk), finrank_top,
    (harmonicKerEquiv M k).finrank_eq, finrank_levelSpace, finrank_levelSpace] at h
  omega

/-- At i=0 the absent lower binomial term is zero, not choose(M,0). -/
theorem finrank_harmonicSpace {i : ℕ} (hi : 2 * i ≤ M) :
    finrank ℝ (harmonicSpace M i) =
      M.choose i - (if i = 0 then 0 else M.choose (i - 1)) := by
  cases i with
  | zero => rw [harmonicSpace_zero, finrank_levelSpace]; simp
  | succ i => simpa using finrank_harmonicSpace_succ (M := M) (k := i) (by omega)

theorem sum_finrank_harmonicSpace (r : ℕ) (hr : 2 * r ≤ M) :
    (∑ i ∈ range (r + 1), finrank ℝ (harmonicSpace M i)) = M.choose r := by
  induction r with
  | zero => simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
            rw [harmonicSpace_zero, finrank_levelSpace]
  | succ r ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    have h := LinearMap.finrank_range_add_finrank_ker (downLevel M r)
    rw [LinearMap.range_eq_top.mpr (downLevel_surjective (M := M) (k := r) (by omega)),
      finrank_top, (harmonicKerEquiv M r).finrank_eq,
      finrank_levelSpace, finrank_levelSpace] at h
    exact h

/-- The low-half orthogonal split is constructed using the invertible D U map. -/
theorem split_level {k : ℕ} (hk : 2 * k < M) (f : levelSpace M (k + 1)) :
    ∃ (g : levelSpace M k) (h : harmonicSpace M (k + 1)),
      f.val = up g.val + h.val ∧ counting (up g.val) h.val = 0 := by
  obtain ⟨g,hg⟩ := LinearMap.surjective_of_injective (downUp_injective hk) (downLevel M k f)
  have hd : down (up g.val) = down f.val := congrArg Subtype.val hg
  have hs : OnLevel (k + 1) (f.val - up g.val) :=
    (levelSpace M (k + 1)).sub_mem f.property (onLevel_up g.property)
  let h : harmonicSpace M (k + 1) := ⟨f.val - up g.val, hs, by
    change down (f.val - up g.val) = 0
    rw [map_sub, hd, sub_self]⟩
  refine ⟨g,h,?_,?_⟩
  · dsimp [h]
    abel
  · rw [counting_up, h.property.2, counting_zero_right]

end
end CoefficientwiseRigidity.Spectral
