import CoefficientwiseRigidity.SliceSymmetry
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Counting-isometric harmonic embeddings and the normalized direct sum. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M k : ℕ}

def normalizedLift (i j : ℕ) : Space M →ₗ[ℝ] Space M :=
  (Real.sqrt ((M - 2 * i).choose j : ℝ))⁻¹ • incidenceLift j

theorem counting_smul_left (c : ℝ) (f g : Space M) :
    counting (c • f) g = c * counting f g := by
  rw [counting_symm, counting_smul_right, counting_symm g f]

theorem counting_normalizedLift {i j : ℕ} {h : Space M} (hh : Harmonic i h)
    (hi : 2 * i ≤ M) (hj : j ≤ M - 2 * i) (f : Space M) :
    counting (normalizedLift i j f) (normalizedLift i j h) = counting f h := by
  have hc : (0 : ℝ) < (M - 2 * i).choose j := by exact_mod_cast Nat.choose_pos hj
  have hs : Real.sqrt ((M - 2 * i).choose j : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  simp only [normalizedLift, LinearMap.smul_apply, counting_smul_left, counting_smul_right]
  rw [counting_incidenceLift hh hi]
  have he := Real.sq_sqrt hc.le
  rw [← he]
  field_simp

theorem permute_normalizedLift (σ : Equiv.Perm (Fin M)) (i j : ℕ) (f : Space M) :
    permute σ (normalizedLift i j f) = normalizedLift i j (permute σ f) := by
  simp only [normalizedLift, LinearMap.smul_apply, map_smul, permute_incidenceLift]

def normalizingScalar (i : BlockIndex M k) : ℝ :=
  (Real.sqrt ((M - 2 * i.val).choose (k - i.val) : ℝ))⁻¹ * ((k - i.val).factorial : ℝ)⁻¹

theorem normalizingScalar_ne_zero (hk : k ≤ M) (i : BlockIndex M k) :
    normalizingScalar i ≠ 0 := by
  have hb := block_index_bounds i
  have hc : (0 : ℝ) < (M - 2 * i.val).choose (k - i.val) := by
    exact_mod_cast Nat.choose_pos (show k - i.val ≤ M - 2 * i.val by omega)
  exact mul_ne_zero (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hc)))
    (inv_ne_zero (by exact_mod_cast (k - i.val).factorial_ne_zero))

def normalizedBlock (i : BlockIndex M k) : harmonicSpace M i.val →ₗ[ℝ] levelSpace M k :=
  normalizingScalar i • blockLift i

theorem normalizedBlock_val (i : BlockIndex M k) (f : harmonicSpace M i.val) :
    (normalizedBlock i f).val = normalizedLift i.val (k - i.val) f.val := by
  simp only [normalizedBlock, normalizingScalar, LinearMap.smul_apply, Submodule.coe_smul,
    blockLift, LinearMap.coe_mk, AddHom.coe_mk, normalizedLift, incidenceLift, smul_smul]

/-- The same harmonic space is embedded isometrically in every surviving slice. -/
theorem counting_normalizedBlock (hk : k ≤ M) (i : BlockIndex M k)
    (f g : harmonicSpace M i.val) :
    counting (normalizedBlock i f).val (normalizedBlock i g).val = counting f.val g.val := by
  rw [normalizedBlock_val, normalizedBlock_val]
  have hb := block_index_bounds i
  exact counting_normalizedLift g.property (by omega) (by omega) f.val

theorem normalizedBlock_orthogonal {i j : BlockIndex M k} (hij : i ≠ j)
    (f : harmonicSpace M i.val) (g : harmonicSpace M j.val) :
    counting (normalizedBlock i f).val (normalizedBlock j g).val = 0 := by
  simp only [normalizedBlock, LinearMap.smul_apply, Submodule.coe_smul,
    counting_smul_left, counting_smul_right, blockLift_orthogonal hij, mul_zero]

def normalizeBlocks (hk : k ≤ M) : Blocks M k ≃ₗ[ℝ] Blocks M k :=
  LinearEquiv.piCongrRight fun i =>
    LinearEquiv.smulOfNeZero ℝ (harmonicSpace M i.val) (normalizingScalar i)
      (normalizingScalar_ne_zero hk i)

def normalizedDecomposition (hk : k ≤ M) : Blocks M k ≃ₗ[ℝ] levelSpace M k :=
  (normalizeBlocks hk).trans (harmonicDecomposition hk)

theorem normalizedDecomposition_apply (hk : k ≤ M) (h : Blocks M k) :
    normalizedDecomposition hk h = ∑ i, normalizedBlock i (h i) := by
  change assemble M k (normalizeBlocks hk h) = _
  simp [assemble, normalizeBlocks, LinearEquiv.smulOfNeZero_apply, normalizedBlock]

/-- Uniqueness and completeness hold on both sides of the middle rank. -/
theorem exists_unique_normalized_components (hk : k ≤ M) (f : levelSpace M k) :
    ∃! h : Blocks M k, (∑ i, normalizedBlock i (h i)) = f := by
  obtain ⟨h,hh⟩ := (normalizedDecomposition hk).surjective f
  refine ⟨h, ?_, ?_⟩
  · simpa only [normalizedDecomposition_apply] using hh
  · intro g hg
    apply (normalizedDecomposition hk).injective
    rw [normalizedDecomposition_apply, normalizedDecomposition_apply]
    exact hg.trans (by simpa only [normalizedDecomposition_apply] using hh.symm)

end
end CoefficientwiseRigidity.Spectral
