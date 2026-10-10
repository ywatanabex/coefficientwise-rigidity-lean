import CoefficientwiseRigidity.SliceSpaces
import Mathlib.LinearAlgebra.FiniteDimensional

/-!
Full harmonic decomposition of every valid slice, including the dense half.
Orthogonality proves independence; exact dimensions then prove surjectivity.
-/
namespace CoefficientwiseRigidity.Spectral
open Finset Module
noncomputable section
variable {M k : ℕ}

abbrev BlockIndex (M k : ℕ) := Fin (min k (M - k) + 1)
abbrev Blocks (M k : ℕ) := (i : BlockIndex M k) → harmonicSpace M i.val

theorem block_index_bounds (i : BlockIndex M k) :
    i.val ≤ k ∧ i.val ≤ M - k := by
  have := i.isLt
  omega

def blockLift (i : BlockIndex M k) : harmonicSpace M i.val →ₗ[ℝ] levelSpace M k where
  toFun h := ⟨raise (k - i.val) h.val, by
    have hlevel := onLevel_raise h.property.1 (k - i.val)
    simpa only [Nat.add_sub_of_le (block_index_bounds i).1] using hlevel⟩
  map_add' f g := by apply Subtype.ext; exact map_add (raise _) f.val g.val
  map_smul' c f := by apply Subtype.ext; exact map_smul (raise _) c f.val

def assemble (M k : ℕ) : Blocks M k →ₗ[ℝ] levelSpace M k where
  toFun h := ∑ i, blockLift i (h i)
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.smul_sum]

theorem counting_sum_left {ι : Type} [Fintype ι] (f : ι → Space M) (g : Space M) :
    counting (∑ i, f i) g = ∑ i, counting (f i) g := by
  simp only [counting, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem blockLift_orthogonal {i j : BlockIndex M k} (hij : i ≠ j)
    (f : harmonicSpace M i.val) (g : harmonicSpace M j.val) :
    counting (blockLift i f).val (blockLift j g).val = 0 := by
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact harmonic_lifts_orthogonal g.property h (block_index_bounds j).1
  · rw [counting_symm]
    exact harmonic_lifts_orthogonal f.property h (block_index_bounds i).1

theorem counting_assemble_block (f : Blocks M k) (i : BlockIndex M k)
    (g : harmonicSpace M i.val) :
    counting (assemble M k f).val (blockLift i g).val =
      counting (blockLift i (f i)).val (blockLift i g).val := by
  change counting ((∑ j, blockLift j (f j) : levelSpace M k).val) _ = _
  rw [Submodule.coe_sum, counting_sum_left]
  apply Finset.sum_eq_single i
  · intro j _ hji
    exact blockLift_orthogonal hji _ _
  · simp

theorem blockLift_injective (hk : k ≤ M) (i : BlockIndex M k) :
    Function.Injective (blockLift i) := by
  have hb := block_index_bounds i
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  have hz : raise (k - i.val) f.val = 0 := congrArg Subtype.val hf
  apply Subtype.ext
  exact raise_injective_on_harmonic (by omega) (by omega) f.property hz

theorem assemble_injective (hk : k ≤ M) : Function.Injective (assemble M k) := by
  apply LinearMap.ker_eq_bot.mp
  rw [Submodule.eq_bot_iff]
  intro f hf
  funext i
  apply blockLift_injective hk i
  change blockLift i (f i) = blockLift i 0
  rw [map_zero]
  apply Subtype.ext
  apply (counting_self_eq_zero_iff _).mp
  rw [← counting_assemble_block f i (f i)]
  rw [show assemble M k f = 0 from hf, counting_symm]
  exact counting_zero_right _

theorem finrank_blocks (hk : k ≤ M) : finrank ℝ (Blocks M k) = M.choose k := by
  rw [Module.finrank_pi_fintype]
  change (∑ i : Fin (min k (M - k) + 1), finrank ℝ (harmonicSpace M i.val)) = _
  have he := Fin.sum_univ_eq_sum_range (fun i => finrank ℝ (harmonicSpace M i)) (min k (M - k) + 1)
  rw [he, sum_finrank_harmonicSpace _ (by omega)]
  by_cases h : k ≤ M - k
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), Nat.choose_symm hk]

/-- No block-completeness or representation-theoretic theorem is an assumption. -/
theorem assemble_bijective (hk : k ≤ M) : Function.Bijective (assemble M k) := by
  have hdim : finrank ℝ (Blocks M k) = finrank ℝ (levelSpace M k) := by
    rw [finrank_blocks hk, finrank_levelSpace]
  exact ⟨assemble_injective hk,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp (assemble_injective hk)⟩

def harmonicDecomposition (hk : k ≤ M) : Blocks M k ≃ₗ[ℝ] levelSpace M k :=
  LinearEquiv.ofBijective (assemble M k) (assemble_bijective hk)

/-- Every slice function has a unique tuple of harmonic components. -/
theorem exists_unique_harmonic_components (hk : k ≤ M) (f : levelSpace M k) :
    ∃! h : Blocks M k, (∑ i, blockLift i (h i)) = f := by
  obtain ⟨h,hh⟩ := (assemble_bijective hk).2 f
  exact ⟨h,hh,fun g hg => (assemble_bijective hk).1 (hg.trans hh.symm)⟩

end
end CoefficientwiseRigidity.Spectral
