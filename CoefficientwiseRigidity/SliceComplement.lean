import CoefficientwiseRigidity.HarmonicAction

/-! Complementation is a counting isometry and preserves the shifted overlap operator. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def complementEquiv : Equiv.Perm (Finset (Fin M)) where
  toFun := compl
  invFun := compl
  left_inv := compl_compl
  right_inv := compl_compl

def complement : Space M ≃ₗ[ℝ] Space M :=
  LinearEquiv.piCongrLeft' ℝ (fun _ : Finset (Fin M) => ℝ) complementEquiv

@[simp] theorem complement_apply (f : Space M) (A : Finset (Fin M)) :
    complement f A = f Aᶜ := rfl

@[simp] theorem complement_complement (f : Space M) : complement (complement f) = f := by
  ext A
  simp

theorem counting_complement (f g : Space M) :
    counting (complement f) (complement g) = counting f g := by
  unfold counting
  exact Equiv.sum_comp complementEquiv (fun A => f A * g A)

theorem onLevel_complement {k : ℕ} {f : Space M} (hk : k ≤ M) (hf : OnLevel k f) :
    OnLevel (M - k) (complement f) := by
  intro A hA
  apply hf
  change Aᶜ.card ≠ k
  rw [Finset.card_compl, Fintype.card_fin]
  have := Finset.card_le_univ A
  simp only [Fintype.card_fin] at this
  omega

theorem complement_permute (σ : Equiv.Perm (Fin M)) (f : Space M) :
    complement (permute σ f) = permute σ (complement f) := by
  ext A
  simp only [complement_apply, permute_apply]
  congr 1
  ext x
  simp

def sliceComplementEquiv {k : ℕ} (hk : k ≤ M) : Kernel.Slice M k ≃ Kernel.Slice M (M - k) where
  toFun := Kernel.complementSlice
  invFun A := ⟨A.valᶜ, by simp only [Finset.card_compl, Fintype.card_fin, A.property]; omega⟩
  left_inv A := by apply Subtype.ext; simp [Kernel.complementSlice]
  right_inv A := by apply Subtype.ext; simp [Kernel.complementSlice]

def kernelMatrix (p q : ℕ) (F : ℕ → ℝ) : Space M →ₗ[ℝ] Space M where
  toFun f A := if A.card = p then ∑ B : Kernel.Slice M q,
    F ((A ∩ B.val).card - Kernel.overlapShift M p q) * f B.val else 0
  map_add' f g := by ext A; by_cases hA : A.card = p <;> simp [hA, mul_add, Finset.sum_add_distrib]
  map_smul' c f := by ext A; simp [Finset.mul_sum, mul_left_comm, mul_assoc]

theorem kernelMatrix_apply {p q : ℕ} (F : ℕ → ℝ) (f : Space M) (A : Kernel.Slice M p) :
    kernelMatrix p q F f A.val = ∑ B : Kernel.Slice M q, F (Kernel.overlap A B) * f B.val := by
  simp [kernelMatrix, A.property, Kernel.overlap]

theorem kernelMatrix_onLevel (p q : ℕ) (F : ℕ → ℝ) (f : Space M) :
    OnLevel p (kernelMatrix p q F f) := by
  intro A hA
  simp [kernelMatrix, hA]

/-- Exact conjugacy, including the zero extension off the two slices. -/
theorem kernelMatrix_complement {p q : ℕ} (hp : p ≤ M) (hq : q ≤ M)
    (F : ℕ → ℝ) (f : Space M) :
    kernelMatrix p q F f = complement (kernelMatrix (M - p) (M - q) F (complement f)) := by
  ext A
  by_cases hA : A.card = p
  · have hc : Aᶜ.card = M - p := by simp [Finset.card_compl, hA]
    change kernelMatrix p q F f A = kernelMatrix (M - p) (M - q) F (complement f) Aᶜ
    rw [kernelMatrix_apply F f ⟨A,hA⟩, kernelMatrix_apply F (complement f) ⟨Aᶜ,hc⟩]
    apply Fintype.sum_equiv (sliceComplementEquiv hq)
    intro B
    have he := Kernel.overlap_complement (⟨A,hA⟩ : Kernel.Slice M p) B
    change F (Kernel.overlap ⟨A,hA⟩ B) * f B.val =
      F (Kernel.overlap (Kernel.complementSlice ⟨A,hA⟩) (Kernel.complementSlice B)) * f B.valᶜᶜ
    rw [he, compl_compl]
  · rw [kernelMatrix_onLevel p q F f A hA]
    symm
    apply onLevel_complement (Nat.sub_le M p)
      (kernelMatrix_onLevel (M - p) (M - q) F (complement f)) A
    simpa only [Nat.sub_sub_self hp] using hA

theorem kernelMatrix_newton {p q r : ℕ} (hpq : p + q ≤ M) (c : ℕ → ℝ) :
    kernelMatrix (M := M) p q (fun n => ∑ d ∈ range (r + 1), c d * (n.choose d : ℝ)) =
      newtonMatrix p q r c := by
  apply LinearMap.ext
  intro f
  funext A
  by_cases hA : A.card = p
  · simp only [kernelMatrix, LinearMap.coe_mk, AddHom.coe_mk, if_pos hA,
      Kernel.overlapShift, Nat.sub_eq_zero_of_le hpq, Nat.sub_zero,
      newtonMatrix, LinearMap.sum_apply, LinearMap.smul_apply, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, overlapMatrix]
    simp only [if_pos hA, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  · simp [kernelMatrix, newtonMatrix, overlapMatrix, hA]

end
end CoefficientwiseRigidity.Spectral
