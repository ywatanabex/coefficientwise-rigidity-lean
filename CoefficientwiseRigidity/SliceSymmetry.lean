import CoefficientwiseRigidity.SliceDecomposition

/-! Label permutations preserve the counting form and commute with all lifts. -/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

def permute (σ : Equiv.Perm (Fin M)) : Space M ≃ₗ[ℝ] Space M :=
  LinearEquiv.piCongrLeft' ℝ (fun _ : Finset (Fin M) => ℝ) σ.finsetCongr

theorem permute_apply (σ : Equiv.Perm (Fin M)) (f : Space M) (A : Finset (Fin M)) :
    permute σ f A = f (A.map σ.symm.toEmbedding) := rfl

theorem counting_permute (σ : Equiv.Perm (Fin M)) (f g : Space M) :
    counting (permute σ f) (permute σ g) = counting f g := by
  unfold counting
  change (∑ A, (fun B => f B * g B) (σ.symm.finsetCongr A)) = _
  exact Equiv.sum_comp σ.symm.finsetCongr (fun A => f A * g A)

theorem onLevel_permute (σ : Equiv.Perm (Fin M)) {k : ℕ} {f : Space M}
    (hf : OnLevel k f) : OnLevel k (permute σ f) := by
  intro A hA
  apply hf
  simpa using hA

theorem permute_up (σ : Equiv.Perm (Fin M)) (f : Space M) :
    permute σ (up f) = up (permute σ f) := by
  ext A
  rw [permute_apply, up_apply, ← Equiv.sum_comp σ.symm]
  simp [up_apply, permute_apply, Finset.map_erase]

theorem permute_down (σ : Equiv.Perm (Fin M)) (f : Space M) :
    permute σ (down f) = down (permute σ f) := by
  ext A
  rw [permute_apply, down_apply, ← Equiv.sum_comp σ.symm]
  simp [down_apply, permute_apply, Finset.map_insert]

theorem harmonic_permute (σ : Equiv.Perm (Fin M)) {i : ℕ} {f : Space M}
    (hf : Harmonic i f) : Harmonic i (permute σ f) := by
  refine ⟨onLevel_permute σ hf.1, ?_⟩
  rw [← permute_down, hf.2, map_zero]

theorem permute_raise (σ : Equiv.Perm (Fin M)) (j : ℕ) (f : Space M) :
    permute σ (raise j f) = raise j (permute σ f) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [raise_succ, permute_up, ih, ← raise_succ]

theorem permute_incidenceLift (σ : Equiv.Perm (Fin M)) (j : ℕ) (f : Space M) :
    permute σ (incidenceLift j f) = incidenceLift j (permute σ f) := by
  simp only [incidenceLift, LinearMap.smul_apply, map_smul, permute_raise]

end
end CoefficientwiseRigidity.Spectral
