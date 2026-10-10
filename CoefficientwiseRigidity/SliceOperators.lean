import CoefficientwiseRigidity.Slices

/-!
Counting-normalized Boolean-lattice operators. A fixed slice is represented
by functions supported on that level of the full powerset. This avoids
dependent casts between adjacent ranks and includes levels 0 and M.
-/
namespace CoefficientwiseRigidity.Spectral
open Finset
noncomputable section
variable {M : ℕ}

abbrev Space (M : ℕ) := Finset (Fin M) → ℝ

def counting (f g : Space M) : ℝ := ∑ A, f A * g A

theorem counting_symm (f g : Space M) : counting f g = counting g f := by
  simp only [counting, mul_comm]

theorem counting_add_right (f g h : Space M) :
    counting f (g + h) = counting f g + counting f h := by
  simp [counting, mul_add, Finset.sum_add_distrib]

theorem counting_smul_right (c : ℝ) (f g : Space M) :
    counting f (c • g) = c * counting f g := by
  simp [counting, Finset.mul_sum, mul_left_comm]

@[simp] theorem counting_zero_right (f : Space M) : counting f 0 = 0 := by simp [counting]

def upAt (i : Fin M) : Space M →ₗ[ℝ] Space M where
  toFun f A := if i ∈ A then f (A.erase i) else 0
  map_add' f g := by ext A; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by ext A; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

def downAt (i : Fin M) : Space M →ₗ[ℝ] Space M where
  toFun f A := if i ∈ A then 0 else f (insert i A)
  map_add' f g := by ext A; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' c f := by ext A; simp only [Pi.smul_apply, smul_eq_mul]; split_ifs <;> simp

def up : Space M →ₗ[ℝ] Space M := ∑ i, upAt i
def down : Space M →ₗ[ℝ] Space M := ∑ i, downAt i

theorem up_apply (f : Space M) (A : Finset (Fin M)) :
    up f A = ∑ i, if i ∈ A then f (A.erase i) else 0 := by
  simp [up, upAt, LinearMap.sum_apply]

theorem down_apply (f : Space M) (A : Finset (Fin M)) :
    down f A = ∑ i, if i ∈ A then 0 else f (insert i A) := by
  simp [down, downAt, LinearMap.sum_apply]

theorem upAt_downAt_of_ne (i j : Fin M) (hij : i ≠ j) (f : Space M) :
    downAt i (upAt j f) = upAt j (downAt i f) := by
  ext A
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;>
    simp [upAt, downAt, hi, hj, hij, hij.symm, Finset.erase_insert_of_ne]

theorem local_commutator (i : Fin M) (f : Space M) (A : Finset (Fin M)) :
    downAt i (upAt i f) A - upAt i (downAt i f) A =
      (if i ∈ A then -1 else 1) * f A := by
  by_cases hi : i ∈ A <;> simp [upAt, downAt, hi]

/-- Toggle one label; it bijects the two sides of each covering relation. -/
def toggle (i : Fin M) (A : Finset (Fin M)) : Finset (Fin M) :=
  if i ∈ A then A.erase i else insert i A

theorem toggle_involutive (i : Fin M) : Function.Involutive (toggle i) := by
  intro A
  by_cases hi : i ∈ A <;> simp [toggle, hi]

def toggleEquiv (i : Fin M) : Finset (Fin M) ≃ Finset (Fin M) :=
  ⟨toggle i, toggle i, toggle_involutive i, toggle_involutive i⟩

/-- Adjointness uses a sum, with no uniform-probability normalizing factor. -/
theorem counting_upAt (i : Fin M) (f g : Space M) :
    counting (upAt i f) g = counting f (downAt i g) := by
  unfold counting
  rw [← Equiv.sum_comp (toggleEquiv i)]
  apply Finset.sum_congr rfl
  intro A _
  change upAt i f (toggle i A) * g (toggle i A) = f A * downAt i g A
  by_cases hi : i ∈ A <;> simp [upAt, downAt, toggle, hi]

theorem counting_up (f g : Space M) : counting (up f) g = counting f (down g) := by
  simp only [counting, up, down, LinearMap.sum_apply, Finset.sum_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => counting_upAt i f g

/-- The off-diagonal exchanges cancel; only the M-|A| and |A| diagonal terms remain. -/
theorem commutator (f : Space M) (A : Finset (Fin M)) :
    down (up f) A - up (down f) A = ((M : ℝ) - 2 * A.card) * f A := by
  have hdiag : ∀ i : Fin M,
      (∑ j, (downAt i (upAt j f) A - upAt j (downAt i f) A)) =
        (if i ∈ A then -1 else 1) * f A := by
    intro i
    rw [Finset.sum_eq_single i]
    · exact local_commutator i f A
    · intro j _ hji
      rw [upAt_downAt_of_ne i j hji.symm]
      simp
    · simp
  calc
    down (up f) A - up (down f) A =
        ∑ i, ∑ j, (downAt i (upAt j f) A - upAt j (downAt i f) A) := by
      simp only [down, up, LinearMap.sum_apply, map_sum, Finset.sum_apply,
        Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_comm
    _ = ∑ i : Fin M, (if i ∈ A then -1 else 1) * f A := by simp_rw [hdiag]
    _ = ((M : ℝ) - 2 * A.card) * f A := by
      rw [← Finset.sum_mul]
      congr 1
      have he : (∑ i : Fin M, if i ∈ A then (-1 : ℝ) else 1) =
          (∑ i : Fin M, 1) - 2 * ∑ i : Fin M, if i ∈ A then (1 : ℝ) else 0 := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        split_ifs <;> norm_num
      rw [he]
      simp

/-- Support on a fixed level, including the empty out-of-range levels. -/
def OnLevel (k : ℕ) (f : Space M) : Prop := ∀ A, A.card ≠ k → f A = 0

theorem onLevel_up {k : ℕ} {f : Space M} (hf : OnLevel k f) : OnLevel (k + 1) (up f) := by
  intro A hA
  rw [up_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · apply hf
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  · rfl

theorem onLevel_down {k : ℕ} {f : Space M} (hf : OnLevel (k + 1) f) : OnLevel k (down f) := by
  intro A hA
  rw [down_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with hi
  · rfl
  · apply hf
    rw [Finset.card_insert_of_not_mem hi]
    omega

theorem commutator_onLevel {k : ℕ} {f : Space M} (hf : OnLevel k f) :
    down (up f) = up (down f) + ((M : ℝ) - 2 * k) • f := by
  ext A
  have h := commutator f A
  by_cases hA : A.card = k
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hA] at h
    linarith
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf A hA, mul_zero] at *
    linarith

theorem counting_self_nonneg (f : Space M) : 0 ≤ counting f f :=
  Finset.sum_nonneg fun A _ => mul_self_nonneg (f A)

theorem counting_self_eq_zero_iff (f : Space M) : counting f f = 0 ↔ f = 0 := by
  classical
  constructor
  · intro h
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun A (_ : A ∈ Finset.univ) =>
      mul_self_nonneg (f A))).mp h
    funext A
    have := hz A (Finset.mem_univ A)
    exact mul_self_eq_zero.mp this
  · rintro rfl
    simp [counting]

theorem up_injective_onLevel {k : ℕ} (hk : 2 * k < M) {f : Space M}
    (hf : OnLevel k f) (hu : up f = 0) : f = 0 := by
  have hid := congrArg (counting f) (commutator_onLevel hf)
  have hneg := counting_self_nonneg (down f)
  have hpos : 0 < (M : ℝ) - 2 * k := by exact_mod_cast (show (0 : ℤ) < M - 2 * (k : ℤ) by omega)
  rw [hu, map_zero] at hid
  rw [counting_zero_right, counting_add_right, counting_smul_right,
    counting_symm f (up (down f)), counting_up] at hid
  apply (counting_self_eq_zero_iff f).mp
  have hn := counting_self_nonneg f
  nlinarith

end
end CoefficientwiseRigidity.Spectral
