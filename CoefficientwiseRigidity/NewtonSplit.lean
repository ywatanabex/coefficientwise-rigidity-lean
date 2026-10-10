import CoefficientwiseRigidity.Newton
import CoefficientwiseRigidity.Split

/-!
Paper K3 (VERIFIED paper result), now with the actual finite Newton cones.
All hypotheses concern 0,...,r, even though `splitF` and `splitG` are stored
as functions on ℕ. The arguments do not assume global monotonicity.
-/
namespace CoefficientwiseRigidity.Kernel

theorem delta_splitF (f g : ℕ → ℚ) :
    delta (splitF f g) = fun n => delta f n * g (n + 1) := by
  funext n
  exact splitF_difference f g n

theorem delta_splitG (f g : ℕ → ℚ) :
    delta (splitG f g) = fun n => f n * delta g n := by
  funext n
  simp [delta, fwdDiff, splitG]

theorem newtonCone_splitF {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g) : NewtonCone r (splitF f g) := by
  cases r with
  | zero =>
    rw [newtonCone_iff_differences, differenceCone_zero_iff]
    exact mul_nonneg (newtonCone_nonneg hf (le_refl 0)) (newtonCone_nonneg hg (le_refl 0))
  | succ r =>
    rw [newtonCone_succ_iff, delta_splitF]
    exact ⟨mul_nonneg (newtonCone_nonneg hf (by omega)) (newtonCone_nonneg hg (by omega)),
      newtonCone_mul (newtonCone_delta hf) (newtonCone_shift hg)⟩

theorem newtonCone_splitG {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g) : NewtonCone r (splitG f g) := by
  cases r with
  | zero =>
    rw [newtonCone_iff_differences, differenceCone_zero_iff]
    exact le_refl 0
  | succ r =>
    rw [newtonCone_succ_iff, delta_splitG]
    exact ⟨le_refl 0, newtonCone_mul (newtonCone_restrict hf (by omega)) (newtonCone_delta hg)⟩

theorem split_bound_above_on {r : ℕ} (f g : ℕ → ℚ)
    (hf : ∀ x y, x ≤ y → y ≤ r → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → y ≤ r → g x ≤ g y)
    (x y : ℕ) (hxy : x ≤ y) (hy : y ≤ r) :
    f x * g y ≤ splitF f g x + splitG f g y := by
  induction y, hxy using Nat.le_induction with
  | base => exact (split_diagonal f g x).symm.le
  | succ n hn ih =>
    have hprev := ih (by omega)
    have hfn := hf x n hn (by omega)
    have hgn := hg n (n + 1) (by omega) hy
    have hmul := mul_nonneg (sub_nonneg.mpr hfn) (sub_nonneg.mpr hgn)
    simp only [splitG]
    nlinarith

theorem split_bound_below_on {r : ℕ} (f g : ℕ → ℚ)
    (hf : ∀ x y, x ≤ y → y ≤ r → f x ≤ f y)
    (hg : ∀ x y, x ≤ y → y ≤ r → g x ≤ g y)
    (x y : ℕ) (hyx : y ≤ x) (hx : x ≤ r) :
    f x * g y ≤ splitF f g x + splitG f g y := by
  induction x, hyx using Nat.le_induction with
  | base => exact (split_diagonal f g y).symm.le
  | succ n hn ih =>
    have hprev := ih (by omega)
    have hfn := hf n (n + 1) (by omega) hx
    have hgn := hg y (n + 1) (by omega) hx
    have hmul := mul_nonneg (sub_nonneg.mpr hfn) (sub_nonneg.mpr hgn)
    simp only [splitF]
    nlinarith

theorem newton_split_bound {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g)
    {x y : ℕ} (hx : x ≤ r) (hy : y ≤ r) :
    f x * g y ≤ splitF f g x + splitG f g y := by
  have hf' := fun x y hxy hy => @newtonCone_monotone r f hf x y hxy hy
  have hg' := fun x y hxy hy => @newtonCone_monotone r g hg x y hxy hy
  rcases le_total x y with h | h
  · exact split_bound_above_on f g hf' hg' x y h hy
  · exact split_bound_below_on f g hf' hg' x y h hx

theorem newton_splitF_reserve {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone (r + 1) f) (hg : NewtonCone (r + 1) g)
    {n : ℕ} (hn : n ≤ r) : delta f n * delta g n ≤ delta (splitF f g) n := by
  rw [delta_splitF]
  have h := mul_nonneg (newtonCone_nonneg (newtonCone_delta hf) hn)
    (newtonCone_nonneg hg (by omega : n ≤ r + 1))
  dsimp [delta, fwdDiff] at *
  nlinarith

theorem newton_splitF_last_strict {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone (r + 1) f) (hg : NewtonCone (r + 1) g)
    (hfn : ∃ n, n ≤ r + 1 ∧ f n ≠ f 0)
    (hgn : ∃ n, n ≤ r + 1 ∧ g n ≠ g 0) :
    splitF f g r < splitF f g (r + 1) :=
  splitF_strict_step f g r ((newtonCone_last_strict_iff hf).mpr hfn)
    (newtonCone_endpoint_pos hg hgn)

/-- The finite K3 statement, including cone membership, exactness, reserve and strictness. -/
theorem finite_newton_split {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g) :
    ∃ F G : ℕ → ℚ, NewtonCone r F ∧ NewtonCone r G ∧
      (∀ x y, x ≤ r → y ≤ r → f x * g y ≤ F x + G y) ∧
      (∀ z, z ≤ r → F z + G z = f z * g z) ∧
      (∀ z, z + 1 ≤ r → delta f z * delta g z ≤ delta F z) ∧
      ((∃ n, n ≤ r ∧ f n ≠ f 0) → (∃ n, n ≤ r ∧ g n ≠ g 0) →
        ∃ n, n ≤ r ∧ F n ≠ F 0) := by
  refine ⟨splitF f g, splitG f g, newtonCone_splitF hf hg, newtonCone_splitG hf hg,
    (fun _ _ hx hy => newton_split_bound hf hg hx hy),
    (fun z _ => split_diagonal f g z), ?_, ?_⟩
  · intro z hz
    cases r with
    | zero => omega
    | succ r => exact newton_splitF_reserve hf hg (by omega)
  · intro hfn hgn
    cases r with
    | zero =>
      obtain ⟨n, hn, hne⟩ := hfn
      have : n = 0 := by omega
      exact False.elim (hne (congrArg f this))
    | succ r =>
      exact (newtonCone_last_strict_iff (newtonCone_splitF hf hg)).mp
        (newton_splitF_last_strict hf hg hfn hgn)

end CoefficientwiseRigidity.Kernel
