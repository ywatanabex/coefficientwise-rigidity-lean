import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Tactic

/-!
Paper K1 (VERIFIED paper result): the nonnegative Newton cone on the
finite interval 0,...,r. Functions are represented on ℕ for convenience,
but membership depends only on values at or below r (`newtonCone_congr`).
No positivity or extrapolation beyond that endpoint is assumed.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset

def delta (f : ℕ → ℚ) : ℕ → ℚ := fwdDiff 1 f

def newtonSum (r : ℕ) (c : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ d ∈ range (r + 1), c d * (n.choose d : ℚ)

/-- The explicit finite, nonnegative binomial expansion used in the paper. -/
def NewtonCone (r : ℕ) (f : ℕ → ℚ) : Prop :=
  ∃ c : ℕ → ℚ, (∀ d, d ≤ r → 0 ≤ c d) ∧
    ∀ n, n ≤ r → f n = newtonSum r c n

/-- An auxiliary criterion; its equivalence with `NewtonCone` is proved below. -/
def DifferenceCone (r : ℕ) (f : ℕ → ℚ) : Prop :=
  ∀ d, d ≤ r → 0 ≤ (delta^[d] f) 0

theorem differenceCone_zero_iff (f : ℕ → ℚ) : DifferenceCone 0 f ↔ 0 ≤ f 0 := by
  simp [DifferenceCone]

theorem differenceCone_succ_iff (r : ℕ) (f : ℕ → ℚ) :
    DifferenceCone (r + 1) f ↔ 0 ≤ f 0 ∧ DifferenceCone r (delta f) := by
  constructor
  · intro h
    refine ⟨h 0 (by omega), ?_⟩
    intro d hd
    simpa only [Function.iterate_succ_apply] using h (d + 1) (by omega)
  · rintro ⟨h0, hd⟩ d hle
    cases d with
    | zero => simpa using h0
    | succ d => simpa only [Function.iterate_succ_apply] using hd d (by omega)

theorem differenceCone_restrict {r s : ℕ} {f : ℕ → ℚ}
    (h : DifferenceCone r f) (hs : s ≤ r) : DifferenceCone s f :=
  fun d hd => h d (hd.trans hs)

theorem differenceCone_add {r : ℕ} {f g : ℕ → ℚ}
    (hf : DifferenceCone r f) (hg : DifferenceCone r g) :
    DifferenceCone r (fun n => f n + g n) := by
  intro d hd
  change 0 ≤ ((fwdDiff (1 : ℕ))^[d] (f + g)) 0
  rw [fwdDiff_iter_add]
  exact add_nonneg (hf d hd) (hg d hd)

theorem differenceCone_scale {r : ℕ} {f : ℕ → ℚ} (c : ℚ) (hc : 0 ≤ c)
    (hf : DifferenceCone r f) : DifferenceCone r (fun n => c * f n) := by
  intro d hd
  change 0 ≤ ((fwdDiff (1 : ℕ))^[d] (c • f)) 0
  rw [fwdDiff_iter_const_smul]
  exact mul_nonneg hc (hf d hd)

theorem differenceCone_const (r : ℕ) (c : ℚ) (hc : 0 ≤ c) :
    DifferenceCone r (fun _ => c) := by
  induction r generalizing c with
  | zero => exact (differenceCone_zero_iff _).mpr hc
  | succ r ih =>
    rw [differenceCone_succ_iff]
    refine ⟨hc, ?_⟩
    simpa [delta, fwdDiff_const] using ih 0 (le_refl 0)

theorem differenceCone_sum {ι : Type*} (s : Finset ι) {r : ℕ} (f : ι → ℕ → ℚ)
    (h : ∀ i ∈ s, DifferenceCone r (f i)) :
    DifferenceCone r (fun n => ∑ i ∈ s, f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differenceCone_const r 0 (le_refl 0)
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact differenceCone_add (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

theorem delta_choose (d : ℕ) :
    delta (fun n => (n.choose (d + 1) : ℚ)) = fun n => (n.choose d : ℚ) := by
  funext n
  simp [delta, fwdDiff, Nat.choose_succ_succ']

theorem differenceCone_choose (r d : ℕ) :
    DifferenceCone r (fun n => (n.choose d : ℚ)) := by
  induction r generalizing d with
  | zero => exact (differenceCone_zero_iff _).mpr (Nat.cast_nonneg _)
  | succ r ih =>
    rw [differenceCone_succ_iff]
    refine ⟨Nat.cast_nonneg _, ?_⟩
    cases d with
    | zero => simpa [delta, fwdDiff] using differenceCone_const r 0 (le_refl 0)
    | succ d => rw [delta_choose]; exact ih d

theorem differenceCone_newtonSum (r s : ℕ) (c : ℕ → ℚ)
    (hc : ∀ d, d ≤ s → 0 ≤ c d) : DifferenceCone r (newtonSum s c) := by
  apply differenceCone_sum
  intro d hd
  exact differenceCone_scale (c d) (hc d (by have := mem_range.mp hd; omega))
    (differenceCone_choose r d)

theorem differenceCone_congr {r : ℕ} {f g : ℕ → ℚ}
    (heq : ∀ n, n ≤ r → f n = g n) : DifferenceCone r f ↔ DifferenceCone r g := by
  have hiter : ∀ d, d ≤ r → (delta^[d] f) 0 = (delta^[d] g) 0 := by
    intro d hd
    change ((fwdDiff (1 : ℕ))^[d] f) 0 = ((fwdDiff (1 : ℕ))^[d] g) 0
    simp only [fwdDiff_iter_eq_sum_shift, zero_add, nsmul_eq_mul, Nat.cast_id, mul_one]
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq i (by have := Finset.mem_range.mp hi; omega)]
  constructor <;> intro h d hd
  · rw [← hiter d hd]; exact h d hd
  · rw [hiter d hd]; exact h d hd

theorem newton_expansion (f : ℕ → ℚ) {r n : ℕ} (hn : n ≤ r) :
    f n = newtonSum r (fun d => (delta^[d] f) 0) n := by
  have h := shift_eq_sum_fwdDiff_iter (1 : ℕ) f n 0
  simp only [zero_add, nsmul_eq_mul, Nat.cast_id, mul_one] at h
  rw [h, newtonSum]
  symm
  calc
    (∑ d ∈ range (r + 1), (delta^[d] f) 0 * (n.choose d : ℚ)) =
        ∑ d ∈ range (n + 1), (delta^[d] f) 0 * (n.choose d : ℚ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (by omega))
      intro d _ hd
      rw [Nat.choose_eq_zero_of_lt (by simp only [mem_range] at hd; omega)]
      simp
    _ = _ := by apply Finset.sum_congr rfl; intro d _; exact mul_comm _ _

theorem newtonCone_iff_differences {r : ℕ} {f : ℕ → ℚ} :
    NewtonCone r f ↔ DifferenceCone r f := by
  constructor
  · rintro ⟨c, hc, heq⟩
    exact (differenceCone_congr heq).mpr (differenceCone_newtonSum r r c hc)
  · intro h
    exact ⟨fun d => (delta^[d] f) 0, h, fun n hn => newton_expansion f hn⟩

theorem newtonCone_congr {r : ℕ} {f g : ℕ → ℚ}
    (heq : ∀ n, n ≤ r → f n = g n) : NewtonCone r f ↔ NewtonCone r g := by
  rw [newtonCone_iff_differences, newtonCone_iff_differences]
  exact differenceCone_congr heq

theorem newtonCone_succ_iff (r : ℕ) (f : ℕ → ℚ) :
    NewtonCone (r + 1) f ↔ 0 ≤ f 0 ∧ NewtonCone r (delta f) := by
  simp only [newtonCone_iff_differences, differenceCone_succ_iff]

theorem differenceCone_shift {r : ℕ} {f : ℕ → ℚ}
    (hf : DifferenceCone (r + 1) f) : DifferenceCone r (fun n => f (n + 1)) := by
  have heq : (fun n => f (n + 1)) = fun n => f n + delta f n := by
    funext n
    simp [delta, fwdDiff]
  rw [heq]
  exact differenceCone_add (differenceCone_restrict hf (by omega))
    ((differenceCone_succ_iff r f).mp hf).2

theorem delta_mul (f g : ℕ → ℚ) :
    delta (fun n => f n * g n) =
      fun n => delta f n * g (n + 1) + f n * delta g n := by
  funext n
  simp only [delta, fwdDiff]
  ring

theorem differenceCone_mul {r : ℕ} {f g : ℕ → ℚ}
    (hf : DifferenceCone r f) (hg : DifferenceCone r g) :
    DifferenceCone r (fun n => f n * g n) := by
  induction r generalizing f g with
  | zero =>
    apply (differenceCone_zero_iff _).mpr
    exact mul_nonneg (hf 0 (le_refl 0)) (hg 0 (le_refl 0))
  | succ r ih =>
    apply (differenceCone_succ_iff r _).mpr
    refine ⟨mul_nonneg (hf 0 (by omega)) (hg 0 (by omega)), ?_⟩
    rw [delta_mul]
    exact differenceCone_add
      (ih ((differenceCone_succ_iff r f).mp hf).2 (differenceCone_shift hg))
      (ih (differenceCone_restrict hf (by omega)) ((differenceCone_succ_iff r g).mp hg).2)

theorem newtonCone_const (r : ℕ) (c : ℚ) (hc : 0 ≤ c) : NewtonCone r (fun _ => c) :=
  newtonCone_iff_differences.mpr (differenceCone_const r c hc)

theorem newtonCone_choose (r d : ℕ) : NewtonCone r (fun n => (n.choose d : ℚ)) :=
  newtonCone_iff_differences.mpr (differenceCone_choose r d)

theorem newtonCone_restrict {r s : ℕ} {f : ℕ → ℚ}
    (hf : NewtonCone r f) (hs : s ≤ r) : NewtonCone s f :=
  newtonCone_iff_differences.mpr
    (differenceCone_restrict (newtonCone_iff_differences.mp hf) hs)

theorem newtonCone_add {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g) : NewtonCone r (fun n => f n + g n) :=
  newtonCone_iff_differences.mpr (differenceCone_add
    (newtonCone_iff_differences.mp hf) (newtonCone_iff_differences.mp hg))

theorem newtonCone_scale {r : ℕ} {f : ℕ → ℚ} (c : ℚ) (hc : 0 ≤ c)
    (hf : NewtonCone r f) : NewtonCone r (fun n => c * f n) :=
  newtonCone_iff_differences.mpr (differenceCone_scale c hc (newtonCone_iff_differences.mp hf))

theorem newtonCone_sum {ι : Type*} (s : Finset ι) {r : ℕ} (f : ι → ℕ → ℚ)
    (hf : ∀ i ∈ s, NewtonCone r (f i)) : NewtonCone r (fun n => ∑ i ∈ s, f i n) :=
  newtonCone_iff_differences.mpr
    (differenceCone_sum s f (fun i hi => newtonCone_iff_differences.mp (hf i hi)))

theorem newtonCone_mul {r : ℕ} {f g : ℕ → ℚ}
    (hf : NewtonCone r f) (hg : NewtonCone r g) : NewtonCone r (fun n => f n * g n) :=
  newtonCone_iff_differences.mpr (differenceCone_mul
    (newtonCone_iff_differences.mp hf) (newtonCone_iff_differences.mp hg))

/-- The domain really decreases: no difference at the original right endpoint is used. -/
theorem newtonCone_delta {r : ℕ} {f : ℕ → ℚ}
    (hf : NewtonCone (r + 1) f) : NewtonCone r (delta f) :=
  newtonCone_iff_differences.mpr
    ((differenceCone_succ_iff r f).mp (newtonCone_iff_differences.mp hf)).2

theorem newtonCone_shift {r : ℕ} {f : ℕ → ℚ}
    (hf : NewtonCone (r + 1) f) : NewtonCone r (fun n => f (n + 1)) :=
  newtonCone_iff_differences.mpr (differenceCone_shift (newtonCone_iff_differences.mp hf))

def integral (c : ℚ) (f : ℕ → ℚ) (n : ℕ) : ℚ := c + ∑ i ∈ range n, f i

theorem integral_zero (c : ℚ) (f : ℕ → ℚ) : integral c f 0 = c := by
  simp [integral]

theorem delta_integral (c : ℚ) (f : ℕ → ℚ) : delta (integral c f) = f := by
  funext n
  simp [delta, fwdDiff, integral, Finset.sum_range_succ]

theorem newtonCone_integral {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone r f)
    (c : ℚ) (hc : 0 ≤ c) : NewtonCone (r + 1) (integral c f) := by
  rw [newtonCone_iff_differences, differenceCone_succ_iff, integral_zero, delta_integral]
  exact ⟨hc, newtonCone_iff_differences.mp hf⟩

theorem newtonCone_nonneg {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone r f)
    {n : ℕ} (hn : n ≤ r) : 0 ≤ f n := by
  obtain ⟨c, hc, heq⟩ := hf
  rw [heq n hn, newtonSum]
  apply Finset.sum_nonneg
  intro d hd
  exact mul_nonneg (hc d (by have := mem_range.mp hd; omega)) (Nat.cast_nonneg _)

theorem newtonCone_monotone {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone r f)
    {x y : ℕ} (hxy : x ≤ y) (hy : y ≤ r) : f x ≤ f y := by
  obtain ⟨c, hc, heq⟩ := hf
  rw [heq x (hxy.trans hy), heq y hy]
  apply Finset.sum_le_sum
  intro d hd
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (Nat.choose_le_choose d hxy))
    (hc d (by have := mem_range.mp hd; omega))

theorem integral_delta (f : ℕ → ℚ) (n : ℕ) : integral (f 0) (delta f) n = f n := by
  induction n with
  | zero => simp [integral]
  | succ n ih =>
    simp only [integral, Finset.sum_range_succ] at *
    simp only [delta, fwdDiff] at *
    linarith

theorem newtonCone_nonconstant_iff {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone r f) :
    (∃ n, n ≤ r ∧ f n ≠ f 0) ↔ f 0 < f r := by
  constructor
  · rintro ⟨n, hn, hne⟩
    have h0 := newtonCone_monotone hf (Nat.zero_le n) hn
    have h1 := newtonCone_monotone hf hn (le_refl r)
    exact (lt_of_le_of_ne h0 (Ne.symm hne)).trans_le h1
  · intro h
    exact ⟨r, le_refl r, ne_of_gt h⟩

/-- For a nonconstant cone function the *last* valid forward difference is positive. -/
theorem newtonCone_last_strict_iff {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone (r + 1) f) :
    f r < f (r + 1) ↔ (∃ n, n ≤ r + 1 ∧ f n ≠ f 0) := by
  rw [newtonCone_nonconstant_iff hf]
  constructor
  · intro h
    exact (newtonCone_monotone hf (Nat.zero_le r) (by omega)).trans_lt h
  · intro h
    by_contra hlast
    have hdlast : delta f r ≤ 0 := sub_nonpos.mpr (le_of_not_gt hlast)
    have hsum : (∑ i ∈ range (r + 1), delta f i) ≤ 0 := by
      apply Finset.sum_nonpos
      intro i hi
      exact (newtonCone_monotone (newtonCone_delta hf)
        (by have := mem_range.mp hi; omega) (le_refl r)).trans hdlast
    have hi := integral_delta f (r + 1)
    dsimp [integral] at hi
    linarith

theorem newtonCone_endpoint_pos {r : ℕ} {f : ℕ → ℚ} (hf : NewtonCone r f)
    (h : ∃ n, n ≤ r ∧ f n ≠ f 0) : 0 < f r :=
  (newtonCone_nonneg hf (Nat.zero_le r)).trans_lt ((newtonCone_nonconstant_iff hf).mp h)

theorem iter_delta_int_cast (f : ℕ → ℤ) (k : ℕ) :
    delta^[k] (fun n => (f n : ℚ)) = fun n => (((fwdDiff (1 : ℕ))^[k] f) n : ℚ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih]
    funext n
    simp [delta, fwdDiff]

theorem iter_delta_choose_zero (d k : ℕ) :
    (delta^[k] (fun n => (n.choose d : ℚ))) 0 = if k = d then 1 else 0 := by
  have h := congrFun (iter_delta_int_cast (fun n => (n.choose d : ℤ)) k) 0
  simpa only [Int.cast_natCast, fwdDiff_iter_choose_zero, Int.cast_ite,
    Int.cast_one, Int.cast_zero] using h

theorem iter_delta_newtonSum_zero (r : ℕ) (c : ℕ → ℚ) (k : ℕ) :
    (delta^[k] (newtonSum r c)) 0 = if k ≤ r then c k else 0 := by
  have heq : newtonSum r c = ∑ d ∈ range (r + 1), c d • (fun n => (n.choose d : ℚ)) := by
    funext n
    simp [newtonSum]
  rw [heq]
  change ((fwdDiff (1 : ℕ))^[k] (∑ d ∈ range (r + 1),
    c d • (fun n => (n.choose d : ℚ)))) 0 = _
  rw [fwdDiff_iter_finset_sum]
  simp only [Finset.sum_apply, fwdDiff_iter_const_smul, Pi.smul_apply, smul_eq_mul]
  change (∑ d ∈ range (r + 1), c d * (delta^[k] (fun n => (n.choose d : ℚ))) 0) = _
  simp_rw [iter_delta_choose_zero]
  simp [mul_ite, eq_comm, Nat.lt_succ_iff]

/-- Coefficients are forced by the finite values; a witness expansion is not arbitrary. -/
theorem newton_coefficients_unique {r : ℕ} {f : ℕ → ℚ} (c : ℕ → ℚ)
    (heq : ∀ n, n ≤ r → f n = newtonSum r c n) {k : ℕ} (hk : k ≤ r) :
    (delta^[k] f) 0 = c k := by
  have hiter : (delta^[k] f) 0 = (delta^[k] (newtonSum r c)) 0 := by
    change ((fwdDiff (1 : ℕ))^[k] f) 0 = ((fwdDiff (1 : ℕ))^[k] (newtonSum r c)) 0
    simp only [fwdDiff_iter_eq_sum_shift, zero_add, nsmul_eq_mul, Nat.cast_id, mul_one]
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq i (by have := mem_range.mp hi; omega)]
  rw [hiter, iter_delta_newtonSum_zero, if_pos hk]

theorem newtonCone_iter_delta {r k : ℕ} {f : ℕ → ℚ}
    (hf : NewtonCone r f) (hk : k ≤ r) : NewtonCone (r - k) (delta^[k] f) := by
  apply newtonCone_iff_differences.mpr
  intro d hd
  have h := newtonCone_iff_differences.mp hf (d + k) (by omega)
  simpa only [Function.iterate_add_apply] using h

theorem newtonCone_difference_nonneg {r k n : ℕ} {f : ℕ → ℚ}
    (hf : NewtonCone r f) (hkn : k + n ≤ r) : 0 ≤ (delta^[k] f) n :=
  newtonCone_nonneg (newtonCone_iter_delta hf (by omega)) (by omega)

end CoefficientwiseRigidity.Kernel
