import Mathlib.Tactic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
Paper G3/G4, algebra of a finite seam. These are genuine theorems for arbitrary
finite boundary fibres. Producing the fibre bounds and ordinary constants from
the graph classes remains a distinct obligation (G1/G2); no such premise is an axiom.
-/
namespace CoefficientwiseRigidity.Seam
open scoped BigOperators
variable {B : Type*} [Fintype B]

def total (K : B → ℚ) : ℚ := ∑ s, K s
def productTotal (K L : B → ℚ) : ℚ := ∑ s, K s * L s
def ordinaryTotal (c : ℚ) : ℚ := Fintype.card B * c
def ordinaryProduct (c d : ℚ) : ℚ := Fintype.card B * c * d

/-- G1's amplification step. Graph copy-closure must supply the premise for every k. -/
theorem pointwise_of_power_comparison (K : B → ℚ) (c : ℚ)
    (hK : ∀ s, 0 ≤ K s) (hc : 0 ≤ c)
    (hp : ∀ k : ℕ, (∑ s, K s ^ k) ≤ (Fintype.card B : ℚ) * c ^ k) :
    ∀ s, K s ≤ c := by
  intro s
  have hs : ∀ k, K s ^ k ≤ (Fintype.card B : ℚ) * c ^ k := by
    intro k
    exact le_trans (Finset.single_le_sum (fun t _ => pow_nonneg (hK t) k)
      (Finset.mem_univ s)) (hp k)
  rcases eq_or_lt_of_le hc with hz | hc
  · have h := hs 1
    simpa [← hz] using h
  · by_contra hn
    have hratio : 1 < K s / c := (one_lt_div hc).mpr (lt_of_not_ge hn)
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (Fintype.card B : ℚ) hratio
    have hb : (K s / c) ^ k ≤ (Fintype.card B : ℚ) := by
      rw [div_pow]
      exact (div_le_iff₀ (pow_pos hc k)).mpr (hs k)
    exact (not_lt_of_ge hb) hk

theorem deficit_identity (K L : B → ℚ) (c d : ℚ) :
    ordinaryProduct (B := B) c d - productTotal K L =
      d * (ordinaryTotal (B := B) c - total K) + ∑ s, K s * (d - L s) := by
  simp only [ordinaryProduct, productTotal, ordinaryTotal, total,
    mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

theorem total_le (K : B → ℚ) (c : ℚ) (hK : ∀ s, K s ≤ c) :
    total K ≤ ordinaryTotal (B := B) c := by
  calc
    total K ≤ ∑ _s : B, c := Finset.sum_le_sum (fun s _ => hK s)
    _ = ordinaryTotal (B := B) c := by simp [ordinaryTotal]

theorem product_le (K L : B → ℚ) (c d : ℚ)
    (hK0 : ∀ s, 0 ≤ K s) (hK : ∀ s, K s ≤ c)
    (hL : ∀ s, L s ≤ d) (hd : 0 ≤ d) :
    productTotal K L ≤ ordinaryProduct (B := B) c d := by
  calc
    productTotal K L ≤ ∑ _s : B, c * d :=
      Finset.sum_le_sum (fun s _ => le_trans
        (mul_le_mul_of_nonneg_left (hL s) (hK0 s))
        (mul_le_mul_of_nonneg_right (hK s) hd))
    _ = ordinaryProduct (B := B) c d := by simp [ordinaryProduct, mul_assoc]

theorem deficit_ge_left (K L : B → ℚ) (c d : ℚ)
    (hK0 : ∀ s, 0 ≤ K s) (hL : ∀ s, L s ≤ d) :
    d * (ordinaryTotal (B := B) c - total K) ≤
      ordinaryProduct (B := B) c d - productTotal K L := by
  rw [deficit_identity]
  have h : 0 ≤ ∑ s, K s * (d - L s) :=
    Finset.sum_nonneg (fun s _ => mul_nonneg (hK0 s) (sub_nonneg.mpr (hL s)))
  linarith

theorem total_eq_iff (K : B → ℚ) (c : ℚ) (hK : ∀ s, K s ≤ c) :
    total K = ordinaryTotal (B := B) c ↔ ∀ s, K s = c := by
  constructor
  · intro heq
    have hz : ∑ s, (c - K s) = 0 := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change ordinaryTotal (B := B) c - total K = 0
      rw [heq, sub_self]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun s (_ : s ∈ Finset.univ) => sub_nonneg.mpr (hK s))).mp hz
    intro s
    have := hall s (Finset.mem_univ s)
    linarith
  · intro h
    simp [total, h, ordinaryTotal]

theorem equality_iff (K L : B → ℚ) (c d : ℚ)
    (hK0 : ∀ s, 0 ≤ K s) (hL0 : ∀ s, 0 ≤ L s)
    (hK : ∀ s, K s ≤ c) (hL : ∀ s, L s ≤ d)
    (hc : 0 < c) (hd : 0 < d) :
    productTotal K L = ordinaryProduct (B := B) c d ↔
      total K = ordinaryTotal (B := B) c ∧ total L = ordinaryTotal (B := B) d := by
  constructor
  · intro heq
    have hk := total_le K c hK
    have hl := total_le L d hL
    have h₁ := deficit_ge_left K L c d hK0 hL
    have h₂ := deficit_ge_left L K d c hL0 hK
    have hswap : productTotal L K = productTotal K L := by
      simp [productTotal, mul_comm]
    rw [hswap] at h₂
    have hoswap : ordinaryProduct (B := B) d c = ordinaryProduct (B := B) c d := by
      unfold ordinaryProduct
      ring
    rw [hoswap, heq] at h₂
    rw [heq] at h₁
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    have hkc := (total_eq_iff K c hK).mp h₁
    have hld := (total_eq_iff L d hL).mp h₂
    simp [productTotal, hkc, hld, ordinaryProduct, mul_assoc]

/-- The original reduced ordinary coefficient is retained: no normalization factor. -/
theorem quantitative_step (K L : B → ℚ) (c d k R₁ R₁₂ d' : ℚ)
    (hK0 : ∀ s, 0 ≤ K s) (hL : ∀ s, L s ≤ d)
    (hd : 0 ≤ d) (hk : 0 ≤ k) (hR : 0 ≤ R₁)
    (hbound : k * R₁ ≤ ordinaryTotal (B := B) c - total K)
    (hinsert : d' ≤ d) (hfactor : R₁₂ = R₁ * d') :
    k * R₁₂ ≤ ordinaryProduct (B := B) c d - productTotal K L := by
  have h₁ := deficit_ge_left K L c d hK0 hL
  have h₂ := mul_le_mul_of_nonneg_left hbound hd
  have h₃ := mul_nonneg (mul_nonneg hk hR) (sub_nonneg.mpr hinsert)
  rw [hfactor]
  nlinarith

theorem relative_deficit_left (K L : B → ℚ) (c d : ℚ)
    (hK0 : ∀ s, 0 ≤ K s) (hL : ∀ s, L s ≤ d)
    (hP : 0 < ordinaryTotal (B := B) c) (hd : 0 < d) :
    (ordinaryTotal (B := B) c - total K) / ordinaryTotal (B := B) c ≤
      (ordinaryProduct (B := B) c d - productTotal K L) /
        ordinaryProduct (B := B) c d := by
  have he : ordinaryProduct (B := B) c d = ordinaryTotal (B := B) c * d := rfl
  have hPD : 0 < ordinaryProduct (B := B) c d := by rw [he]; exact mul_pos hP hd
  apply (div_le_div_iff₀ hP hPD).mpr
  have h := mul_le_mul_of_nonneg_left (deficit_ge_left K L c d hK0 hL) hP.le
  rw [he]
  nlinarith

end CoefficientwiseRigidity.Seam
