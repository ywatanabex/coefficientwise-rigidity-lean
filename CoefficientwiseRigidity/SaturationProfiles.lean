import CoefficientwiseRigidity.CoverIntersections

/-! Capped binomial profiles and their positive Pascal decomposition (C4). -/
namespace CoefficientwiseRigidity.Saturation
open Finset Compression
open scoped Classical
noncomputable section

def capped (a b d : ℕ) : ℚ := ((min d b).choose a : ℚ)
def threshold (b d : ℕ) : ℚ := if b ≤ d then 1 else 0
def pascalWeight (a b : ℕ) : ℚ := ((b - 1).choose (a - 1) : ℚ)

theorem capped_nonneg (a b d : ℕ) : 0 ≤ capped a b d := by
  exact Nat.cast_nonneg _

theorem capped_mono (a b : ℕ) : Monotone (capped a b) := by
  intro x y h
  exact Nat.cast_le.mpr (Nat.choose_le_choose a (min_le_min_right b h))

theorem threshold_nonneg (b d : ℕ) : 0 ≤ threshold b d := by
  unfold threshold; split <;> norm_num

theorem threshold_mono (b : ℕ) : Monotone (threshold b) := by
  intro x y h
  unfold threshold
  split_ifs with hx hy hy <;> try norm_num
  exact (hy (hx.trans h)).elim

theorem pascalWeight_nonneg (a b : ℕ) : 0 ≤ pascalWeight a b := by
  exact Nat.cast_nonneg _

theorem pascalWeight_pos {a b : ℕ} (hab : a ≤ b) : 0 < pascalWeight a b := by
  exact Nat.cast_pos.mpr (Nat.choose_pos (Nat.sub_le_sub_right hab 1))

theorem capped_split {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) (d : ℕ) :
    capped a b d = capped a (b - 1) d + pascalWeight a b * threshold b d := by
  by_cases hd : b ≤ d
  · have hb : 0 < b := ha.trans_le hab
    have he : b - 1 + 1 = b := by omega
    have hp := Nat.choose_succ_left (b - 1) a ha
    rw [he] at hp
    simp only [capped,pascalWeight,threshold,if_pos hd,min_eq_right hd,
      min_eq_right (show b - 1 ≤ d by omega),mul_one]
    exact_mod_cast (hp.trans (Nat.add_comm _ _))
  · have hdb : d ≤ b - 1 := by omega
    simp [capped,threshold,hd,min_eq_left hdb,min_eq_left (show d ≤ b by omega)]

theorem capped_eq_choose {d b : ℕ} (a : ℕ) (hd : d ≤ b) :
    capped a b d = (d.choose a : ℚ) := by simp [capped,min_eq_left hd]

theorem threshold_eq_choose {d b : ℕ} (hd : d ≤ b) :
    threshold b d = (d.choose b : ℚ) := by
  by_cases he : d = b
  · subst d; simp [threshold]
  · have hlt : d < b := lt_of_le_of_ne hd he
    simp [threshold,not_le.mpr hlt,Nat.choose_eq_zero_of_lt hlt]

theorem capped_same_remainder {a : ℕ} (ha : 0 < a) (d : ℕ) :
    capped a (a - 1) d = 0 := by
  have h : min d (a - 1) < a := (min_le_right _ _).trans_lt (by omega)
  simp [capped,Nat.choose_eq_zero_of_lt h]

end
end CoefficientwiseRigidity.Saturation
