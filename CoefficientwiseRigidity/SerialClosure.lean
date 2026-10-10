import CoefficientwiseRigidity.SerialDifference

/-!
K2: general serial closure for all finite slices, including dense outputs.
The proof uses label-number induction and the independently proved two-label
cancellation identity. It does not assume any of the four regime formulas,
general convolution positivity, or a graph-comparison theorem.
-/
namespace CoefficientwiseRigidity.Kernel

theorem overlapRank_reduce {M p q : ℕ} (hp : p ≤ M) (hq : q ≤ M) :
    overlapRank (M + 2) (p + 1) (q + 1) = overlapRank M p q + 1 := by
  dsimp [overlapRank, overlapShift]
  omega

/-- Paper K2, with the original concrete sum and no additional proof premises. -/
theorem serial_newton_closure (M : ℕ) :
    ∀ (p m q : ℕ), p ≤ M → m ≤ M → q ≤ M → ∀ (f g : ℕ → ℚ),
    NewtonCone (overlapRank M p m) f → NewtonCone (overlapRank M m q) g →
    ∃ h : ℕ → ℚ, NewtonCone (overlapRank M p q) h ∧
      ∀ (A : Slice M p) (B : Slice M q), serial (m := m) f g A B = h (overlap A B) := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro p m q hp hm hq f g hf hg
    obtain ⟨h, hh⟩ := exists_serial_profile (m := m) hp hq f g
    have h0 : 0 ≤ h 0 := serial_profile_nonneg hp hq hf hg hh (Nat.zero_le _)
    by_cases hr : overlapRank M p q = 0
    · refine ⟨h, ?_, hh⟩
      rw [hr, newtonCone_iff_differences, differenceCone_zero_iff]
      exact h0
    by_cases hm0 : m = 0
    · exact serial_endpoint_closure (Or.inl hm0) hf hg
    by_cases hmM : m = M
    · exact serial_endpoint_closure (Or.inr hmM) hf hg
    have hp0 : 0 < p := by dsimp [overlapRank, overlapShift] at hr; omega
    have hq0 : 0 < q := by dsimp [overlapRank, overlapShift] at hr; omega
    have hpM : p < M := by dsimp [overlapRank, overlapShift] at hr; omega
    have hqM : q < M := by dsimp [overlapRank, overlapShift] at hr; omega
    have hM : 2 ≤ M := by omega
    obtain ⟨N, rfl⟩ : ∃ N, M = N + 2 := ⟨M - 2, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    have hp' : p ≤ N := by omega
    have hm' : m ≤ N := by omega
    have hq' : q ≤ N := by omega
    have hf' : NewtonCone (overlapRank N p m + 1) f := by
      simpa only [overlapRank_reduce hp' hm'] using hf
    have hg' : NewtonCone (overlapRank N m q + 1) g := by
      simpa only [overlapRank_reduce hm' hq'] using hg
    obtain ⟨hred, hredCone, hredEq⟩ := ih N (by omega) p m q hp' hm' hq'
      (delta f) (delta g) (newtonCone_delta hf') (newtonCone_delta hg')
    refine ⟨h, ?_, hh⟩
    rw [overlapRank_reduce hp' hq', newtonCone_succ_iff]
    refine ⟨h0, ?_⟩
    apply (newtonCone_congr (f := delta h) (g := hred) ?_).mpr hredCone
    intro z hz
    let A : Slice N p := ⟨initialSegment N p, card_prefix N p hp'⟩
    obtain ⟨B, hB⟩ := exists_overlap A hq' z hz
    have hd := serial_profile_difference hh A B
    rw [hredEq A B, hB] at hd
    exact hd

end CoefficientwiseRigidity.Kernel
