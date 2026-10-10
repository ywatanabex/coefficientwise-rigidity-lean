import CoefficientwiseRigidity.GraphSaturation

/-! C4a as an exact identity of integers: explicit mixed counts and nonnegative differences. -/
namespace CoefficientwiseRigidity.Saturation
open Finset Structure Intersections
open scoped Classical
noncomputable section
variable {I : Type*} [Fintype I]

def weightNat (a c : I → ℕ) (T : Finset I) : ℕ :=
  ∏ i ∈ T, (c i - 1).choose (a i - 1)

def mixedNat (a c : I → ℕ) (T : Finset I) (d : I → ℕ) : ℕ :=
  ∏ i, if i ∈ T then (if c i ≤ d i then 1 else 0) else (min (d i) (c i - 1)).choose (a i)

omit [Fintype I] in
theorem weightNat_cast (a c : I → ℕ) (T : Finset I) :
    (weightNat a c T : ℚ) = weight a c T := by
  simp [weightNat,weight,pascalWeight]

theorem mixedNat_cast (a c : I → ℕ) (T : Finset I) (d : I → ℕ) :
    (mixedNat a c T d : ℚ) = mixedCost a c T d := by
  simp [mixedNat,mixedCost,threshold,capped,Nat.cast_ite]

variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

def mixedCount (b : Bipartition G) (σ : LeftRows b → V → Equiv.Perm (Fin M))
    (q : V → ℕ) (a c : LeftRows b → ℕ) (T : Finset (LeftRows b)) : ℕ :=
  ∑ Q : V → Finset (Fin M), if ValidOn q (columnSet b) (fun _ => ∅) Q then
    mixedNat a c T (ranks (graphRows b) σ Q) else 0

theorem mixedCount_cast (b : Bipartition G) (σ : LeftRows b → V → Equiv.Perm (Fin M))
    (q : V → ℕ) (a c : LeftRows b → ℕ) (T : Finset (LeftRows b)) :
    (mixedCount b σ q a c T : ℚ) = sumSet q (columnSet b)
      (fun Q => mixedCost a c T (ranks (graphRows b) σ Q)) (fun _ => ∅) := by
  simp [mixedCount,sumSet_eq_assignment_sum,mixedNat_cast,Nat.cast_ite]

def mixedDeficit (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (T : Finset (LeftRows b)) : ℤ :=
  (mixedCount b (fun _ _ => Equiv.refl (Fin M)) (columnRanks M a) (rowRanks b a) (rowCaps b M a) T : ℤ) -
    mixedCount b (coverGains b X) (columnRanks M a) (rowRanks b a) (rowCaps b M a) T

theorem mixedDeficit_cast (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (T : Finset (LeftRows b)) :
    (mixedDeficit b X a T : ℚ) = coneDeficit b (coverGains b X) (columnRanks M a)
      (mixedCost (rowRanks b a) (rowCaps b M a) T) := by
  simp only [mixedDeficit,Int.cast_sub,Int.cast_natCast,mixedCount_cast,coneDeficit]

theorem mixedDeficit_nonneg (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (T : Finset (LeftRows b)) : 0 ≤ mixedDeficit b X a T := by
  have h := coneDeficit_nonneg b hg (coverGains b X) (columnRanks M a)
    (mixedCost_cone (rowRanks b a) (rowCaps b M a) T)
  rw [← mixedDeficit_cast] at h
  exact_mod_cast h

variable [DecidableEq V]

def integerSurplus (b : Bipartition G) (X : Cover G M) (a : V → ℕ) : ℤ :=
  ∑ T ∈ (univ : Finset (Finset (LeftRows b))).erase univ,
    (weightNat (rowRanks b a) (rowCaps b M a) T : ℤ) * mixedDeficit b X a T

theorem integerSurplus_cast (b : Bipartition G) (X : Cover G M) (a : V → ℕ) :
    (integerSurplus b X a : ℚ) = surplus b X a := by
  simp only [integerSurplus,Int.cast_sum,Int.cast_mul,Int.cast_natCast,weightNat_cast,
    mixedDeficit_cast,surplus]

theorem integerSurplus_nonneg (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) : 0 ≤ integerSurplus b X a := by
  apply Finset.sum_nonneg
  intro T _
  exact mul_nonneg (Int.natCast_nonneg _) (mixedDeficit_nonneg b hg X a T)

theorem saturation_integer_identity (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : Feasible G M a) (hp : Positive a) :
    deficit X a = (multiplier b M a : ℤ) * deficit X (occupation b M a) + integerSurplus b X a := by
  have h := saturation_identity b X a ha hp
  rw [← integerSurplus_cast] at h
  exact_mod_cast h

theorem right_saturation_integer_identity (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : Feasible G M a) (hp : Positive a) :
    deficit X a = (multiplier b.flip M a : ℤ) * deficit X (rightOccupation b M a) +
      integerSurplus b.flip X a := saturation_integer_identity b.flip X a ha hp

end
end CoefficientwiseRigidity.Saturation
