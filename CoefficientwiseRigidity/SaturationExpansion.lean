import CoefficientwiseRigidity.SaturationProfiles
import CoefficientwiseRigidity.ColumnLinearity

/-! The full subset expansion: each proper-subset surplus is a product-cone comparison. -/
namespace CoefficientwiseRigidity.Saturation
open Finset Compression Intersections Structure
open scoped Classical
noncomputable section
variable {I : Type*} [Fintype I]

def mixedCost (a b : I → ℕ) (T : Finset I) (d : I → ℕ) : ℚ :=
  ∏ i, if i ∈ T then threshold (b i) (d i) else capped (a i) (b i - 1) (d i)

def weight (a b : I → ℕ) (T : Finset I) : ℚ := ∏ i ∈ T, pascalWeight (a i) (b i)

omit [Fintype I] in
theorem weight_nonneg (a b : I → ℕ) (T : Finset I) : 0 ≤ weight a b T :=
  Finset.prod_nonneg (fun _ _ => pascalWeight_nonneg _ _)

omit [Fintype I] in
theorem weight_pos (a b : I → ℕ) (hab : ∀ i, a i ≤ b i) (T : Finset I) : 0 < weight a b T :=
  Finset.prod_pos (fun i _ => pascalWeight_pos (hab i))

theorem mixedCost_cone (a b : I → ℕ) (T : Finset I) : ProductCone (mixedCost a b T) := by
  apply ProductCone.prod (I := I) (A := ℕ)
    (fun i n => if i ∈ T then threshold (b i) n else capped (a i) (b i - 1) n)
  · intro i n
    split_ifs
    · exact threshold_nonneg _ _
    · exact capped_nonneg _ _ _
  · intro i x y h
    split_ifs
    · exact threshold_mono _ h
    · exact capped_mono _ _ h

theorem mixedCost_factor (a b : I → ℕ) (T : Finset I) (d : I → ℕ) :
    mixedCost a b T d = (∏ i ∈ T, threshold (b i) (d i)) *
      ∏ i ∈ Tᶜ, capped (a i) (b i - 1) (d i) := by
  unfold mixedCost
  rw [Finset.prod_ite]
  congr 1 <;> congr 1 <;> ext i <;> simp

theorem product_expansion (a b : I → ℕ) (ha : ∀ i, 0 < a i)
    (hab : ∀ i, a i ≤ b i) (d : I → ℕ) :
    (∏ i, capped (a i) (b i) (d i)) = ∑ T : Finset I, weight a b T * mixedCost a b T d := by
  simp_rw [capped_split (ha _) (hab _),add_comm (capped _ _ _)]
  rw [Fintype.prod_add]
  apply Finset.sum_congr rfl
  intro T _
  rw [mixedCost_factor,Finset.prod_mul_distrib]
  unfold weight
  ring

theorem mixedCost_univ (a b : I → ℕ) (d : I → ℕ) :
    mixedCost a b univ d = ∏ i, threshold (b i) (d i) := by simp [mixedCost]

variable {V : Type} [Fintype V] {G : SimpleGraph V} {M : ℕ}

def coneDeficit (b : Bipartition G) (σ : LeftRows b → V → Equiv.Perm (Fin M))
    (q : V → ℕ) (F : (LeftRows b → ℕ) → ℚ) : ℚ :=
  sumSet q (columnSet b) (fun Q => F (ranks (graphRows b) (fun _ _ => Equiv.refl (Fin M)) Q)) (fun _ => ∅) -
  sumSet q (columnSet b) (fun Q => F (ranks (graphRows b) σ Q)) (fun _ => ∅)

theorem coneDeficit_nonneg (b : Bipartition G) (hg : ChordalBipartite G)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ)
    {F : (LeftRows b → ℕ) → ℚ} (hF : ProductCone F) : 0 ≤ coneDeficit b σ q F :=
  sub_nonneg.mpr (graph_cone_comparison b hg σ q hF (fun _ => ∅))

theorem coneDeficit_expansion (b : Bipartition G)
    (σ : LeftRows b → V → Equiv.Perm (Fin M)) (q : V → ℕ) (a c : LeftRows b → ℕ)
    (ha : ∀ i, 0 < a i) (hac : ∀ i, a i ≤ c i) :
    coneDeficit b σ q (fun d => ∏ i, capped (a i) (c i) (d i)) =
      ∑ T : Finset (LeftRows b), weight a c T * coneDeficit b σ q (mixedCost a c T) := by
  simp only [coneDeficit,product_expansion a c ha hac,sumSet_sum,sumSet_mul,
    ← Finset.sum_sub_distrib,← mul_sub]

end
end CoefficientwiseRigidity.Saturation
