import CoefficientwiseRigidity.CompressionSets

/-! Exact nonnegative product rearrangement and one simultaneous compression. -/
namespace CoefficientwiseRigidity.Compression
open Finset
open scoped Classical
noncomputable section
variable {I α : Type*} [Fintype I] [Fintype α]

/-- The two-block product inequality uses no division, including zero factors. -/
theorem prod_pair_le (f g : I → ℚ) (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    (∏ i, f i) + (∏ i, g i) ≤ (∏ i, max (f i) (g i)) + ∏ i, min (f i) (g i) := by
  let A := Finset.univ.filter (fun i => f i ≤ g i)
  let B := Finset.univ.filter (fun i => ¬ f i ≤ g i)
  have hprod (h : I → ℚ) : (∏ i, h i) = (∏ i ∈ A, h i) * ∏ i ∈ B, h i :=
    (Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => f i ≤ g i) h).symm
  have hmax : (∏ i, max (f i) (g i)) = (∏ i ∈ A, g i) * ∏ i ∈ B, f i := by
    rw [hprod]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      exact max_eq_right (Finset.mem_filter.mp hi).2
    · apply Finset.prod_congr rfl
      intro i hi
      exact max_eq_left (le_of_not_ge (Finset.mem_filter.mp hi).2)
  have hmin : (∏ i, min (f i) (g i)) = (∏ i ∈ A, f i) * ∏ i ∈ B, g i := by
    rw [hprod]
    congr 1
    · apply Finset.prod_congr rfl
      intro i hi
      exact min_eq_left (Finset.mem_filter.mp hi).2
    · apply Finset.prod_congr rfl
      intro i hi
      exact min_eq_right (le_of_not_ge (Finset.mem_filter.mp hi).2)
  have hA : (∏ i ∈ A, f i) ≤ ∏ i ∈ A, g i :=
    Finset.prod_le_prod (fun i _ => hf i) (fun i hi => (Finset.mem_filter.mp hi).2)
  have hB : (∏ i ∈ B, g i) ≤ ∏ i ∈ B, f i :=
    Finset.prod_le_prod (fun i _ => hg i) (fun i hi => le_of_not_ge (Finset.mem_filter.mp hi).2)
  have hh := mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hB)
  rw [hmax,hmin,hprod f,hprod g]
  nlinarith

def productCost (h : I → ℕ → ℚ) (D : I → Finset α) (Q : Finset α) : ℚ :=
  ∏ i, h i (Q ∩ D i).card

def sliceSum (q : ℕ) (h : I → ℕ → ℚ) (D : I → Finset α) : ℚ :=
  ∑ Q : Finset α, if Q.card = q then productCost h D Q else 0

omit [Fintype α] in
theorem productCost_pair_le (a b : α) (hab : a ≠ b) (h : I → ℕ → ℚ)
    (hn : ∀ i n, 0 ≤ h i n) (hm : ∀ i, Monotone (h i)) (D : I → Finset α)
    (Q : Finset α) :
    productCost h D Q + productCost h D (swapSet a b Q) ≤
      productCost h (fun i => shift a b (D i)) Q +
        productCost h (fun i => shift a b (D i)) (swapSet a b Q) := by
  have horiented (P : Finset α) (ha : a ∈ P) (hb : b ∉ P) :
      productCost h D P + productCost h D (swapSet a b P) ≤
        productCost h (fun i => shift a b (D i)) P +
          productCost h (fun i => shift a b (D i)) (swapSet a b P) := by
    have hsa : a ∉ swapSet a b P := by simpa [mem_swapSet] using hb
    have hsb : b ∈ swapSet a b P := by simpa [mem_swapSet] using ha
    have hmax (i : I) : h i (P ∩ shift a b (D i)).card =
        max (h i (P ∩ D i).card) (h i (swapSet a b P ∩ D i).card) := by
      rw [inter_shift_max hab P (D i) ha hb,(hm i).map_max]
    have hmin (i : I) : h i (swapSet a b P ∩ shift a b (D i)).card =
        min (h i (P ∩ D i).card) (h i (swapSet a b P ∩ D i).card) := by
      rw [inter_shift_min hab _ (D i) hsa hsb,swapSet_involutive,(hm i).map_min,min_comm]
    simp only [productCost,hmax,hmin]
    exact prod_pair_le _ _ (fun i => hn i _) (fun i => hn i _)
  by_cases ha : a ∈ Q <;> by_cases hb : b ∈ Q
  · have hQ : a ∈ Q ↔ b ∈ Q := by simp [ha,hb]
    simp only [swapSet_fixed Q hQ,productCost,inter_shift_fixed hab Q _ hQ,le_refl]
  · exact horiented Q ha hb
  · have hsa : a ∈ swapSet a b Q := by simpa [mem_swapSet] using hb
    have hsb : b ∉ swapSet a b Q := by simpa [mem_swapSet] using ha
    simpa only [swapSet_involutive,add_comm] using horiented (swapSet a b Q) hsa hsb
  · have hQ : a ∈ Q ↔ b ∈ Q := by simp [ha,hb]
    simp only [swapSet_fixed Q hQ,productCost,inter_shift_fixed hab Q _ hQ,le_refl]

/-- Pairwise orbit comparison summed without dividing by an orbit size. -/
theorem sum_le_of_pair_le {T : Type*} [Fintype T] (e : Equiv.Perm T) (f g : T → ℚ)
    (h : ∀ x, f x + f (e x) ≤ g x + g (e x)) : ∑ x, f x ≤ ∑ x, g x := by
  have hf : (∑ x, f (e x)) = ∑ x, f x := Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hg : (∑ x, g (e x)) = ∑ x, g x := Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hs := Finset.sum_le_sum (fun x (_ : x ∈ (Finset.univ : Finset T)) => h x)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,hf,hg] at hs
  linarith

theorem sliceSum_shift_le (a b : α) (hab : a ≠ b) (q : ℕ) (h : I → ℕ → ℚ)
    (hn : ∀ i n, 0 ≤ h i n) (hm : ∀ i, Monotone (h i)) (D : I → Finset α) :
    sliceSum q h D ≤ sliceSum q h (fun i => shift a b (D i)) := by
  apply sum_le_of_pair_le (Equiv.swap a b).finsetCongr
  intro Q
  change (if Q.card = q then _ else _) +
    (if (swapSet a b Q).card = q then _ else _) ≤ _
  rw [card_swapSet]
  by_cases hq : Q.card = q
  · simpa only [Equiv.finsetCongr_apply,Finset.card_map,hq,if_true,swapSet]
      using productCost_pair_le a b hab h hn hm D Q
  · simp [Equiv.finsetCongr_apply,hq,card_swapSet]

theorem sliceSum_map (e : Equiv.Perm α) (q : ℕ) (h : I → ℕ → ℚ) (D : I → Finset α) :
    sliceSum q h (fun i => (D i).map e.toEmbedding) = sliceSum q h D := by
  symm
  apply Fintype.sum_equiv e.finsetCongr
  intro Q
  simp only [Equiv.finsetCongr_apply,Finset.card_map,productCost,← Finset.map_inter]

theorem sliceSum_shift_eq_of_nested (a b : α) (hab : a ≠ b) (q : ℕ)
    (h : I → ℕ → ℚ) (D : I → Finset α) (hD : ∀ i j, D i ⊆ D j ∨ D j ⊆ D i) :
    sliceSum q h (fun i => shift a b (D i)) = sliceSum q h D := by
  rcases nested_shift_common D hab hD with he | he
  · simp only [he]
  · simp only [he,swapSet]
    exact sliceSum_map _ q h D

end
end CoefficientwiseRigidity.Compression
