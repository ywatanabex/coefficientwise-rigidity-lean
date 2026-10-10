import CoefficientwiseRigidity.Compression

/-! The full increasing product cone: finite nonnegative linear combinations
of products of nonnegative monotone one-coordinate functions. -/
namespace CoefficientwiseRigidity.Compression
open Finset
open scoped Classical
noncomputable section
variable {I A B : Type*} [Fintype I] [Preorder A] [Preorder B]

inductive ProductCone : ((I → A) → ℚ) → Prop
  | zero : ProductCone (fun _ => 0)
  | prod (f : I → A → ℚ) (hn : ∀ i a, 0 ≤ f i a) (hm : ∀ i, Monotone (f i)) :
      ProductCone (fun d => ∏ i, f i (d i))
  | add {F G : (I → A) → ℚ} : ProductCone F → ProductCone G → ProductCone (fun d => F d + G d)
  | scale (c : ℚ) (hc : 0 ≤ c) {F : (I → A) → ℚ} :
      ProductCone F → ProductCone (fun d => c * F d)

theorem ProductCone.congr {F G : (I → A) → ℚ} (h : ProductCone F) (he : ∀ d, F d = G d) :
    ProductCone G := (funext he) ▸ h

theorem ProductCone.nonneg {F : (I → A) → ℚ} (h : ProductCone F) (d : I → A) : 0 ≤ F d := by
  induction h with
  | zero => exact le_refl _
  | prod f hn _ => exact Finset.prod_nonneg (fun i _ => hn i _)
  | add _ _ ih ih' => exact add_nonneg ih ih'
  | scale c hc _ ih => exact mul_nonneg hc ih

theorem ProductCone.sum {T : Type*} (s : Finset T) (F : T → (I → A) → ℚ)
    (h : ∀ t ∈ s, ProductCone (F t)) : ProductCone (fun d => ∑ t ∈ s, F t d) := by
  induction s using Finset.induction_on with
  | empty => simpa using (ProductCone.zero : ProductCone (fun _ : I → A => (0 : ℚ)))
  | @insert t s ht ih =>
    have h1 := h t (Finset.mem_insert_self _ _)
    have h2 := ih (fun u hu => h u (Finset.mem_insert_of_mem hu))
    simpa only [Finset.sum_insert ht] using h1.add h2

theorem ProductCone.comp_coordinate {F : (I → A) → ℚ} (h : ProductCone F)
    (φ : I → B → A) (hm : ∀ i, Monotone (φ i)) : ProductCone (fun d => F (fun i => φ i (d i))) := by
  induction h with
  | zero => exact .zero
  | prod f hn hf => exact .prod (fun i x => f i (φ i x)) (fun i x => hn i _) (fun i => (hf i).comp (hm i))
  | add _ _ ih ih' => exact ih.add ih'
  | scale c hc _ ih => exact ih.scale c hc

variable {M : ℕ}

def clampRank (M n : ℕ) : Fin (M + 1) := ⟨min n M,by omega⟩

theorem clampRank_mono (M : ℕ) : Monotone (clampRank M) := by
  intro n m h
  exact min_le_min_right M h

/-- Every cone on the paper's finite domain extends constantly above M. -/
theorem ProductCone.extend_finite {F : (I → Fin (M + 1)) → ℚ} (h : ProductCone F) :
    ProductCone (fun d : I → ℕ => F (fun i => clampRank M (d i))) :=
  h.comp_coordinate (fun _ => clampRank M) (fun _ => clampRank_mono M)

theorem ProductCone.restrict_finite {F : (I → ℕ) → ℚ} (h : ProductCone F) :
    ProductCone (fun d : I → Fin (M + 1) => F (fun i => (d i).val)) :=
  h.comp_coordinate (fun _ => Fin.val) (fun _ _ _ h => h)

theorem initialSegment_mono {n m : ℕ} (h : n ≤ m) : initialSegment M n ⊆ initialSegment M m := by
  intro x hx
  exact (mem_prefix M m x).mpr (((mem_prefix M n x).mp hx).trans_le h)

def mixedRanks (S : Finset I) (d : I → ℕ) (D : I → Finset (Fin M))
    (Q : Finset (Fin M)) : I → ℕ := fun i => if i ∈ S then (Q ∩ D i).card else d i

def setOperator (S : Finset I) (q : ℕ) (F : (I → ℕ) → ℚ)
    (D : I → Finset (Fin M)) (d : I → ℕ) : ℚ :=
  ∑ Q : Finset (Fin M), if Q.card = q then F (mixedRanks S d D Q) else 0

def prefixOperator (M : ℕ) (S : Finset I) (q : ℕ) (F : (I → ℕ) → ℚ) (d : I → ℕ) : ℚ :=
  setOperator S q F (fun i => initialSegment M (d i)) d

theorem ProductCone.prefixOperator {F : (I → ℕ) → ℚ} (h : ProductCone F)
    (M : ℕ) (S : Finset I) (q : ℕ) : ProductCone (prefixOperator M S q F) := by
  induction h with
  | zero =>
    apply ProductCone.zero.congr
    intro d
    simp [Compression.prefixOperator,setOperator]
  | prod f hn hf =>
    unfold Compression.prefixOperator setOperator
    apply ProductCone.sum
    intro Q _
    by_cases hq : Q.card = q
    · simp only [hq,if_true]
      change ProductCone (fun d => ∏ i, f i (if i ∈ S then (Q ∩ initialSegment M (d i)).card else d i))
      apply ProductCone.prod (fun i n => f i (if i ∈ S then (Q ∩ initialSegment M n).card else n))
      · intro i n
        exact hn i _
      · intro i n m hnm
        apply hf i
        by_cases hi : i ∈ S
        · simp only [hi,if_true]
          exact Finset.card_le_card (Finset.inter_subset_inter_left (initialSegment_mono hnm))
        · simpa only [hi,if_false] using hnm
    · simpa only [hq,if_false] using (ProductCone.zero : ProductCone (fun _ : I → ℕ => (0 : ℚ)))
  | add h h' ih ih' =>
    apply (ih.add ih').congr
    intro d
    simp only [Compression.prefixOperator,setOperator,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro Q _
    split_ifs <;> simp
  | scale c hc h ih =>
    apply (ih.scale c hc).congr
    intro d
    simp [Compression.prefixOperator,setOperator,Finset.mul_sum]

end
end CoefficientwiseRigidity.Compression
