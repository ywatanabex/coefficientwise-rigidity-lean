import CoefficientwiseRigidity.CompressionStep

/-! Terminating simultaneous compression to prefixes, including nested equality. -/
namespace CoefficientwiseRigidity.Compression
open Finset
open scoped Classical
noncomputable section
variable {M : ℕ} {I : Type*} [Fintype I]

def setWeight (D : Finset (Fin M)) : ℕ := ∑ x ∈ D, x.val
def familyWeight (D : I → Finset (Fin M)) : ℕ := ∑ i, setWeight (D i)

theorem setWeight_shift_lt {a b : Fin M} (hab : a < b) (D : Finset (Fin M))
    (hb : b ∈ D) (ha : a ∉ D) : setWeight (shift a b D) < setWeight D :=
  shift_weight_lt Fin.val hab D hb ha

theorem setWeight_shift_le {a b : Fin M} (hab : a < b) (D : Finset (Fin M)) :
    setWeight (shift a b D) ≤ setWeight D := by
  by_cases h : b ∈ D ∧ a ∉ D
  · exact (setWeight_shift_lt hab D h.1 h.2).le
  · simp [shift,h]

theorem exists_inversion (D : Finset (Fin M)) (hD : D ≠ initialSegment M D.card) :
    ∃ a b : Fin M, a < b ∧ a ∉ D ∧ b ∈ D := by
  have hcard : (initialSegment M D.card).card = D.card :=
    card_prefix M D.card (by simpa using D.card_le_univ)
  have hp : ¬ initialSegment M D.card ⊆ D := by
    intro h
    exact hD (Finset.eq_of_subset_of_card_le h hcard.symm.le).symm
  have hd : ¬ D ⊆ initialSegment M D.card := by
    intro h
    exact hD (Finset.eq_of_subset_of_card_le h hcard.le)
  obtain ⟨a,ha,haD⟩ := Finset.not_subset.mp hp
  obtain ⟨b,hbD,hb⟩ := Finset.not_subset.mp hd
  refine ⟨a,b,?_,haD,hbD⟩
  have ha' := (mem_prefix M D.card a).mp ha
  have hb' : ¬ b.val < D.card := fun h => hb ((mem_prefix M D.card b).mpr h)
  show a.val < b.val
  omega

private theorem simultaneous_aux (n : ℕ) (q : ℕ) (h : I → ℕ → ℚ)
    (hn : ∀ i k, 0 ≤ h i k) (hm : ∀ i, Monotone (h i)) :
    ∀ D : I → Finset (Fin M), familyWeight D = n →
      sliceSum q h D ≤ sliceSum q h (fun i => initialSegment M (D i).card) ∧
      ((∀ i j, D i ⊆ D j ∨ D j ⊆ D i) →
        sliceSum q h D = sliceSum q h (fun i => initialSegment M (D i).card)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro D hweight
    by_cases hdone : ∀ i, D i = initialSegment M (D i).card
    · have he : D = fun i => initialSegment M (D i).card := funext hdone
      exact ⟨le_of_eq (congrArg (sliceSum q h) he),fun _ => congrArg (sliceSum q h) he⟩
    · push_neg at hdone
      obtain ⟨i,hi⟩ := hdone
      obtain ⟨a,b,hab,ha,hb⟩ := exists_inversion (D i) hi
      let E := fun j => shift a b (D j)
      have hlt : familyWeight E < n := by
        rw [← hweight]
        exact Finset.sum_lt_sum (fun j _ => setWeight_shift_le hab (D j))
          ⟨i,Finset.mem_univ _,setWeight_shift_lt hab (D i) hb ha⟩
      have hcard : ∀ j, (E j).card = (D j).card := fun j => card_shift (D j)
      obtain ⟨hle,heq⟩ := ih (familyWeight E) hlt E rfl
      simp only [hcard] at hle heq
      refine ⟨(sliceSum_shift_le a b (ne_of_lt hab) q h hn hm D).trans hle,?_⟩
      intro hnest
      have hEnest : ∀ i j, E i ⊆ E j ∨ E j ⊆ E i := by
        intro i j
        exact (hnest i j).imp (shift_mono (ne_of_lt hab)) (shift_mono (ne_of_lt hab))
      exact (sliceSum_shift_eq_of_nested a b (ne_of_lt hab) q h D hnest).symm.trans (heq hEnest)

/-- Paper C1 for every number of factors, arbitrary sizes and every slice. -/
theorem simultaneous_compression (q : ℕ) (h : I → ℕ → ℚ)
    (hn : ∀ i k, 0 ≤ h i k) (hm : ∀ i, Monotone (h i)) (D : I → Finset (Fin M)) :
    sliceSum q h D ≤ sliceSum q h (fun i => initialSegment M (D i).card) :=
  (simultaneous_aux (familyWeight D) q h hn hm D rfl).1

theorem simultaneous_compression_eq_of_nested (q : ℕ) (h : I → ℕ → ℚ)
    (hn : ∀ i k, 0 ≤ h i k) (hm : ∀ i, Monotone (h i)) (D : I → Finset (Fin M))
    (hD : ∀ i j, D i ⊆ D j ∨ D j ⊆ D i) :
    sliceSum q h D = sliceSum q h (fun i => initialSegment M (D i).card) :=
  (simultaneous_aux (familyWeight D) q h hn hm D rfl).2 hD

end
end CoefficientwiseRigidity.Compression
