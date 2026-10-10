import CoefficientwiseRigidity.SerialTransport

/-!
Two-label cancellation for the ACTUAL subset sum, with no use of K2.
This is the paper W1 counting identity before any radial cone is assumed.
It supplies an alternative all-regime induction proof of K2.
-/
namespace CoefficientwiseRigidity.Kernel
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]

def liftSet (A : Finset α) (b : Bool) : Finset (α ⊕ Bool) := A.disjSum {b}

omit [Fintype α] [DecidableEq α] in
theorem card_liftSet (A : Finset α) (b : Bool) : (liftSet A b).card = A.card + 1 := by
  simp [liftSet]

omit [Fintype α] in
theorem inter_disjSum (A B : Finset α) (s t : Finset Bool) :
    A.disjSum s ∩ B.disjSum t = (A ∩ B).disjSum (s ∩ t) := by
  ext x
  cases x <;> simp

theorem setOverlap_lift (A B : Finset α) (b c : Bool) :
    setOverlap (liftSet A b) (liftSet B c) = setOverlap A B + if b = c then 1 else 0 := by
  have hlo := setOverlap_lower A B
  dsimp [setOverlap, liftSet]
  rw [inter_disjSum]
  by_cases h : b = c
  · subst c
    simp only [Finset.inter_self, Finset.card_disjSum, Finset.card_singleton,
      Fintype.card_sum, Fintype.card_bool, if_true]
    omega
  · have hi : ({b} ∩ {c} : Finset Bool) = ∅ := by ext x; simp; aesop
    rw [hi]
    simp only [Finset.card_disjSum, Finset.card_empty, Finset.card_singleton,
      Fintype.card_sum, Fintype.card_bool, if_neg h]
    omega

theorem setOverlap_no_flags (C B : Finset α) :
    setOverlap (C.disjSum (∅ : Finset Bool)) (liftSet B false) =
      setOverlap (C.disjSum (∅ : Finset Bool)) (liftSet B true) := by
  unfold setOverlap liftSet
  rw [inter_disjSum, inter_disjSum]
  simp

theorem setOverlap_both_flags (C B : Finset α) :
    setOverlap (C.disjSum ({false,true} : Finset Bool)) (liftSet B false) =
      setOverlap (C.disjSum ({false,true} : Finset Bool)) (liftSet B true) := by
  simp [setOverlap, liftSet, inter_disjSum]

theorem sum_bool_finsets (F : Finset Bool → ℚ) :
    (∑ D : Finset Bool, F D) = F ∅ + F {false} + F {true} + F {false,true} := by
  have hu : (Finset.univ : Finset (Finset Bool)) = {∅,{false},{true},{false,true}} := by decide
  rw [hu]
  have h0 : (∅ : Finset Bool) ∉ ({ {false}, {true}, {false,true} } : Finset (Finset Bool)) := by decide
  have h1 : ({false} : Finset Bool) ∉ ({ {true}, {false,true} } : Finset (Finset Bool)) := by decide
  have h2 : ({true} : Finset Bool) ∉ ({ {false,true} } : Finset (Finset Bool)) := by decide
  rw [Finset.sum_insert h0, Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_singleton]
  ring

omit [DecidableEq α] in
theorem sum_finsets_sum (F : Finset (α ⊕ Bool) → ℚ) :
    (∑ C, F C) = ∑ C : Finset α, ∑ D : Finset Bool, F (C.disjSum D) := by
  calc
    (∑ C, F C) = ∑ CD : Finset α × Finset Bool, F (CD.1.disjSum CD.2) :=
      Fintype.sum_equiv Finset.sumEquiv.toEquiv _ _ (fun C => by
        change F C = F (C.toLeft.disjSum C.toRight)
        rw [Finset.toLeft_disjSum_toRight])
    _ = _ := Fintype.sum_prod_type _

theorem two_label_summand (m : ℕ) (f g : ℕ → ℚ) (A B C : Finset α) :
    (∑ D : Finset Bool, if (C.disjSum D).card = m + 1 then
      f (setOverlap (liftSet A false) (C.disjSum D)) *
        g (setOverlap (C.disjSum D) (liftSet B false)) else 0) -
    (∑ D : Finset Bool, if (C.disjSum D).card = m + 1 then
      f (setOverlap (liftSet A false) (C.disjSum D)) *
        g (setOverlap (C.disjSum D) (liftSet B true)) else 0) =
    if C.card = m then delta f (setOverlap A C) * delta g (setOverlap C B) else 0 := by
  rw [sum_bool_finsets, sum_bool_finsets]
  have hfalse : C.disjSum {false} = liftSet C false := rfl
  have htrue : C.disjSum {true} = liftSet C true := rfl
  rw [setOverlap_no_flags C B, setOverlap_both_flags C B, hfalse, htrue]
  simp only [card_liftSet, Nat.add_right_cancel_iff, setOverlap_lift,
    Bool.false_eq_true, Bool.true_eq_false, if_false, if_true, add_zero]
  by_cases hc : C.card = m <;> simp only [hc, if_true, if_false]
  · simp only [delta, fwdDiff]
    ring
  · ring

/-- Exact two-label difference identity, with no normalization factor or cone premise. -/
theorem setSerial_two_label_difference (m : ℕ) (f g : ℕ → ℚ) (A B : Finset α) :
    setSerial (m + 1) f g (liftSet A false) (liftSet B false) -
      setSerial (m + 1) f g (liftSet A false) (liftSet B true) =
        setSerial m (delta f) (delta g) A B := by
  unfold setSerial
  rw [sum_finsets_sum, sum_finsets_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro C _
  exact two_label_summand m f g A B C

/-- W1 in the original slice notation; only the proved radial representation is needed. -/
theorem serial_profile_difference {M p m q : ℕ} {f g h : ℕ → ℚ}
    (hh : ∀ (A : Slice (M + 2) (p + 1)) (B : Slice (M + 2) (q + 1)),
      serial (m := m + 1) f g A B = h (overlap A B))
    (A : Slice M p) (B : Slice M q) :
    delta h (overlap A B) = serial (m := m) (delta f) (delta g) A B := by
  have hhi := setSerial_of_profile hh (liftSet A.val false) (liftSet B.val false)
    (by simp) (by simp [card_liftSet, A.property]) (by simp [card_liftSet, B.property])
  have hlo := setSerial_of_profile hh (liftSet A.val false) (liftSet B.val true)
    (by simp) (by simp [card_liftSet, A.property]) (by simp [card_liftSet, B.property])
  have he := setSerial_two_label_difference m f g A.val B.val
  rw [hhi, hlo, setOverlap_lift, setOverlap_lift] at he
  simp only [Bool.false_eq_true, if_false, if_true, add_zero, setOverlap_slice] at he
  rw [serial_eq_setSerial]
  exact he

end CoefficientwiseRigidity.Kernel
