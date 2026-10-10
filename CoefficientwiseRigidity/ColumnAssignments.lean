import CoefficientwiseRigidity.ColumnSums

/-! Exact identification of iterated column sums with complete assignments. -/
namespace CoefficientwiseRigidity.Intersections
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {M : ℕ}

theorem sumColumns_zero (q : V → ℕ) (L : List V) (Q : V → Finset (Fin M)) :
    sumColumns q L (fun _ => 0) Q = 0 := by
  induction L with
  | nil => rfl
  | cons v L ih => simpa only [sumColumns,ite_self,Finset.sum_const_zero] using ih

theorem sumColumns_guard (q : V → ℕ) (L : List V) (p : Prop) [Decidable p]
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q L (fun R => if p then F R else 0) Q = if p then sumColumns q L F Q else 0 := by
  by_cases hp : p <;> simp [hp,sumColumns_zero]

theorem sumColumns_update (q : V → ℕ) (L : List V) (v : V) (hv : v ∉ L)
    (A : Finset (Fin M)) (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q L (fun R => F (Function.update R v A)) Q = sumColumns q L F (Function.update Q v A) := by
  induction L generalizing F with
  | nil => rfl
  | cons w L ih =>
    have hv' : v ≠ w ∧ v ∉ L := by simpa using hv
    simp only [sumColumns]
    rw [← ih hv'.2]
    apply sumColumns_congr
    intro R
    apply Finset.sum_congr rfl
    intro B _
    rw [Function.update_comm hv'.1]

theorem sumColumns_cons_outer (q : V → ℕ) (L : List V) (v : V) (hv : v ∉ L)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q (v :: L) F Q = ∑ A : Finset (Fin M),
      if A.card = q v then sumColumns q L F (Function.update Q v A) else 0 := by
  rw [sumColumns,sumColumns_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [sumColumns_guard,sumColumns_update q L v hv]

/-- Exactly the sliced columns are free; every other coordinate is pinned. -/
def ValidOn (q : V → ℕ) (U : Finset V) (Q S : V → Finset (Fin M)) : Prop :=
  (∀ v ∈ U, (S v).card = q v) ∧ ∀ v ∉ U, Q v = S v

theorem validOn_insert (q : V → ℕ) (U : Finset V) (v : V) (hv : v ∉ U)
    (Q S : V → Finset (Fin M)) :
    ValidOn q (insert v U) Q S ↔ (S v).card = q v ∧ ValidOn q U (Function.update Q v (S v)) S := by
  simp only [ValidOn,Finset.mem_insert]
  constructor
  · rintro ⟨hc,hp⟩
    refine ⟨hc v (Or.inl rfl),fun w hw => hc w (Or.inr hw),?_⟩
    intro w hw
    by_cases hwv : w = v
    · subst w; simp
    · rw [Function.update_of_ne hwv]
      exact hp w (by simp [hwv,hw])
  · rintro ⟨hc,hd,hp⟩
    constructor
    · intro w hw
      rcases hw with rfl | hw
      · exact hc
      · exact hd w hw
    · intro w hw
      have hwv : w ≠ v := fun he => hw (Or.inl he)
      have hwU : w ∉ U := fun hm => hw (Or.inr hm)
      simpa only [Function.update_of_ne hwv] using hp w hwU

/-- Each complete assignment occurs once, not a power of the number of
unused labels or a normalised average. -/
theorem sumColumns_delta [DecidableEq (V → Finset (Fin M))] (q : V → ℕ) (L : List V) (hnd : L.Nodup)
    (S Q : V → Finset (Fin M)) (c : ℚ) :
    sumColumns q L (fun R => if R = S then c else 0) Q =
      if ValidOn q L.toFinset Q S then c else 0 := by
  induction L generalizing Q with
  | nil =>
    have he : ValidOn q ([] : List V).toFinset Q S ↔ Q = S := by
      simpa [ValidOn] using (funext_iff : Q = S ↔ ∀ v, Q v = S v).symm
    simp only [sumColumns,he]
  | cons v L ih =>
    have hn := List.nodup_cons.mp hnd
    rw [sumColumns_cons_outer q L v hn.1]
    simp_rw [ih hn.2]
    rw [Finset.sum_eq_single (S v)]
    · rw [List.toFinset_cons,validOn_insert q L.toFinset v (by simpa using hn.1)]
      split_ifs <;> simp_all
    · intro A _ hA
      have hbad : ¬ ValidOn q L.toFinset (Function.update Q v A) S := by
        intro h
        have hv := h.2 v (by simpa using hn.1)
        exact hA (by simpa using hv)
      simp [hbad]
    · simp

theorem sumColumns_eq_assignment_sum [Fintype V] (q : V → ℕ) (L : List V) (hnd : L.Nodup)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumColumns q L F Q = ∑ S : V → Finset (Fin M), if ValidOn q L.toFinset Q S then F S else 0 := by
  have he : F = fun R => ∑ S : V → Finset (Fin M), if R = S then F S else 0 := by
    funext R
    simp
  calc
    _ = sumColumns q L (fun R => ∑ S : V → Finset (Fin M), if R = S then F S else 0) Q := congrArg (fun f => sumColumns q L f Q) he
    _ = ∑ S : V → Finset (Fin M), sumColumns q L (fun R => if R = S then F S else 0) Q := sumColumns_sum _ _ _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S _
      exact sumColumns_delta q L hnd S Q (F S)

theorem sumSet_eq_assignment_sum [Fintype V] (q : V → ℕ) (U : Finset V)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U F Q = ∑ S : V → Finset (Fin M), if ValidOn q U Q S then F S else 0 := by
  simpa only [sumSet,Finset.toList_toFinset] using sumColumns_eq_assignment_sum q U.toList U.nodup_toList F Q

end
end CoefficientwiseRigidity.Intersections
