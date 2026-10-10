import CoefficientwiseRigidity.LabelledCover
import CoefficientwiseRigidity.Feasibility

/-! Select one original label per simple edge, with exact ordinary counts and a configuration injection. -/
namespace CoefficientwiseRigidity.LabelledCover
open scoped Classical
noncomputable section
variable {V E : Type*} {M : ℕ}

theorem exists_forward (X : LabelledCover V E M) {u v : V}
    (he : X.graph.Adj u v) (hu : X.side u = true) : ∃ e, X.left e = u ∧ X.right e = v := by
  obtain ⟨e,h | h⟩ := he
  · exact ⟨e,h⟩
  · have hh := X.right_side e
    rw [h.2,hu] at hh
    cases hh

def forwardMap (X : LabelledCover V E M) (u v : V) : Equiv.Perm (Fin M) :=
  if h : ∃ e, X.left e = u ∧ X.right e = v then X.transport (Classical.choose h) else Equiv.refl _

def representative (X : LabelledCover V E M) : Cover X.graph M where
  transport u v := if X.side u = true then X.forwardMap u v else (X.forwardMap v u).symm
  reverse := by
    intro u v he
    have hn := X.bipartition.opposite he
    change X.side u ≠ X.side v at hn
    cases hu : X.side u <;> cases hv : X.side v <;> simp_all

theorem representative_forward (X : LabelledCover V E M) {u v : V}
    (he : X.graph.Adj u v) (hu : X.side u = true) :
    ∃ e, X.left e = u ∧ X.right e = v ∧ X.representative.transport u v = X.transport e := by
  have hx := X.exists_forward he hu
  exact ⟨Classical.choose hx,(Classical.choose_spec hx).1,(Classical.choose_spec hx).2,
    by simp [representative,forwardMap,hu,hx]⟩

theorem admissible_representative (X : LabelledCover V E M) {a : V → ℕ}
    {S : Assignment V M} (hs : X.Admissible a S) :
    CoefficientwiseRigidity.Admissible X.representative a S := by
  refine ⟨hs.1,?_⟩
  intro u v he i hi hj
  cases hu : X.side u with
  | true =>
    obtain ⟨e,hl,hr,ht⟩ := X.representative_forward he hu
    have h := hs.2 e i
    rw [hl,hr,← ht] at h
    exact h hi hj
  | false =>
    have hv : X.side v = true := by
      have hn := X.bipartition.opposite he
      change X.side u ≠ X.side v at hn
      rw [hu] at hn
      cases h : X.side v <;> simp_all
    obtain ⟨e,hl,hr,ht⟩ := X.representative_forward (X.graph.symm he) hv
    have h := hs.2 e (X.representative.transport u v i)
    rw [hl,hr,← ht,X.representative.reverse he,Equiv.symm_apply_apply] at h
    exact h hj hi

def toRepresentative (X : LabelledCover V E M) (a : V → ℕ) :
    X.Configuration a → CoefficientwiseRigidity.Configuration X.representative a :=
  fun S => ⟨S.val,X.admissible_representative S.property⟩

theorem toRepresentative_injective (X : LabelledCover V E M) (a : V → ℕ) :
    Function.Injective (X.toRepresentative a) := by
  intro S T h
  exact Subtype.ext (congrArg (fun Z : CoefficientwiseRigidity.Configuration X.representative a => Z.val) h)

theorem ordinary_admissible_iff (X : LabelledCover V E M) (a : V → ℕ) (S : Assignment V M) :
    X.ordinary.Admissible a S ↔ CoefficientwiseRigidity.Admissible (trivialCover X.graph M) a S := by
  constructor
  · rintro ⟨hc,he⟩
    refine ⟨hc,?_⟩
    rintro u v ⟨e,h | h⟩ i hi hj
    · have hh := he e i
      change i ∈ S (X.left e) → i ∉ S (X.right e) at hh
      rw [h.1,h.2] at hh
      exact hh hi hj
    · have hh := he e i
      change i ∈ S (X.left e) → i ∉ S (X.right e) at hh
      rw [h.1,h.2] at hh
      exact hh hj hi
  · rintro ⟨hc,he⟩
    exact ⟨hc,fun e i hi => he (X.left e) (X.right e) ⟨e,Or.inl ⟨rfl,rfl⟩⟩ i hi⟩

def ordinaryConfigurationEquiv (X : LabelledCover V E M) (a : V → ℕ) :
    X.ordinary.Configuration a ≃ CoefficientwiseRigidity.Configuration (trivialCover X.graph M) a where
  toFun S := ⟨S.val,(X.ordinary_admissible_iff a S.val).mp S.property⟩
  invFun S := ⟨S.val,(X.ordinary_admissible_iff a S.val).mpr S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype V] [DecidableEq V]

theorem coefficient_le_representative (X : LabelledCover V E M) (a : V → ℕ) :
    X.coefficient a ≤ CoefficientwiseRigidity.coefficient X.representative a :=
  Fintype.card_le_of_injective (X.toRepresentative a) (X.toRepresentative_injective a)

theorem ordinary_coefficient_eq (X : LabelledCover V E M) (a : V → ℕ) :
    X.ordinary.coefficient a = CoefficientwiseRigidity.ordinary X.graph M a :=
  Fintype.card_congr (X.ordinaryConfigurationEquiv a)

end
end CoefficientwiseRigidity.LabelledCover
