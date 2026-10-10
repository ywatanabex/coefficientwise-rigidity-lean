import CoefficientwiseRigidity.Definitions

/-! Bipartite labelled-edge covers: distinct parallel constraints are retained. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section

structure LabelledCover (V E : Type*) (M : ℕ) where
  side : V → Bool
  left : E → V
  right : E → V
  left_side : ∀ e, side (left e) = true
  right_side : ∀ e, side (right e) = false
  transport : E → Equiv.Perm (Fin M)

namespace LabelledCover
variable {V E : Type*} {M : ℕ}

def Admissible (X : LabelledCover V E M) (a : V → ℕ) (S : Assignment V M) : Prop :=
  (∀ v, (S v).card = a v) ∧ ∀ e, ∀ i ∈ S (X.left e), X.transport e i ∉ S (X.right e)

abbrev Configuration (X : LabelledCover V E M) (a : V → ℕ) :=
  {S : Assignment V M // X.Admissible a S}

instance configurationFintype [Fintype V] (X : LabelledCover V E M) (a : V → ℕ) :
    Fintype (X.Configuration a) := inferInstanceAs (Fintype {S : Assignment V M // X.Admissible a S})

def coefficient [Fintype V] (X : LabelledCover V E M) (a : V → ℕ) : ℕ :=
  Fintype.card (X.Configuration a)

def ordinary (X : LabelledCover V E M) : LabelledCover V E M :=
  {X with transport := fun _ => Equiv.refl _}

def Flat (X : LabelledCover V E M) : Prop :=
  ∃ γ : V → Equiv.Perm (Fin M), ∀ e i, X.transport e (γ (X.left e) i) = γ (X.right e) i

theorem endpoints_ne (X : LabelledCover V E M) (e : E) : X.left e ≠ X.right e := by
  intro he
  have h := X.left_side e
  rw [he,X.right_side e] at h
  cases h

def graph (X : LabelledCover V E M) : SimpleGraph V where
  Adj u v := ∃ e, (X.left e = u ∧ X.right e = v) ∨ (X.left e = v ∧ X.right e = u)
  symm := by
    rintro u v ⟨e,h | h⟩
    · exact ⟨e,Or.inr h⟩
    · exact ⟨e,Or.inl h⟩
  loopless := by
    rintro u ⟨e,h | h⟩ <;> exact X.endpoints_ne e (h.1.trans h.2.symm)

def bipartition (X : LabelledCover V E M) : Bipartition X.graph where
  side := X.side
  opposite := by
    rintro u v ⟨e,h | h⟩
    · rw [← h.1,← h.2,X.left_side,X.right_side]; decide
    · rw [← h.1,← h.2,X.left_side,X.right_side]; decide

theorem ordinary_graph (X : LabelledCover V E M) : X.ordinary.graph = X.graph := rfl

end LabelledCover
end
end CoefficientwiseRigidity
