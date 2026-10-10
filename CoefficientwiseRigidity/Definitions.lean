import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic

/-!
Concrete finite objects for paper §01. No graph-counting or comparison axioms.
`coefficient` is the number of fixed-occupation subset configurations (F1).
The identification with a multivariate polynomial coefficient is proved in
`Polynomial` and `Lift`; it is not silently built into a theorem name.
-/
namespace CoefficientwiseRigidity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Left/right colouring witnessing bipartiteness. -/
structure Bipartition (G : SimpleGraph V) where
  side : V → Bool
  opposite : ∀ {u v}, G.Adj u v → side u ≠ side v

/-- Permutation transports, with the correct inverse on reversed edges. -/
structure Cover (G : SimpleGraph V) (M : ℕ) where
  transport : V → V → Equiv.Perm (Fin M)
  reverse : ∀ {u v}, G.Adj u v → transport v u = (transport u v).symm

def trivialCover (G : SimpleGraph V) (M : ℕ) : Cover G M where
  transport := fun _ _ => Equiv.refl _
  reverse := fun _ => rfl

abbrev Assignment (V : Type*) (M : ℕ) := V → Finset (Fin M)

def Admissible {G : SimpleGraph V} {M : ℕ} (X : Cover G M)
    (a : V → ℕ) (S : Assignment V M) : Prop :=
  (∀ v, (S v).card = a v) ∧
    ∀ u v, G.Adj u v → ∀ i ∈ S u, X.transport u v i ∉ S v

abbrev Configuration {G : SimpleGraph V} {M : ℕ} (X : Cover G M) (a : V → ℕ) :=
  {S : Assignment V M // Admissible X a S}

noncomputable instance configurationFintype {G : SimpleGraph V} {M : ℕ}
    (X : Cover G M) (a : V → ℕ) : Fintype (Configuration X a) := by
  classical
  unfold Configuration
  infer_instance

noncomputable def coefficient {G : SimpleGraph V} {M : ℕ}
    (X : Cover G M) (a : V → ℕ) : ℕ := Fintype.card (Configuration X a)

noncomputable def ordinary (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) : ℕ :=
  coefficient (trivialCover G M) a

/-- Signed deficit: negative counts are not hidden by truncated subtraction. -/
noncomputable def deficit {G : SimpleGraph V} {M : ℕ}
    (X : Cover G M) (a : V → ℕ) : ℤ := (ordinary G M a : ℤ) - coefficient X a

def Feasible (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) : Prop :=
  (∀ v, a v ≤ M) ∧ ∀ u v, G.Adj u v → a u + a v ≤ M

def Positive (a : V → ℕ) : Prop := ∀ v, 0 < a v

/-- Gauge flatness on precisely the positive support. -/
def ActiveFlat {G : SimpleGraph V} {M : ℕ} (X : Cover G M) (a : V → ℕ) : Prop :=
  ∃ γ : V → Equiv.Perm (Fin M), ∀ u v, G.Adj u v →
    0 < a u → 0 < a v → ∀ i, X.transport u v (γ u i) = γ v i

def Flat {G : SimpleGraph V} {M : ℕ} (X : Cover G M) : Prop :=
  ∃ γ : V → Equiv.Perm (Fin M), ∀ u v, G.Adj u v →
    ∀ i, X.transport u v (γ u i) = γ v i

def activeGraph (G : SimpleGraph V) (a : V → ℕ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ 0 < a u ∧ 0 < a v
  symm := fun _ _ h => ⟨G.symm h.1, h.2.2, h.2.1⟩
  loopless := fun v h => G.loopless v h.1

/-- Zero occupations are genuinely deleted at the type level. -/
abbrev ActiveVertex (a : V → ℕ) := {v : V // 0 < a v}

def supportGraph (G : SimpleGraph V) (a : V → ℕ) : SimpleGraph (ActiveVertex a) :=
  G.induce {v | 0 < a v}

noncomputable def reserve (G : SimpleGraph V) (M : ℕ) (a : V → ℕ) : ℕ :=
  ordinary G (M - 2) (fun v => a v - 1)

end CoefficientwiseRigidity
