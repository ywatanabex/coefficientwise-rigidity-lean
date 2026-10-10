import CoefficientwiseRigidity.Feasibility
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.Finset.Max

/-!
Exact graph-level propositions for the paper's main theorems.
These are definitions of proof obligations, NOT theorems or axioms.
In particular, a successful build of this module does not prove A, B or C.
-/
namespace CoefficientwiseRigidity
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The standard bag definition, including the running-intersection condition. -/
def TreewidthAtMostTwo (G : SimpleGraph V) : Prop :=
  ∃ (n : ℕ) (T : SimpleGraph (Fin n)) (bag : Fin n → Finset V),
    T.IsTree ∧ (∀ t, (bag t).card ≤ 3) ∧
    (∀ v, ∃ t, v ∈ bag t) ∧
    (∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
    ∀ v, (T.induce {t | v ∈ bag t}).Preconnected

/-- Circular adjacency is given arithmetically, without a graph-class oracle. -/
def CycleAdjacent {n : ℕ} (i j : Fin n) : Prop :=
  (i.val + 1) % n = j.val ∨ (j.val + 1) % n = i.val

def ChordalBipartite (G : SimpleGraph V) : Prop :=
  Nonempty (Bipartition G) ∧ ∀ (n : ℕ), 6 ≤ n →
    ¬ ∃ f : Fin n → V, Function.Injective f ∧
      ∀ i j, G.Adj (f i) (f j) ↔ CycleAdjacent i j

def StructuralAtom (G : SimpleGraph V) : Prop :=
  TreewidthAtMostTwo G ∨ ChordalBipartite G

def SupportedOn (G : SimpleGraph V) (U : Finset V) : Prop :=
  ∀ u v, G.Adj u v → u ∈ U ∧ v ∈ U

/-- Exactly an empty, vertex, or actual-edge intersection. -/
def LegalSeam (U₁ U₂ : Finset V) (G₁ G₂ : SimpleGraph V) : Prop :=
  U₁ ∩ U₂ = ∅ ∨
  (∃ v, U₁ ∩ U₂ = {v}) ∨
  ∃ u v, U₁ ∩ U₂ = {u, v} ∧ G₁.Adj u v ∧ G₂.Adj u v

inductive StructuralHull : Finset V → SimpleGraph V → Prop
  | atom (U : Finset V) (G : SimpleGraph V) (hs : SupportedOn G U)
      (ha : StructuralAtom (G.induce (↑U : Set V))) : StructuralHull U G
  | glue {U₁ U₂ : Finset V} {G₁ G₂ : SimpleGraph V}
      (h₁ : StructuralHull U₁ G₁) (h₂ : StructuralHull U₂ G₂)
      (hs : LegalSeam U₁ U₂ G₁ G₂) : StructuralHull (U₁ ∪ U₂) (G₁ ⊔ G₂)

/-- A designated leaf in a construction; it cannot be replaced by an arbitrary subgraph. -/
inductive WitnessHull (W : Finset V) (H : SimpleGraph V) : Finset V → SimpleGraph V → Prop
  | here (hs : SupportedOn H W) (ha : StructuralAtom (H.induce (↑W : Set V))) :
      WitnessHull W H W H
  | left {U₁ U₂ : Finset V} {G₁ G₂ : SimpleGraph V}
      (h₁ : WitnessHull W H U₁ G₁) (h₂ : StructuralHull U₂ G₂)
      (hs : LegalSeam U₁ U₂ G₁ G₂) : WitnessHull W H (U₁ ∪ U₂) (G₁ ⊔ G₂)
  | right {U₁ U₂ : Finset V} {G₁ G₂ : SimpleGraph V}
      (h₁ : StructuralHull U₁ G₁) (h₂ : WitnessHull W H U₂ G₂)
      (hs : LegalSeam U₁ U₂ G₁ G₂) : WitnessHull W H (U₁ ∪ U₂) (G₁ ⊔ G₂)

def restrictCover {G : SimpleGraph V} {M : ℕ} (X : Cover G M)
    (U : Finset V) (H : SimpleGraph V) (hle : H ≤ G) :
    Cover (H.induce (↑U : Set V)) M where
  transport u v := X.transport u.val v.val
  reverse h := X.reverse (hle h)

def walkTransport {G : SimpleGraph V} {M : ℕ} (X : Cover G M) :
    {u v : V} → G.Walk u v → Equiv.Perm (Fin M)
  | _, _, .nil => Equiv.refl _
  | u, _, .cons (v := v) _ p => (X.transport u v).trans (walkTransport X p)

def holonomyGroup {G : SimpleGraph V} {M : ℕ} (X : Cover G M) (root : V) :
    Subgroup (Equiv.Perm (Fin M)) :=
  Subgroup.closure {σ | ∃ p : G.Walk root root, walkTransport X p = σ}

noncomputable def movedSubsets (M : ℕ) (σ : Equiv.Perm (Fin M)) (k : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter (fun A : Finset (Fin M) =>
    A.card = k ∧ A.map σ.toEmbedding ≠ A)).card

/-- Finite minimum of the ratios in paper S3; the empty minimum is set to zero. -/
noncomputable def kappa (M : ℕ) (Γ : Subgroup (Equiv.Perm (Fin M))) : ℚ := by
  classical
  let ratios : Finset ℚ := (Finset.univ.filter
    (fun σ : Equiv.Perm (Fin M) => σ ∈ Γ ∧ σ ≠ 1)).biUnion fun σ =>
      (Finset.Icc 1 (M / 2)).image fun k =>
        (movedSubsets M σ k : ℚ) / (Nat.choose (M - 2) (k - 1) : ℚ)
  exact if h : ratios.Nonempty then ratios.min' h else 0

noncomputable def rootFibre {G : SimpleGraph V} {M : ℕ}
    (X : Cover G M) (a : V → ℕ) (u : V) (A : Finset (Fin M)) : ℕ := by
  classical
  exact Fintype.card {S : Configuration X a // S.val u = A}

noncomputable def edgeFibre {G : SimpleGraph V} {M : ℕ}
    (X : Cover G M) (a : V → ℕ) (u v : V) (A B : Finset (Fin M)) : ℕ := by
  classical
  exact Fintype.card {S : Configuration X a // S.val u = A ∧ S.val v = B}

def MainA (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 1 ≤ M → ∀ (X : Cover G M) (a : V → ℕ),
    Feasible G M a → StructuralAtom (supportGraph G a) →
      coefficient X a ≤ ordinary G M a ∧
      (coefficient X a = ordinary G M a ↔ ActiveFlat X a)

def MainBTwo (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 2 ≤ M → ∀ (X : Cover G M) (a : V → ℕ),
    G.Connected → (∃ u v, G.Adj u v) → TreewidthAtMostTwo G →
    Positive a → Feasible G M a → ¬ Flat X →
      coefficient X a + 2 * reserve G M a ≤ ordinary G M a ∧ 0 < reserve G M a

def MainBKappa (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 2 ≤ M → ∀ (X : Cover G M) (a : V → ℕ) (root : V),
    G.Connected → (∃ u v, G.Adj u v) → TreewidthAtMostTwo G →
    Positive a → Feasible G M a → ¬ Flat X →
      let κ := kappa M (holonomyGroup X root)
      2 ≤ κ ∧ (Odd (Nat.card (holonomyGroup X root)) → 3 ≤ κ) ∧
      (coefficient X a : ℚ) + κ * reserve G M a ≤ (ordinary G M a : ℚ) ∧
      0 < reserve G M a

def MainBOdd (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 2 ≤ M → ∀ (X : Cover G M) (a : V → ℕ) (root : V),
    G.Connected → (∃ u v, G.Adj u v) → TreewidthAtMostTwo G →
    Positive a → Feasible G M a → ¬ Flat X → Odd (Nat.card (holonomyGroup X root)) →
      coefficient X a + 3 * reserve G M a ≤ ordinary G M a

def MainCComparisonRigidity (G : SimpleGraph V) : Prop :=
  StructuralHull Finset.univ G → ∀ (M : ℕ), 1 ≤ M →
    ∀ (X : Cover G M) (a : V → ℕ), coefficient X a ≤ ordinary G M a ∧
      (Feasible G M a → (coefficient X a = ordinary G M a ↔ ActiveFlat X a))

/-- Multiplication avoids a convention for dividing by a zero boundary cardinality. -/
def MainCFibres (G : SimpleGraph V) : Prop :=
  StructuralHull Finset.univ G → ∀ (M : ℕ), 1 ≤ M →
    ∀ (X : Cover G M) (a : V → ℕ),
      (∀ u A, A.card = a u →
        Nat.choose M (a u) * rootFibre X a u A ≤ ordinary G M a) ∧
      (∀ u v A B, G.Adj u v → A.card = a u → B.card = a v →
        Disjoint (A.map (X.transport u v).toEmbedding) B →
        (Nat.choose M (a u) * Nat.choose (M - a u) (a v)) *
          edgeFibre X a u v A B ≤ ordinary G M a)

def MainCQuantitative (G : SimpleGraph V) : Prop :=
  ∀ (M : ℕ), 2 ≤ M → ∀ (X : Cover G M) (a : V → ℕ),
    Positive a → Feasible G M a → ∀ (W : Finset V) (H : SimpleGraph V)
      (hle : H ≤ G), WitnessHull W H Finset.univ G → ∀ (k : ℚ), 0 < k →
    let Y := restrictCover X W H hle
    let aW := fun v : (↑W : Set V) => a v.val
    (coefficient Y aW : ℚ) + k * reserve (H.induce (↑W : Set V)) M aW ≤
      (ordinary (H.induce (↑W : Set V)) M aW : ℚ) →
    (coefficient X a : ℚ) + k * reserve G M a ≤ (ordinary G M a : ℚ)

/-- Bipartiteness is an explicit outer hypothesis of every publication target. -/
def PaperMainTheorems : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), Nonempty (Bipartition G) →
    MainA G ∧ MainBTwo G ∧ MainBKappa G ∧ MainBOdd G ∧
      MainCComparisonRigidity G ∧ MainCFibres G ∧ MainCQuantitative G

end CoefficientwiseRigidity
