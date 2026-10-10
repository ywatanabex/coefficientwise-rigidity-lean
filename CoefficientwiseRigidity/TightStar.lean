import CoefficientwiseRigidity.StarVertices

/-! Exact configurations under tight-star contraction, retaining all labelled edges. -/
namespace CoefficientwiseRigidity.Star
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {M : ℕ}

def Normalized (X : Cover G M) (u : V) : Prop :=
  ∀ v, G.Adj u v → X.transport u v = Equiv.refl _

def Tight (a : V → ℕ) (u : V) (M : ℕ) : Prop :=
  ∀ v, G.Adj u v → a v = M - a u

theorem star_complement (X : Cover G M) {a : V → ℕ} {u : V}
    (hn : Normalized X u) (ht : Tight (G := G) a u M)
    {S : Assignment V M} (hs : Admissible X a S) {v : V} (he : G.Adj u v) :
    S v = (S u)ᶜ := by
  apply Finset.eq_of_subset_of_card_le
  · intro i hi
    rw [Finset.mem_compl]
    intro hu
    have h := hs.2 u v he i hu
    rw [hn v he] at h
    exact h hi
  · rw [Finset.card_compl,Fintype.card_fin,hs.1,hs.1,ht v he]

def contract (u : V) (S : Assignment V M) : Assignment (Vertex G u) M
  | none => (S u)ᶜ
  | some v => S v.val

def expand (u : V) (T : Assignment (Vertex G u) M) : Assignment V M :=
  fun v => if v = u then (T none)ᶜ else T (project G u v)

@[simp] theorem expand_self (u : V) (T : Assignment (Vertex G u) M) :
    expand u T u = (T none)ᶜ := by simp [expand]

theorem expand_ne (u : V) (T : Assignment (Vertex G u) M) {v : V} (hv : v ≠ u) :
    expand u T v = T (project G u v) := by simp [expand,hv]

@[simp] theorem expand_outside (u : V) (T : Assignment (Vertex G u) M) (v : Outside G u) :
    expand u T v.val = T (some v) := by simp [expand,v.property.1]

theorem contract_project (X : Cover G M) {a : V → ℕ} {u : V}
    (hn : Normalized X u) (ht : Tight (G := G) a u M)
    {S : Assignment V M} (hs : Admissible X a S) {v : V} (hv : v ≠ u) :
    contract u S (project G u v) = S v := by
  by_cases he : G.Adj u v
  · rw [project_neighbor he]; exact (star_complement X hn ht hs he).symm
  · simp [project,hv,he,contract]

theorem contract_admissible (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (hn : Normalized X u) (ht : Tight (G := G) a u M)
    {S : Assignment V M} (hs : Admissible X a S) :
    (cover b u hu X).Admissible (occupation u M a) (contract u S) := by
  constructor
  · intro v
    cases v with
    | none => simp [contract,occupation,Finset.card_compl,hs.1]
    | some v => exact hs.1 v.val
  · intro e i hi hj
    change i ∈ contract u S (project G u e.val.1) at hi
    change X.transport e.val.1 e.val.2 i ∈ contract u S (project G u e.val.2) at hj
    rw [contract_project X hn ht hs e.property.2.2.1] at hi
    rw [contract_project X hn ht hs e.property.2.2.2] at hj
    exact hs.2 _ _ e.property.2.1 i hi hj

theorem expand_admissible (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (hn : Normalized X u)
    (ht : Tight (G := G) a u M) {T : Assignment (Vertex G u) M}
    (hT : (cover b u hu X).Admissible (occupation u M a) T) :
    Admissible X a (expand u T) := by
  constructor
  · intro v
    by_cases hv : v = u
    · subst v
      simp only [expand_self,Finset.card_compl,Fintype.card_fin,hT.1,occupation]
      exact Nat.sub_sub_self ha
    · rw [expand_ne u T hv,hT.1,occupation_project u a ht hv]
  · intro x y he i hi hj
    by_cases hx : x = u
    · subst x
      have hy : y ≠ u := (G.ne_of_adj he).symm
      rw [expand_self,Finset.mem_compl] at hi
      rw [hn y he,expand_ne u T hy,project_neighbor he] at hj
      exact hi hj
    by_cases hy : y = u
    · subst y
      have hr : X.transport x u = Equiv.refl _ := by rw [X.reverse (G.symm he),hn x (G.symm he)]; rfl
      rw [hr,expand_self,Finset.mem_compl] at hj
      rw [expand_ne u T hx,project_neighbor (G.symm he)] at hi
      exact hj hi
    rw [expand_ne u T hx] at hi
    rw [expand_ne u T hy] at hj
    cases hside : b.side x with
    | true => exact hT.2 ⟨(x,y),hside,he,hx,hy⟩ i hi hj
    | false =>
      have hsy : b.side y = true := by
        have hh := b.opposite he
        rw [hside] at hh
        cases h : b.side y <;> simp_all
      have h := hT.2 ⟨(y,x),hsy,G.symm he,hy,hx⟩ (X.transport x y i) hj
      change X.transport y x (X.transport x y i) ∉ T (project G u x) at h
      rw [X.reverse he,Equiv.symm_apply_apply] at h
      exact h hi

theorem expand_contract (X : Cover G M) {a : V → ℕ} {u : V}
    (hn : Normalized X u) (ht : Tight (G := G) a u M)
    {S : Assignment V M} (hs : Admissible X a S) : expand (G := G) u (contract u S) = S := by
  funext v
  by_cases hv : v = u
  · subst v; simp [contract]
  · rw [expand_ne u _ hv,contract_project X hn ht hs hv]

theorem contract_expand (u : V) (T : Assignment (Vertex G u) M) : contract u (expand u T) = T := by
  funext v
  cases v with
  | none => simp [contract]
  | some v => exact expand_outside u T v

def configurationEquiv (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (hn : Normalized X u)
    (ht : Tight (G := G) a u M) :
    Configuration X a ≃ (cover b u hu X).Configuration (occupation u M a) where
  toFun S := ⟨contract u S.val,contract_admissible b u hu X a hn ht S.property⟩
  invFun T := ⟨expand u T.val,expand_admissible b u hu X a ha hn ht T.property⟩
  left_inv S := Subtype.ext (expand_contract X hn ht S.property)
  right_inv T := Subtype.ext (contract_expand u T.val)

variable [Fintype V] [DecidableEq V]

theorem coefficient_eq (b : Bipartition G) (u : V) (hu : b.side u = true)
    (X : Cover G M) (a : V → ℕ) (ha : a u ≤ M) (hn : Normalized X u)
    (ht : Tight (G := G) a u M) :
    coefficient X a = (cover b u hu X).coefficient (occupation u M a) :=
  Fintype.card_congr (configurationEquiv b u hu X a ha hn ht)

end
end CoefficientwiseRigidity.Star
