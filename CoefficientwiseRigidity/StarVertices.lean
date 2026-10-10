import CoefficientwiseRigidity.LabelledCover
import CoefficientwiseRigidity.SaturationRanks

/-! The actual vertex and edge labels for deleting a star centre and merging its neighbours. -/
namespace CoefficientwiseRigidity.Star
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V}

abbrev Outside (G : SimpleGraph V) (u : V) := {v : V // v ≠ u ∧ ¬ G.Adj u v}
abbrev Vertex (G : SimpleGraph V) (u : V) := Option (Outside G u)

/-- Both the removed centre and all its neighbours project to the new vertex.
The centre's assignment will be complemented when lifted. -/
def project (G : SimpleGraph V) (u v : V) : Vertex G u :=
  if h : v ≠ u ∧ ¬ G.Adj u v then some ⟨v,h⟩ else none

@[simp] theorem project_self (u : V) : project G u u = none := by simp [project]

theorem project_neighbor {u v : V} (h : G.Adj u v) : project G u v = none := by simp [project,h]

@[simp] theorem project_outside (u : V) (v : Outside G u) : project G u v.val = some v := by
  simp [project,v.property]

theorem project_eq_none {u v : V} : project G u v = none ↔ v = u ∨ G.Adj u v := by
  by_cases hv : v = u <;> simp [project,hv]

def side (b : Bipartition G) (u : V) : Vertex G u → Bool
  | none => false
  | some v => b.side v.val

theorem project_side (b : Bipartition G) {u v : V} (hu : b.side u = true) (hv : v ≠ u) :
    side b u (project G u v) = b.side v := by
  by_cases he : G.Adj u v
  · have hh : b.side v = false := by
      have hn := b.opposite he
      rw [hu] at hn
      cases h : b.side v <;> simp_all
    simp [project_neighbor he,side,hh]
  · simp [project,he,hv,side]

/-- Original oriented edge labels; deleting u does not merge parallel labels. -/
abbrev Edge (b : Bipartition G) (u : V) :=
  {e : V × V // b.side e.1 = true ∧ G.Adj e.1 e.2 ∧ e.1 ≠ u ∧ e.2 ≠ u}

def cover {M : ℕ} (b : Bipartition G) (u : V) (hu : b.side u = true) (X : Cover G M) :
    LabelledCover (Vertex G u) (Edge b u) M where
  side := side b u
  left e := project G u e.val.1
  right e := project G u e.val.2
  left_side e := (project_side b hu e.property.2.2.1).trans e.property.1
  right_side e := by
    rw [project_side b hu e.property.2.2.2]
    have hn := b.opposite e.property.2.1
    rw [e.property.1] at hn
    cases h : b.side e.val.2 <;> simp_all
  transport e := X.transport e.val.1 e.val.2

def occupation (u : V) (M : ℕ) (a : V → ℕ) : Vertex G u → ℕ
  | none => M - a u
  | some v => a v.val

theorem occupation_project {M : ℕ} (u : V) (a : V → ℕ)
    (ht : ∀ v, G.Adj u v → a v = M - a u) {v : V} (hv : v ≠ u) :
    occupation u M a (project G u v) = a v := by
  by_cases he : G.Adj u v
  · simp [project_neighbor he,occupation,ht v he]
  · simp [project,hv,he,occupation]

variable [Fintype V]

/-- Exact cardinal balance, including an isolated centre. -/
theorem card_vertices (u : V) :
    Fintype.card (Vertex G u) + (univ.filter (G.Adj u)).card = Fintype.card V := by
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (univ : Finset V)) (p := fun v => v ≠ u ∧ ¬ G.Adj u v)
  have he : univ.filter (fun v => ¬ (v ≠ u ∧ ¬ G.Adj u v)) = insert u (univ.filter (G.Adj u)) := by
    ext v
    by_cases hv : v = u <;> simp [hv]
  rw [he,Finset.card_insert_of_not_mem (by simp)] at hpart
  have hc : Fintype.card (Outside G u) = (univ.filter (fun v => v ≠ u ∧ ¬ G.Adj u v)).card := by
    exact Fintype.card_subtype _
  simp only [Vertex,Fintype.card_option,hc,Finset.card_univ] at *
  omega

theorem card_vertices_lt {u v : V} (he : G.Adj u v) :
    Fintype.card (Vertex G u) < Fintype.card V := by
  have hn : 0 < (univ.filter (G.Adj u)).card := Finset.card_pos.mpr ⟨v,by simp [he]⟩
  have hc := card_vertices u (G := G)
  omega

end
end CoefficientwiseRigidity.Star
