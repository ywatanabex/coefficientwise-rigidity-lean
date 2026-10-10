import CoefficientwiseRigidity.NetworkExactPacking
import Mathlib.Logic.Equiv.Option

/-!
An exact degree-zero/one/two presentation is constructed from the original
tree-bag definition. The original factors, gains and scalar are retained.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
open scoped Classical
noncomputable section
variable {M : ℕ} {V : Type} {p q : V → ℕ}

def Net.changeRanks (N : Net M p) (h : p = q) : Net M q := h ▸ N

theorem Net.changeRanks_value [Fintype V] (N : Net M p) (h : p = q) (b : Bool) :
    (N.changeRanks h).value b = N.value b := by cases h; rfl

theorem Net.changeRanks_scalar (N : Net M p) (h : p = q) :
    (N.changeRanks h).scalar = N.scalar := by cases h; rfl

theorem Net.changeRanks_flat (N : Net M p) (h : p = q) :
    (N.changeRanks h).Flat ↔ N.Flat := by cases h; rfl

theorem Net.changeRanks_rigid (N : Net M p) (h : p = q)
    (Γ : Subgroup (Equiv.Perm (Fin M))) :
    (N.changeRanks h).Rigid Γ ↔ N.Rigid Γ := by cases h; rfl

theorem Net.changeRanks_simple (N : Net M p) (h : p = q) :
    (N.changeRanks h).Simple ↔ N.Simple := by cases h; rfl

theorem Net.changeRanks_supported (N : Net M p) (h : p = q) (G : SimpleGraph V) :
    (∀ e ∈ (N.changeRanks h).edges, G.Adj e.left e.right) ↔
      ∀ e ∈ N.edges, G.Adj e.left e.right := by cases h; rfl

theorem optionRanks (p : V → ℕ) (v : V) :
    p ∘ Equiv.optionSubtypeNe v = extendRanks (p v) (fun w : {w : V // w ≠ v} => p w.val) := by
  funext w
  cases w <;> rfl

/-- Separate a named vertex without changing its ranks, factors or scalar. -/
def Net.atVertex (N : Net M p) (v : V) :
    Net M (extendRanks (p v) (fun w : {w : V // w ≠ v} => p w.val)) :=
  (N.rename (Equiv.optionSubtypeNe v).symm).changeRanks (optionRanks p v)

theorem Net.atVertex_value [Fintype V] (N : Net M p) (v : V) (b : Bool) :
    (N.atVertex v).value b = N.value b := by
  rw [Net.atVertex, Net.changeRanks_value, Net.rename_value]

theorem Net.atVertex_flat (N : Net M p) (v : V) : (N.atVertex v).Flat ↔ N.Flat := by
  rw [Net.atVertex, Net.changeRanks_flat, Net.flat_rename_iff]

/-- No low-degree presentation is assumed: bags supply the vertex, its genuine
neighbours, and the width-two smoothed graph used by the smaller induction. -/
theorem Net.low_degree_rigid_presentation [Fintype V] [Nonempty V]
    (N : Net M p) (Γ : Subgroup (Equiv.Perm (Fin M)))
    (hr : N.Rigid Γ) (hs : N.Simple) (hw : TreewidthAtMostTwo N.graph) :
    ∃ v : V,
      let W := {w : V // w ≠ v}
      let q : W → ℕ := fun w => p w.val
      ∃ (R : Net M q) (S : List W) (K : Spokes M q (p v) S),
        R.scalar = N.scalar ∧ EdgeListEquiv (N.atVertex v).edges (R.attachSpokes (p v) K).edges ∧
        R.Rigid Γ ∧ K.Rigid Γ ∧ R.Simple ∧ S.Nodup ∧ S.length ≤ 2 ∧
        Fintype.card W < Fintype.card V ∧ TreewidthAtMostTwo (Structure.smooth N.graph v) ∧
        (∀ e ∈ R.edges, (Structure.smooth N.graph v).Adj e.left e.right) ∧
        (∀ u ∈ S, ∀ w ∈ S, u ≠ w → (Structure.smooth N.graph v).Adj u w) := by
  classical
  obtain ⟨v,T,_,hsize,hT,hw'⟩ := Structure.treewidth_smoothing_step hw
  let W := {w : V // w ≠ v}
  let e : Option W ≃ V := Equiv.optionSubtypeNe v
  let H := N.graph.comap e.toEmbedding
  let U : Finset W := T.subtype (fun w => w ≠ v)
  have hU (w : W) : w ∈ U ↔ w.val ∈ T := Finset.mem_subtype
  have hH : ∀ f ∈ (N.atVertex v).edges, H.Adj f.left f.right := by
    apply ((N.rename e.symm).changeRanks_supported (optionRanks p v) H).mpr
    intro f hf
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hf
    change N.graph.Adj (e (e.symm g.left)) (e (e.symm g.right))
    simp only [e.apply_symm_apply]
    exact ⟨g,hg,Or.inl ⟨rfl,rfl⟩⟩
  have hr' : (N.atVertex v).Rigid Γ :=
    ((N.rename e.symm).changeRanks_rigid _ Γ).mpr (N.rigid_rename e.symm Γ hr)
  have hs' : (N.atVertex v).Simple :=
    ((N.rename e.symm).changeRanks_simple _).mpr (N.simple_rename e.symm hs)
  obtain ⟨R,S,K,hc,he,hR,hK,hRs,hS,hcS,hSU,hE⟩ :=
    (N.atVertex v).pack_rigid_simple Γ hr' hs' H hH U
      (fun u hu => (hU u).mpr ((hT u.val).mp hu))
  refine ⟨v,R,S,K,?_,he,hR,hK,hRs,hS,?_,?_,hw',?_,?_⟩
  · simpa only [Net.atVertex, Net.changeRanks_scalar, Net.rename] using hc
  · exact hcS.trans ((Finset.card_subtype _ _).trans_le
      ((Finset.card_filter_le _ _).trans hsize))
  · exact Fintype.card_subtype_lt (by simp : ¬ (v ≠ v))
  · intro f hf
    exact ⟨f.distinct, Or.inl (hE f hf)⟩
  · intro u hu w hw huw
    exact ⟨huw, Or.inr ⟨((hT u.val).mpr ((hU u).mp (hSU u hu))).symm,
      (hT w.val).mpr ((hU w).mp (hSU w hw))⟩⟩

end
end CoefficientwiseRigidity.Network
