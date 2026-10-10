import CoefficientwiseRigidity.NetworkPacking
import CoefficientwiseRigidity.TreeElimination
import CoefficientwiseRigidity.Support
import Mathlib.Logic.Equiv.Option

/-!
K4 comparison from the original width-two tree-bag definition. The induction
uses concrete finite sums and gain lists; no elimination-existence hypothesis
or comparison oracle is assumed.
-/
namespace CoefficientwiseRigidity.Network
open Kernel Finset
noncomputable section
variable {M m : ℕ} {V : Type} [Fintype V] {p : V → ℕ}

theorem Net.twoSpokes_value (N : Net M p) (u w : V)
    (L : GainList M (p u) m) (K : GainList M (p w) m) (b : Bool) :
    (N.attachSpokes m (.cons u L (.cons w K .nil))).value b =
      (N.attachSeries m u w L (reverseList K)).value b := by
  classical
  unfold Net.value
  simp only [Net.attachSpokes, Net.attachSeries, Net.addEdge, weight_cons, Edge.eval,
    kernel_reverse]

/-- The remaining proof for a packed star has only zero, one or two spokes. -/
theorem Net.star_comparison (N : Net M p) {S : List V} (K : Spokes M p m S)
    (hsize : S.length ≤ 2) (hnd : S.Nodup) (hp : ∀ u, p u ≤ M) (hm : m ≤ M)
    (G : SimpleGraph V) (hE : ∀ e ∈ N.edges, G.Adj e.left e.right)
    (hfill : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → G.Adj u w)
    (hrec : ∀ R : Net M p, (∀ e ∈ R.edges, G.Adj e.left e.right) → R.value false ≤ R.value true) :
    (N.attachSpokes m K).value false ≤ (N.attachSpokes m K).value true := by
  cases K with
  | nil =>
    simpa only [Net.attachSpokes, Net.isolated_value] using
      mul_le_mul_of_nonneg_left (hrec N hE) (Nat.cast_nonneg (M.choose m) : (0 : ℚ) ≤ _)
  | @cons S u L K =>
    cases K with
    | nil =>
      change (N.attachLeaf m u L).value false ≤ (N.attachLeaf m u L).value true
      simpa only [Net.leaf_value N m u (hp u) L] using
        mul_le_mul_of_nonneg_left (hrec N hE) (rowMass_nonneg (hp u) L)
    | @cons T w J K =>
      have huv : u ≠ w := by
        have := (List.nodup_cons.mp hnd).1
        simp only [List.mem_cons, not_or] at this
        exact this.1
      cases K with
      | nil =>
        rw [Net.twoSpokes_value, Net.twoSpokes_value,
          Net.series_value N m u w huv (hp u) hm (hp w),
          Net.series_value N m u w huv (hp u) hm (hp w)]
        apply hrec
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hfill u (by simp) w (by simp) huv
        · exact hE e he
      | cons z P K => simp only [List.length_cons] at hsize; omega

/-- One real elimination step for an arbitrary network on `Option V`. -/
theorem Net.option_comparison (q : Option V → ℕ) (N : Net M q)
    (H : SimpleGraph (Option V)) (S : List V) (hsize : S.length ≤ 2) (hnd : S.Nodup)
    (hq : ∀ u, q u ≤ M) (hS : ∀ u, H.Adj none (some u) → u ∈ S)
    (hE : ∀ e ∈ N.edges, H.Adj e.left e.right)
    (G : SimpleGraph V) (hold : ∀ u w, H.Adj (some u) (some w) → G.Adj u w)
    (hfill : ∀ u ∈ S, ∀ w ∈ S, u ≠ w → G.Adj u w)
    (hrec : ∀ (p : V → ℕ) (R : Net M p), (∀ u, p u ≤ M) →
      (∀ e ∈ R.edges, G.Adj e.left e.right) → R.value false ≤ R.value true) :
    N.value false ≤ N.value true := by
  obtain ⟨m,p,rfl⟩ : ∃ (m : ℕ) (p : V → ℕ), q = extendRanks m p :=
    ⟨q none, fun u => q (some u), by funext u; cases u <;> rfl⟩
  obtain ⟨R,K,hR,hK⟩ := N.pack H S hS hE
  have hcomp := R.star_comparison K hsize hnd (fun u => hq (some u)) (hq none) G
    (fun e he => hold _ _ (hR e he)) hfill
    (fun R hR => hrec p R (fun u => hq (some u)) hR)
  exact hK.1.trans (hcomp.trans_eq hK.2.symm)

private theorem treewidth_comparison_aux (n : ℕ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
      Fintype.card V = n → TreewidthAtMostTwo G →
      ∀ (p : V → ℕ) (N : Net M p), (∀ u, p u ≤ M) →
        (∀ e ∈ N.edges, G.Adj e.left e.right) → N.value false ≤ N.value true := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ G hcard hG p N hp hN
    cases isEmpty_or_nonempty V with
    | inl h =>
      haveI := h
      simp only [Net.empty_value, le_refl]
    | inr h =>
      haveI := h
      obtain ⟨v,S,hv,hsize,hS,hGs⟩ := Structure.treewidth_smoothing_step hG
      let W := {w : V // w ≠ v}
      let e : Option W ≃ V := Equiv.optionSubtypeNe v
      let H := G.comap e.toEmbedding
      let T : List W := (S.subtype (fun w => w ≠ v)).toList
      have hlt : Fintype.card W < n := by
        rw [← hcard]
        exact Fintype.card_subtype_lt (by simp : ¬ (v ≠ v))
      have hT (w : W) : w ∈ T ↔ w.val ∈ S := by
        change w ∈ (S.subtype (fun w => w ≠ v)).toList ↔ w.val ∈ S
        rw [Finset.mem_toList]
        exact Finset.mem_subtype
      have hcomp : (N.rename e.symm).value false ≤ (N.rename e.symm).value true := by
        apply Net.option_comparison _ _ H T
          (G := Structure.smooth G v)
        · dsimp [T]
          rw [Finset.length_toList, Finset.card_subtype]
          exact (Finset.card_filter_le _ _).trans hsize
        · exact Finset.nodup_toList _
        · intro u
          exact hp (e u)
        · intro u hu
          exact (hT u).mpr ((hS u.val).mp hu)
        · intro f hf
          obtain ⟨g,hg,rfl⟩ := List.mem_map.mp
            (show f ∈ N.edges.map (Edge.rename e.symm) from hf)
          change G.Adj (e (e.symm g.left)) (e (e.symm g.right))
          simpa only [e.apply_symm_apply] using hN g hg
        · intro u w huw
          exact ⟨fun he => huw.ne (congrArg some he), Or.inl huw⟩
        · intro u hu w hw huw
          exact ⟨huw, Or.inr ⟨((hS u.val).mpr ((hT u).mp hu)).symm,
            (hS w.val).mpr ((hT w).mp hw)⟩⟩
        · intro p R hp hR
          exact ih _ hlt W (Structure.smooth G v) rfl hGs p R hp hR
      simpa only [Net.rename_value] using hcomp

/-- General K4a for rational Newton-cone gain lists on a width-two graph.
Ranks zero and M, zero factors, parallel edges, and disconnected graphs are included. -/
theorem Net.comparison_of_treewidth [DecidableEq V] (N : Net M p)
    (hp : ∀ u, p u ≤ M) (hG : TreewidthAtMostTwo N.graph) :
    N.value false ≤ N.value true := by
  apply treewidth_comparison_aux (Fintype.card V) V N.graph rfl hG p N hp
  intro e he
  exact ⟨e,he,Or.inl ⟨rfl,rfl⟩⟩

end
end CoefficientwiseRigidity.Network

namespace CoefficientwiseRigidity
open Network
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ} {a : V → ℕ}

/-- Coefficient comparison on bipartite width-two bases, without an assumed
elimination derivation. This is the comparison part, not the rigidity converse. -/
theorem coefficient_le_of_treewidth_feasible (b : Bipartition G) (X : Cover G M)
    (ha : Feasible G M a) (hG : TreewidthAtMostTwo G) :
    coefficient X a ≤ ordinary G M a := by
  have hp : ∀ u, inclusionRanks b M a u ≤ M := by
    intro u
    unfold inclusionRanks
    split
    · exact ha.1 u
    · exact Nat.sub_le _ _
  have h := (inclusionNetwork b X a).comparison_of_treewidth hp (by
    simpa only [inclusionNetwork_graph] using hG)
  rw [inclusionNetwork_value b X ha, inclusionNetwork_ordinary b X ha] at h
  exact_mod_cast h

/-- All occupation vectors, including the infeasible zero-count boundary. -/
theorem coefficient_le_of_treewidth (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (hG : TreewidthAtMostTwo G) : coefficient X a ≤ ordinary G M a := by
  classical
  by_cases ha : Feasible G M a
  · exact coefficient_le_of_treewidth_feasible b X ha hG
  · rw [coefficient_zero_of_not_feasible X a ha]
    exact Nat.zero_le _

/-- The exact support-dependent comparison in the width-two branch of Main A.
Bipartiteness remains explicit; no rigidity converse is claimed here. -/
theorem coefficient_le_of_active_treewidth (b : Bipartition G) (X : Cover G M)
    (a : V → ℕ) (hG : TreewidthAtMostTwo (supportGraph G a)) :
    coefficient X a ≤ ordinary G M a := by
  let b' : Bipartition (supportGraph G a) :=
    ⟨fun v => b.side v.val, fun h => b.opposite h⟩
  rw [coefficient_support_eq X a, ordinary_support_eq G M a]
  exact coefficient_le_of_treewidth b' (supportCover X a) (fun v => a v.val) hG

end
end CoefficientwiseRigidity
