import CoefficientwiseRigidity.MainC
import Mathlib.GroupTheory.OrderOfElement

/-! Kernel-checked attainment examples for the uniform constants in Theorem B. -/
namespace CoefficientwiseRigidity
namespace Sharpness

def cycleFour : SimpleGraph (Fin 4) where
  Adj u v := u.val % 2 ≠ v.val % 2
  symm := fun _ _ h => h.symm
  loopless := fun _ h => h rfl

instance : DecidableRel cycleFour.Adj := fun _ _ => inferInstanceAs (Decidable (_ ≠ _))

def cycleFourBipartition : Bipartition cycleFour where
  side v := v.val % 2 == 0
  opposite := by decide

theorem cycleFour_connected : cycleFour.Connected := by
  have hr (v : Fin 4) : cycleFour.Reachable v 0 := by
    fin_cases v
    · exact SimpleGraph.Reachable.rfl
    · exact (by decide : cycleFour.Adj 1 0).reachable
    · exact (by decide : cycleFour.Adj 2 1).reachable.trans
        (by decide : cycleFour.Adj 1 0).reachable
    · exact (by decide : cycleFour.Adj 3 0).reachable
  exact { preconnected := fun u v => (hr u).trans (hr v).symm, nonempty := inferInstance }

theorem cycleFour_treewidth : TreewidthAtMostTwo cycleFour := by
  let T : SimpleGraph (Fin 2) := ⊤
  have ht : T.IsTree := by
    refine { isConnected := { preconnected := ?_, nonempty := inferInstance }, IsAcyclic := ?_ }
    · intro u v
      by_cases h : u = v
      · subst v; exact SimpleGraph.Reachable.rfl
      · exact (show T.Adj u v from h).reachable
    · intro v p hp
      have hlen := hp.isTrail.length_le_card_edgeFinset
      have hcard : T.edgeFinset.card = 1 := by decide
      have hmin := hp.three_le_length
      omega
  let bag : Fin 2 → Finset (Fin 4) := fun t => if t = 0 then {0,1,2} else {0,2,3}
  refine ⟨2, T, bag, ht, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · intro v x y
    by_cases h : x = y
    · subst y; exact SimpleGraph.Reachable.rfl
    · apply SimpleGraph.Adj.reachable
      change x.val ≠ y.val
      exact fun he => h (Subtype.ext he)

def twistedCycle (M : ℕ) (σ : Equiv.Perm (Fin M)) : Cover cycleFour M where
  transport u v := if u = 3 ∧ v = 0 then σ else
    if u = 0 ∧ v = 3 then σ.symm else Equiv.refl _
  reverse := by
    intro u v _
    fin_cases u <;> fin_cases v <;> simp

def cycleWalk : cycleFour.Walk 0 0 :=
  .cons (by decide : cycleFour.Adj 0 1)
    (.cons (by decide : cycleFour.Adj 1 2)
      (.cons (by decide : cycleFour.Adj 2 3)
        (.cons (by decide : cycleFour.Adj 3 0) .nil)))

theorem cycleWalk_transport (M : ℕ) (σ : Equiv.Perm (Fin M)) :
    walkTransport (twistedCycle M σ) cycleWalk = σ := by
  ext i
  simp [cycleWalk, walkTransport, twistedCycle]

theorem twistedCycle_holonomy (M : ℕ) (σ : Equiv.Perm (Fin M)) :
    holonomyGroup (twistedCycle M σ) 0 = Subgroup.zpowers σ := by
  have he (u v : Fin 4) : (twistedCycle M σ).transport u v ∈ Subgroup.zpowers σ := by
    simp only [twistedCycle]
    split_ifs
    · exact Subgroup.mem_zpowers σ
    · exact (Subgroup.zpowers σ).inv_mem (Subgroup.mem_zpowers σ)
    · exact (Subgroup.zpowers σ).one_mem
  have hw {u v : Fin 4} (p : cycleFour.Walk u v) :
      walkTransport (twistedCycle M σ) p ∈ Subgroup.zpowers σ := by
    induction p with
    | nil => exact (Subgroup.zpowers σ).one_mem
    | cons _ p ih => exact (Subgroup.zpowers σ).mul_mem ih (he _ _)
  apply le_antisymm
  · exact (Subgroup.closure_le _).mpr (by rintro τ ⟨p, rfl⟩; exact hw p)
  · apply Subgroup.zpowers_le.mpr
    exact Subgroup.subset_closure ⟨cycleWalk, cycleWalk_transport M σ⟩

theorem twistedCycle_nonflat (M : ℕ) (σ : Equiv.Perm (Fin M)) (hσ : σ ≠ 1) :
    ¬ Flat (twistedCycle M σ) := by
  intro hf
  have h := flat_trivial_closed_walks _ hf 0 cycleWalk
  rw [cycleWalk_transport] at h
  exact hσ h

def LegalColoring {M : ℕ} (X : Cover cycleFour M) (c : Fin 4 → Fin M) : Prop :=
  ∀ u v, cycleFour.Adj u v → X.transport u v (c u) ≠ c v

instance {M : ℕ} (X : Cover cycleFour M) : DecidablePred (LegalColoring X) :=
  fun c => inferInstanceAs (Decidable (∀ u v, cycleFour.Adj u v → X.transport u v (c u) ≠ c v))

noncomputable def singletonColor (M : ℕ) (S : Finset (Fin M)) (h : S.card = 1) : Fin M :=
  (Finset.card_eq_one.mp h).choose

theorem singletonColor_set (M : ℕ) (S : Finset (Fin M)) (h : S.card = 1) :
    S = {singletonColor M S h} := (Finset.card_eq_one.mp h).choose_spec

theorem singletonColor_mem (M : ℕ) (S : Finset (Fin M)) (h : S.card = 1) :
    singletonColor M S h ∈ S :=
  (congrArg (fun T : Finset (Fin M) => singletonColor M S h ∈ T)
    (singletonColor_set M S h)).mpr (Finset.mem_singleton_self _)

noncomputable def singletonEquiv {M : ℕ} (X : Cover cycleFour M) :
    Configuration X (fun _ => 1) ≃ {c : Fin 4 → Fin M // LegalColoring X c} where
  toFun S := ⟨fun v => singletonColor M (S.val v) (S.property.1 v), by
    intro u v he h
    exact S.property.2 u v he (singletonColor M (S.val u) (S.property.1 u))
      (singletonColor_mem M _ _) (by simpa only [h] using singletonColor_mem M (S.val v) (S.property.1 v))⟩
  invFun c := ⟨fun v => {c.val v}, by
    refine ⟨fun _ => Finset.card_singleton _, ?_⟩
    intro u v he i hi hj
    simp only [Finset.mem_singleton] at hi hj
    exact c.property u v he (by simpa [hi] using hj)⟩
  left_inv S := by
    apply Subtype.ext
    funext v
    exact (singletonColor_set M (S.val v) (S.property.1 v)).symm
  right_inv c := by
    apply Subtype.ext
    funext v
    have h := singletonColor_set M {c.val v} (Finset.card_singleton _)
    exact (Finset.singleton_injective h).symm

theorem singleton_count {M : ℕ} (X : Cover cycleFour M) :
    coefficient X (fun _ => 1) = Fintype.card {c : Fin 4 → Fin M // LegalColoring X c} :=
  Fintype.card_congr (singletonEquiv X)

def swapTwo : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def rotateThree : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2

theorem two_counts : ordinary cycleFour 2 (fun _ => 1) = 2 ∧
    coefficient (twistedCycle 2 swapTwo) (fun _ => 1) = 0 := by
  constructor
  · rw [ordinary, singleton_count]; decide
  · rw [singleton_count]; decide

theorem three_counts : ordinary cycleFour 3 (fun _ => 1) = 18 ∧
    coefficient (twistedCycle 3 rotateThree) (fun _ => 1) = 15 := by
  constructor
  · rw [ordinary, singleton_count]; decide
  · rw [singleton_count]; decide

theorem rotateThree_order : orderOf rotateThree = 3 := by
  apply (orderOf_eq_iff (by norm_num : 0 < (3 : ℕ))).mpr
  constructor
  · decide
  · intro m hm hp
    interval_cases m <;> decide

theorem three_holonomy_order : Nat.card (holonomyGroup (twistedCycle 3 rotateThree) 0) = 3 := by
  rw [twistedCycle_holonomy, Nat.card_zpowers, rotateThree_order]

end Sharpness
end CoefficientwiseRigidity
