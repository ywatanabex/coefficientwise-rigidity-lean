import CoefficientwiseRigidity.Elimination

/-!
All-size, arbitrary-list examples of actual elimination derivations, including
a four-cycle. These establish nonvacuous use of the derivation relation;
they do not identify that relation with the tree-bag definition.
-/
namespace CoefficientwiseRigidity.Network.Examples
open Kernel
noncomputable section

abbrev Endpoints := Option (Option Empty)
def left : Endpoints := some none
def right : Endpoints := none
theorem left_ne_right : left ≠ right := by simp [left, right]

def emptyNet (M : ℕ) (s : ℚ) (hs : 0 ≤ s) : Net M (fun e : Empty => nomatch e) := ⟨s, hs, []⟩

def twoBase (M p q : ℕ) (s : ℚ) (hs : 0 ≤ s) := ((emptyNet M s hs).lift p).lift q

theorem edge_eliminates (M p q : ℕ) (hp : p ≤ M) (s : ℚ) (hs : 0 ≤ s) (L : GainList M p q) :
    Eliminates M ((twoBase M p q s hs).addEdge left right left_ne_right L) := by
  change Eliminates M (((emptyNet M s hs).lift p).attachLeaf q none L)
  apply Eliminates.leaf ((emptyNet M s hs).lift p) q none hp L
  change Eliminates M ((emptyNet M (rowMass hp L * s) (mul_nonneg (rowMass_nonneg hp L) hs)).lift p)
  exact Eliminates.isolated _ p (Eliminates.empty _)

theorem parallel_eliminates (M p q : ℕ) (hp : p ≤ M) (s : ℚ) (hs : 0 ≤ s)
    (L K : GainList M p q) :
    Eliminates M (((twoBase M p q s hs).addEdge left right left_ne_right K).addEdge left right left_ne_right L) :=
  Eliminates.parallel (twoBase M p q s hs) left right left_ne_right L K
    (edge_eliminates M p q hp s hs (parallelLists L K))

theorem triangle_eliminates (M p m q : ℕ) (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (s : ℚ) (hs : 0 ≤ s) (L : GainList M p m) (K : GainList M m q) (J : GainList M p q) :
    Eliminates M (((twoBase M p q s hs).addEdge left right left_ne_right J).attachSeries m left right L K) :=
  Eliminates.series ((twoBase M p q s hs).addEdge left right left_ne_right J)
    m left right left_ne_right hp hm hq L K
    (parallel_eliminates M p q hp s hs (serialLists hp hm hq L K) J)

theorem path_with_chord_eliminates (M p m q : ℕ) (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M)
    (s : ℚ) (hs : 0 ≤ s) (L : GainList M p m) (K : GainList M m q) (J : GainList M p q) :
    Eliminates M (((twoBase M p q s hs).attachSeries m left right L K).addEdge
      (some left) (some right) (fun h => left_ne_right (Option.some.inj h)) J) := by
  let target := ((twoBase M p q s hs).addEdge left right left_ne_right J).attachSeries m left right L K
  apply Eliminates.reorder _ target.edges
  · change List.Perm [_ , _, _] [_, _, _]
    exact List.Perm.trans (List.Perm.swap _ _ _) (List.Perm.cons _ (List.Perm.swap _ _ _))
  · exact triangle_eliminates M p m q hp hm hq s hs L K J

/-- The concrete four-cycle with arbitrary lists and gains at every edge. -/
theorem cycle_four_eliminates (M p m q n : ℕ)
    (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M) (hn : n ≤ M)
    (s : ℚ) (hs : 0 ≤ s) (L : GainList M p m) (K : GainList M m q)
    (L' : GainList M p n) (K' : GainList M n q) :
    Eliminates M (((twoBase M p q s hs).attachSeries m left right L K).attachSeries
      n (some left) (some right) L' K') := by
  apply Eliminates.series ((twoBase M p q s hs).attachSeries m left right L K) n (some left) (some right)
    (fun h => left_ne_right (Option.some.inj h)) hp hn hq L' K'
  exact path_with_chord_eliminates M p m q hp hm hq s hs L K (serialLists hp hn hq L' K')

theorem cycle_four_comparison (M p m q n : ℕ)
    (hp : p ≤ M) (hm : m ≤ M) (hq : q ≤ M) (hn : n ≤ M)
    (s : ℚ) (hs : 0 ≤ s) (L : GainList M p m) (K : GainList M m q)
    (L' : GainList M p n) (K' : GainList M n q) :
    let N := ((twoBase M p q s hs).attachSeries m left right L K).attachSeries
      n (some left) (some right) L' K'
    N.value false ≤ N.value true :=
  (cycle_four_eliminates M p m q n hp hm hq hn s hs L K L' K').comparison

end
end CoefficientwiseRigidity.Network.Examples
