import CoefficientwiseRigidity.Feasibility

/-! Global ordinary assignments with any two distinct labels at opposite edge ends. -/
namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section

theorem exists_perm_two {A : Type*} {a b c d : A} (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ ρ : Equiv.Perm A, ρ a = c ∧ ρ b = d := by
  let p := Equiv.swap a c
  have hp : p a = c := Equiv.swap_apply_left _ _
  have hb : p b ≠ c := by
    rw [← hp]
    exact fun h => hab (p.injective h).symm
  refine ⟨p.trans (Equiv.swap (p b) d),?_,?_⟩
  · simp only [Equiv.trans_apply,hp]
    exact Equiv.swap_apply_of_ne_of_ne hb.symm hcd
  · simp

variable {V : Type*} {G : SimpleGraph V} {M : ℕ}

theorem exists_ordinary_edge_labels (b : Bipartition G) (a : V → ℕ)
    (ha : Feasible G M a) {x y : V} (hxy : G.Adj x y) (hx : b.side x = true)
    (hp : 0 < a x) (hq : 0 < a y) {i j : Fin M} (hij : i ≠ j) :
    ∃ S : Configuration (trivialCover G M) a, i ∈ S.val x ∧ j ∈ S.val y := by
  have hM : 2 ≤ M := by have := ha.2 x y hxy; omega
  let first : Fin M := ⟨0,by omega⟩
  let last : Fin M := ⟨M - 1,by omega⟩
  have hfl : first ≠ last := by
    intro h
    have hv := congrArg Fin.val h
    dsimp [first,last] at hv
    omega
  obtain ⟨ρ,hρ0,hρ1⟩ := exists_perm_two hfl hij
  have hs : Admissible (trivialCover G M) a (relabel (fun _ => ρ) (nestedAssignment b M a)) :=
    relabel_admissible _ _ a (fun _ => ρ) (fun _ _ _ _ _ _ => rfl) (nestedAssignment_admissible b a ha)
  refine ⟨⟨_,hs⟩,?_,?_⟩
  · apply Finset.mem_map.mpr
    refine ⟨first,?_,hρ0⟩
    simpa [nestedAssignment,hx,first] using hp
  · have hy : b.side y = false := by
      have hn := b.opposite hxy
      rw [hx] at hn
      cases h : b.side y <;> simp_all
    apply Finset.mem_map.mpr
    refine ⟨last,?_,hρ1⟩
    have hay := ha.1 y
    simp [nestedAssignment,hy,last]
    omega

end
end CoefficientwiseRigidity
