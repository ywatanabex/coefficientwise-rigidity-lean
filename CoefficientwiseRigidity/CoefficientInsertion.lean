import CoefficientwiseRigidity.KernelInsertion

/-!
The ordinary insertion for the ORIGINAL independent-set coefficients.
The two sides receive opposite new labels, so every existing disjointness
constraint is retained. No auxiliary overlap-network normalization is used.
-/
namespace CoefficientwiseRigidity
open Kernel Finset
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def insertAssignment (b : Bipartition G) (S : Assignment V M) : Assignment V (M + 2) :=
  fun v => (liftSet (S v) (b.side v)).map (insertionLabels M).toEmbedding

omit [Fintype V] [DecidableEq V] in
theorem insertAssignment_injective (b : Bipartition G) :
    Function.Injective (@insertAssignment V _ M b) := by
  intro S T h
  funext v
  have hm : liftSet (S v) (b.side v) = liftSet (T v) (b.side v) :=
    Finset.map_injective _ (congrFun h v)
  simpa [liftSet] using congrArg Finset.toLeft hm

omit [Fintype V] [DecidableEq V] in
theorem insertAssignment_admissible (b : Bipartition G) (a : V → ℕ)
    {S : Assignment V M} (hS : Admissible (trivialCover G M) a S) :
    Admissible (trivialCover G (M + 2)) (fun v => a v + 1) (insertAssignment b S) := by
  refine ⟨fun v => by simp [insertAssignment, card_liftSet, hS.1], ?_⟩
  intro u v huv i hi hj
  have hi' : (insertionLabels M).symm i ∈ liftSet (S u) (b.side u) :=
    Finset.mem_map_equiv.mp hi
  have hj' : (insertionLabels M).symm i ∈ liftSet (S v) (b.side v) :=
    Finset.mem_map_equiv.mp hj
  cases h : (insertionLabels M).symm i with
  | inl k =>
    have hk : k ∈ S u := by simpa [h, liftSet] using hi'
    have hl : k ∈ S v := by simpa [h, liftSet] using hj'
    exact hS.2 u v huv k hk hl
  | inr c =>
    have hk : c = b.side u := by simpa [h, liftSet] using hi'
    have hl : c = b.side v := by simpa [h, liftSet] using hj'
    exact b.opposite huv (hk.symm.trans hl)

def insertConfiguration (b : Bipartition G) (a : V → ℕ) :
    Configuration (trivialCover G M) a →
      Configuration (trivialCover G (M + 2)) (fun v => a v + 1) :=
  fun S => ⟨insertAssignment b S.val, insertAssignment_admissible b a S.property⟩

omit [Fintype V] [DecidableEq V] in
theorem insertConfiguration_injective (b : Bipartition G) (a : V → ℕ) :
    Function.Injective (insertConfiguration (M := M) b a) := by
  intro S T h
  exact Subtype.ext (insertAssignment_injective b (congrArg Subtype.val h))

theorem ordinary_le_inserted (b : Bipartition G) (a : V → ℕ) :
    ordinary G M a ≤ ordinary G (M + 2) (fun v => a v + 1) :=
  Fintype.card_le_of_injective _ (insertConfiguration_injective b a)

/-- The actual reserve is at most the actual ordinary coefficient.
Full original occupations at isolated vertices are allowed: their reserve is zero. -/
theorem reserve_le_ordinary (b : Bipartition G) (a : V → ℕ)
    (hM : 2 ≤ M) (ha : Positive a) : reserve G M a ≤ ordinary G M a := by
  have he : M - 2 + 2 = M := by omega
  have hr : (fun v => a v - 1 + 1) = a := by
    funext v
    have := ha v
    omega
  have h := ordinary_le_inserted (M := M - 2) b (fun v => a v - 1)
  rw [he, hr] at h
  exact h

end
end CoefficientwiseRigidity
