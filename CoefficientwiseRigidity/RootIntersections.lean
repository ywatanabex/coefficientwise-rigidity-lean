import CoefficientwiseRigidity.BipartiteAssignments

/-! Exact retained-root fibre comparison for actual independent-set configurations. -/
namespace CoefficientwiseRigidity.Intersections
open Finset Compression Structure
open scoped Classical
noncomputable section
variable {V : Type} {M : ℕ}

def remainingColumns (U : Finset V) (root : V) : Finset V := U.erase root

def pinColumn (Q : V → Finset (Fin M)) (root : V) (A : Finset (Fin M)) : V → Finset (Fin M) :=
  Function.update Q root A

theorem sumSet_pin (q : V → ℕ) (U : Finset V) (root : V) (hr : root ∈ U)
    (A : Finset (Fin M)) (hA : A.card = q root)
    (F : (V → Finset (Fin M)) → ℚ) (Q : V → Finset (Fin M)) :
    sumSet q U (fun R => if R root = A then F R else 0) Q =
      sumSet q (remainingColumns U root) F (pinColumn Q root A) := by
  unfold remainingColumns pinColumn
  let L := (U.erase root).toList
  have hn : root ∉ L := by simp [L]
  have hnd : (root :: L).Nodup := List.nodup_cons.mpr ⟨hn,(U.erase root).nodup_toList⟩
  have he : (root :: L).toFinset = U := by simp [L,Finset.insert_erase hr]
  rw [sumSet_of_list q U (root :: L) hnd he]
  simp only [sumColumns,Function.update_self]
  have hh : ∀ R : V → Finset (Fin M),
      (∑ B : Finset (Fin M), if B.card = q root then if B = A then F (Function.update R root B) else 0 else 0) =
        F (Function.update R root A) := by
    intro R
    rw [Finset.sum_eq_single A]
    · simp [hA]
    · intro B _ hB; simp [hB]
    · simp
  rw [sumColumns_congr q L hh Q,sumColumns_update q L root hn]
  rfl

variable [Fintype V] [DecidableEq V] {G : SimpleGraph V}

theorem rootFibre_eq_intersection_sum (b : Bipartition G) (X : Cover G M) (a : V → ℕ)
    (ha : ∀ v, a v ≤ M) (root : V) (hr : b.side root = false)
    (A : Finset (Fin M)) (hA : A.card = a root) :
    (rootFibre X a root A : ℚ) = sumSet (columnRanks M a) (remainingColumns (columnSet b) root)
      (fun Q => binomialCost (fun u : LeftRows b => a u.val) (ranks (graphRows b) (coverGains b X) Q))
      (pinColumn (fun _ => ∅) root Aᶜ) := by
  let e := configurationBipartiteEquiv b X a ha
  have hcount : (rootFibre X a root A : ℚ) =
      ∑ S : Configuration X a, if S.val root = A then 1 else 0 := by
    rw [rootFibre,Fintype.card_subtype,Finset.card_filter]
    push_cast
    rfl
  rw [hcount]
  have he : (∑ S : Configuration X a, if S.val root = A then (1 : ℚ) else 0) =
      ∑ C : BipartiteChoices b X a, if C.1.val root = Aᶜ then 1 else 0 := by
    apply Fintype.sum_equiv e
    intro S
    simp [e,configurationBipartiteEquiv,toBipartiteChoices,rightComplements,hr]
  rw [he,Fintype.sum_sigma]
  have htotal : (∑ Q : ColumnChoices b M a, ∑ _C : RowCompletions b X a Q.val,
      if Q.val root = Aᶜ then (1 : ℚ) else 0) =
      ∑ Q : ColumnChoices b M a, if Q.val root = Aᶜ then (Fintype.card (RowCompletions b X a Q.val) : ℚ) else 0 := by
    apply Finset.sum_congr rfl
    intro Q _
    by_cases hQ : Q.val root = Aᶜ <;> simp [hQ]
  rw [htotal]
  have hsum : (∑ Q : ColumnChoices b M a,
      if Q.val root = Aᶜ then (Fintype.card (RowCompletions b X a Q.val) : ℚ) else 0) =
      sumSet (columnRanks M a) (columnSet b)
        (fun Q => if Q root = Aᶜ then (Fintype.card (RowCompletions b X a Q) : ℚ) else 0) (fun _ => ∅) := by
    rw [sumSet_eq_assignment_sum]
    symm
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun Q => by simp) _
  rw [hsum,sumSet_pin (columnRanks M a) (columnSet b) root (by simp [columnSet,hr]) Aᶜ
    (by simp [Finset.card_compl,hA,columnRanks])]
  simp only [card_rowCompletions]

theorem rootFibre_le_of_chordalBipartite (b : Bipartition G) (hg : ChordalBipartite G)
    (X : Cover G M) (a : V → ℕ) (ha : ∀ v, a v ≤ M)
    (root : V) (hr : b.side root = false) (A : Finset (Fin M)) (hA : A.card = a root) :
    rootFibre X a root A ≤ rootFibre (trivialCover G M) a root A := by
  have h := graph_root_cone_comparison b hg root hr (coverGains b X) (columnRanks M a)
    (binomialCost_cone (fun u : LeftRows b => a u.val)) (pinColumn (fun _ => ∅) root Aᶜ)
  have hx := rootFibre_eq_intersection_sum b X a ha root hr A hA
  have hy := rootFibre_eq_intersection_sum b (trivialCover G M) a ha root hr A hA
  dsimp only [remainingColumns] at hx hy
  rw [← hx] at h
  change (rootFibre X a root A : ℚ) ≤ sumSet (columnRanks M a) (remainingColumns (columnSet b) root)
    (fun Q => binomialCost (fun u : LeftRows b => a u.val)
      (ranks (graphRows b) (coverGains b (trivialCover G M)) Q)) (pinColumn (fun _ => ∅) root Aᶜ) at h
  dsimp only [remainingColumns] at h
  rw [← hy] at h
  exact_mod_cast h

end
end CoefficientwiseRigidity.Intersections

namespace CoefficientwiseRigidity
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def Bipartition.flip (b : Bipartition G) : Bipartition G where
  side v := !(b.side v)
  opposite := by
    intro u v he
    have hn := b.opposite he
    cases hu : b.side u <;> cases hv : b.side v <;> simp_all

/-- Either side can contain the prescribed root. No feasibility, interior-rank
or pin-cardinality assumption is needed for the final fibre inequality. -/
theorem rootFibre_le_of_chordalBipartite (X : Cover G M) (a : V → ℕ)
    (hg : ChordalBipartite G) (root : V) (A : Finset (Fin M)) :
    rootFibre X a root A ≤ rootFibre (trivialCover G M) a root A := by
  by_cases hf : Feasible G M a
  · by_cases hA : A.card = a root
    · obtain ⟨b⟩ := hg.1
      cases hr : b.side root with
      | false => exact Intersections.rootFibre_le_of_chordalBipartite b hg X a hf.1 root hr A hA
      | true =>
        exact Intersections.rootFibre_le_of_chordalBipartite b.flip hg X a hf.1 root
          (by simp [Bipartition.flip,hr]) A hA
    · haveI : IsEmpty {S : Configuration X a // S.val root = A} := ⟨by
        intro S
        apply hA
        rw [← S.property]
        exact S.val.property.1 root⟩
      have hz : rootFibre X a root A = 0 := Fintype.card_eq_zero
      rw [hz]
      exact Nat.zero_le _
  · haveI : IsEmpty (Configuration X a) := ⟨fun S => hf (feasible_of_admissible X a S.property)⟩
    have hz : rootFibre X a root A = 0 := Fintype.card_eq_zero
    rw [hz]
    exact Nat.zero_le _

end
end CoefficientwiseRigidity
