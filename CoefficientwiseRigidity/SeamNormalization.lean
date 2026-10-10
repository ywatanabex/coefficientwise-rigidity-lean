import CoefficientwiseRigidity.SeamConfigurations
import CoefficientwiseRigidity.SerialTransport
import CoefficientwiseRigidity.RootIntersections

/-!
Concrete root/edge boundary cardinalities and ordinary fibre uniformity.
These results require no graph-class assumption. They justify the binomial
multipliers in the unchanged `MainCFibres` target.

Adapted from the user-supplied PRO handoff and checked locally.
-/
namespace CoefficientwiseRigidity.Gluing
open scoped BigOperators Classical
noncomputable section

section Fibres
variable {A B : Type*} [Fintype A] [Fintype B]

def allFibresEquiv (f : A → B) : A ≃ Σ b : B, {x : A // f x = b} where
  toFun x := ⟨f x, ⟨x, rfl⟩⟩
  invFun p := p.2.val
  left_inv x := rfl
  right_inv := by
    rintro ⟨b, x, hx⟩
    cases hx
    rfl

theorem card_eq_sum_fibres (f : A → B) :
    Fintype.card A = ∑ b : B, Fintype.card {x : A // f x = b} := by
  classical
  rw [Fintype.card_congr (allFibresEquiv f), Fintype.card_sigma]

end Fibres

/-- Normalized legal edge pins, including zero and full-rank boundary cases. -/
abbrev EdgePin (M p q : ℕ) :=
  {AB : Finset (Fin M) × Finset (Fin M) //
    AB.1.card = p ∧ AB.2.card = q ∧ Disjoint AB.1 AB.2}

def edgePinSigmaEquiv (M p q : ℕ) :
    EdgePin M p q ≃ Σ A : Kernel.Slice M p,
      {B : Finset (Fin M) // B.card = q ∧ Disjoint A.val B} where
  toFun AB := ⟨⟨AB.val.1, AB.property.1⟩,
    ⟨AB.val.2, AB.property.2.1, AB.property.2.2⟩⟩
  invFun AB := ⟨(AB.1.val, AB.2.val), AB.1.property, AB.2.property⟩
  left_inv AB := by apply Subtype.ext; rfl
  right_inv := by
    rintro ⟨⟨A, hA⟩, ⟨B, hB⟩⟩
    rfl

theorem card_disjoint_slice {M : ℕ} (A : Finset (Fin M)) (q : ℕ) :
    Fintype.card {B : Finset (Fin M) // B.card = q ∧ Disjoint A B} =
      (M - A.card).choose q := by
  classical
  calc
    Fintype.card {B : Finset (Fin M) // B.card = q ∧ Disjoint A B} =
        (Aᶜ.powersetCard q).card := by
      rw [Fintype.subtype_card]
      congr 1
      ext B
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powersetCard]
      constructor
      · rintro ⟨hB, hd⟩
        refine ⟨?_, hB⟩
        intro i hi
        exact Finset.mem_compl.mpr (fun hiA => Finset.disjoint_left.mp hd hiA hi)
      · rintro ⟨hBA, hB⟩
        refine ⟨hB, Finset.disjoint_left.mpr ?_⟩
        intro i hiA hiB
        exact Finset.mem_compl.mp (hBA hiB) hiA
    _ = (M - A.card).choose q := by
      rw [Finset.card_powersetCard, Finset.card_compl, Fintype.card_fin]

theorem card_edgePin (M p q : ℕ) :
    Fintype.card (EdgePin M p q) = M.choose p * (M - p).choose q := by
  classical
  rw [Fintype.card_congr (edgePinSigmaEquiv M p q), Fintype.card_sigma]
  simp only [card_disjoint_slice]
  have he : ∀ A : Kernel.Slice M p, (M - A.val.card).choose q = (M - p).choose q := by
    intro A
    rw [A.property]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Kernel.slice_card]
  simp

/-- Actual (not gauge-normalized) legal pins at an edge with transport σ. -/
abbrev TransportedEdgePin {M : ℕ} (σ : Equiv.Perm (Fin M)) (p q : ℕ) :=
  {AB : Finset (Fin M) × Finset (Fin M) //
    AB.1.card = p ∧ AB.2.card = q ∧ Disjoint (AB.1.map σ.toEmbedding) AB.2}

def transportedEdgePinEquiv {M : ℕ} (σ : Equiv.Perm (Fin M)) (p q : ℕ) :
    TransportedEdgePin σ p q ≃ EdgePin M p q where
  toFun AB := ⟨(AB.val.1.map σ.toEmbedding, AB.val.2),
    (Finset.card_map _).trans AB.property.1, AB.property.2⟩
  invFun AB := ⟨(AB.val.1.map σ.symm.toEmbedding, AB.val.2),
    (Finset.card_map _).trans AB.property.1, AB.property.2.1, by
      have hm : (AB.val.1.map σ.symm.toEmbedding).map σ.toEmbedding = AB.val.1 := by
        ext i
        simp
      rw [hm]
      exact AB.property.2.2⟩
  left_inv AB := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      simp
    · rfl
  right_inv AB := by
    apply Subtype.ext
    apply Prod.ext
    · ext i
      simp
    · rfl

theorem card_transportedEdgePin {M : ℕ} (σ : Equiv.Perm (Fin M)) (p q : ℕ) :
    Fintype.card (TransportedEdgePin σ p q) = M.choose p * (M - p).choose q := by
  classical
  rw [Fintype.card_congr (transportedEdgePinEquiv σ p q), card_edgePin]

/-- The common finite labelling action is transitive on equal-sized pairs
with equal intersection size; the disjoint case is the actual-edge boundary. -/
theorem exists_disjoint_pair_perm {M : ℕ} (A B A' B' : Finset (Fin M))
    (hA : A.card = A'.card) (hB : B.card = B'.card)
    (hd : Disjoint A B) (hd' : Disjoint A' B') :
    ∃ σ : Equiv.Perm (Fin M), A.map σ.toEmbedding = A' ∧ B.map σ.toEmbedding = B' := by
  apply Kernel.exists_pair_equiv A B A' B' rfl hA hB
  have hI : A ∩ B = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd
  have hI' : A' ∩ B' = ∅ := Finset.disjoint_iff_inter_eq_empty.mp hd'
  simp [hI, hI']

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

/-- A single permutation applied at every vertex preserves every ordinary configuration. -/
def ordinaryPermutationEquiv (a : V → ℕ) (σ : Equiv.Perm (Fin M)) :
    Configuration (trivialCover G M) a ≃ Configuration (trivialCover G M) a :=
  gaugeConfigurationEquiv (trivialCover G M) (trivialCover G M) a
    (fun _ => σ) (fun _ _ _ _ _ _ => rfl)

private theorem map_inverse_of_map_eq {A A' : Finset (Fin M)}
    (σ : Equiv.Perm (Fin M)) (h : A.map σ.toEmbedding = A') :
    A'.map σ.symm.toEmbedding = A := by
  rw [← h]
  ext i
  simp

def ordinaryRootFibrePermEquiv (a : V → ℕ) (root : V)
    (A A' : Finset (Fin M)) (σ : Equiv.Perm (Fin M)) (hσ : A.map σ.toEmbedding = A') :
    {S : Configuration (trivialCover G M) a // S.val root = A} ≃
      {S : Configuration (trivialCover G M) a // S.val root = A'} where
  toFun S := ⟨ordinaryPermutationEquiv a σ S.val, by
    change (S.val.val root).map σ.toEmbedding = A'
    rw [S.property, hσ]⟩
  invFun S := ⟨(ordinaryPermutationEquiv a σ).symm S.val, by
    change (S.val.val root).map σ.symm.toEmbedding = A
    rw [S.property]
    exact map_inverse_of_map_eq σ hσ⟩
  left_inv S := by apply Subtype.ext; exact (ordinaryPermutationEquiv a σ).symm_apply_apply S.val
  right_inv S := by apply Subtype.ext; exact (ordinaryPermutationEquiv a σ).apply_symm_apply S.val

theorem ordinary_rootFibre_eq (a : V → ℕ) (root : V) (A A' : Finset (Fin M))
    (hA : A.card = A'.card) :
    rootFibre (trivialCover G M) a root A = rootFibre (trivialCover G M) a root A' := by
  obtain ⟨σ, hσ, _⟩ := Kernel.exists_pair_equiv A ∅ A' ∅ rfl hA rfl (by simp)
  exact Fintype.card_congr (ordinaryRootFibrePermEquiv a root A A' σ hσ)

def ordinaryEdgeFibrePermEquiv (a : V → ℕ) (u v : V)
    (A B A' B' : Finset (Fin M)) (σ : Equiv.Perm (Fin M))
    (hA : A.map σ.toEmbedding = A') (hB : B.map σ.toEmbedding = B') :
    {S : Configuration (trivialCover G M) a // S.val u = A ∧ S.val v = B} ≃
      {S : Configuration (trivialCover G M) a // S.val u = A' ∧ S.val v = B'} where
  toFun S := ⟨ordinaryPermutationEquiv a σ S.val, by
    constructor
    · change (S.val.val u).map σ.toEmbedding = A'
      rw [S.property.1, hA]
    · change (S.val.val v).map σ.toEmbedding = B'
      rw [S.property.2, hB]⟩
  invFun S := ⟨(ordinaryPermutationEquiv a σ).symm S.val, by
    constructor
    · change (S.val.val u).map σ.symm.toEmbedding = A
      rw [S.property.1]
      exact map_inverse_of_map_eq σ hA
    · change (S.val.val v).map σ.symm.toEmbedding = B
      rw [S.property.2]
      exact map_inverse_of_map_eq σ hB⟩
  left_inv S := by apply Subtype.ext; exact (ordinaryPermutationEquiv a σ).symm_apply_apply S.val
  right_inv S := by apply Subtype.ext; exact (ordinaryPermutationEquiv a σ).apply_symm_apply S.val

theorem ordinary_edgeFibre_eq (a : V → ℕ) (u v : V)
    (A B A' B' : Finset (Fin M))
    (hA : A.card = A'.card) (hB : B.card = B'.card)
    (hd : Disjoint A B) (hd' : Disjoint A' B') :
    edgeFibre (trivialCover G M) a u v A B = edgeFibre (trivialCover G M) a u v A' B' := by
  obtain ⟨σ, hσA, hσB⟩ := exists_disjoint_pair_perm A B A' B' hA hB hd hd'
  exact Fintype.card_congr (ordinaryEdgeFibrePermEquiv a u v A B A' B' σ hσA hσB)

def rootSlice (X : Cover G M) (a : V → ℕ) (root : V)
    (S : Configuration X a) : Kernel.Slice M (a root) := ⟨S.val root, S.property.1 root⟩

def rootSliceFibreEquiv (X : Cover G M) (a : V → ℕ) (root : V)
    (A : Kernel.Slice M (a root)) :
    {S : Configuration X a // rootSlice X a root S = A} ≃
      {S : Configuration X a // S.val root = A.val} where
  toFun S := ⟨S.val, congrArg Subtype.val S.property⟩
  invFun S := ⟨S.val, Subtype.ext S.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coefficient_eq_sum_rootFibre (X : Cover G M) (a : V → ℕ) (root : V) :
    coefficient X a = ∑ A : Kernel.Slice M (a root), rootFibre X a root A.val := by
  classical
  have h := card_eq_sum_fibres (rootSlice X a root)
  change coefficient X a = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro A _
  simp only [rootFibre, edgeFibre, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (rootSliceFibreEquiv X a root A)

/-- The original cover induces a map to its actual transported legal edge pins. -/
def coverEdgePin (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (S : Configuration X a) : TransportedEdgePin (X.transport u v) (a u) (a v) := by
  refine ⟨(S.val u, S.val v), S.property.1 u, S.property.1 v, ?_⟩
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j, hjS, he⟩ := Finset.mem_map.mp hi
  have he' : X.transport u v j = i := he
  exact S.property.2 u v huv j hjS (he'.symm ▸ hj)

def coverEdgePinFibreEquiv (X : Cover G M) (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (AB : TransportedEdgePin (X.transport u v) (a u) (a v)) :
    {S : Configuration X a // coverEdgePin X a u v huv S = AB} ≃
      {S : Configuration X a // S.val u = AB.val.1 ∧ S.val v = AB.val.2} where
  toFun S := ⟨S.val,
    congrArg (fun p : TransportedEdgePin (X.transport u v) (a u) (a v) => p.val.1) S.property,
    congrArg (fun p : TransportedEdgePin (X.transport u v) (a u) (a v) => p.val.2) S.property⟩
  invFun S := ⟨S.val, Subtype.ext (Prod.ext S.property.1 S.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem coefficient_eq_sum_edgeFibre (X : Cover G M) (a : V → ℕ)
    (u v : V) (huv : G.Adj u v) :
    coefficient X a = ∑ AB : TransportedEdgePin (X.transport u v) (a u) (a v),
      edgeFibre X a u v AB.val.1 AB.val.2 := by
  classical
  have h := card_eq_sum_fibres (coverEdgePin X a u v huv)
  change coefficient X a = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro AB _
  simp only [rootFibre, edgeFibre, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (coverEdgePinFibreEquiv X a u v huv AB)

/-- Exactly the root multiplier in MainCFibres, without division or feasibility assumptions. -/
theorem ordinary_root_normalization (a : V → ℕ) (root : V)
    (A : Finset (Fin M)) (hA : A.card = a root) :
    M.choose (a root) * rootFibre (trivialCover G M) a root A = ordinary G M a := by
  classical
  have h := coefficient_eq_sum_rootFibre (trivialCover G M) a root
  have he : ∀ B : Kernel.Slice M (a root),
      rootFibre (trivialCover G M) a root B.val = rootFibre (trivialCover G M) a root A := by
    intro B
    exact ordinary_rootFibre_eq a root B.val A (B.property.trans hA.symm)
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Kernel.slice_card] at h
  exact h.symm

def ordinaryEdgePin (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (S : Configuration (trivialCover G M) a) : EdgePin M (a u) (a v) :=
  ⟨(S.val u, S.val v), S.property.1 u, S.property.1 v,
    Finset.disjoint_left.mpr (fun i hi hj => S.property.2 u v huv i hi hj)⟩

def ordinaryEdgePinFibreEquiv (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (AB : EdgePin M (a u) (a v)) :
    {S : Configuration (trivialCover G M) a // ordinaryEdgePin a u v huv S = AB} ≃
      {S : Configuration (trivialCover G M) a // S.val u = AB.val.1 ∧ S.val v = AB.val.2} where
  toFun S := ⟨S.val, congrArg (fun p : EdgePin M (a u) (a v) => p.val.1) S.property,
    congrArg (fun p : EdgePin M (a u) (a v) => p.val.2) S.property⟩
  invFun S := ⟨S.val, Subtype.ext (Prod.ext S.property.1 S.property.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ordinary_eq_sum_edgeFibre (a : V → ℕ) (u v : V) (huv : G.Adj u v) :
    ordinary G M a = ∑ AB : EdgePin M (a u) (a v),
      edgeFibre (trivialCover G M) a u v AB.val.1 AB.val.2 := by
  classical
  have h := card_eq_sum_fibres (ordinaryEdgePin a u v huv (M := M))
  change ordinary G M a = _ at h
  rw [h]
  apply Finset.sum_congr rfl
  intro AB _
  simp only [rootFibre, edgeFibre, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (ordinaryEdgePinFibreEquiv a u v huv AB)

/-- Exactly the real-edge multiplier in MainCFibres. -/
theorem ordinary_edge_normalization (a : V → ℕ) (u v : V) (huv : G.Adj u v)
    (A B : Finset (Fin M)) (hA : A.card = a u) (hB : B.card = a v)
    (hd : Disjoint A B) :
    (M.choose (a u) * (M - a u).choose (a v)) *
      edgeFibre (trivialCover G M) a u v A B = ordinary G M a := by
  classical
  have h := ordinary_eq_sum_edgeFibre a u v huv (M := M)
  have he : ∀ AB : EdgePin M (a u) (a v),
      edgeFibre (trivialCover G M) a u v AB.val.1 AB.val.2 =
        edgeFibre (trivialCover G M) a u v A B := by
    intro AB
    exact ordinary_edgeFibre_eq a u v AB.val.1 AB.val.2 A B
      (AB.property.1.trans hA.symm) (AB.property.2.1.trans hB.symm) AB.property.2.2 hd
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_edgePin] at h
  exact h.symm

/-- Existing chordal root comparison, now in the unchanged publication normalization. -/
theorem chordal_root_normalized (X : Cover G M) (a : V → ℕ)
    (hg : ChordalBipartite G) (root : V) (A : Finset (Fin M)) (hA : A.card = a root) :
    M.choose (a root) * rootFibre X a root A ≤ ordinary G M a := by
  calc
    M.choose (a root) * rootFibre X a root A ≤
        M.choose (a root) * rootFibre (trivialCover G M) a root A :=
      by
        apply Nat.mul_le_mul_left
        exact rootFibre_le_of_chordalBipartite X a hg root A
    _ = ordinary G M a := ordinary_root_normalization a root A hA

end
end CoefficientwiseRigidity.Gluing
