import CoefficientwiseRigidity.ReplicaConfigurations

/-!
Concrete boundary uniformity and the amplification implication for actual
finite graph copies. No comparison oracle is hidden in a definition: the
all-copy scalar comparison is an explicit hypothesis of the last theorem.
-/
namespace CoefficientwiseRigidity.Replica
open scoped BigOperators Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {M : ℕ}

/-- The three allowed boundary shapes, with an actual edge in the third case. -/
def BoundaryShape (G : SimpleGraph V) (S : Finset V) : Prop :=
  S = ∅ ∨ (∃ u, S = {u}) ∨ ∃ u v, S = {u,v} ∧ G.Adj u v

omit [Fintype V] in
theorem boundary_flat (X : Cover G M) {S : Finset V} (hS : BoundaryShape G S) :
    Flat (restrictCover X S G le_rfl) := by
  rcases hS with hS | ⟨u,hS⟩ | ⟨u,v,hS,huv⟩
  · refine ⟨fun _ => Equiv.refl _,?_⟩
    intro x
    have hx := x.property
    simp [hS] at hx
  · refine ⟨fun _ => Equiv.refl _,?_⟩
    intro x y hxy
    have hx : x.val = u := by simpa [hS] using x.property
    have hy : y.val = u := by simpa [hS] using y.property
    have h : G.Adj x.val y.val := hxy
    rw [hx,hy] at h
    exact False.elim (G.loopless u h)
  · have hne : u ≠ v := by intro h; subst v; exact G.loopless u huv
    let γ : S → Equiv.Perm (Fin M) :=
      fun w => if w.val = u then Equiv.refl _ else X.transport u v
    refine ⟨γ,?_⟩
    intro x y hxy i
    have hx : x.val = u ∨ x.val = v := by simpa [hS] using x.property
    have hy : y.val = u ∨ y.val = v := by simpa [hS] using y.property
    change X.transport x.val y.val (γ x i) = γ y i
    have he : G.Adj x.val y.val := hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · exact False.elim (G.loopless u (by simp [hx,hy] at he))
    · simp [γ,hx,hy,hne.symm]
    · simp [γ,hx,hy,hne.symm,X.reverse huv]
    · exact False.elim (G.loopless v (by simp [hx,hy] at he))

omit [Fintype V] in
theorem boundary_card_eq (X : Cover G M) (a : V → ℕ) {S : Finset V}
    (hS : BoundaryShape G S) :
    Fintype.card (BoundaryConfiguration X a S) =
      Fintype.card (BoundaryConfiguration (trivialCover G M) a S) := by
  change coefficient (restrictCover X S G le_rfl) (fun v => a v.val) =
    ordinary (G.induce (↑S : Set V)) M (fun v => a v.val)
  apply activeFlat_coefficient_eq
  exact flat_activeFlat _ _ (boundary_flat X hS)

def ordinaryFibrePermEquiv (a : V → ℕ) (S : Finset V)
    (b b' : BoundaryConfiguration (trivialCover G M) a S)
    (σ : Equiv.Perm (Fin M)) (hσ : ∀ v, (b.val v).map σ.toEmbedding = b'.val v) :
    Fibre (trivialCover G M) a S b ≃ Fibre (trivialCover G M) a S b' where
  toFun C := ⟨Gluing.ordinaryPermutationEquiv a σ C.val,by
    apply Subtype.ext
    funext v
    change (C.val.val v.val).map σ.toEmbedding = b'.val v
    have hv := congrFun (congrArg Subtype.val C.property) v
    change C.val.val v.val = b.val v at hv
    rw [hv,hσ]⟩
  invFun C := ⟨(Gluing.ordinaryPermutationEquiv a σ).symm C.val,by
    apply Subtype.ext
    funext v
    change (C.val.val v.val).map σ.symm.toEmbedding = b.val v
    have hv := congrFun (congrArg Subtype.val C.property) v
    change C.val.val v.val = b'.val v at hv
    rw [hv,← hσ v]
    ext i
    simp⟩
  left_inv C := by
    apply Subtype.ext
    exact (Gluing.ordinaryPermutationEquiv a σ).symm_apply_apply C.val
  right_inv C := by
    apply Subtype.ext
    exact (Gluing.ordinaryPermutationEquiv a σ).apply_symm_apply C.val

omit [Fintype V] in
theorem exists_boundary_perm (a : V → ℕ) {S : Finset V} (hS : BoundaryShape G S)
    (b b' : BoundaryConfiguration (trivialCover G M) a S) :
    ∃ σ : Equiv.Perm (Fin M), ∀ v, (b.val v).map σ.toEmbedding = b'.val v := by
  rcases hS with hS | ⟨u,hS⟩ | ⟨u,v,hS,huv⟩
  · refine ⟨Equiv.refl _,?_⟩
    intro v
    have hv := v.property
    simp [hS] at hv
  · let uS : S := ⟨u,by simp [hS]⟩
    obtain ⟨σ,hσ,_⟩ := Kernel.exists_pair_equiv (b.val uS) ∅ (b'.val uS) ∅ rfl
      ((b.property.1 uS).trans (b'.property.1 uS).symm) rfl (by simp)
    refine ⟨σ,?_⟩
    intro w
    have hw : w.val = u := by simpa [hS] using w.property
    have he : w = uS := Subtype.ext hw
    simpa [he] using hσ
  · let uS : S := ⟨u,by simp [hS]⟩
    let vS : S := ⟨v,by simp [hS]⟩
    have hd (c : BoundaryConfiguration (trivialCover G M) a S) :
        Disjoint (c.val uS) (c.val vS) := by
      apply Finset.disjoint_left.mpr
      intro i hi hj
      exact c.property.2 uS vS huv i hi hj
    obtain ⟨σ,hσ,hτ⟩ := Gluing.exists_disjoint_pair_perm
      (b.val uS) (b.val vS) (b'.val uS) (b'.val vS)
      ((b.property.1 uS).trans (b'.property.1 uS).symm)
      ((b.property.1 vS).trans (b'.property.1 vS).symm) (hd b) (hd b')
    refine ⟨σ,?_⟩
    intro w
    have hw : w.val = u ∨ w.val = v := by simpa [hS] using w.property
    rcases hw with hw | hw
    · have he : w = uS := Subtype.ext hw
      simpa [he] using hσ
    · have he : w = vS := Subtype.ext hw
      simpa [he] using hτ

theorem ordinary_fibre_constant (a : V → ℕ) {S : Finset V} (hS : BoundaryShape G S)
    (b b' : BoundaryConfiguration (trivialCover G M) a S) :
    Fintype.card (Fibre (trivialCover G M) a S b) =
      Fintype.card (Fibre (trivialCover G M) a S b') := by
  obtain ⟨σ,hσ⟩ := exists_boundary_perm a hS b b'
  exact Fintype.card_congr (ordinaryFibrePermEquiv a S b b' σ hσ)

theorem coefficient_eq_sum_fibres (X : Cover G M) (a : V → ℕ) (S : Finset V) :
    coefficient X a = ∑ b : BoundaryConfiguration X a S, Fintype.card (Fibre X a S b) := by
  change Fintype.card (Configuration X a) = _
  rw [Fintype.card_congr (Gluing.allFibresEquiv (restriction X a S)), Fintype.card_sigma]

theorem ordinary_boundary_normalization (a : V → ℕ) {S : Finset V}
    (hS : BoundaryShape G S) (b : BoundaryConfiguration (trivialCover G M) a S) :
    Fintype.card (BoundaryConfiguration (trivialCover G M) a S) *
      Fintype.card (Fibre (trivialCover G M) a S b) = ordinary G M a := by
  have h := coefficient_eq_sum_fibres (trivialCover G M) a S
  have hc : ∀ c : BoundaryConfiguration (trivialCover G M) a S,
      Fintype.card (Fibre (trivialCover G M) a S c) =
        Fintype.card (Fibre (trivialCover G M) a S b) :=
    fun c => ordinary_fibre_constant a hS c b
  simp only [hc,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at h
  exact h.symm

/-- G1, now for the literal copied graph and the literal configuration fibre.
The scalar comparison for all copy counts remains an explicit premise. -/
theorem fibre_bound_of_all_copies (X : Cover G M) (a : V → ℕ) {S : Finset V}
    (hS : BoundaryShape G S)
    (hcomp : ∀ k : ℕ,
      coefficient (cover X S (Fin k)) (fun x => a (base S x)) ≤
        ordinary (graph G S (Fin k)) M (fun x => a (base S x)))
    (b : BoundaryConfiguration X a S) :
    Fintype.card (BoundaryConfiguration X a S) * Fintype.card (Fibre X a S b) ≤
      ordinary G M a := by
  classical
  have hcard := boundary_card_eq X a hS
  have hpos : 0 < Fintype.card (BoundaryConfiguration (trivialCover G M) a S) := by
    rw [← hcard]
    exact Fintype.card_pos_iff.mpr ⟨b⟩
  obtain ⟨b₀⟩ := Fintype.card_pos_iff.mp hpos
  let c : ℕ := Fintype.card (Fibre (trivialCover G M) a S b₀)
  have hc : ∀ t : BoundaryConfiguration (trivialCover G M) a S,
      Fintype.card (Fibre (trivialCover G M) a S t) = c :=
    fun t => ordinary_fibre_constant a hS t b₀
  have hp : ∀ k : ℕ,
      (∑ t : BoundaryConfiguration X a S, (Fintype.card (Fibre X a S t) : ℚ) ^ k) ≤
        (Fintype.card (BoundaryConfiguration X a S) : ℚ) * (c : ℚ) ^ k := by
    intro k
    have h := hcomp k
    change coefficient (cover X S (Fin k)) (fun x => a (base S x)) ≤
      coefficient (cover (trivialCover G M) S (Fin k)) (fun x => a (base S x)) at h
    have h₁ := coefficient_eq_sum_powers (I := Fin k) X a S
    have h₂ := coefficient_eq_sum_powers (I := Fin k) (trivialCover G M) a S
    simp only [coefficient, ← Nat.card_eq_fintype_card] at h h₁ h₂
    rw [h₁,h₂] at h
    simp only [Nat.card_eq_fintype_card,Fintype.card_fin,hc,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← hcard] at h
    exact_mod_cast h
  have hb := Seam.pointwise_of_power_comparison
    (fun t : BoundaryConfiguration X a S => (Fintype.card (Fibre X a S t) : ℚ))
    (c : ℚ) (fun _ => Nat.cast_nonneg _) (Nat.cast_nonneg _) hp b
  have hb' : Fintype.card (Fibre X a S b) ≤ c := by exact_mod_cast hb
  calc
    Fintype.card (BoundaryConfiguration X a S) * Fintype.card (Fibre X a S b) ≤
        Fintype.card (BoundaryConfiguration X a S) * c := Nat.mul_le_mul_left _ hb'
    _ = ordinary G M a := by
      rw [hcard]
      exact ordinary_boundary_normalization a hS b₀

end
end CoefficientwiseRigidity.Replica
