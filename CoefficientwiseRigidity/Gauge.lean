import CoefficientwiseRigidity.Definitions

/-! Paper F3/F4, proved for concrete configurations, including zero occupations. -/
namespace CoefficientwiseRigidity
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {M : ℕ}

def relabel (γ : V → Equiv.Perm (Fin M)) (S : Assignment V M) : Assignment V M :=
  fun v => (S v).map (γ v).toEmbedding

omit [Fintype V] [DecidableEq V] in
@[simp] theorem mem_relabel (γ : V → Equiv.Perm (Fin M)) (S : Assignment V M)
    (v : V) (i : Fin M) : i ∈ relabel γ S v ↔ (γ v).symm i ∈ S v :=
  Finset.mem_map_equiv

omit [Fintype V] [DecidableEq V] in
@[simp] theorem card_relabel (γ : V → Equiv.Perm (Fin M)) (S : Assignment V M)
    (v : V) : (relabel γ S v).card = (S v).card := Finset.card_map _

omit [Fintype V] [DecidableEq V] in
@[simp] theorem relabel_inverse (γ : V → Equiv.Perm (Fin M)) (S : Assignment V M) :
    relabel (fun v => (γ v).symm) (relabel γ S) = S := by
  funext v
  ext i
  simp

omit [Fintype V] [DecidableEq V] in
@[simp] theorem relabel_inverse' (γ : V → Equiv.Perm (Fin M)) (S : Assignment V M) :
    relabel γ (relabel (fun v => (γ v).symm) S) = S := by
  funext v
  ext i
  simp

/-- Transport intertwining is required only on active edges. -/
def GaugeEquivalent (X Y : Cover G M) (a : V → ℕ) : Prop :=
  ∃ γ : V → Equiv.Perm (Fin M), ∀ u v, G.Adj u v →
    0 < a u → 0 < a v → ∀ i,
      Y.transport u v (γ u i) = γ v (X.transport u v i)

omit [Fintype V] [DecidableEq V] in
theorem relabel_admissible (X Y : Cover G M) (a : V → ℕ)
    (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ u v, G.Adj u v → 0 < a u → 0 < a v → ∀ i,
      Y.transport u v (γ u i) = γ v (X.transport u v i))
    {S : Assignment V M} (hS : Admissible X a S) :
    Admissible Y a (relabel γ S) := by
  refine ⟨fun v => (card_relabel γ S v).trans (hS.1 v), ?_⟩
  intro u v huv i hi hj
  have hi' := (mem_relabel γ S u i).mp hi
  have hj' := (mem_relabel γ S v (Y.transport u v i)).mp hj
  have hu : 0 < a u := by
    rw [← hS.1 u]
    exact Finset.card_pos.mpr ⟨_, hi'⟩
  have hv : 0 < a v := by
    rw [← hS.1 v]
    exact Finset.card_pos.mpr ⟨_, hj'⟩
  have heq := hγ u v huv hu hv ((γ u).symm i)
  simp only [Equiv.apply_symm_apply] at heq
  rw [heq] at hj'
  simp only [Equiv.symm_apply_apply] at hj'
  exact hS.2 u v huv _ hi' hj'

noncomputable def gaugeConfigurationEquiv (X Y : Cover G M) (a : V → ℕ)
    (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ u v, G.Adj u v → 0 < a u → 0 < a v → ∀ i,
      Y.transport u v (γ u i) = γ v (X.transport u v i)) :
    Configuration X a ≃ Configuration Y a where
  toFun S := ⟨relabel γ S.val, relabel_admissible X Y a γ hγ S.property⟩
  invFun S := ⟨relabel (fun v => (γ v).symm) S.val,
    relabel_admissible Y X a (fun v => (γ v).symm) (by
      intro u v huv hu hv i
      apply (γ v).injective
      simpa using (hγ u v huv hu hv ((γ u).symm i)).symm) S.property⟩
  left_inv S := by apply Subtype.ext; exact relabel_inverse γ S.val
  right_inv S := by apply Subtype.ext; exact relabel_inverse' γ S.val

theorem coefficient_eq_of_gauge (X Y : Cover G M) (a : V → ℕ)
    (h : GaugeEquivalent X Y a) : coefficient X a = coefficient Y a := by
  obtain ⟨γ, hγ⟩ := h
  exact Fintype.card_congr (gaugeConfigurationEquiv X Y a γ hγ)

theorem activeFlat_coefficient_eq (X : Cover G M) (a : V → ℕ)
    (h : ActiveFlat X a) : coefficient X a = ordinary G M a := by
  obtain ⟨γ, hγ⟩ := h
  symm
  apply coefficient_eq_of_gauge
  exact ⟨γ, hγ⟩

theorem activeFlat_deficit_zero (X : Cover G M) (a : V → ℕ)
    (h : ActiveFlat X a) : deficit X a = 0 := by
  simp [deficit, activeFlat_coefficient_eq X a h]

omit [Fintype V] [DecidableEq V] in
theorem flat_activeFlat (X : Cover G M) (a : V → ℕ) (h : Flat X) : ActiveFlat X a := by
  obtain ⟨γ, hγ⟩ := h
  exact ⟨γ, fun u v huv _ _ => hγ u v huv⟩

omit [Fintype V] [DecidableEq V] in
theorem activeFlat_iff_flat_of_positive (X : Cover G M) (a : V → ℕ)
    (ha : Positive a) : ActiveFlat X a ↔ Flat X := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨γ, fun u v huv => hγ u v huv (ha u) (ha v)⟩
  · exact flat_activeFlat X a

omit [Fintype V] [DecidableEq V] in
theorem trivialCover_flat : Flat (trivialCover G M) :=
  ⟨fun _ => Equiv.refl _, fun _ _ _ _ => rfl⟩

end CoefficientwiseRigidity
