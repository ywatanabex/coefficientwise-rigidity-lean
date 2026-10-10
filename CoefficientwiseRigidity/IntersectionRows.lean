import CoefficientwiseRigidity.ConeCompression
import CoefficientwiseRigidity.GraphNestOrder

/-! Actual gained row intersections and the residual neighbourhood family. -/
namespace CoefficientwiseRigidity.Intersections
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {I : Type*} {M : ℕ}

/-- Empty row intersections are the whole label set. -/
def row (J : Finset V) (σ : V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) : Finset (Fin M) :=
  univ.filter (fun x => ∀ v ∈ J, x ∈ (Q v).map (σ v).toEmbedding)

@[simp] theorem mem_row (J : Finset V) (σ : V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (x : Fin M) :
    x ∈ row J σ Q ↔ ∀ v ∈ J, x ∈ (Q v).map (σ v).toEmbedding := by simp [row]

@[simp] theorem row_empty (σ : V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) :
    row ∅ σ Q = univ := by ext x; simp

@[simp] theorem row_singleton (v : V) (σ : V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) :
    row {v} σ Q = (Q v).map (σ v).toEmbedding := by ext x; simp

theorem row_antitone {J K : Finset V} (h : J ⊆ K)
    (σ : V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) : row K σ Q ⊆ row J σ Q := by
  intro x hx
  exact (mem_row _ _ _ _).mpr (fun v hv => (mem_row _ _ _ _).mp hx v (h hv))

theorem row_update (J : Finset V) (σ : V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) (v : V) (A : Finset (Fin M)) :
    row J σ (Function.update Q v A) =
      (if v ∈ J then A.map (σ v).toEmbedding else univ) ∩ row (J.erase v) σ Q := by
  ext x
  simp only [mem_row,Finset.mem_inter]
  constructor
  · intro h
    constructor
    · by_cases hv : v ∈ J
      · simpa only [hv,if_true,Function.update_self] using h v hv
      · simp [hv]
    · intro w hw
      have hw' := Finset.mem_erase.mp hw
      simpa only [Function.update_of_ne hw'.1] using h w hw'.2
  · rintro ⟨hA,h⟩ w hw
    by_cases hwv : w = v
    · subst w
      simpa only [hw,if_true,Function.update_self] using hA
    · simpa only [Function.update_of_ne hwv] using h w (Finset.mem_erase.mpr ⟨hwv,hw⟩)

theorem card_map_inter (e : Equiv.Perm (Fin M)) (A D : Finset (Fin M)) :
    (A.map e.toEmbedding ∩ D).card = (A ∩ D.map e.symm.toEmbedding).card := by
  have he : A.map e.toEmbedding ∩ D = (A ∩ D.map e.symm.toEmbedding).map e.toEmbedding := by
    ext x
    simp [Finset.mem_map_equiv]
  rw [he,Finset.card_map]

def ranks (J : I → Finset V) (σ : I → V → Equiv.Perm (Fin M))
    (Q : V → Finset (Fin M)) : I → ℕ := fun i => (row (J i) (σ i) Q).card

def eraseRows (J : I → Finset V) (v : V) : I → Finset V := fun i => (J i).erase v

def family [Fintype I] (J : I → Finset V) : Finset (Finset V) := univ.image J

@[simp] theorem mem_family [Fintype I] (J : I → Finset V) (E : Finset V) :
    E ∈ family J ↔ ∃ i, J i = E := by simp [family]

/-- The structural trace is exactly the rowwise deletion; duplicate rows may
collapse in this family but remain indexed separately in the cost. -/
theorem trace_family_erase [Fintype I] (J : I → Finset V) (v : V) (U : Finset V)
    (hs : ∀ i, J i ⊆ insert v U) (hv : v ∉ U) :
    Structure.Trace (family J) U = family (eraseRows J v) := by
  simp only [Structure.Trace,family,Finset.image_image]
  apply Finset.image_congr
  intro i _
  ext w
  simp only [Finset.mem_inter,eraseRows,Finset.mem_erase,Function.comp_apply]
  constructor
  · rintro ⟨hw,hu⟩
    exact ⟨fun he => hv (he ▸ hu),hw⟩
  · rintro ⟨hne,hw⟩
    exact ⟨hw,(Finset.mem_insert.mp (hs i hw)).resolve_left hne⟩

theorem identity_residual_nested [Fintype I] (J : I → Finset V) (v : V)
    (hn : Structure.NestPoint (family J) v) (Q : V → Finset (Fin M))
    {i j : I} (hi : v ∈ J i) (hj : v ∈ J j) :
    row ((J i).erase v) (fun _ => Equiv.refl _) Q ⊆ row ((J j).erase v) (fun _ => Equiv.refl _) Q ∨
    row ((J j).erase v) (fun _ => Equiv.refl _) Q ⊆ row ((J i).erase v) (fun _ => Equiv.refl _) Q := by
  rcases hn (J i) ((mem_family _ _).mpr ⟨i,rfl⟩) (J j) ((mem_family _ _).mpr ⟨j,rfl⟩) hi hj with hij | hji
  · exact Or.inr (row_antitone (Finset.erase_subset_erase v hij) _ _)
  · exact Or.inl (row_antitone (Finset.erase_subset_erase v hji) _ _)

theorem ranks_eq_identity_of_single_root (J : I → Finset V) (root : V)
    (hs : ∀ i, J i ⊆ {root}) (σ : I → V → Equiv.Perm (Fin M)) (Q : V → Finset (Fin M)) :
    ranks J σ Q = ranks J (fun _ _ => Equiv.refl _) Q := by
  funext i
  rcases Finset.subset_singleton_iff.mp (hs i) with h | h
  · simp [ranks,h]
  · simp [ranks,h]

end
end CoefficientwiseRigidity.Intersections
