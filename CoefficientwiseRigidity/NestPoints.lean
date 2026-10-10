import CoefficientwiseRigidity.Targets

/-!
Finite nest-point induction for the structural route in paper §05 B3–B4.
The hereditary alpha-leaf premise is explicit; its derivation from the original
induced-cycle prohibition is proved in ChordalNestOrder and GraphNestOrder.
-/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} [DecidableEq V]

/-- Empty and repeated rows are harmless; the finite set collapses duplicates. -/
def Trace (H : Finset (Finset V)) (U : Finset V) : Finset (Finset V) :=
  H.image (fun e => e ∩ U)

def FamilySupported (U : Finset V) (H : Finset (Finset V)) : Prop :=
  ∀ e ∈ H, e ⊆ U

/-- A virtual singleton includes isolated columns without adding rows. -/
def AlphaLeaf (U : Finset V) (H : Finset (Finset V)) (x : V) (E : Finset V) : Prop :=
  x ∈ E ∧ E ⊆ U ∧ (E ∈ H ∨ E = {x}) ∧ ∀ e ∈ H, x ∈ e → e ⊆ E

def HasAlpha (U : Finset V) (H : Finset (Finset V)) : Prop :=
  ∃ x ∈ U, ∃ E, AlphaLeaf U H x E

/-- The exact hereditary input needed by B3: every subfamily of every trace
has an alpha leaf. This is not the definition of chordal bipartiteness. -/
def HereditaryAlpha (U : Finset V) (H : Finset (Finset V)) : Prop :=
  ∀ W ⊆ U, W.Nonempty → ∀ K ⊆ Trace H W, HasAlpha W K

def NestPoint (H : Finset (Finset V)) (x : V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, x ∈ e → x ∈ f → e ⊆ f ∨ f ⊆ e

/-- The two points are nonadjacent after removing the possible full row. -/
def ProperSeparated (U : Finset V) (H : Finset (Finset V)) (x y : V) : Prop :=
  ∀ e ∈ H, x ∈ e → y ∈ e → e = U

@[simp] theorem trace_self {U : Finset V} {H : Finset (Finset V)} (h : FamilySupported U H) : Trace H U = H := by
  unfold Trace
  calc
    H.image (fun e => e ∩ U) = H.image id := Finset.image_congr (fun e he =>
      Finset.inter_eq_left.mpr (h e he))
    _ = H := Finset.image_id

theorem trace_supported (H : Finset (Finset V)) (U : Finset V) :
    FamilySupported U (Trace H U) := by
  intro e he
  obtain ⟨f,_,rfl⟩ := Finset.mem_image.mp he
  exact Finset.inter_subset_right

theorem trace_mono {H K : Finset (Finset V)} (h : K ⊆ H) (U : Finset V) :
    Trace K U ⊆ Trace H U := Finset.image_subset_image h

theorem trace_trace (H : Finset (Finset V)) {U W : Finset V} (h : W ⊆ U) :
    Trace (Trace H U) W = Trace H W := by
  simp only [Trace, Finset.image_image]
  congr 1
  funext e
  change (e ∩ U) ∩ W = e ∩ W
  rw [Finset.inter_assoc, Finset.inter_eq_right.mpr h]

theorem HereditaryAlpha.subfamily {U : Finset V} {H K : Finset (Finset V)}
    (h : HereditaryAlpha U H) (hK : K ⊆ H) : HereditaryAlpha U K := by
  intro W hW hn L hL
  exact h W hW hn L (hL.trans (trace_mono hK W))

theorem HereditaryAlpha.trace {U W : Finset V} {H : Finset (Finset V)}
    (h : HereditaryAlpha U H) (hW : W ⊆ U) : HereditaryAlpha W (Trace H W) := by
  intro T hT hn K hK
  rw [trace_trace H hT] at hK
  exact h T (hT.trans hW) hn K hK

theorem HereditaryAlpha.hasAlpha {U : Finset V} {H : Finset (Finset V)}
    (h : HereditaryAlpha U H) (hs : FamilySupported U H) (hn : U.Nonempty) : HasAlpha U H := by
  apply h U (Finset.Subset.refl _) hn H
  rw [trace_self hs]

theorem NestPoint.alpha {U : Finset V} {H : Finset (Finset V)} {x : V}
    (h : NestPoint H x) (hs : FamilySupported U H) (hx : x ∈ U) :
    ∃ E, AlphaLeaf U H x E := by
  by_cases hn : (H.filter (fun e => x ∈ e)).Nonempty
  · obtain ⟨E,hE,hmax⟩ := Finset.exists_max_image (H.filter (fun e => x ∈ e)) Finset.card hn
    obtain ⟨hEH,hxE⟩ := Finset.mem_filter.mp hE
    refine ⟨E,hxE,hs E hEH,Or.inl hEH,?_⟩
    intro e he hxe
    rcases h e he E hEH hxe hxE with hsub | hsub
    · exact hsub
    · have hc := hmax e (Finset.mem_filter.mpr ⟨he,hxe⟩)
      rw [← Finset.eq_of_subset_of_card_le hsub hc]
  · refine ⟨{x},by simp,Finset.singleton_subset_iff.mpr hx,Or.inr rfl,?_⟩
    intro e he hxe
    exact False.elim (hn ⟨e,Finset.mem_filter.mpr ⟨he,hxe⟩⟩)

theorem nestPoint_insert_full {U : Finset V} {H : Finset (Finset V)} {x : V}
    (hs : FamilySupported U H) (hn : NestPoint H x) : NestPoint (insert U H) x := by
  intro e he f hf hx hy
  rcases Finset.mem_insert.mp he with heU | heH
  · subst e
    rcases Finset.mem_insert.mp hf with hfU | hfH
    · subst f
      exact Or.inl (Finset.Subset.refl _)
    · exact Or.inr (hs f hfH)
  · rcases Finset.mem_insert.mp hf with hfU | hfH
    · subst f
      exact Or.inl (hs e heH)
    · exact hn e heH f hfH hx hy

/-- A proper row on at most two vertices cannot contain two distinct points. -/
theorem properSeparated_of_card_le_two {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (hc : U.card ≤ 2) {x y : V} (hxy : x ≠ y) :
    ProperSeparated U H x y := by
  intro e he hx hy
  apply Finset.eq_of_subset_of_card_le (hs e he)
  have hpair : ({x,y} : Finset V) ⊆ e := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hx
    · exact (Finset.mem_singleton.mp hw) ▸ hy
  have hle : 2 ≤ e.card := by simpa [hxy] using Finset.card_le_card hpair
  exact hc.trans hle

theorem nestPoint_of_small_no_full {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (hc : U.card ≤ 2) (hfull : U ∉ H) (x : V) : NestPoint H x := by
  intro e he f hf hx hy
  left
  intro y hye
  have hyx : y = x := by
    by_contra hn
    have heq := properSeparated_of_card_le_two hs hc (Ne.symm hn) e he hx hye
    exact hfull (heq ▸ he)
  exact hyx ▸ hy

/-- Lift a nest point from a vertex deletion when it lies outside a largest
row at the deleted vertex. No original row incident to it was changed. -/
theorem nestPoint_lift {U : Finset V} {H : Finset (Finset V)} {x y : V} {E : Finset V}
    (hα : AlphaLeaf U H x E) (hy : y ∉ E)
    (hn : NestPoint (Trace H (U.erase x)) y) (hs : FamilySupported U H) : NestPoint H y := by
  have unchanged (f : Finset V) (hf : f ∈ H) (hyf : y ∈ f) : f ∩ U.erase x = f := by
    apply Finset.inter_eq_left.mpr
    intro z hz
    apply Finset.mem_erase.mpr
    refine ⟨?_, hs f hf hz⟩
    intro hzx
    exact hy (hα.2.2.2 f hf (hzx ▸ hz) hyf)
  intro e he f hf hye hyf
  have heq := unchanged e he hye
  have hfq := unchanged f hf hyf
  have hem : e ∈ Trace H (U.erase x) := Finset.mem_image.mpr ⟨e,he,heq⟩
  have hfm : f ∈ Trace H (U.erase x) := Finset.mem_image.mpr ⟨f,hf,hfq⟩
  exact hn e hem f hfm hye hyf

/-- The deletion step in B3, using two separated nest points on the smaller set. -/
theorem nestPoint_outside_alpha {U : Finset V} {H : Finset (Finset V)} {x : V} {E : Finset V}
    (hs : FamilySupported U H) (hα : AlphaLeaf U H x E) (hp : E ≠ U)
    (hdel : ∃ y ∈ U.erase x, ∃ z ∈ U.erase x, y ≠ z ∧
      NestPoint (Trace H (U.erase x)) y ∧ NestPoint (Trace H (U.erase x)) z ∧
      ProperSeparated (U.erase x) (Trace H (U.erase x)) y z) :
    ∃ y ∈ U, NestPoint H y ∧ y ∉ E := by
  obtain ⟨y,hy,z,hz,hyz,hyn,hzn,hsep⟩ := hdel
  have hnot : ¬ (y ∈ E ∧ z ∈ E) := by
    rintro ⟨hyE,hzE⟩
    rcases hα.2.2.1 with hEH | hEs
    · have hm : E ∩ U.erase x ∈ Trace H (U.erase x) := Finset.mem_image.mpr ⟨E,hEH,rfl⟩
      have heq := hsep _ hm (Finset.mem_inter.mpr ⟨hyE,hy⟩) (Finset.mem_inter.mpr ⟨hzE,hz⟩)
      apply hp
      apply Finset.Subset.antisymm hα.2.1
      intro w hw
      by_cases hwx : w = x
      · exact hwx ▸ hα.1
      · have : w ∈ E ∩ U.erase x := by
          rw [heq]
          exact Finset.mem_erase.mpr ⟨hwx,hw⟩
        exact Finset.mem_inter.mp this |>.1
    · rw [hEs, Finset.mem_singleton] at hyE
      exact (Finset.mem_erase.mp hy).1 hyE
  by_cases hyE : y ∈ E
  · have hzE : z ∉ E := fun hzE => hnot ⟨hyE,hzE⟩
    exact ⟨z,(Finset.mem_erase.mp hz).2,nestPoint_lift hα hzE hzn hs,hzE⟩
  · exact ⟨y,(Finset.mem_erase.mp hy).2,nestPoint_lift hα hyE hyn hs,hyE⟩

private theorem two_nest_points_aux (n : ℕ) :
    ∀ (U : Finset V) (H : Finset (Finset V)), U.card + H.card = n →
      FamilySupported U H → HereditaryAlpha U H → 2 ≤ U.card →
      ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ NestPoint H x ∧ NestPoint H y ∧ ProperSeparated U H x y := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U H hsize hs ha hc
    by_cases hfull : U ∈ H
    · have hlt := Finset.card_erase_lt_of_mem hfull
      have hs' : FamilySupported U (H.erase U) := fun e he => hs e (Finset.mem_of_mem_erase he)
      obtain ⟨x,hx,y,hy,hxy,hxn,hyn,hsep⟩ :=
        ih (U.card + (H.erase U).card) (by omega) U (H.erase U) rfl hs'
          (ha.subfamily (Finset.erase_subset _ _)) hc
      have hn (v : V) (hv : NestPoint (H.erase U) v) : NestPoint H v := by
        rw [← Finset.insert_erase hfull]
        exact nestPoint_insert_full hs' hv
      refine ⟨x,hx,y,hy,hxy,hn x hxn,hn y hyn,?_⟩
      intro e he hxe hye
      by_cases heU : e = U
      · exact heU
      · exact hsep e (Finset.mem_erase.mpr ⟨heU,he⟩) hxe hye
    · by_cases hc2 : U.card ≤ 2
      · obtain ⟨x,hx,y,hy,hxy⟩ := Finset.one_lt_card.mp (by omega : 1 < U.card)
        exact ⟨x,hx,y,hy,hxy,nestPoint_of_small_no_full hs hc2 hfull x,
          nestPoint_of_small_no_full hs hc2 hfull y,properSeparated_of_card_le_two hs hc2 hxy⟩
      · have outside (x : V) (hx : x ∈ U) (E : Finset V) (hα : AlphaLeaf U H x E) :
            ∃ y ∈ U, NestPoint H y ∧ y ∉ E := by
          have hproper : E ≠ U := by
            intro heq
            rcases hα.2.2.1 with hEH | hEs
            · exact hfull (heq ▸ hEH)
            · have hcard : U.card = 1 := by rw [← heq,hEs]; simp
              omega
          have hcard := Finset.card_erase_add_one hx
          have htrace : (Trace H (U.erase x)).card ≤ H.card := Finset.card_image_le
          apply nestPoint_outside_alpha hs hα hproper
          exact ih ((U.erase x).card + (Trace H (U.erase x)).card) (by omega)
            (U.erase x) (Trace H (U.erase x)) rfl (trace_supported _ _)
            (ha.trace (Finset.erase_subset _ _)) (by omega)
        obtain ⟨x,hx,E,hα⟩ := ha.hasAlpha hs (Finset.card_pos.mp (by omega))
        obtain ⟨y,hy,hyn,_⟩ := outside x hx E hα
        obtain ⟨F,hβ⟩ := hyn.alpha hs hy
        obtain ⟨z,hz,hzn,hzF⟩ := outside y hy F hβ
        refine ⟨y,hy,z,hz,?_,hyn,hzn,?_⟩
        · intro heq
          exact hzF (heq ▸ hβ.1)
        · intro f hf hyf hzf
          exact False.elim (hzF (hβ.2.2.2 f hf hyf hzf))

/-- B3's full two-leaf conclusion, including separation after deleting a full
row. Hereditary alpha leaves are the explicit structural input. -/
theorem two_nest_points {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (ha : HereditaryAlpha U H) (hc : 2 ≤ U.card) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ NestPoint H x ∧ NestPoint H y ∧ ProperSeparated U H x y :=
  two_nest_points_aux (U.card + H.card) U H rfl hs ha hc

/-- In particular, a nonroot nest point exists whenever two columns remain. -/
theorem exists_nest_ne {U : Finset V} {H : Finset (Finset V)}
    (hs : FamilySupported U H) (ha : HereditaryAlpha U H) (hc : 2 ≤ U.card) (root : V) :
    ∃ x ∈ U, x ≠ root ∧ NestPoint H x := by
  obtain ⟨x,hx,y,hy,hxy,hxn,hyn,_⟩ := two_nest_points hs ha hc
  by_cases hxr : x = root
  · exact ⟨y,hy,fun hyr => hxy (hxr.trans hyr.symm),hyn⟩
  · exact ⟨x,hx,hxr,hxn⟩

namespace Examples
/-- A full row makes every column an alpha leaf, while the three pair rows
still prevent every nest point. The hereditary premise cannot be dropped. -/
def triangleWithFull : Finset (Finset (Fin 3)) := {{0,1},{0,2},{1,2},univ}

theorem triangleWithFull_alpha (x : Fin 3) :
    AlphaLeaf univ triangleWithFull x univ := by
  exact ⟨Finset.mem_univ _,Finset.Subset.refl _,Or.inl (by simp [triangleWithFull]),
    fun _ _ _ => Finset.subset_univ _⟩

theorem triangleWithFull_no_nest : ∀ x : Fin 3, ¬ NestPoint triangleWithFull x := by
  simp only [NestPoint,triangleWithFull]
  decide

theorem triangleWithFull_not_hereditary : ¬ HereditaryAlpha univ triangleWithFull := by
  intro h
  obtain ⟨x,_,_,_,_,hx,_,_⟩ := two_nest_points
    (fun _ _ => Finset.subset_univ _) h (by decide : 2 ≤ (univ : Finset (Fin 3)).card)
  exact triangleWithFull_no_nest x hx
end Examples

end
end CoefficientwiseRigidity.Structure
