import CoefficientwiseRigidity.ChordalPathCycle

/-! Minimal separators in the original induced-cycle model are cliques. -/
namespace CoefficientwiseRigidity.Structure
open Finset
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {U S : Finset V} {x y : V}

def CliqueOn (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, x ≠ y → G.Adj x y

def componentIn (G : SimpleGraph V) (U : Finset V) (x : V) : Finset V :=
  U.filter (fun y => ReachIn G (↑U : Set V) x y)

theorem componentIn_subset : componentIn G U x ⊆ U := Finset.filter_subset _ _

theorem mem_componentIn_self (hx : x ∈ U) : x ∈ componentIn G U x :=
  Finset.mem_filter.mpr ⟨hx,ReachIn.refl hx⟩

theorem reach_componentIn (h : ReachIn G (↑U : Set V) x y) :
    ReachIn G (↑(componentIn G U x) : Set V) x y := by
  obtain ⟨hx,h⟩ := h
  induction h with
  | refl => exact ReachIn.refl (mem_componentIn_self hx)
  | tail hab he ih =>
    exact ih.step he.1 (Finset.mem_filter.mpr ⟨he.2.2,⟨hx,hab.tail he⟩⟩)

theorem componentIn_connected {u v : V} (hu : u ∈ componentIn G U x)
    (hv : v ∈ componentIn G U x) : ReachIn G (↑(componentIn G U x) : Set V) u v :=
  (reach_componentIn (Finset.mem_filter.mp hu).2).symm.trans
    (reach_componentIn (Finset.mem_filter.mp hv).2)

theorem componentIn_separated (hxy : ¬ ReachIn G (↑U : Set V) x y)
    {u v : V} (hu : u ∈ componentIn G U x) (hv : v ∈ componentIn G U y) :
    u ≠ v ∧ ¬ G.Adj u v := by
  have hx := (Finset.mem_filter.mp hu).2
  have hy := (Finset.mem_filter.mp hv).2
  constructor
  · intro he
    exact hxy (hx.trans (he ▸ hy.symm))
  · intro hadj
    exact hxy ((hx.step hadj hy.end_mem).trans hy.symm)

def Separates (G : SimpleGraph V) (U S : Finset V) (x y : V) : Prop :=
  S ⊆ U ∧ x ∈ U \ S ∧ y ∈ U \ S ∧ ¬ ReachIn G (↑(U \ S) : Set V) x y

def MinimalSeparator (G : SimpleGraph V) (U S : Finset V) (x y : V) : Prop :=
  Separates G U S x y ∧ ∀ T, Separates G U T x y → S.card ≤ T.card

/-- An actual minimum-cardinality separator exists, even for disconnected
vertices (where it may be empty). No connectivity hypothesis is needed. -/
theorem exists_minimalSeparator (hx : x ∈ U) (hy : y ∈ U) (hne : x ≠ y)
    (hnadj : ¬ G.Adj x y) : ∃ S, MinimalSeparator G U S x y := by
  have hsep : Separates G U (U \ {x,y}) x y := by
    refine ⟨Finset.sdiff_subset,by simp [hx],by simp [hy],?_⟩
    rintro ⟨_,hr⟩
    have every : ∀ v, Relation.ReflTransGen
        (fun u v => G.Adj u v ∧ u ∈ (↑(U \ (U \ {x,y})) : Set V) ∧
          v ∈ (↑(U \ (U \ {x,y})) : Set V)) x v → v = x := by
      intro v hv
      induction hv with
      | refl => rfl
      | @tail u v _ he ih =>
        have hv := Finset.mem_sdiff.mp he.2.2
        have hp : v ∈ ({x,y} : Finset V) := by
          by_contra hn
          exact hv.2 (Finset.mem_sdiff.mpr ⟨hv.1,hn⟩)
        rcases Finset.mem_insert.mp hp with hvx | hvy
        · exact hvx
        · have hvy := Finset.mem_singleton.mp hvy
          exact False.elim (hnadj (by simpa only [ih,hvy] using he.1))
    exact hne (every y hr).symm
  let A := U.powerset.filter (fun S => Separates G U S x y)
  have hA : A.Nonempty := ⟨U \ {x,y},Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,hsep⟩⟩
  obtain ⟨S,hS,hmin⟩ := Finset.exists_min_image A Finset.card hA
  refine ⟨S,(Finset.mem_filter.mp hS).2,?_⟩
  intro T hT
  exact hmin T (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hT.1,hT⟩)

theorem MinimalSeparator.erase_reachable (h : MinimalSeparator G U S x y)
    {s : V} (hs : s ∈ S) : ReachIn G (↑(U \ S.erase s) : Set V) x y := by
  by_contra hn
  have hm := h.2 (S.erase s) ⟨(Finset.erase_subset _ _).trans h.1.1,
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h.1.2.1).1,
      fun he => (Finset.mem_sdiff.mp h.1.2.1).2 (Finset.mem_of_mem_erase he)⟩,
    Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp h.1.2.2.1).1,
      fun he => (Finset.mem_sdiff.mp h.1.2.2.1).2 (Finset.mem_of_mem_erase he)⟩,hn⟩
  have := Finset.card_erase_lt_of_mem hs
  omega

theorem MinimalSeparator.symm (h : MinimalSeparator G U S x y) :
    MinimalSeparator G U S y x := by
  refine ⟨⟨h.1.1,h.1.2.2.1,h.1.2.1,fun hr => h.1.2.2.2 hr.symm⟩,?_⟩
  intro T hT
  exact h.2 T ⟨hT.1,hT.2.2.1,hT.2.1,fun hr => hT.2.2.2 hr.symm⟩

/-- Restoring one necessary separator vertex forces an edge from the
original component to that vertex, by inspecting the first exit. -/
theorem separator_first_exit (hx : x ∈ U \ S)
    (hxy : ¬ ReachIn G (↑(U \ S) : Set V) x y) {s : V}
    (hr : ReachIn G (↑(U \ S.erase s) : Set V) x y) :
    ∃ u ∈ componentIn G (U \ S) x, G.Adj u s := by
  have every : ∀ v, Relation.ReflTransGen
      (fun u v => G.Adj u v ∧ u ∈ (↑(U \ S.erase s) : Set V) ∧
        v ∈ (↑(U \ S.erase s) : Set V)) x v →
      ReachIn G (↑(U \ S) : Set V) x v ∨
        ∃ u ∈ componentIn G (U \ S) x, G.Adj u s := by
    intro v hv
    induction hv with
    | refl => exact Or.inl (ReachIn.refl hx)
    | @tail u v _ he ih =>
      rcases ih with hu | hw
      · by_cases hv : v ∈ U \ S
        · exact Or.inl (hu.step he.1 hv)
        · have hvU : v ∈ U := (Finset.mem_sdiff.mp he.2.2).1
          have hvS : v ∈ S := by
            by_contra hn
            exact hv (Finset.mem_sdiff.mpr ⟨hvU,hn⟩)
          have hvs : v = s := by
            by_contra hn
            exact (Finset.mem_sdiff.mp he.2.2).2 (Finset.mem_erase.mpr ⟨hn,hvS⟩)
          exact Or.inr ⟨u,Finset.mem_filter.mpr ⟨hu.end_mem,hu⟩,by simpa only [hvs] using he.1⟩
      · exact Or.inr hw
  exact (every y hr.2).resolve_left hxy

theorem MinimalSeparator.full_component (h : MinimalSeparator G U S x y)
    {s : V} (hs : s ∈ S) : ∃ u ∈ componentIn G (U \ S) x, G.Adj u s :=
  separator_first_exit h.1.2.1 h.1.2.2.2 (h.erase_reachable hs)

theorem InducedPath.interior_mem {a b : V} {T : Set V} (p : InducedPath G a b)
    (hp : p.Inside (T ∪ {a,b})) (i : Fin (p.length + 1))
    (hi0 : 0 < i.val) (hin : i.val < p.length) : p.vertex i ∈ T := by
  rcases hp i with hm | hm
  · exact hm
  · rcases hm with ha | hb
    · have hh := congrArg Fin.val (p.injective (ha.trans p.first.symm))
      simp only [Fin.val_zero] at hh
      omega
    · have hh := congrArg Fin.val (p.injective (hb.trans p.last.symm))
      simp only [Fin.val_mk] at hh
      omega

theorem component_endpoint_path {C : Finset V} {a b : V}
    (hc : ∀ u ∈ C, ∀ v ∈ C, ReachIn G (↑C : Set V) u v)
    (ha : ∃ u ∈ C, G.Adj u a) (hb : ∃ v ∈ C, G.Adj v b) :
    ∃ p : InducedPath G a b, p.Inside ((↑C : Set V) ∪ {a,b}) := by
  obtain ⟨u,hu,hua⟩ := ha
  obtain ⟨v,hv,hvb⟩ := hb
  have hsub : (↑C : Set V) ⊆ ((↑C : Set V) ∪ {a,b}) := Set.subset_union_left
  have har : ReachIn G ((↑C : Set V) ∪ {a,b}) a u :=
    (ReachIn.refl (by simp : a ∈ ((↑C : Set V) ∪ {a,b}))).step (G.symm hua) (hsub hu)
  exact ((har.trans ((hc u hu v hv).mono hsub)).step hvb (by simp)).inducedPath

/-- The clique separator theorem is derived from actual induced cycles. -/
theorem MinimalSeparator.clique (hg : ChordalGraph G)
    (h : MinimalSeparator G U S x y) : CliqueOn G S := by
  intro a ha b hb hab
  by_contra hnadj
  obtain ⟨p,hp⟩ := component_endpoint_path
    (fun _ hu _ hv => componentIn_connected hu hv) (h.full_component ha) (h.full_component hb)
  obtain ⟨q,hq⟩ := component_endpoint_path
    (fun _ hu _ hv => componentIn_connected hu hv) (h.symm.full_component ha) (h.symm.full_component hb)
  apply p.not_separated_of_chordal hg q hab hnadj
  intro i j hi0 hin hj0 hjn
  exact componentIn_separated h.1.2.2.2 (p.interior_mem hp i hi0 hin) (q.interior_mem hq j hj0 hjn)

end
end CoefficientwiseRigidity.Structure
