import CoefficientwiseRigidity.StarVertices

/-! Adjacency of the underlying simple graph of the labelled tight-star contraction. -/
namespace CoefficientwiseRigidity.Star
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V}

def Adj (u : V) : Vertex G u → Vertex G u → Prop
  | none, none => False
  | none, some v => ∃ w, G.Adj u w ∧ G.Adj w v.val
  | some v, none => ∃ w, G.Adj u w ∧ G.Adj w v.val
  | some v, some w => G.Adj v.val w.val

def graph (G : SimpleGraph V) (u : V) : SimpleGraph (Vertex G u) where
  Adj := Adj u
  symm := by
    intro v w he
    cases v <;> cases w <;> try exact he
    exact G.symm he
  loopless := by
    intro v
    cases v with
    | none => exact id
    | some v => exact G.loopless v.val

@[simp] theorem graph_some (u : V) (v w : Outside G u) :
    (graph G u).Adj (some v) (some w) ↔ G.Adj v.val w.val := Iff.rfl

@[simp] theorem graph_none (u : V) (v : Outside G u) :
    (graph G u).Adj none (some v) ↔ ∃ w, G.Adj u w ∧ G.Adj w v.val := Iff.rfl

theorem outside_of_left (b : Bipartition G) {u v : V} (hu : b.side u = true)
    (hv : b.side v = true) (hne : v ≠ u) : v ≠ u ∧ ¬ G.Adj u v := by
  refine ⟨hne,?_⟩
  intro he
  exact b.opposite he (hu.trans hv.symm)

theorem project_eq_some {u v : V} {w : Outside G u} : project G u v = some w ↔ v = w.val := by
  constructor
  · unfold project
    split_ifs with hv
    · intro he; exact congrArg Subtype.val (Option.some.inj he)
    · simp
  · intro he; subst v; exact project_outside u w

theorem graph_project (b : Bipartition G) {u : V} (hu : b.side u = true)
    {x y : V} (he : G.Adj x y) (hx : x ≠ u) (hy : y ≠ u) :
    (graph G u).Adj (project G u x) (project G u y) := by
  by_cases hxu : G.Adj u x <;> by_cases hyu : G.Adj u y
  · have hsx : b.side x ≠ true := by simpa [hu] using (b.opposite hxu).symm
    have hsy : b.side y ≠ true := by simpa [hu] using (b.opposite hyu).symm
    have hsame : b.side x = b.side y := by cases h : b.side x <;> cases h' : b.side y <;> simp_all
    exact (b.opposite he hsame).elim
  · rw [project_neighbor hxu]
    have hp : project G u y = some ⟨y,hy,hyu⟩ := by simp [project,hy,hyu]
    rw [hp]
    exact ⟨x,hxu,he⟩
  · rw [project_neighbor hyu]
    have hp : project G u x = some ⟨x,hx,hxu⟩ := by simp [project,hx,hxu]
    rw [hp]
    exact ⟨y,hyu,G.symm he⟩
  · simpa [project,hx,hy,hxu,hyu,graph,Adj] using he

theorem graph_edge_label (b : Bipartition G) {u : V}
    {x y : Vertex G u} (he : (graph G u).Adj x y) :
    ∃ e : Edge b u, (project G u e.val.1 = x ∧ project G u e.val.2 = y) ∨
      (project G u e.val.1 = y ∧ project G u e.val.2 = x) := by
  have label {v w : V} (h : G.Adj v w) (hv : v ≠ u) (hw : w ≠ u) :
      ∃ e : Edge b u, (e.val.1 = v ∧ e.val.2 = w) ∨ (e.val.1 = w ∧ e.val.2 = v) := by
    cases hs : b.side v with
    | true => exact ⟨⟨(v,w),hs,h,hv,hw⟩,Or.inl ⟨rfl,rfl⟩⟩
    | false =>
      have hs' : b.side w = true := by
        have hn := b.opposite h
        rw [hs] at hn
        cases hh : b.side w <;> simp_all
      exact ⟨⟨(w,v),hs',G.symm h,hw,hv⟩,Or.inr ⟨rfl,rfl⟩⟩
  cases x with
  | none =>
    cases y with
    | none => exact he.elim
    | some y =>
      obtain ⟨w,hw,hy⟩ := he
      obtain ⟨e,h | h⟩ := label hy (G.ne_of_adj hw).symm y.property.1
      · exact ⟨e,Or.inl ⟨by rw [h.1,project_neighbor hw],by rw [h.2,project_outside]⟩⟩
      · exact ⟨e,Or.inr ⟨by rw [h.1,project_outside],by rw [h.2,project_neighbor hw]⟩⟩
  | some x =>
    cases y with
    | none =>
      obtain ⟨w,hw,hx⟩ := he
      obtain ⟨e,h | h⟩ := label hx (G.ne_of_adj hw).symm x.property.1
      · exact ⟨e,Or.inr ⟨by rw [h.1,project_neighbor hw],by rw [h.2,project_outside]⟩⟩
      · exact ⟨e,Or.inl ⟨by rw [h.1,project_outside],by rw [h.2,project_neighbor hw]⟩⟩
    | some y =>
      obtain ⟨e,h | h⟩ := label he x.property.1 y.property.1
      · exact ⟨e,Or.inl ⟨by rw [h.1,project_outside],by rw [h.2,project_outside]⟩⟩
      · exact ⟨e,Or.inr ⟨by rw [h.1,project_outside],by rw [h.2,project_outside]⟩⟩

theorem cover_graph {M : ℕ} (b : Bipartition G) (u : V) (hu : b.side u = true) (X : Cover G M) :
    (cover b u hu X).graph = graph G u := by
  ext x y
  constructor
  · rintro ⟨e,h | h⟩
    · rw [← h.1,← h.2]
      exact graph_project b hu e.property.2.1 e.property.2.2.1 e.property.2.2.2
    · rw [← h.1,← h.2]
      exact (graph G u).symm (graph_project b hu e.property.2.1 e.property.2.2.1 e.property.2.2.2)
  · exact graph_edge_label b

def bipartition (b : Bipartition G) (u : V) (hu : b.side u = true) : Bipartition (graph G u) :=
  cover_graph b u hu (trivialCover G 0) ▸ (cover b u hu (trivialCover G 0)).bipartition

end
end CoefficientwiseRigidity.Star
