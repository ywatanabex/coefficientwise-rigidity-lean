import CoefficientwiseRigidity.Targets

/-! F3 for connected graphs: trivial closed-walk transport iff a flattening gauge exists. -/
namespace CoefficientwiseRigidity
variable {V : Type*} {G : SimpleGraph V} {M : ℕ}

theorem walkTransport_append (X : Cover G M) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkTransport X (p.append q) = (walkTransport X p).trans (walkTransport X q) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [SimpleGraph.Walk.append, walkTransport, ih]
    rfl

theorem walkTransport_reverse (X : Cover G M) {u v : V} (p : G.Walk u v) :
    walkTransport X p.reverse = (walkTransport X p).symm := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkTransport_append, ih]
    ext i
    simp [walkTransport, X.reverse h]

theorem transport_intertwines (X : Cover G M) (γ : V → Equiv.Perm (Fin M))
    (hγ : ∀ u v, G.Adj u v → ∀ i, X.transport u v (γ u i) = γ v i)
    {u v : V} (p : G.Walk u v) (i : Fin M) :
    walkTransport X p (γ u i) = γ v i := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    change walkTransport X p (X.transport u v (γ u i)) = γ w i
    rw [hγ u v h i]
    exact ih

theorem flat_trivial_closed_walks (X : Cover G M) (h : Flat X) :
    ∀ (u : V) (p : G.Walk u u), walkTransport X p = Equiv.refl _ := by
  obtain ⟨γ, hγ⟩ := h
  intro u p
  apply Equiv.ext
  intro i
  obtain ⟨j, rfl⟩ := (γ u).surjective i
  exact transport_intertwines X γ hγ p j

theorem flat_of_trivial_root_walks (X : Cover G M) (hc : G.Connected) (root : V)
    (h : ∀ p : G.Walk root root, walkTransport X p = Equiv.refl _) : Flat X := by
  classical
  let paths : ∀ v, G.Walk root v := fun v => Classical.choice (hc root v)
  let γ : V → Equiv.Perm (Fin M) := fun v => walkTransport X (paths v)
  refine ⟨γ, ?_⟩
  intro u v huv i
  have he := h (((paths u).append (SimpleGraph.Walk.cons huv .nil)).append (paths v).reverse)
  have hi := congrArg (fun e : Equiv.Perm (Fin M) => e i) he
  simp only [walkTransport_append, walkTransport_reverse, walkTransport,
    Equiv.trans_apply, Equiv.refl_apply] at hi
  apply (γ v).symm.injective
  simpa [γ] using hi

theorem flat_iff_trivial_root_walks (X : Cover G M) (hc : G.Connected) (root : V) :
    Flat X ↔ ∀ p : G.Walk root root, walkTransport X p = Equiv.refl _ :=
  ⟨fun h => flat_trivial_closed_walks X h root, flat_of_trivial_root_walks X hc root⟩

end CoefficientwiseRigidity
