import CoefficientwiseRigidity.StarGraph
import CoefficientwiseRigidity.ChordalPathCycle

/-! Two short paths through the original star lift a cycle through the contracted vertex. -/
namespace CoefficientwiseRigidity.Star
open Structure
open scoped Classical
noncomputable section
variable {V : Type} {G : SimpleGraph V} {u : V}

def pathTwo {x y w : V} (hxy : x ≠ y) (hxw : G.Adj x w) (hwy : G.Adj w y)
    (hn : ¬ G.Adj x y) : InducedPath G x y where
  length := 2
  vertex := ![x,w,y]
  first := rfl
  last := rfl
  injective := by
    intro i j h
    have hxw' := G.ne_of_adj hxw
    have hwy' := G.ne_of_adj hwy
    fin_cases i <;> fin_cases j <;> simp_all
  adj_iff := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hxw,hwy,hn,G.symm hxw,G.symm hwy,G.adj_comm]

def pathFour (b : Bipartition G) (hu : b.side u = true) {x y : Outside G u}
    {w z : V} (hx : G.Adj x.val w) (hw : G.Adj u w) (hz : G.Adj u z) (hy : G.Adj z y.val)
    (hxy : x ≠ y) (hnxy : ¬ G.Adj x.val y.val)
    (hcommon : ¬ ∃ v, G.Adj u v ∧ G.Adj x.val v ∧ G.Adj v y.val) :
    InducedPath G x.val y.val where
  length := 4
  vertex := ![x.val,w,u,z,y.val]
  first := rfl
  last := rfl
  injective := by
    have hxu := x.property.1
    have hyu := y.property.1
    have hxy' : x.val ≠ y.val := fun h => hxy (Subtype.ext h)
    have hxw := G.ne_of_adj hx
    have hwu := (G.ne_of_adj hw).symm
    have huz := G.ne_of_adj hz
    have hzy := G.ne_of_adj hy
    have hxz : x.val ≠ z := by intro h; exact x.property.2 (h.symm ▸ hz)
    have hwy : w ≠ y.val := by intro h; exact y.property.2 (h ▸ hw)
    have hwz : w ≠ z := by intro h; exact hcommon ⟨w,hw,hx,h.symm ▸ hy⟩
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all
  adj_iff := by
    have hnux := x.property.2
    have hnuy := y.property.2
    have hnxz : ¬ G.Adj x.val z := fun h => hcommon ⟨z,hz,h,hy⟩
    have hnwy : ¬ G.Adj w y.val := fun h => hcommon ⟨w,hw,hx,h⟩
    have hnwz : ¬ G.Adj w z := by
      intro h
      have hsw : b.side w = false := by
        have hh := b.opposite hw
        rw [hu] at hh
        cases hh' : b.side w <;> simp_all
      have hsz : b.side z = false := by
        have hh := b.opposite hz
        rw [hu] at hh
        cases hh' : b.side z <;> simp_all
      exact b.opposite h (hsw.trans hsz.symm)
    intro i j
    have hnxz' : ¬ G.Adj z x.val := fun h => hnxz (G.symm h)
    fin_cases i <;> fin_cases j <;>
      simp [hx,hw,hz,hy,G.symm hx,G.symm hw,G.symm hz,G.symm hy,
        hnxy,hnux,hnuy,hnxz,hnxz',hnwy,hnwz,G.adj_comm]

/-- An induced outside path of length >=4 whose interior misses all star
neighbours cannot have both endpoints adjacent to the contracted vertex. -/
theorem no_outside_path (b : Bipartition G) (hu : b.side u = true) (hg : ChordalBipartite G)
    {x y : Outside G u} (p : InducedPath G x.val y.val) (hp : 4 ≤ p.length)
    (hout : ∀ i, p.vertex i ≠ u ∧ ¬ G.Adj u (p.vertex i))
    (hmiss : ∀ i, 0 < i.val → i.val < p.length →
      ∀ w, G.Adj u w → ¬ G.Adj (p.vertex i) w)
    (hx : (graph G u).Adj none (some x)) (hy : (graph G u).Adj none (some y)) : False := by
  have hxy : x ≠ y := by
    intro h
    have he := p.injective (p.first.trans ((congrArg Subtype.val h).trans p.last.symm))
    have hv := congrArg Fin.val he
    simp only [Fin.val_zero,Fin.val_mk] at hv
    omega
  have hnxy : ¬ G.Adj x.val y.val := by
    have hh := p.adj_iff 0 ⟨p.length,by omega⟩
    rw [p.first,p.last] at hh
    rw [hh]
    simp only [Fin.val_zero,Fin.val_mk]
    omega
  have sep {q : InducedPath G x.val y.val}
      (hq : ∀ j, 0 < j.val → j.val < q.length → q.vertex j = u ∨ G.Adj u (q.vertex j)) : p.Separated q := by
    intro i j hi hin hj hjn
    rcases hq j hj hjn with he | he
    · rw [he]
      exact ⟨(hout i).1,fun h => (hout i).2 (G.symm h)⟩
    · exact ⟨fun h => (hout i).2 (h.symm ▸ he),hmiss i hi hin _ he⟩
  have contradict {q : InducedPath G x.val y.val} (hq : 2 ≤ q.length) (hs : p.Separated q) : False :=
    hg.2 (p.length + q.length) (by omega)
      ⟨p.cycleVertex q,p.cycle_injective q hs,p.cycle_adj q (by omega) hq hs⟩
  by_cases hc : ∃ w, G.Adj u w ∧ G.Adj x.val w ∧ G.Adj w y.val
  · obtain ⟨w,hw,hxw,hwy⟩ := hc
    let q := pathTwo (fun h => hxy (Subtype.ext h)) hxw hwy hnxy
    apply contradict (q := q) (by rfl) (sep (q := q) ?_)
    intro j hj hjn
    have hj' : j = 1 := Fin.ext (by dsimp [q,pathTwo] at *; omega)
    subst j
    exact Or.inr hw
  · obtain ⟨w,hw,hwx⟩ := hx
    obtain ⟨z,hz,hzy⟩ := hy
    let q := pathFour b hu (G.symm hwx) hw hz hzy hxy hnxy hc
    apply contradict (q := q) (by change 2 ≤ 4; omega) (sep (q := q) ?_)
    intro j hj hjn
    change Fin 5 at j
    change 0 < j.val at hj
    change j.val < 4 at hjn
    fin_cases j
    · norm_num at hj
    · exact Or.inr hw
    · exact Or.inl rfl
    · exact Or.inr hz
    · norm_num at hjn

end
end CoefficientwiseRigidity.Star
