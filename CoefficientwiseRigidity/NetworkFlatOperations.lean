import CoefficientwiseRigidity.NetworkGauge
import CoefficientwiseRigidity.NetworkRelabel

/-!
Flatness invariants for the actual degree-zero/one/two network operations.
These statements concern the stored gains, independently of numerical profiles.
-/
namespace CoefficientwiseRigidity.Network
open Kernel
noncomputable section
variable {M : ℕ} {V W : Type*} {p : V → ℕ}

def Net.Gauge (N : Net M p) (γ : V → Equiv.Perm (Fin M)) : Prop :=
  ∀ e ∈ N.edges, ∀ f ∈ e.kernels, ∀ i, f.gain (γ e.right i) = γ e.left i

theorem Net.flat_iff_gauge (N : Net M p) : N.Flat ↔ ∃ γ, N.Gauge γ := Iff.rfl

theorem Net.gauge_addEdge_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (L : GainList M (p u) (p v)) (γ : V → Equiv.Perm (Fin M)) :
    (N.addEdge u v huv L).Gauge γ ↔
      (∀ f ∈ L, ∀ i, f.gain (γ v i) = γ u i) ∧ N.Gauge γ := by
  simp [Net.Gauge, Net.addEdge]

theorem Net.gauge_addSingle_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (f : GainEntry M (p u) (p v)) (γ : V → Equiv.Perm (Fin M)) :
    (N.addEdge u v huv [f]).Gauge γ ↔
      (∀ i, f.gain (γ v i) = γ u i) ∧ N.Gauge γ := by
  rw [Net.gauge_addEdge_iff]
  simp

theorem Net.gauge_lift_iff (N : Net M p) (m : ℕ)
    (γ : Option V → Equiv.Perm (Fin M)) :
    (N.lift m).Gauge γ ↔ N.Gauge (fun v => γ (some v)) := by
  simp [Net.Gauge, Net.lift, liftEdge]
  rfl

theorem Net.Gauge.trans {N : Net M p} {γ : V → Equiv.Perm (Fin M)}
    (hγ : N.Gauge γ) (σ : Equiv.Perm (Fin M)) :
    N.Gauge (fun v => σ.trans (γ v)) := by
  intro e he f hf i
  exact hγ e he f hf (σ i)

theorem Net.Gauge.of_addEdge {N : Net M p} {u v : V} {huv : u ≠ v}
    {L : GainList M (p u) (p v)} {γ : V → Equiv.Perm (Fin M)}
    (hγ : (N.addEdge u v huv L).Gauge γ) : N.Gauge γ :=
  (N.gauge_addEdge_iff u v huv L γ).mp hγ |>.2

theorem Net.flat_lift_iff (N : Net M p) (m : ℕ) : (N.lift m).Flat ↔ N.Flat := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨fun v => γ (some v), (N.gauge_lift_iff m γ).mp hγ⟩
  · rintro ⟨γ, hγ⟩
    exact ⟨Option.elim' (Equiv.refl _) γ, (N.gauge_lift_iff m _).mpr hγ⟩

/-- A single leaf carries no obstruction to a flattening gauge. -/
theorem Net.flat_attachLeaf_iff (N : Net M p) (m : ℕ) (u : V)
    (f : GainEntry M (p u) m) : (N.attachLeaf m u [f]).Flat ↔ N.Flat := by
  constructor
  · rintro ⟨γ, hγ⟩
    have hg : (N.lift m).Gauge γ := Net.Gauge.of_addEdge hγ
    exact ⟨fun v => γ (some v), (N.gauge_lift_iff m γ).mp hg⟩
  · rintro ⟨γ, hγ⟩
    let γ' := Option.elim' ((γ u).trans f.gain.symm) γ
    refine ⟨γ', ?_⟩
    change ((N.lift m).addEdge (some u) none (by simp) [f]).Gauge γ'
    rw [Net.gauge_addSingle_iff]
    constructor
    · intro i
      simp [γ']
    · exact (N.gauge_lift_iff m γ').mpr hγ

/-- Flatness is preserved by the same gain product used by exact serial counting. -/
theorem Net.flat_attachSeries_iff (N : Net M p) (m : ℕ) (u v : V) (huv : u ≠ v)
    (hu : p u ≤ M) (hm : m ≤ M) (hv : p v ≤ M)
    (e : GainEntry M (p u) m) (f : GainEntry M m (p v)) :
    (N.attachSeries m u v [e] [f]).Flat ↔
      (N.addEdge u v huv [e.compose hu hm hv f]).Flat := by
  constructor
  · rintro ⟨γ, hγ⟩
    change (((N.lift m).addEdge none (some v) (by simp) [f]).addEdge
      (some u) none (by simp) [e]).Gauge γ at hγ
    rw [Net.gauge_addSingle_iff, Net.gauge_addSingle_iff, Net.gauge_lift_iff] at hγ
    obtain ⟨he, hf, hb⟩ := hγ
    refine ⟨fun w => γ (some w), (N.gauge_addSingle_iff u v huv _ _).mpr ⟨?_, hb⟩⟩
    · intro i
      change e.gain (f.gain (γ (some v) i)) = γ (some u) i
      rw [hf i, he i]
  · rintro ⟨γ, hγ⟩
    obtain ⟨hc, hb⟩ := (N.gauge_addSingle_iff u v huv _ _).mp hγ
    let γ' := Option.elim' ((γ v).trans f.gain) γ
    refine ⟨γ', ?_⟩
    change (((N.lift m).addEdge none (some v) (by simp) [f]).addEdge
      (some u) none (by simp) [e]).Gauge γ'
    rw [Net.gauge_addSingle_iff, Net.gauge_addSingle_iff, Net.gauge_lift_iff]
    exact ⟨hc, (fun _ => rfl), hb⟩

theorem Net.flat_addSingle_congr (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) (h : e.gain = f.gain) :
    (N.addEdge u v huv [e]).Flat ↔ (N.addEdge u v huv [f]).Flat := by
  simp only [Net.flat_iff_gauge, Net.gauge_addSingle_iff, h]

theorem Net.flat_splitLeft_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) :
    (N.addEdge u v huv [e.splitLeft f]).Flat ↔ (N.addEdge u v huv [e]).Flat :=
  N.flat_addSingle_congr u v huv _ _ rfl

theorem Net.flat_splitRight_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) :
    (N.addEdge u v huv [e.splitRight f]).Flat ↔ (N.addEdge u v huv [f]).Flat :=
  N.flat_addSingle_congr u v huv _ _ rfl

theorem Net.flat_parallel_same_gain_iff (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v)) (h : e.gain = f.gain) :
    ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat ↔ (N.addEdge u v huv [e]).Flat := by
  simp only [Net.flat_iff_gauge, Net.gauge_addSingle_iff, h, and_self_left]

/-- Nonflatness with two flat choices forces a genuine relative gain. -/
theorem Net.gains_ne_of_nonflat_parallel (N : Net M p) (u v : V) (huv : u ≠ v)
    (e f : GainEntry M (p u) (p v))
    (hn : ¬ ((N.addEdge u v huv [f]).addEdge u v huv [e]).Flat)
    (he : (N.addEdge u v huv [e]).Flat) : e.gain ≠ f.gain := by
  intro h
  exact hn ((N.flat_parallel_same_gain_iff u v huv e f h).mpr he)

theorem Net.gauge_rename_iff (N : Net M p) (e : V ≃ W)
    (γ : W → Equiv.Perm (Fin M)) :
    (N.rename e).Gauge γ ↔ N.Gauge (fun v => γ (e v)) := by
  simp [Net.Gauge, Net.rename, Edge.rename, renameEntry]

theorem Net.flat_rename_iff (N : Net M p) (e : V ≃ W) : (N.rename e).Flat ↔ N.Flat := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨fun v => γ (e v), (N.gauge_rename_iff e γ).mp hγ⟩
  · rintro ⟨γ, hγ⟩
    refine ⟨fun w => γ (e.symm w), (N.gauge_rename_iff e (fun w => γ (e.symm w))).mpr ?_⟩
    simpa using hγ

end
end CoefficientwiseRigidity.Network
