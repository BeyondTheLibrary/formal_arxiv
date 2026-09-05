import Mathlib
import Workspace.Types.Core

/-!
# Two non-cut vertices of a connected set

The proof of 24.7 says *"choose distinct `x₁, x₁' ∈ X₁` such that `X₁ \ {x₁}`, `X₁ \ {x₁'}`
are both anticonnected"*, and the paper leaves the existence of such a pair to the reader.
It is the classical fact that a connected graph on at least two vertices has at least two
non-cut vertices (the two ends of a longest path, or two leaves of a spanning tree).

The proof used here is the distance one, which needs no trees: fix a root `r`, and let `a` be
at maximum distance from `r`.  Then `a` is non-cut, because a vertex `x ≠ a` can be reached
from `r` by descending the distance function, and every vertex on that descent is strictly
closer to `r` than `a` is, hence different from `a`.  Doing it twice — once from an arbitrary
root, then once from `a` — produces two *distinct* non-cut vertices.

Stated for an arbitrary `G`, so the anticonnected version used by §24 is the same lemma
applied to `Gᶜ` (`exists_two_nonanticut`).

No counterpart in the paper; this is infrastructure.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.NonCutVertices

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- **A vertex at maximum distance from a root is non-cut.** -/
private theorem connectedSet_sdiff_of_max_dist {S : Set V} (hS : ConnectedSet G S) {r a : ↥S}
    (hmax : ∀ x : ↥S, (G.induce S).dist r x ≤ (G.induce S).dist r a)
    (hra : (r : V) ≠ (a : V)) :
    ConnectedSet G (S \ {(a : V)}) := by
  have hrT : (r : V) ∈ S \ {(a : V)} := ⟨r.2, hra⟩
  -- every vertex other than `a` can be reached from `r` without using `a`
  have key : ∀ (n : ℕ) (x : V) (hxS : x ∈ S) (hxa : x ≠ (a : V)),
      (G.induce S).dist r ⟨x, hxS⟩ ≤ n →
      (G.induce (S \ {(a : V)})).Reachable ⟨(r : V), hrT⟩ ⟨x, ⟨hxS, hxa⟩⟩ := by
    intro n
    induction n with
    | zero =>
        intro x hxS hxa hd
        have h0 : (G.induce S).dist r ⟨x, hxS⟩ = 0 := by omega
        have hxr : (r : ↥S) = ⟨x, hxS⟩ := ((hS r ⟨x, hxS⟩).dist_eq_zero_iff).mp h0
        have hval : (r : V) = x := congrArg Subtype.val hxr
        have : (⟨(r : V), hrT⟩ : ↥(S \ {(a : V)})) = ⟨x, ⟨hxS, hxa⟩⟩ := Subtype.ext hval
        rw [this]
    | succ m ih =>
        intro x hxS hxa hd
        by_cases h0 : (G.induce S).dist r ⟨x, hxS⟩ = 0
        · have hxr : (r : ↥S) = ⟨x, hxS⟩ := ((hS r ⟨x, hxS⟩).dist_eq_zero_iff).mp h0
          have hval : (r : V) = x := congrArg Subtype.val hxr
          have : (⟨(r : V), hrT⟩ : ↥(S \ {(a : V)})) = ⟨x, ⟨hxS, hxa⟩⟩ := Subtype.ext hval
          rw [this]
        · obtain ⟨w, hw⟩ := (hS r ⟨x, hxS⟩).exists_walk_length_eq_dist
          set d := (G.induce S).dist r ⟨x, hxS⟩ with hdef
          have hd1 : 1 ≤ d := by omega
          have hklt : d - 1 < w.length := by omega
          have hadj := w.adj_getVert_succ hklt
          have hk1 : (d - 1) + 1 = w.length := by omega
          have hend : w.getVert ((d - 1) + 1) = ⟨x, hxS⟩ := by
            rw [hk1]; exact w.getVert_length
          have hdy : (G.induce S).dist r (w.getVert (d - 1)) ≤ d - 1 := by
            have h := SimpleGraph.dist_le (w.take (d - 1))
            rw [SimpleGraph.Walk.take_length] at h
            omega
          have hya : ((w.getVert (d - 1) : ↥S) : V) ≠ (a : V) := by
            intro he
            have : (w.getVert (d - 1) : ↥S) = a := Subtype.ext he
            rw [this] at hdy
            have := hmax ⟨x, hxS⟩
            omega
          have hreach := ih ((w.getVert (d - 1) : ↥S) : V) (w.getVert (d - 1)).2 hya
            (le_trans hdy (by omega))
          refine hreach.trans (SimpleGraph.Adj.reachable ?_)
          show G.Adj ((w.getVert (d - 1) : ↥S) : V) x
          have : G.Adj ((w.getVert (d - 1) : ↥S) : V) ((w.getVert ((d - 1) + 1) : ↥S) : V) := hadj
          rw [hend] at this
          exact this
  intro p q
  have hp : (G.induce (S \ {(a : V)})).Reachable ⟨(r : V), hrT⟩ p := by
    have := key ((G.induce S).dist r ⟨(p : V), p.2.1⟩) (p : V) p.2.1 p.2.2 le_rfl
    convert this using 2
  have hq : (G.induce (S \ {(a : V)})).Reachable ⟨(r : V), hrT⟩ q := by
    have := key ((G.induce S).dist r ⟨(q : V), q.2.1⟩) (q : V) q.2.1 q.2.2 le_rfl
    convert this using 2
  exact hp.symm.trans hq

/-- **Two non-cut vertices.**  A connected set with more than one vertex has two distinct
vertices whose removal leaves it connected. -/
theorem exists_two_noncut [Finite V] {S : Set V} (hS : ConnectedSet G S)
    (hns : ¬ S.Subsingleton) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      ConnectedSet G (S \ {a}) ∧ ConnectedSet G (S \ {b}) := by
  obtain ⟨x₀, hx₀, y₀, hy₀, hxy⟩ := Set.not_subsingleton_iff.mp hns
  have : Nonempty ↥S := ⟨⟨x₀, hx₀⟩⟩
  set r : ↥S := ⟨x₀, hx₀⟩ with hrdef
  -- the first non-cut vertex: at maximum distance from `r`
  obtain ⟨a, hamax⟩ := Finite.exists_max (fun z : ↥S => (G.induce S).dist r z)
  have hra : (r : V) ≠ (a : V) := by
    intro he
    have hare : (a : ↥S) = r := Subtype.ext he.symm
    have h1 : 0 < (G.induce S).dist r ⟨y₀, hy₀⟩ :=
      (hS r ⟨y₀, hy₀⟩).pos_dist_of_ne (by
        intro hcon
        exact hxy (congrArg Subtype.val hcon))
    have h2 := hamax ⟨y₀, hy₀⟩
    rw [hare] at h2
    simp only [SimpleGraph.dist_self] at h2
    omega
  have h1 : ConnectedSet G (S \ {(a : V)}) := connectedSet_sdiff_of_max_dist hS hamax hra
  -- the second: at maximum distance from `a`
  obtain ⟨b, hbmax⟩ := Finite.exists_max (fun z : ↥S => (G.induce S).dist a z)
  have hab : (a : V) ≠ (b : V) := by
    intro he
    have hbae : (b : ↥S) = a := Subtype.ext he.symm
    have h1' : 0 < (G.induce S).dist a r :=
      (hS a r).pos_dist_of_ne (by
        intro hcon
        exact hra (congrArg Subtype.val hcon).symm)
    have h2 := hbmax r
    rw [hbae] at h2
    simp only [SimpleGraph.dist_self] at h2
    omega
  have h2 : ConnectedSet G (S \ {(b : V)}) := connectedSet_sdiff_of_max_dist hS hbmax hab
  exact ⟨(a : V), a.2, (b : V), b.2, hab, h1, h2⟩

/-- The `Gᶜ` form: an anticonnected set with more than one vertex has two distinct vertices
whose removal leaves it anticonnected.  This is the paper's *"choose distinct `x₁, x₁' ∈ X₁`
such that `X₁ \ {x₁}`, `X₁ \ {x₁'}` are both anticonnected"*. -/
theorem exists_two_nonanticut [Finite V] {S : Set V} (hS : AnticonnectedSet G S)
    (hns : ¬ S.Subsingleton) :
    ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      AnticonnectedSet G (S \ {a}) ∧ AnticonnectedSet G (S \ {b}) :=
  exists_two_noncut (G := Gᶜ) hS hns

end Workspace.ProofLemmas.NonCutVertices
