import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StripSystemBasics

/-!
# Choosing a rung on every edge of `J`, with one edge prescribed

PAPER (printed p. 40, opening of the proof of 8.2): *"For each edge `ij` of `J` choose an
`ij`-rung `R_ij`, arbitrarily for every edge of `J` different from `uv`, and such that `R_uv` has
length `≥ 1`; and let this choice of rungs form `L(H)`."*

This module supplies the first half of that sentence — the *choice* — and nothing else.  Two
ingredients only: the seventh axiom of a `J`-strip system already hands out a rung on every edge
(`StripSystemBasics.exists_special_rungs`), and the reverse of a `uv`-rung is a `vu`-rung
(`rung_reverse` below), which is what lets the chosen family be made **symmetric**:
`R_{vu} = (R_{uv})ᴿ`.

Symmetry matters downstream and is not automatic: the union of the vertex sets of the chosen
rungs, which is the vertex set of the appearance `L(H)` that `StripSystems.FormsLineGraph` talks
about, is `⋃_{ab ∈ E(J)} V(R_ab)` taken over *ordered* pairs, so an asymmetric family would drop
two different rungs of the same strip into it and no longer describe a line graph.

Nothing here corresponds to a numbered result of the paper; it is the bookkeeping under the word
*"choose"*.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm82RungFamily

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V}

/-- **The reverse of a `uv`-rung is a `vu`-rung.**

`IsUVRung` names the two ends of the rung, `s` in `N_u` and `t` in `N_v`; reversing the list
exchanges them, and `S_{uv} = S_{vu}` is the first axiom of a strip system. -/
theorem rung_reverse (hSN : IsJStripSystem G J S N) {a b : U} {R : List V}
    (hR : IsUVRung G J S N a b R) : IsUVRung G J S N b a R.reverse := by
  obtain ⟨hab, s, t, hpath, hsub, hs, ht⟩ := hR
  refine ⟨hab.symm, t, s, PathBasics.isPathFrom_reverse hpath, ?_, ?_, ?_⟩
  · intro x hx
    rw [List.mem_reverse] at hx
    rw [← StripSystemBasics.strip_symm hSN hab]
    exact hsub x hx
  · intro x hx
    rw [List.mem_reverse] at hx
    exact ht x hx
  · intro x hx
    rw [List.mem_reverse] at hx
    exact hs x hx

/-- **"For each edge `ij` of `J` choose an `ij`-rung `R_ij`, arbitrarily for every edge of `J`
different from `uv`, and such that `R_uv` has length `≥ 1`."**

Given any prescribed `uv`-rung `R₀` (in the proof of 8.2, one of length `≥ 1`), there is a choice
of rungs — one on every edge of `J`, symmetric under reversing the edge — whose value at `uv` is
`R₀`. -/
theorem exists_symmetric_rung_family [Fintype U]
    (hSN : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v)
    {R₀ : List V} (hR₀ : IsUVRung G J S N u v R₀) :
    ∃ R : U → U → List V,
      (∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b)) ∧
      (∀ a b : U, J.Adj a b → R b a = (R a b).reverse) ∧
      R u v = R₀ := by
  classical
  obtain ⟨Rs, hRs, -⟩ := StripSystemBasics.exists_special_rungs hSN
  have huvne : u ≠ v := huv.ne
  obtain ⟨f, hfinj⟩ : ∃ f : U → ℕ, Function.Injective f :=
    ⟨fun a => ((Fintype.equivFin U a : Fin (Fintype.card U)) : ℕ),
      fun a b h => (Fintype.equivFin U).injective (Fin.ext h)⟩
  refine ⟨fun a b =>
      if a = u ∧ b = v then R₀
      else if a = v ∧ b = u then R₀.reverse
      else if f a < f b then Rs a b else (Rs b a).reverse, ?_, ?_, ?_⟩
  · intro a b hab
    dsimp only
    split_ifs with h1 h2 _
    · obtain ⟨rfl, rfl⟩ := h1
      exact hR₀
    · obtain ⟨rfl, rfl⟩ := h2
      exact rung_reverse hSN hR₀
    · exact hRs a b hab
    · exact rung_reverse hSN (hRs b a hab.symm)
  · intro a b hab
    have hne : a ≠ b := hab.ne
    have hfab : f a ≠ f b := fun h => hne (hfinj h)
    dsimp only
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 <;>
      simp_all <;> omega
  · dsimp only
    rw [if_pos (And.intro rfl rfl)]

/-- **A symmetric choice of rungs meets each strip in exactly its own rung.**

The vertex set of the appearance `L(H)` that a choice of rungs forms is
`K = ⋃_{cd ∈ E(J)} V(R_cd)`.  Because the strips are pairwise disjoint and the family is
symmetric, `K ∩ S_{ab}` is exactly `V(R_ab)`: no *other* vertex of the strip `S_{ab}` sneaks into
`K`.  This is what makes `G|K` decompose into the rungs. -/
theorem mem_rung_of_mem_union (h : IsJStripSystem G J S N) {R : U → U → List V}
    (hR : ∀ a b : U, J.Adj a b → IsUVRung G J S N a b (R a b))
    (hsym : ∀ a b : U, J.Adj a b → R b a = (R a b).reverse)
    {a b : U} (hab : J.Adj a b) {x : V}
    (hxK : x ∈ ⋃ (c : U) (d : U) (_ : J.Adj c d), {z : V | z ∈ R c d})
    (hxS : x ∈ S a b) : x ∈ R a b := by
  simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hxK
  obtain ⟨c, d, hcd, hxcd⟩ := hxK
  have hxScd : x ∈ S c d := StripSystemBasics.rung_subset_strip (hR c d hcd) x hxcd
  have hsame : s(a, b) = s(c, d) :=
    StripSystemBasics.edge_eq_of_mem_strips h hab hcd hxS hxScd
  rcases Sym2.eq_iff.mp hsame with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact hxcd
  · rw [h1, h2, hsym c d hcd, List.mem_reverse]
    exact hxcd

end Workspace.ProofLemmas.Thm82RungFamily
