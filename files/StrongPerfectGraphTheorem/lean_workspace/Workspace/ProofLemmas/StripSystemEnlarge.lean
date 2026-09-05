import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.StripSystemMaximal
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# Rungs survive an enlargement of a `J`-strip system

PAPER (proof of 8.6, printed p. 45): *"Regard `L(H₀)` as a `J`-strip system in the natural way,
and enlarge it to a maximal `J`-strip system `(S,N)`.  **If `L(H₀)` is nondegenerate then so is
the strip system.**"*

The authors state the emphasised sentence without argument.  It is not immediate: the paper's
enlargement relation (printed p. 42, transcribed by
`Workspace.Types.StripSystems.MaximalStripSystem` and by
`StripSystemMaximal.Enlarges`) records only

* `V(S₀,N₀) ⊆ V(S,N)`,
* `S_{uv} ∩ V(S₀,N₀) = S₀_{uv}` for every edge `uv`, and
* `N₀_v ⊆ N_v` for every vertex `v`,

and in particular says nothing about whether the *rungs* of the small system are still rungs of
the big one — the defining clause of a `uv`-rung, "*`s` is the **unique** vertex of `R` in
`N_u`*", could in principle be destroyed by the growth of `N_u`.

`isUVRung_of_enlarges` below shows that it cannot be, using only the axioms:

> Let `R` be a `uv`-rung of `(S₀,N₀)` with `u`-end `s`, and suppose some `x ∈ R` with `x ≠ s`
> has landed in the enlarged `N_u`.  Since `J` is 3-connected, `u` has a neighbour `w ≠ v`; the
> last axiom of `(S₀,N₀)` supplies a `uw`-rung, whose `u`-end `z` lies in `N₀_{uw}`, so
> `z ∈ N_u ∩ S_{uw}` in the big system too.  The big system's axiom *"`N_u ∩ S_{uv}` is complete
> to `N_u ∩ S_{uw}`"* makes `x` adjacent to `z`.  But `x ∈ S₀_{uv}` and `z ∈ S₀_{uw}`, so the
> small system's axiom *"and there are no other edges between `S_{uv}` and `S_{uw}`"* forces
> `x ∈ N₀_u` — whence `x = s`, a contradiction.

Two consequences fall out at once.  `Workspace.Types.StripSystems.FormsLineGraph` mentions the
strip system only through `IsUVRung` (its second conjunct is a bare `IsAppearance`), so a choice
of rungs of `(S₀,N₀)` forming `L(H)` is *the same* choice of rungs of `(S,N)` forming the *same*
`L(H)`; that is the paper's sentence.  And a strip whose rungs are all the same set is exactly
the corresponding strip of the small system, which is what the endgame of 8.6 needs for
*"If `Z` is empty and for all `b₁b₂` there is only one `b₁b₂`-rung, then `G = L(H₀)`"*.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.StripSystemEnlarge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.StripSystemMaximal (Enlarges)

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S₀ S : U → U → Set V} {N₀ N : U → Set V}

/-! ## Elementary consequences of `Enlarges` -/

/-- An enlargement only grows the strips. -/
theorem strip_subset (hE : Enlarges J S₀ N₀ S N) {u v : U} (huv : J.Adj u v) :
    S₀ u v ⊆ S u v := by
  intro x hx
  rw [← hE.2.1 u v huv] at hx
  exact hx.1

/-- An enlargement only grows the neighbourhood sets. -/
theorem N_subset (hE : Enlarges J S₀ N₀ S N) (u : U) : N₀ u ⊆ N u := hE.2.2 u

/-- An enlargement only grows `N_{uv}`. -/
theorem Nuv_subset (hE : Enlarges J S₀ N₀ S N) {u v : U} (huv : J.Adj u v) :
    stripSystemNuv S₀ N₀ u v ⊆ stripSystemNuv S N u v :=
  fun _ hx => ⟨N_subset hE u hx.1, strip_subset hE huv hx.2⟩

/-- A vertex of the small system that lands in an *enlarged* strip was already in the
corresponding small strip. -/
theorem mem_strip_of_mem (hE : Enlarges J S₀ N₀ S N) {u v : U} (huv : J.Adj u v) {x : V}
    (hxV : x ∈ stripSystemVertices J S₀) (hx : x ∈ S u v) : x ∈ S₀ u v := by
  rw [← hE.2.1 u v huv]
  exact ⟨hx, hxV⟩

/-! ## `J` is 3-connected, so every vertex has a second neighbour -/

/-- In a 3-connected graph, every vertex has a neighbour different from any prescribed vertex.
(Used to produce the edge `uw` with `w ≠ v` in the proof below.) -/
theorem exists_adj_ne [Fintype U] (hJ : IsKConnected J 3) (u v : U) :
    ∃ w : U, J.Adj u w ∧ w ≠ v := by
  have h3 : 3 ≤ (J.neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  obtain ⟨w, hw, hwv⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) v
  exact ⟨w, hw, hwv⟩

/-! ## The transport lemma -/

/-- **Rungs survive an enlargement.**

PAPER (proof of 8.6): the unstated content of *"If `L(H₀)` is nondegenerate then so is the strip
system."*

The two `∃ w` hypotheses are the paper's standing *"`J` is 3-connected"*; see `exists_adj_ne`. -/
theorem isUVRung_of_enlarges (h₀ : IsJStripSystem G J S₀ N₀) (h : IsJStripSystem G J S N)
    (hE : Enlarges J S₀ N₀ S N) {u v : U} {R : List V}
    (hwu : ∃ w : U, J.Adj u w ∧ w ≠ v) (hwv : ∃ w : U, J.Adj v w ∧ w ≠ u)
    (hR : IsUVRung G J S₀ N₀ u v R) : IsUVRung G J S N u v R := by
  obtain ⟨huv, s, t, hp, hsub₀, hs₀, ht₀⟩ := hR
  -- The key step, stated once and used at both ends of the rung.
  have key : ∀ (a b : U), J.Adj a b → (∃ w : U, J.Adj a w ∧ w ≠ b) →
      ∀ x ∈ R, (∀ y ∈ R, y ∈ S₀ a b) → x ∈ N a → x ∈ N₀ a := by
    rintro a b hab ⟨w, haw, hwb⟩ x hx hsubab hxN
    -- the small system's `w`-strip already has a `u`-end `z ∈ N₀_{aw}`
    obtain ⟨z, hzN₀, hzS₀⟩ := StripSystemBasics.Nuv_nonempty h₀ haw
    have hzN : z ∈ N a := N_subset hE a hzN₀
    have hzS : z ∈ S a w := strip_subset hE haw hzS₀
    have hxS : x ∈ S a b := strip_subset hE hab (hsubab x hx)
    -- the big system: `N_a ∩ S_{ab}` is complete to `N_a ∩ S_{aw}`
    have hadj : G.Adj x z :=
      StripSystemBasics.Nuv_complete h hab haw (Ne.symm hwb) x ⟨hxN, hxS⟩ z ⟨hzN, hzS⟩
    -- the small system: there are no other edges between `S₀_{ab}` and `S₀_{aw}`
    exact (StripSystemBasics.mem_N_of_adj h₀ hab haw (Ne.symm hwb) (hsubab x hx) hzS₀ hadj).1
  refine ⟨huv, s, t, hp, fun x hx => strip_subset hE huv (hsub₀ x hx), fun x hx => ?_,
    fun x hx => ?_⟩
  · constructor
    · intro hxN
      exact (hs₀ x hx).mp (key u v huv hwu x hx hsub₀ hxN)
    · rintro rfl
      exact N_subset hE u ((hs₀ x hx).mpr rfl)
  · constructor
    · intro hxN
      have hsub₀' : ∀ y ∈ R, y ∈ S₀ v u := by
        intro y hy
        rw [← StripSystemBasics.strip_symm h₀ huv]
        exact hsub₀ y hy
      exact (ht₀ x hx).mp (key v u huv.symm hwv x hx hsub₀' hxN)
    · rintro rfl
      exact N_subset hE v ((ht₀ x hx).mpr rfl)

/-- The same, with the 3-connectivity hypothesis in the form it has in 8.6. -/
theorem isUVRung_of_enlarges' [Fintype U] (hJ : IsKConnected J 3)
    (h₀ : IsJStripSystem G J S₀ N₀) (h : IsJStripSystem G J S N)
    (hE : Enlarges J S₀ N₀ S N) {u v : U} {R : List V}
    (hR : IsUVRung G J S₀ N₀ u v R) : IsUVRung G J S N u v R :=
  isUVRung_of_enlarges h₀ h hE (exists_adj_ne hJ u v) (exists_adj_ne hJ v u) hR

/-! ## Consequences -/

/-- A choice of rungs of the small system forms the *same* `L(H)` for the big one.

`FormsLineGraph` refers to the strip system only through `IsUVRung`; its second conjunct — that
the union of the rungs' vertex sets carries an appearance of `J` — mentions neither `S` nor
`N`. -/
theorem formsLineGraph_of_enlarges [Fintype U] {W : Type*} {H : SimpleGraph W}
    {R : U → U → List V} (hJ : IsKConnected J 3)
    (h₀ : IsJStripSystem G J S₀ N₀) (h : IsJStripSystem G J S N)
    (hE : Enlarges J S₀ N₀ S N) (hF : FormsLineGraph G J S₀ N₀ R H) :
    FormsLineGraph G J S N R H :=
  ⟨fun u v huv => isUVRung_of_enlarges' hJ h₀ h hE (hF.1 u v huv), hF.2⟩

/-- **PAPER: *"If `L(H₀)` is nondegenerate then so is the strip system."*** -/
theorem nondegenerateStripSystem_of_enlarges [Fintype U] (hJ : IsKConnected J 3)
    (h₀ : IsJStripSystem G J S₀ N₀) (h : IsJStripSystem G J S N)
    (hE : Enlarges J S₀ N₀ S N) (hnd : NondegenerateStripSystem G J S₀ N₀) :
    NondegenerateStripSystem G J S N := by
  obtain ⟨n, H, R, hF, hndeg⟩ := hnd
  exact ⟨n, H, R, formsLineGraph_of_enlarges hJ h₀ h hE hF, hndeg⟩

/-- **A strip with only one rung has not grown.**

If every `uv`-rung of the enlarged system has the same vertex set as some fixed `uv`-rung `R` of
the small system, then `S_{uv} = S₀_{uv}` — because every vertex of `S_{uv}` lies on a `uv`-rung
(axiom 4) and hence on `R`.

This is what the endgame of 8.6 needs for *"If `Z` is empty and for all `b₁b₂` there is only one
`b₁b₂`-rung, then `G = L(H₀)`"*. -/
theorem strip_eq_of_unique_rung [Fintype U] (hJ : IsKConnected J 3)
    (h₀ : IsJStripSystem G J S₀ N₀) (h : IsJStripSystem G J S N)
    (hE : Enlarges J S₀ N₀ S N) {u v : U} (huv : J.Adj u v) {R : List V}
    (hR : IsUVRung G J S₀ N₀ u v R) (hRS : S₀ u v = {x : V | x ∈ R})
    (huniq : ∀ R' : List V, IsUVRung G J S N u v R' → {x : V | x ∈ R'} = {x : V | x ∈ R}) :
    S u v = S₀ u v := by
  refine Set.Subset.antisymm (fun x hx => ?_) (strip_subset hE huv)
  obtain ⟨R', hR', hxR'⟩ := StripSystemBasics.exists_rung h huv hx
  have : x ∈ ({x : V | x ∈ R} : Set V) := by rw [← huniq R' hR']; exact hxR'
  rw [hRS]
  exact this

end Workspace.ProofLemmas.StripSystemEnlarge
