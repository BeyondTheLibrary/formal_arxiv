import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting

/-!
# The structure of `N_v` in a `J`-strip system

PAPER (proof of 8.6, claim (2), printed p. 46): *"Since `N_v` is not anticonnected, it follows
that `(F ∪ F', N_v)` is a skew partition."*  and *"Let the neighbours of `v` in `J` be
`u₁,…,u_k`; then every anticomponent of `N_v` is a subset of one of `N_{vu₁},…,N_{vu_k}`."*

Neither sentence is argued in the paper.  Both come from the same two facts:

* `N_v` is the union of the sets `N_{vw}` over the neighbours `w` of `v` in `J`
  (printed p. 40, *"So every vertex of `N_u` belongs to `N_{uv}` for exactly one `v`"*), and
* distinct `N_{vw}`'s are **complete** to one another (the sixth axiom of a `J`-strip system),
  hence pairwise *anti*complete, i.e. mutually unreachable in `Ḡ`.

Since `J` is 3-connected, `v` has at least three neighbours and each `N_{vw}` is nonempty
(`StripSystemBasics.Nuv_nonempty`), so `Ḡ|N_v` really does fall apart.

The module also records the small graph fact behind both statements — a connected set contained
in the union of two anticomplete sets lies wholly inside one of them — and the existence of an
edge of `J` avoiding a prescribed vertex, which is what makes the paper's `F'` nonempty.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.StripSystemNeighbourhood

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} {G : SimpleGraph V} {J : SimpleGraph U}
  {S : U → U → Set V} {N : U → Set V}

/-! ## A connected set inside a union of two anticomplete sets -/

/-- Walking inside `C ⊆ P ∪ Q` from a vertex of `P` can never leave `P`, when `P` is
anticomplete to `Q`. -/
theorem mem_of_walk {P Q C : Set V} (hPQ : Anticomplete G P Q) (hsub : C ⊆ P ∪ Q) :
    ∀ {a b : ↥C}, (G.induce C).Walk a b → (a : V) ∈ P → (b : V) ∈ P := by
  intro a b w
  induction w with
  | nil => exact id
  | @cons x y _ hadj _ ih =>
      intro hx
      refine ih ?_
      have hadj' : G.Adj (x : V) (y : V) := hadj
      rcases hsub y.2 with hy | hy
      · exact hy
      · exact absurd hadj' (hPQ (x : V) hx (y : V) hy)

/-- **A connected set contained in the union of two anticomplete sets lies inside one of
them.** -/
theorem connectedSet_subset_of_anticomplete {P Q C : Set V} (hPQ : Anticomplete G P Q)
    (hC : ConnectedSet G C) (hsub : C ⊆ P ∪ Q) {x : V} (hx : x ∈ C) (hxP : x ∈ P) :
    C ⊆ P :=
  fun _ hy => mem_of_walk hPQ hsub (hC ⟨x, hx⟩ ⟨_, hy⟩).some hxP

/-! ## `N_v` is the union of the `N_{vw}` -/

/-- `N_v = ⋃ (w adjacent to v), N_{vw}` — the paper's *"every vertex of `N_u` belongs to
`N_{uv}` for exactly one `v`"* (printed p. 40), in union form. -/
theorem N_eq_iUnion_Nuv (h : IsJStripSystem G J S N) (v : U) :
    N v = ⋃ (w : U) (_ : J.Adj v w), stripSystemNuv S N v w := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · intro hx
    obtain ⟨w, hvw, hxw⟩ := StripSystemBasics.mem_Nuv_of_mem_N h hx
    exact ⟨w, hvw, hxw⟩
  · rintro ⟨w, -, hxw⟩
    exact hxw.1

/-- Distinct `N_{vw}`'s are complete to each other, so in `Ḡ` they are anticomplete. -/
theorem anticomplete_compl_Nuv (h : IsJStripSystem G J S N) {v w w' : U}
    (hvw : J.Adj v w) (hvw' : J.Adj v w') (hne : w ≠ w') :
    Anticomplete Gᶜ (stripSystemNuv S N v w) (stripSystemNuv S N v w') := by
  intro x hx y hy hadj
  exact (SimpleGraph.compl_adj .. |>.mp hadj).2
    (StripSystemBasics.Nuv_complete h hvw hvw' hne x hx y hy)

/-- `N_{vw}` is anticomplete, in `Ḡ`, to the rest of `N_v`. -/
theorem anticomplete_compl_Nuv_diff (h : IsJStripSystem G J S N) {v w : U} (hvw : J.Adj v w) :
    Anticomplete Gᶜ (stripSystemNuv S N v w) (N v \ stripSystemNuv S N v w) := by
  intro x hx y hy
  obtain ⟨w', hvw', hyw'⟩ := StripSystemBasics.mem_Nuv_of_mem_N h hy.1
  have hne : w ≠ w' := by
    rintro rfl
    exact hy.2 hyw'
  exact anticomplete_compl_Nuv h hvw hvw' hne x hx y hyw'

/-! ## The two sentences of claim (2) -/

/-- **PAPER: *"every anticomponent of `N_v` is a subset of one of `N_{vu₁},…,N_{vu_k}`"***
(printed p. 46).

Stated for an arbitrary anticonnected subset of `N_v`, which is what the argument needs. -/
theorem subset_Nuv_of_anticonnected (h : IsJStripSystem G J S N) {v : U} {D : Set V}
    (hD : AnticonnectedSet G D) (hDsub : D ⊆ N v) {d : V} (hd : d ∈ D) :
    ∃ w : U, J.Adj v w ∧ D ⊆ stripSystemNuv S N v w := by
  obtain ⟨w, hvw, hdw⟩ := StripSystemBasics.mem_Nuv_of_mem_N h (hDsub hd)
  refine ⟨w, hvw, connectedSet_subset_of_anticomplete (anticomplete_compl_Nuv_diff h hvw) hD
    (fun y hy => ?_) hd hdw⟩
  by_cases hyw : y ∈ stripSystemNuv S N v w
  · exact Or.inl hyw
  · exact Or.inr ⟨hDsub hy, hyw⟩

/-- **PAPER: *"Since `N_v` is not anticonnected …"*** (printed p. 46).

`v` has at least three neighbours in the 3-connected graph `J`; pick two of them, `w ≠ w'`.
Both `N_{vw}` and `N_{vw'}` are nonempty, and they are anticomplete in `Ḡ`, so `Ḡ|N_v` is
disconnected. -/
theorem not_anticonnectedSet_N [Fintype U] (hJ : IsKConnected J 3)
    (h : IsJStripSystem G J S N) (v : U) : ¬ AnticonnectedSet G (N v) := by
  -- two distinct neighbours of `v`
  have h3 : 3 ≤ (J.neighborSet v).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ v
  obtain ⟨w, hw, -⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet v) (by omega) v
  obtain ⟨w', hw', hw'w⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet v) (by omega) w
  have hvw : J.Adj v w := hw
  have hvw' : J.Adj v w' := hw'
  obtain ⟨a, ha⟩ := StripSystemBasics.Nuv_nonempty h hvw
  obtain ⟨b, hb⟩ := StripSystemBasics.Nuv_nonempty h hvw'
  intro hcon
  -- `b` would have to lie in `N_{vw}`, but it lies in `N_{vw'}`
  have hbw : b ∈ stripSystemNuv S N v w := by
    refine connectedSet_subset_of_anticomplete (anticomplete_compl_Nuv_diff h hvw) hcon
      (fun y hy => ?_) ha.1 ha hb.1
    by_cases hyw : y ∈ stripSystemNuv S N v w
    · exact Or.inl hyw
    · exact Or.inr ⟨hy, hyw⟩
  exact hw'w (StripSystemBasics.Nuv_eq_of_mem h hvw hvw' hbw hb).symm

/-! ## An edge of `J` avoiding a prescribed vertex -/

/-- A 3-connected graph has an edge both of whose ends differ from any prescribed vertex.

PAPER (proof of 8.6, claim (2)): the sentence *"then `F' ≠ ∅`"* — the strip on such an edge is
nonempty and misses `N_v`. -/
theorem exists_adj_avoiding [Fintype U] (hJ : IsKConnected J 3) (v : U) :
    ∃ c d : U, J.Adj c d ∧ c ≠ v ∧ d ≠ v := by
  obtain ⟨hcard, hconn⟩ := hJ
  have hcard1 : ({v} : Set U).ncard < 3 := by
    rw [Set.ncard_singleton]; omega
  have hc := hconn {v} hcard1
  -- `{v}ᶜ` has at least three elements, so it has two distinct ones
  have hcompl : 1 < (({v} : Set U)ᶜ : Set U).ncard := by
    have h1 := Set.ncard_add_ncard_compl ({v} : Set U)
    rw [Nat.card_eq_fintype_card, Set.ncard_singleton] at h1
    omega
  obtain ⟨a, ha⟩ : (({v} : Set U)ᶜ : Set U).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard hcompl a
  have hne : (⟨a, ha⟩ : ↥(({v} : Set U)ᶜ)) ≠ ⟨b, hb⟩ := by
    intro hcon
    exact hba (congrArg Subtype.val hcon).symm
  obtain ⟨c, hcadj⟩ :=
    SubdivisionCounting.exists_adj_of_reachable (hc.preconnected ⟨a, ha⟩ ⟨b, hb⟩) hne
  exact ⟨a, (c : U), hcadj, ha, c.2⟩

/-- The vertex set of a strip on an edge avoiding `v` is a nonempty set disjoint from `N_v`. -/
theorem exists_mem_not_mem_N [Fintype U] (hJ : IsKConnected J 3) (h : IsJStripSystem G J S N)
    (v : U) : ∃ x : V, x ∈ stripSystemVertices J S ∧ x ∉ N v := by
  obtain ⟨c, d, hcd, hcv, hdv⟩ := exists_adj_avoiding hJ v
  obtain ⟨x, hx⟩ := StripSystemBasics.strip_nonempty h hcd
  refine ⟨x, StripSystemBasics.strip_subset_vertices hcd hx, fun hxN => ?_⟩
  have := StripSystemBasics.strip_inter_N_eq_empty h hcd (Ne.symm hcv) (Ne.symm hdv)
  rw [Set.eq_empty_iff_forall_notMem] at this
  exact this x ⟨hx, hxN⟩

end Workspace.ProofLemmas.StripSystemNeighbourhood
