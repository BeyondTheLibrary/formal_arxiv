import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.Thm96Assembly
import Workspace.ProofLemmas.Thm96Claim2
import Workspace.ProofLemmas.Thm96Claim1Steps
import Workspace.ProofLemmas.Thm96StriationTools
import Workspace.ProofLemmas.Thm96TwoJoin
import Workspace.ProofLemmas.Thm96ClosingSteps
import Workspace.ProofLemmas.DegenerateStriationIsDoubleSplit
import Workspace.ProofLemmas.DisconnectedLargeGraphHasBalancedSkewPartition

/-!
# The body of 9.6 — claims (1), (2), (3) and the closing paragraph

PAPER (9.6, printed pp. 54–55), everything downstream of *"By 9.4 we can partition
`V(G) \ V(L)` into two sets `M, N` …"*:

> *"(1) If there exists `f ∈ N` with a nonneighbour in `V(S₁) ∪ ⋯ ∪ V(S_m)` then the theorem
> holds. …*
>
> *From (1) we may assume that `N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`, and by taking
> complements, that `M` is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`.*
>
> *(2) If `M, N` are both nonempty then the theorem holds. …*
>
> *(3) If `M, N` are both empty then the theorem holds. …*
>
> *From (2) and (3), and taking complements if necessary, we may assume that `N` is empty and
> `M` is nonempty. …  Then `(M₁ ∪ V(S₁), V(G) \ (M₁ ∪ V(S₁)))` is a proper 2-join of `G`.  This
> proves 9.6."*

This module cuts that text at exactly the paper's own seams.

* `Setup` bundles the standing hypotheses at the point where the printed proof reaches (1):
  `G` Berge, no `K₄`-enlargement appearance and no overshadowed `K₄`-appearance in either
  orientation, `|V(G)| ≥ 8`, a **maximal** striation `L = (S, T)`, and 9.4's partition of
  `V(G) \ V(L)` into `M` (local neighbour set) and `N` (resolving neighbour set).
* `Balanced` is the pair of conclusions the paper draws from (1) and its complement:
  *"`N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`"* and *"`M` is anticomplete to
  `V(T₁) ∪ ⋯ ∪ V(T_n)`"*.
* `setup_compl` / `balanced_compl` are the complement-symmetry the four printed *"by taking
  complements"* steps rest on: the complement of a striation is the striation with the strips
  and the antistrips exchanged, and this exchange swaps *local* with *resolves*, hence `M` with
  `N`.  (`Thm96Assembly.concl_compl` supplies the other half — that 9.6's conclusion is
  complement-stable.)
* `claim1`, `claim2`, `claim3`, `closing` are the four printed steps, in the order printed.

`Thm96Assembly.Concl` is 9.6's four-way conclusion, byte-identical to the conclusion of
`thm_9_6`; it is reused here rather than restated.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm96Body

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The standing hypotheses at the point where the printed proof reaches claim (1) -/

/-- The hypothesis package of 9.6 at the sentence *"By 9.4 we can partition `V(G) \ V(L)` into
two sets `M, N` …"*. -/
def Setup (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M N : Set V) : Prop :=
  Berge Gx ∧
  (¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
    IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J')) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gx.induce K'),
    IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ) ∧
  (¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V) (φ : H.lineGraph ≃g Gxᶜ.induce K'),
    IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ) ∧
  8 ≤ Nat.card V ∧
  MaximalStriation Gx S T ∧
  M ∪ N = (striationVertices S T)ᶜ ∧
  Disjoint M N ∧
  (∀ v ∈ M, LocalForStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T)) ∧
  (∀ v ∈ N, ResolvesStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T))

/-- PAPER: *"From (1) we may assume that `N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`, and by taking
complements, that `M` is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`."* -/
def Balanced (Gx : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M N : Set V) : Prop :=
  (∀ f ∈ N, ∀ u ∈ (⋃ i : Fin m, stripVertices (S i)), Gx.Adj f u) ∧
  (∀ f ∈ M, ∀ u ∈ (⋃ j : Fin n, stripVertices (T j)), ¬ Gx.Adj f u)

/-! ### The complement symmetry -/

/-- **The complement of the whole configuration.**

PAPER (9.4, printed p. 51, the definition of *resolves*): *"We say `X` resolves `L` if
`V(L) \ X` is local with respect to the striation in `Ḡ` obtained from `L` by exchanging the
strips and antistrips."*  Hence exchanging `S` with `T` and passing to `Ḡ` turns 9.4's set `N`
into the complement configuration's `M` and vice versa: this is what every *"by taking
complements"* of the printed proof of 9.6 means. -/
theorem setup_compl {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (h : Setup Gx S T M N) :
    Setup Gxᶜ T S N M := by
  obtain ⟨hB, henl, hov, hovc, hcard, hmax, hpart, hdisj, hMloc, hNres⟩ := h
  have hcc : Gxᶜᶜ = Gx := compl_compl Gx
  have hswap : striationVertices T S = striationVertices S T :=
    StriationCompl.striationVertices_swap S T
  -- `v ∈ M ∪ N` lies off `V(L)`.
  have hoff : ∀ v : V, v ∈ M ∪ N → v ∉ striationVertices S T := by
    intro v hv
    have : v ∈ (striationVertices S T)ᶜ := hpart ▸ hv
    exact this
  refine ⟨HoleBasics.berge_compl.mpr hB, ?_, hovc, ?_, hcard,
    StriationCompl.maximalStriation_compl hmax, ?_, hdisj.symm, ?_, ?_⟩
  · -- the `K₄`-enlargement hypothesis is a disjunction over the two orientations
    rintro ⟨k, J', hJ, hA⟩
    refine henl ⟨k, J', hJ, ?_⟩
    rcases hA with h | h
    · exact Or.inr h
    · exact Or.inl (hcc ▸ h)
  · rw [hcc]; exact hov
  · rw [hswap, ← hpart, Set.union_comm]
  · -- PAPER: *"`X` resolves `L` if `V(L) \ X` is local … in `Ḡ`"* — 9.4's `N` is the
    -- complement configuration's `M`.
    intro v hv
    have hvL : v ∉ striationVertices S T := hoff v (Set.mem_union_right _ hv)
    have hsub : Gx.neighborSet v ∩ striationVertices S T ⊆ striationVertices S T :=
      Set.inter_subset_right
    have hloc := (StriationCompl.resolves_iff_local_compl hmax.1 hsub).mp (hNres v hv)
    rw [hswap, StriationCompl.compl_neighborSet_inter hvL]
    exact hloc
  · intro v hv
    have hvL : v ∉ striationVertices S T := hoff v (Set.mem_union_left _ hv)
    have hsub : Gx.neighborSet v ∩ striationVertices S T ⊆ striationVertices S T :=
      Set.inter_subset_right
    have hres := (StriationCompl.local_iff_resolves_compl hmax.1 hsub).mp (hMloc v hv)
    rw [hswap, StriationCompl.compl_neighborSet_inter hvL]
    exact hres

/-- The complement transport of `Balanced`: *"`N` is complete to the strips"* in `G` is
*"`M` is anticomplete to the antistrips"* in `Ḡ` after the exchange, and conversely. -/
theorem balanced_compl {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (hs : Setup Gx S T M N) (h : Balanced Gx S T M N) :
    Balanced Gxᶜ T S N M := by
  obtain ⟨-, -, -, -, -, -, hpart, -, -, -⟩ := hs
  have hoff : ∀ v : V, v ∈ M ∪ N → v ∉ striationVertices S T := by
    intro v hv
    have : v ∈ (striationVertices S T)ᶜ := hpart ▸ hv
    exact this
  constructor
  · -- *"`M` is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`"* is completeness in `Ḡ`
    intro f hf u hu
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hu
    refine (SimpleGraph.compl_adj Gx f u).mpr ⟨?_, h.2 f hf u hu⟩
    rintro rfl
    exact hoff f (Set.mem_union_left _ hf) (StriationCompl.stripVertices_T_subset S T j hj)
  · -- *"`N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`"* is anticompleteness in `Ḡ`
    intro f hf u hu hadj
    exact ((SimpleGraph.compl_adj Gx f u).mp hadj).2 (h.1 f hf u hu)

/-! ### Claim (1) -/

/-- **PAPER (9.6, printed p. 54), claim (1).**

*"(1) If there exists `f ∈ N` with a nonneighbour in `V(S₁) ∪ ⋯ ∪ V(S_m)` then the theorem
holds.*

*For let `f` have a nonneighbour in `S₁` say.  Let `N₁` be the anticomponent of `N` containing
`f`, and let `X` be the set of all `N₁`-complete vertices in `V(G)`.  From 9.5 applied in the
complement, it follows that `X` resolves `L`.  Since `f` has a nonneighbour in `V(S₁)`, there is
a vertex `u` of `S₁` not in `X`.  Let `U` be the component of `V(G) \ (X ∪ N)` containing `u`.
We claim that `U` is disjoint from `V(L) \ V(S₁)`, and no vertex in `V(S₂) ∪ ⋯ ∪ V(S_m)` has a
neighbour in `U`.  …  This proves that `U` is disjoint from `V(L) \ V(S₁)`.  Let `X'` be the set
of vertices in `X` with neighbours in `U`, and let `V' = V(G) \ (U ∪ N₁ ∪ X')`.  Then `V'` is
nonempty because `V(S₂) ⊆ V'`; and so `U ∪ V', N₁ ∪ X'` is a skew partition of `G`.  Since there
is a vertex of `S₂` in `X` (because `X` resolves `L`), and this vertex is in `V'`, we deduce that
the skew partition is loose, and hence by 4.2 `G` admits a balanced skew partition.  This proves
(1)."* -/
theorem claim1 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (hs : Setup Gx S T M N)
    (hf : ∃ f ∈ N, ∃ u ∈ (⋃ i : Fin m, stripVertices (S i)), ¬ Gx.Adj f u) :
    Thm96Assembly.Concl Gx := by
  classical
  obtain ⟨f, hfN, u, huSs, hfu⟩ := hf
  obtain ⟨i, huS⟩ := Set.mem_iUnion.mp huSs
  have hsCompl := setup_compl hs
  obtain ⟨hG, hnoenl, hnoover, hnooverc, -, hmax, hpart, -, hMloc, -⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  obtain ⟨N₁, hN₁, hfN₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gxᶜ N hfN
  have hN₁sub : N₁ ⊆ (striationVertices S T)ᶜ := by
    intro x hx
    exact hpart ▸ Set.mem_union_right M (hN₁.1 hx)
  obtain ⟨hGc, hnoenlc, hnooverc', hnoovercc, -, hmaxc, -, -, hNlocal, -⟩ :=
    hsCompl
  have hres : ResolvesStriation Gx S T (Thm96Claim1Steps.completeSet Gx N₁) :=
    Thm96Claim1Steps.completeSet_resolves Gx S T hL hGc hnoenlc hnooverc'
      hnoovercc hmaxc N N₁ hN₁ hN₁sub (fun x hx => hNlocal x (hN₁.1 hx))
  have huL : u ∈ striationVertices S T :=
    Or.inl (Set.mem_iUnion.mpr ⟨i, huS⟩)
  have huNotX : u ∉ Thm96Claim1Steps.completeSet Gx N₁ := by
    intro huX
    exact hfu (huX f hfN₁).symm
  have huNotN : u ∉ N := fun huN => (hpart ▸ Set.mem_union_right M huN) huL
  have huW : u ∈ (Thm96Claim1Steps.completeSet Gx N₁ ∪ N)ᶜ :=
    fun h => h.elim huNotX huNotN
  obtain ⟨U, hU, huU⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gx
    (Thm96Claim1Steps.completeSet Gx N₁ ∪ N)ᶜ huW
  have hattLocal : ∀ F : Set V, IsComponent Gx M F →
      LocalForStriation Gx S T (attachments Gx F (striationVertices S T)) := by
    intro F hF
    exact _root_.Workspace.Statements.S09.SPGT.thm_9_5 Gx hG hnoenl hnoover
      hnooverc m n S T hmax F
      (fun x hx => hpart ▸ Set.mem_union_left N (hF.1 hx)) hF.2.1
      (fun x hx => hMloc x (hF.1 hx))
  obtain ⟨hconf, hanti⟩ := Thm96Claim1Steps.component_confined_to_strip
    Gx S T M N (Thm96Claim1Steps.completeSet Gx N₁) hL hpart hres
      hattLocal i u huS huW U hU huU
  have hNsub : N ⊆ (striationVertices S T)ᶜ := by
    intro x hx
    exact hpart ▸ Set.mem_union_right M hx
  have hloose := Thm96Claim1Steps.loose_partition_from_confined
    Gx S T N N₁ hL hNsub hN₁ f hfN₁ hres i u huS huNotX U hU huU hconf hanti
  have hbsp := _root_.Workspace.Statements.S04.SPGT.thm_4_2 Gx hG hloose
  exact Or.inr (Or.inl hbsp)

/-! ### Claim (2) -/

/-- **PAPER (9.6, printed p. 54), claim (2).**

*"(2) If `M, N` are both nonempty then the theorem holds.*

*For let `M₁` be a component of `M`, and `N₁` an anticomponent of `N`.  By taking complements we
may assume that there is a nonedge between `M₁` and `N₁`.  Since the set of attachments of `M₁`
in `V(L)` is local by 9.5, and since it has no attachments in `V(T₁) ∪ ⋯ ∪ V(T_n)`, we may assume
that all its attachments are in `V(S₁)`.  Let `V' = V(G) \ (M₁ ∪ N₁ ∪ V(S₁))`.  Since every
vertex of `S₁` is `N₁`-complete, it follows that `(M₁ ∪ V', N₁ ∪ V(S₁))` is a skew partition of
`G`, and since there are `N₁`-complete vertices with no neighbours in `M₁` (for instance, any
vertex of `V(S₂)`), the skew partition is loose, and by 4.2 `G` admits a balanced skew
partition.  This proves (2)."* -/
theorem claim2 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (hs : Setup Gx S T M N) (hb : Balanced Gx S T M N)
    (hM : M.Nonempty) (hN : N.Nonempty) :
    Thm96Assembly.Concl Gx := by
  classical
  -- PAPER: *"let `M₁` be a component of `M`, and `N₁` an anticomponent of `N`"*
  obtain ⟨u₀, hu₀⟩ := id hM
  obtain ⟨M₁, hM₁, hu₀M₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gx M hu₀
  obtain ⟨f₀, hf₀⟩ := id hN
  obtain ⟨N₁, hN₁, hf₀N₁⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gxᶜ N hf₀
  by_cases hne : ∃ u ∈ M₁, ∃ f ∈ N₁, ¬ Gx.Adj u f
  · -- the printed case: there is a nonedge between `M₁` and `N₁`
    obtain ⟨hB, henl, hov, hovc, -, hmax, hpart, hdisj, hMloc, hNres⟩ := hs
    exact Thm96Claim2.claim2_core hB henl hov hovc hmax hpart hdisj hMloc hNres
      hb.1 hb.2 hM₁ hN₁ hne
  · -- PAPER: *"By taking complements we may assume that there is a nonedge between `M₁` and
    -- `N₁`."*  If `M₁` is complete to `N₁` in `G`, then in `Ḡ` — where the strips and the
    -- antistrips, hence `M` and `N`, are exchanged — `N₁` is a component of the `M`-side and
    -- `M₁` an anticomponent of the `N`-side, and every `N₁`-`M₁` pair is a nonedge.
    push_neg at hne
    refine Thm96Assembly.concl_compl ?_
    have hb' : Balanced Gxᶜ T S N M := balanced_compl hs hb
    obtain ⟨hB, henl, hov, hovc, -, hmax, hpart, hdisj, hMloc, hNres⟩ := setup_compl hs
    have hM₁' : IsAnticomponent Gxᶜ M M₁ := by
      show IsComponent Gxᶜᶜ M M₁
      rw [compl_compl]; exact hM₁
    have hnonedge : ∃ u ∈ N₁, ∃ f ∈ M₁, ¬ Gxᶜ.Adj u f := by
      refine ⟨f₀, hf₀N₁, u₀, hu₀M₁, ?_⟩
      intro hadj
      exact ((SimpleGraph.compl_adj Gx f₀ u₀).mp hadj).2 (hne u₀ hu₀M₁ f₀ hf₀N₁).symm
    exact Thm96Claim2.claim2_core hB henl hov hovc hmax hpart hdisj hMloc hNres
      hb'.1 hb'.2 hN₁ hM₁' hnonedge

/-! ### Claim (3) -/

/-- **PAPER (9.6, printed p. 55), claim (3).**

*"(3) If `M, N` are both empty then the theorem holds.*

*For then by 9.1, we may assume that for `1 ≤ j ≤ n` all `Qⱼ`-antirungs have length 1.  If
`|V(S₁)| > 2`, then `(V(S₁), V(L) \ V(S₁))` is a proper 2-join of `G`; for every vertex in
`V(T₁) ∪ ⋯ ∪ V(T_n)` is either complete to `A₁` and anticomplete to `B₁ ∪ C₁`, or complete to
`B₁` and anticomplete to `A₁ ∪ C₁` (since all the antirungs have length 1).  So we may assume
that each `Sᵢ` has only two vertices.  In particular, every `Sᵢ`-rung has length 1, so by taking
complements the same argument shows that we may assume every `V(Tⱼ)` has only two vertices.  But
then `G` is a double split graph and the theorem holds.  This proves (3)."* -/
theorem claim3 {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (hs : Setup Gx S T M N) (hb : Balanced Gx S T M N)
    (hM : M = ∅) (hN : N = ∅) :
    Thm96Assembly.Concl Gx := by
  classical
  obtain ⟨hG, -, -, -, -, hmax, hpart, -, -, -⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  have hcover : striationVertices S T = (Set.univ : Set V) := by
    apply Set.eq_univ_of_forall
    intro v
    by_contra hv
    have hvc : v ∈ (striationVertices S T)ᶜ := hv
    rw [← hpart, hM, hN] at hvc
    rcases hvc with hvc | hvc <;> exact hvc
  have hpartEmpty : (∅ : Set V) = (striationVertices S T)ᶜ := by
    rw [hcover, Set.compl_univ]
  have hassignEmpty : ∀ F : Set V, IsComponent Gx ∅ F →
      ∃ k : Fin m, attachments Gx F (striationVertices S T) ⊆ stripVertices (S k) := by
    intro F hF
    let k : Fin m := ⟨0, by have := hL.2.2.2.2.2.2.2.1; omega⟩
    refine ⟨k, ?_⟩
    rintro v ⟨hvL, f, hfF, -⟩
    exact (hF.1 hfF).elim
  have hneEmpty : ∀ F : Set V, IsComponent Gx ∅ F → F.Nonempty →
      (attachments Gx F (striationVertices S T)).Nonempty := by
    intro F hF hFne
    exact False.elim ((hF.1 hFne.choose_spec).elim)
  have hLc : IsStriation Gxᶜ T S := StriationCompl.isStriation_compl hL
  have hpartEmptyC : (∅ : Set V) = (striationVertices T S)ᶜ := by
    rw [StriationCompl.striationVertices_swap, hcover, Set.compl_univ]
  have hassignEmptyC : ∀ F : Set V, IsComponent Gxᶜ ∅ F →
      ∃ k : Fin n, attachments Gxᶜ F (striationVertices T S) ⊆ stripVertices (T k) := by
    intro F hF
    let k : Fin n := ⟨0, by have := hL.2.2.2.2.2.2.2.2.1; omega⟩
    refine ⟨k, ?_⟩
    rintro v ⟨hvL, f, hfF, -⟩
    exact (hF.1 hfF).elim
  have hneEmptyC : ∀ F : Set V, IsComponent Gxᶜ ∅ F → F.Nonempty →
      (attachments Gxᶜ F (striationVertices T S)).Nonempty := by
    intro F hF hFne
    exact False.elim ((hF.1 hFne.choose_spec).elim)
  have properG (hmid : ∀ j : Fin n,
      Thm96StriationTools.middlePart (T j) = ∅) (i : Fin m)
      (hi : 2 < (stripVertices (S i)).ncard) : Thm96Assembly.Concl Gx := by
    have h2 := Thm96TwoJoin.proper2Join_of_side Gx S T hL ∅ hpartEmpty
      hassignEmpty hneEmpty hmid i (Or.inl hi)
    exact Or.inr (Or.inr (Or.inl (Or.inl h2)))
  have properGc (hmid : ∀ i : Fin m,
      Thm96StriationTools.middlePart (S i) = ∅) (j : Fin n)
      (hj : 2 < (stripVertices (T j)).ncard) : Thm96Assembly.Concl Gx := by
    have h2 := Thm96TwoJoin.proper2Join_of_side Gxᶜ T S hLc ∅ hpartEmptyC
      hassignEmptyC hneEmptyC hmid j (Or.inl hj)
    exact Or.inr (Or.inr (Or.inl (Or.inr h2)))
  by_cases hTedge : ∀ (j : Fin n) (Q : List V),
      IsSRung Gxᶜ (T j) Q → pathLength Q = 1
  · have hmidT : ∀ j : Fin n, Thm96StriationTools.middlePart (T j) = ∅ :=
      fun j => Thm96StriationTools.middle_eq_empty_of_rungs_one (hL.2.1 j) (hTedge j)
    by_cases hS2 : ∀ i : Fin m, (stripVertices (S i)).ncard = 2
    · have hSedge : ∀ (i : Fin m) (P : List V),
          IsSRung Gx (S i) P → pathLength P = 1 := by
        intro i P hP
        exact Thm96StriationTools.rung_one_of_strip_ncard_two
          (hL.1 i) (hS2 i) (hL.2.2.2.2.2.1 i) hP
      have hmidS : ∀ i : Fin m, Thm96StriationTools.middlePart (S i) = ∅ :=
        fun i => Thm96StriationTools.middle_eq_empty_of_rungs_one (hL.1 i) (hSedge i)
      by_cases hT2 : ∀ j : Fin n, (stripVertices (T j)).ncard = 2
      · exact Or.inl
          (DegenerateStriationIsDoubleSplit.isDoubleSplitGraph_of_striation_two_vertices
            hL hcover hS2 hT2)
      · push_neg at hT2
        obtain ⟨j, hj⟩ := hT2
        have htwo := Thm96StriationTools.two_le_strip_ncard (hL.2.1 j)
        exact properGc hmidS j (by omega)
    · push_neg at hS2
      obtain ⟨i, hi⟩ := hS2
      have htwo := Thm96StriationTools.two_le_strip_ncard (hL.1 i)
      exact properG hmidT i (by omega)
  · have hlong : ∃ j : Fin n, ∃ Q : List V,
        IsSRung Gxᶜ (T j) Q ∧ pathLength Q ≠ 1 := by
      push_neg at hTedge
      obtain ⟨j, Q, hQ, hQlong⟩ := hTedge
      exact ⟨j, Q, hQ, hQlong⟩
    obtain ⟨j₀, Q, hQ, hQlong⟩ := hlong
    have hSedge := Thm96StriationTools.all_rungs_one_of_long_antirung hG hL hQ hQlong
    have hmidS : ∀ i : Fin m, Thm96StriationTools.middlePart (S i) = ∅ :=
      fun i => Thm96StriationTools.middle_eq_empty_of_rungs_one (hL.1 i) (hSedge i)
    have hT2false : ¬ ∀ j : Fin n, (stripVertices (T j)).ncard = 2 := by
      intro hT2
      exact hQlong (Thm96StriationTools.rung_one_of_strip_ncard_two
        (hL.2.1 j₀) (hT2 j₀) (hL.2.2.2.2.2.2.1 j₀) hQ)
    push_neg at hT2false
    obtain ⟨j, hj⟩ := hT2false
    have htwo := Thm96StriationTools.two_le_strip_ncard (hL.2.1 j)
    exact properGc hmidS j (by omega)

/-! ### The closing paragraph -/

/-- **PAPER (9.6, printed p. 55), the closing paragraph.**

*"From (2) and (3), and taking complements if necessary, we may assume that `N` is empty and `M`
is nonempty.  For `1 ≤ i ≤ m` let `Mᵢ` be the union of the components of `M` that have an
attachment in `V(Sᵢ)`, and let `M₀` be the union of the components of `M` that have no
attachments in `V(L)`.  Then `M₀, M₁, …, M_n` are pairwise disjoint and have union `M`.  If `M₀`
is nonempty then `G` is not connected, and since `|V(G)| ≥ 8` it therefore admits a balanced
skew partition, so we may assume that `M₀` is empty.  Since `M` is nonempty we may assume that
`M₁` is nonempty.  We recall that `T₁ = (X₁, Z₁, Y₁)`; suppose that `z ∈ Z₁`.  Then `z` is
complete to `V(S₁)` by 9.1, and hence if we define `V' = V(G) \ (M₁ ∪ V(S₁) ∪ {z})`, then
`(M₁ ∪ V', V(S₁) ∪ {z})` is a skew partition of `G`, and by 4.1 `G` admits a balanced skew
partition.  So we may assume that `Z₁` is empty, and similarly every `Zⱼ` is empty.  Then
`(M₁ ∪ V(S₁), V(G) \ (M₁ ∪ V(S₁)))` is a proper 2-join of `G`.  This proves 9.6."* -/
theorem closing {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V} (hs : Setup Gx S T M N) (hb : Balanced Gx S T M N)
    (hN : N = ∅) (hM : M.Nonempty) :
    Thm96Assembly.Concl Gx := by
  classical
  obtain ⟨hG, hnoenl, hnoover, hnooverc, hcard, hmax, hpart, -, hMloc, -⟩ := hs
  have hL : IsStriation Gx S T := hmax.1
  have hpartM : M = (striationVertices S T)ᶜ := by
    simpa only [hN, Set.union_empty] using hpart
  have hassign : ∀ F : Set V, IsComponent Gx M F →
      ∃ i : Fin m, attachments Gx F (striationVertices S T) ⊆ stripVertices (S i) := by
    intro F hF
    exact Thm96Claim2.attachments_in_one_strip hG hnoenl hnoover hnooverc hmax
      hpart hMloc hb.2 hF
  by_cases hunattached : ∃ F : Set V, IsComponent Gx M F ∧ F.Nonempty ∧
      attachments Gx F (striationVertices S T) = ∅
  · obtain ⟨F, hF, hFne, hatt⟩ := hunattached
    have hdisc := Thm96ClosingSteps.not_connected_of_unattached_component
      Gx S T M F hL hpartM hF hFne hatt
    have hedge : ∃ u v : V, Gx.Adj u v := by
      let i : Fin m := ⟨0, by have := hL.2.2.2.2.2.2.2.1; omega⟩
      obtain ⟨P, hP⟩ := Thm96StriationTools.exists_rung (hL.1 i)
      obtain ⟨a, b, hPab, ha, hb', htail, hdrop, hint⟩ := hP
      have hodd := hL.2.2.2.2.2.1 i P
        ⟨a, b, hPab, ha, hb', htail, hdrop, hint⟩
      obtain ⟨q, hq⟩ := hodd
      have hlen := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hPab.1
      have h1 : 1 < P.length := by omega
      exact ⟨P[0]'(by omega), P[1]'h1,
        (hPab.1.2.2 0 1 (by omega) h1).mpr (Or.inl rfl)⟩
    have hbsp :=
      DisconnectedLargeGraphHasBalancedSkewPartition.admitsBalancedSkewPartition_of_not_connected
        Gx hG hcard hedge hdisc
    exact Or.inr (Or.inl hbsp)
  · have hne : ∀ F : Set V, IsComponent Gx M F → F.Nonempty →
        (attachments Gx F (striationVertices S T)).Nonempty := by
      intro F hF hFne
      by_contra hnot
      exact hunattached ⟨F, hF, hFne, Set.not_nonempty_iff_eq_empty.mp hnot⟩
    obtain ⟨u, huM⟩ := hM
    obtain ⟨F, hF, huF⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gx M huM
    obtain ⟨i, hFatt⟩ := hassign F hF
    have hFne : F.Nonempty := ⟨u, huF⟩
    by_cases hmid : ∀ j : Fin n, Thm96StriationTools.middlePart (T j) = ∅
    · have huSide : u ∈ Thm96TwoJoin.sideSet Gx S T M i :=
        Or.inr ⟨F, hF, huF, hne F hF hFne, hFatt⟩
      have huNotStrip : u ∉ stripVertices (S i) := by
        intro huS
        exact (hpartM ▸ huM)
          (Or.inl (Set.mem_iUnion.mpr ⟨i, huS⟩))
      have h2 := Thm96TwoJoin.proper2Join_of_side Gx S T hL M hpartM
        hassign hne hmid i (Or.inr ⟨u, huSide, huNotStrip⟩)
      exact Or.inr (Or.inr (Or.inl (Or.inl h2)))
    · push_neg at hmid
      obtain ⟨j, hj⟩ := hmid
      obtain ⟨z, hz⟩ := hj
      have hbsp := Thm96ClosingSteps.balancedSkewPartition_of_middle_vertex
        Gx hG S T M hL hpartM hb.2 F hF hFne i hFatt j z hz
      exact Or.inr (Or.inl hbsp)

end Workspace.ProofLemmas.Thm96Body
