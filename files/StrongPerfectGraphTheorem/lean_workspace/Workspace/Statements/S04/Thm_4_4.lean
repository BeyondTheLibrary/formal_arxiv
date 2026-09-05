import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.ProofLemmas.Thm44Spread
import Workspace.ProofLemmas.Thm44Reorder
import Workspace.ProofLemmas.Thm44Step1

/-!
# Section 4 — Skew partitions

The six numbered statements 4.1 – 4.6 of Chudnovsky–Robertson–Seymour–Thomas,
*The Strong Perfect Graph Theorem* (published / *Annals* version; printed pages 14–18).
Every definition used here is imported, never restated:

* `Workspace.Types.Core` — `Berge`, `IsPathFrom`, `IsAntipathFrom`, `pathLength`,
  `SPGT.interior`, `IsComponent`, `IsAnticomponent`, `VertexComplete`,
  `VertexAnticomplete`, `Complete`, `Anticomplete`, `SPGT.Balanced`
* `Workspace.Types.Decompositions` — `IsSkewPartition`, `IsBalancedSkewPartition`,
  `AdmitsBalancedSkewPartition`
* `Workspace.Types.SkewTools` — `IsLooseSkewPartition`, `AdmitsLooseSkewPartition`,
  `IsPathPair`, `IsAntipathPair`, `IsKernel`

## Encoding conventions specific to this section

* A path / antipath is the list `p` of its vertices in order, with named ends via
  `IsPathFrom` / `IsAntipathFrom`; "with interior in `S`" is
  `∀ x ∈ SPGT.interior p, x ∈ S`; "odd" / "even" refer to `SPGT.pathLength p`, the number of
  edges.  (`SPGT.interior` and `SPGT.Balanced` are always written with their `SPGT.`
  prefix, since the bare names are captured by Mathlib's topological `interior` and by
  Mathlib's `Balanced` set-in-a-module predicate.)
* The paper's *"let `A₁,…,A_m` be the components of `A`, and `B₁,…,B_n` the anticomponents of
  `B`"* fixes an enumeration only in order to index the alternatives of 4.4 by `(i,j)`; since
  the published 4.4 quantifies over *all* `i,j`, the enumeration is rendered by universally
  quantifying over all components `A'` of `A` and all anticomponents `B'` of `B`.  (The
  published paper itself made this change: it indexes path/antipath pairs by the *sets*
  `(A_i,B_j)` rather than by the index pair `(i,j)`.)
* *"has only one vertex"* is `∃ a, S = {a}`.

## Published vs. arXiv v1

**4.6 is strictly stronger in the published version and it is the published form that is
transcribed here.**  The arXiv draft's hypotheses read *"joined by an even path with interior
in `A₁`"* and *"joined by an even antipath with interior in `W`"*; the published 4.6 reads
*"with interior in `A`"* and *"with interior in `B`"*.  Since `A₁ ⊆ A` and `W ⊆ B`, the
published hypotheses are weaker, hence the published theorem is stronger.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S04

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT

namespace SPGT

namespace Helpers44

open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A path pair of `(Ḡ; B, A)` is an antipath pair of `(G; A, B)`.  (The two ends of the odd
path are distinct, so `¬ Ḡ`-adjacent is the same as `G`-adjacent for them.) -/
theorem antipathPair_of_pathPair_compl {G : SimpleGraph V} {A B A' B' : Set V}
    (h : IsPathPair Gᶜ B A B' A') : IsAntipathPair G A B A' B' := by
  obtain ⟨hskew, hB', hA', p, u, v, hu, hv, hnadj, hp, hint, hodd⟩ := h
  refine ⟨ClassLemmas.isSkewPartition_compl.mp hskew, ?_, hB', p, u, v, hu, hv, ?_, hp,
    hint, hodd⟩
  · rwa [IsAnticomponent, compl_compl] at hA'
  · have hne : u ≠ v :=
      PathBasics.isPathFrom_ends_ne hp (by obtain ⟨k, hk⟩ := hodd; omega)
    by_contra hg
    exact hnadj ((SimpleGraph.compl_adj G u v).mpr ⟨hne, hg⟩)

end Helpers44

section Main44

open Workspace.ProofLemmas
open Helpers44

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **4.4** (printed p. 16)

PAPER: *"Let `(A,B)` be a skew partition of a Berge graph `G`, and let `A₁,…,A_m` be the
components of `A`, and `B₁,…,B_n` the anticomponents of `B`.  Then either:*

*• `(A,B)` is loose or balanced, or*

*• `(A_i,B_j)` is a path pair for all `i,j` with `1 ≤ i ≤ m` and `1 ≤ j ≤ n`, or*

*• `(A_i,B_j)` is an antipath pair for all `i,j` with `1 ≤ i ≤ m` and `1 ≤ j ≤ n`."*

Transcription notes.

* `A₁,…,A_m` is just an enumeration of *all* components of `A`, and `B₁,…,B_n` of all
  anticomponents of `B`; since the last two alternatives range over all `i` and all `j`, they
  are rendered by universal quantification over all components `A'` of `A` and all
  anticomponents `B'` of `B`.
* *"`(A,B)` is loose or balanced"*: `(A,B)` is a skew partition by hypothesis, so *balanced*
  here is the balanced-skew-partition notion (equivalently, under that hypothesis, the pair
  `(A,B)` being balanced in the sense of `SPGT.Balanced`).
* *Path pair* and *antipath pair* are the printed-p.-16 notions
  (`SkewTools.IsPathPair`, `SkewTools.IsAntipathPair`), which carry along the standing context
  "`(A,B)` is a skew partition, `A'` a component of `A`, `B'` an anticomponent of `B`". -/
theorem thm_4_4 (G : SimpleGraph V) (hG : Berge G) (A B : Set V)
    (hAB : IsSkewPartition G A B) :
    (IsLooseSkewPartition G A B ∨ IsBalancedSkewPartition G A B) ∨
    (∀ A' B' : Set V, IsComponent G A A' → IsAnticomponent G B B' →
      IsPathPair G A B A' B') ∨
    (∀ A' B' : Set V, IsComponent G A A' → IsAnticomponent G B B' →
      IsAntipathPair G A B A' B') := by
  -- *"We may assume `(A,B)` is not loose and not balanced."*
  by_cases hloose : IsLooseSkewPartition G A B
  · exact Or.inl (Or.inl hloose)
  by_cases hbal : Workspace.Types.Core.SPGT.Balanced G A B
  · exact Or.inl (Or.inr ⟨hAB, hbal⟩)
  have hGc : Berge Gᶜ := HoleBasics.berge_compl.mpr hG
  have hABc : IsSkewPartition Gᶜ B A := ClassLemmas.isSkewPartition_compl.mpr hAB
  have hloosec : ¬ IsLooseSkewPartition Gᶜ B A := fun h =>
    hloose (LooseSkewPartition.isLooseSkewPartition_of_compl h)
  ------------------------------------------------------------------
  -- (1) *"If for some `i, j` there is an odd path of length `≥ 5` with ends in `B_j` and
  --      interior in `A_i`, then the theorem holds."*
  ------------------------------------------------------------------
  by_cases hlong : ∃ (A' B' : Set V) (u v : V) (P : List V),
      IsComponent G A A' ∧ IsAnticomponent G B B' ∧ u ∈ B' ∧ v ∈ B' ∧
      IsPathFrom G P u v ∧ (∀ x ∈ SPGT.interior P, x ∈ A') ∧
      Odd (pathLength P) ∧ 5 ≤ pathLength P
  · obtain ⟨A₁, B₁, u, v, P, hA₁, hB₁, hu, hv, hP, hPint, hPodd, hPlen⟩ := hlong
    exact Or.inr (Or.inl
      (Thm44Step1.step1 hG hAB hloose hA₁ hB₁ hu hv hP hPint hPodd hPlen))
  -- the same statement in the complement: *"and similarly every odd antipath of length `> 1`
  -- with ends in `A_i` and interior in `B_j` has length `3`"*
  by_cases hlongc : ∃ (X Y : Set V) (u v : V) (P : List V),
      IsComponent Gᶜ B X ∧ IsAnticomponent Gᶜ A Y ∧ u ∈ Y ∧ v ∈ Y ∧
      IsPathFrom Gᶜ P u v ∧ (∀ x ∈ SPGT.interior P, x ∈ X) ∧
      Odd (pathLength P) ∧ 5 ≤ pathLength P
  · obtain ⟨X, Y, u, v, P, hX, hY, hu, hv, hP, hPint, hPodd, hPlen⟩ := hlongc
    refine Or.inr (Or.inr (fun A' B' hA' hB' => antipathPair_of_pathPair_compl ?_))
    exact Thm44Step1.step1 hGc hABc hloosec hX hY hu hv hP hPint hPodd hPlen B' A'
      hB' (by rw [IsAnticomponent, compl_compl]; exact hA')
  ------------------------------------------------------------------
  -- *"From (1) we may assume that for all `i,j`, every odd path of length `> 1` with ends in
  --  `B_j` and interior in `A_i` has length `3`; and similarly … for antipaths."*
  ------------------------------------------------------------------
  have hshort : ∀ (A' B' : Set V) (u v : V) (P : List V),
      IsComponent G A A' → IsAnticomponent G B B' → u ∈ B' → v ∈ B' →
      IsPathFrom G P u v → (∀ x ∈ SPGT.interior P, x ∈ A') → Odd (pathLength P) →
      pathLength P ≤ 4 := by
    intro A' B' u v P h1 h2 h3 h4 h5 h6 h7
    by_contra hc
    exact hlong ⟨A', B', u, v, P, h1, h2, h3, h4, h5, h6, h7, by omega⟩
  have hshortc : ∀ (X Y : Set V) (u v : V) (P : List V),
      IsComponent Gᶜ B X → IsAnticomponent Gᶜ A Y → u ∈ Y → v ∈ Y →
      IsPathFrom Gᶜ P u v → (∀ x ∈ SPGT.interior P, x ∈ X) → Odd (pathLength P) →
      pathLength P ≤ 4 := by
    intro X Y u v P h1 h2 h3 h4 h5 h6 h7
    by_contra hc
    exact hlongc ⟨X, Y, u, v, P, h1, h2, h3, h4, h5, h6, h7, by omega⟩
  ------------------------------------------------------------------
  -- *"We may assume that `(A₁,B₁)` is a path pair, and so there exist `b₁,b₁' ∈ B₁` and
  --  `a₁,a₁' ∈ A₁` such that `b₁-a₁-a₁'-b₁'` is a path `P₁` say."*
  --
  -- `(A,B)` is not balanced, so one of the two clauses of *balanced* fails.  If the path
  -- clause fails we already have the seed; if the antipath clause fails, the printed
  -- parenthesis *"a path of length 3 can be reordered to be an antipath of length 3"*,
  -- read in the complement, converts it into one.
  ------------------------------------------------------------------
  have hseed : ∃ (B₀ : Set V) (s t : V) (Q : List V), IsAnticomponent G B B₀ ∧
      s ∈ B₀ ∧ t ∈ B₀ ∧ ¬ G.Adj s t ∧ IsPathFrom G Q s t ∧
      (∀ x ∈ SPGT.interior Q, x ∈ A) ∧ Odd (pathLength Q) := by
    rcases not_and_or.mp hbal with hb | hb
    · -- the path clause of *balanced* fails
      push_neg at hb
      obtain ⟨u, v, Q, hu, hv, hnadj, hQ, hQint, hQodd⟩ := hb
      have hne : u ≠ v :=
        PathBasics.isPathFrom_ends_ne hQ (by obtain ⟨k, hk⟩ := hQodd; omega)
      obtain ⟨B₀, hB₀, huB₀⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hu
      obtain ⟨B₀', hB₀', hvB₀'⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hv
      have heq : B₀ = B₀' :=
        LooseSkewPartition.same_anticomponent hB₀ hB₀' huB₀ hvB₀' hne hnadj
      exact ⟨B₀, u, v, Q, hB₀, huB₀, heq ▸ hvB₀', hnadj, hQ, hQint, hQodd⟩
    · -- the antipath clause of *balanced* fails
      push_neg at hb
      obtain ⟨u, v, q, hu, hv, hadj, hq, hqint, hqodd⟩ := hb
      -- the component of `A` containing the two (adjacent) ends
      obtain ⟨A₀, hA₀, huA₀⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hu
      obtain ⟨A₀', hA₀', hvA₀'⟩ := ComponentsOfSetBasics.exists_isComponent_mem G A hv
      have heq : A₀ = A₀' := by
        by_contra hc
        exact ComponentsOfSetBasics.anticomplete_of_isComponent G hA₀ hA₀' hc u huA₀ v
          hvA₀' hadj
      have hvA₀ : v ∈ A₀ := heq ▸ hvA₀'
      have hA₀c : IsAnticomponent Gᶜ A A₀ := by rw [IsAnticomponent, compl_compl]; exact hA₀
      -- some anticomponent of `B`
      obtain ⟨w, hw⟩ : B.Nonempty :=
        LooseSkewPartition.nonempty_of_not_anticonnected hAB.2.2.2
      obtain ⟨B₀, hB₀, -⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ B hw
      -- push the antipath into `B₀`
      obtain ⟨R, hR, hRint, hRodd⟩ :=
        Thm44Spread.spread (G := Gᶜ) hGc hABc hloosec hu hv hq hqint hqodd hB₀
      have hR3 : pathLength R = 3 := by
        have h4 := hshortc B₀ A₀ u v R hB₀ hA₀c huA₀ hvA₀ hR hRint hRodd
        have h1 : pathLength R ≠ 1 := fun h =>
          ((SimpleGraph.compl_adj G u v).mp
            (PathBasics.isPathFrom_ends_adj_of_length_one hR h)).2 hadj
        obtain ⟨k, hk⟩ := hRodd
        omega
      obtain ⟨x, y, hxy, hx, hy, hant⟩ :=
        Thm44Reorder.antipath_of_path_three (G := Gᶜ) hR hR3
      refine ⟨B₀, x, y, [x, v, u, y], hB₀, hRint x hx, hRint y hy,
        ((SimpleGraph.compl_adj G x y).mp hxy).2,
        PathBasics.isAntipathFrom_compl.mp hant, ?_, ⟨1, rfl⟩⟩
      intro z hz
      simp [SPGT.interior] at hz
      rcases hz with rfl | rfl
      · exact hA₀.1 hvA₀
      · exact hA₀.1 huA₀
  obtain ⟨B₀, s, t, Q₀, hB₀, hs, ht, hst, hQ₀, hQ₀int, hQ₀odd⟩ := hseed
  ------------------------------------------------------------------
  -- *"Let `2 ≤ i ≤ m`.  Since `b₁` and `b₁'` both have neighbours in `A_i`, they are joined
  --  by a path with interior in `A_i`, odd by 4.3; and so by (1) it has length 3.  Hence
  --  there exist `a_i,a_i' ∈ A_i` such that `b₁-a_i-a_i'-b₁'` is a path.  By the same argument
  --  in the complement, it follows that for all `1 ≤ i ≤ m` and `2 ≤ j ≤ n`, there exist
  --  `b_j,b_j' ∈ B_j` such that `b_j-a_i-a_i'-b_j'` is a path."*
  ------------------------------------------------------------------
  refine Or.inr (Or.inl (fun A' B' hA' hB' => ?_))
  -- into the component `A'`
  obtain ⟨R, hR, hRint, hRodd⟩ :=
    Thm44Spread.spread hG hAB hloose (hB₀.1 hs) (hB₀.1 ht) hQ₀ hQ₀int hQ₀odd hA'
  have hR3 : pathLength R = 3 := by
    have h4 := hshort A' B₀ s t R hA' hB₀ hs ht hR hRint hRodd
    have h1 : pathLength R ≠ 1 := fun h =>
      hst (PathBasics.isPathFrom_ends_adj_of_length_one hR h)
    obtain ⟨k, hk⟩ := hRodd
    omega
  obtain ⟨a, a', haa', ha, ha', hant⟩ := Thm44Reorder.antipath_of_path_three hR hR3
  have haA' : a ∈ A' := hRint a ha
  have ha'A' : a' ∈ A' := hRint a' ha'
  have hA'c : IsAnticomponent Gᶜ A A' := by rw [IsAnticomponent, compl_compl]; exact hA'
  -- into the anticomponent `B'`, in the complement
  obtain ⟨S, hS, hSint, hSodd⟩ :=
    Thm44Spread.spread (G := Gᶜ) hGc hABc hloosec (hA'.1 haA') (hA'.1 ha'A') hant
      (by
        intro z hz
        simp [SPGT.interior] at hz
        rcases hz with rfl | rfl
        · exact hB₀.1 ht
        · exact hB₀.1 hs)
      ⟨1, rfl⟩ hB'
  have hS3 : pathLength S = 3 := by
    have h4 := hshortc B' A' a a' S hB' hA'c haA' ha'A' hS hSint hSodd
    have h1 : pathLength S ≠ 1 := fun h =>
      ((SimpleGraph.compl_adj G a a').mp
        (PathBasics.isPathFrom_ends_adj_of_length_one hS h)).2 haa'
    obtain ⟨k, hk⟩ := hSodd
    omega
  obtain ⟨x, y, hxy, hx, hy, hant2⟩ :=
    Thm44Reorder.antipath_of_path_three (G := Gᶜ) hS hS3
  refine ⟨hAB, hA', hB', [x, a', a, y], x, y, hSint x hx, hSint y hy,
    ((SimpleGraph.compl_adj G x y).mp hxy).2,
    PathBasics.isAntipathFrom_compl.mp hant2, ?_, ⟨1, rfl⟩⟩
  intro z hz
  simp [SPGT.interior] at hz
  rcases hz with rfl | rfl
  · exact ha'A'
  · exact haA'

end Main44

end SPGT

end Workspace.Statements.S04
