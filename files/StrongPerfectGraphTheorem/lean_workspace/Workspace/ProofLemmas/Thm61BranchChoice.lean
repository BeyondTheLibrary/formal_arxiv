import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.Thm82BranchDelta
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.NaturalAppearanceStripSystemCore
import Workspace.ProofLemmas.Thm75BranchEnds

/-!
# 6.1: triads, and the proof-local choice of `b`, `eᵢ`, `Bᵢ`, `bᵢ`, `fᵢ`

PAPER (proof of 6.1, printed p. 30).  Immediately after claim (3) the authors fix, once and for
all, a configuration that claims (4), (5), (6) and (7) all speak about.  The two printed
paragraphs are:

> *"In the arguments to come there is a certain amount of moving from `H` to `L(H)` and back, and
> to facilitate this, for every subgraph `H'` of `H` we denote by `L(H')` the induced subgraph of
> `L(H)` formed by the edges of `H'`.  So for any track `P` of `H`, `L(P)` is a path of `L(H)`.
> We say a branch-vertex `b` of `H` is a **triad** if `b` is incident with at most one edge in
> `X`.  It follows that every triad has degree 3 in `H`, and is incident with exactly one edge in
> each of `X, X₁, X₂`."*
>
> *"There is a branch-vertex `b` of `H` incident with at least two edges not in `X`.  For
> `i = 1, 2` let `eᵢ ∈ Xᵢ` be incident with `b`, and let `e₃` be some third edge incident with
> `b`.  For `i = 1, 2, 3`, let `Bᵢ` be the branch of `H` containing `eᵢ`, and let `bᵢ` be its
> other end.  If `Q` is odd, let `fᵢ ∈ X` be incident with `bᵢ`, chosen in addition such that
> `fᵢ ∉ E(Bᵢ)` if possible (`1 ≤ i ≤ 3`).  (If `Q` is even we choose the `fᵢ`'s a little
> differently, described later.)"*

This module only *names* that configuration, so that the modules proving claims (4), (5), (6),
(7) and the module assembling them agree on it byte-for-byte.  It follows the pattern of
`Workspace.ProofLemmas.Thm61EvenClaims`, which names the three claims of the even case for the
same reason.

Encoding notes.

* `X = completeEdges G H K φ Y` and `Xᵢ = extraEdges G H K φ Y yᵢ`
  (`Workspace.ProofLemmas.Thm61Setup`); `y₁, y₂` are the ends of the antipath `Q` whose vertex
  set is `Y`.
* *"incident with at most one edge in `X`"* is `(incidentEdges H v ∩ X).Subsingleton`, matching
  the shape of `Appearances.SaturatesLineGraph`, which is
  `∀ v ∈ branchVertices H, (incidentEdges H v \ W).Subsingleton`.
* *"There is a branch-vertex `b` of `H` incident with at least two edges not in `X`"* is exactly
  the negation of `SaturatesLineGraph H X`, which is the hypothesis of 6.1; the existence
  statement `exists_branchChoice` below records this together with the rest of the choice.
* A branch `Bᵢ` is a list of vertices (a track, `Tracks.IsBranch`); *"`bᵢ` is its other end"* is
  `IsTrackFrom H Bᵢ b bᵢ`, and *"`E(Bᵢ)`"* is `trackEdges Bᵢ`.  *"`Bᵢ` has length `> 1`"* is
  `1 < trackLength Bᵢ`, and *"`E(Bᵢ) = {eᵢ}`"* is `trackLength Bᵢ = 1`.
* *"chosen in addition such that `fᵢ ∉ E(Bᵢ) if possible`"* is rendered as the implication *if
  some edge of `X` incident with `bᵢ` lies outside `E(Bᵢ)` then `fᵢ` does too*, which is what the
  printed proof of (4) uses (*"suppose not; then `f₃ ∉ E(B₃)`, and there is a second edge
  `f₃' ∈ X` incident with `b₃`"*).

**Status: definitions plus two statement-only existence lemmas and one statement-only
consequence — this module is a work item.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61BranchChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm61Setup

/-- **Triad** (printed p. 30): *"We say a branch-vertex `b` of `H` is a triad if `b` is incident
with at most one edge in `X`."* -/
def Triad {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (v : Fin n) : Prop :=
  v ∈ branchVertices H ∧ (incidentEdges H v ∩ completeEdges G H K φ Y).Subsingleton

/-- **The choice of `b`, `e₁, e₂, e₃`, `B₁, B₂, B₃`, `b₁, b₂, b₃`** (printed p. 30):

*"There is a branch-vertex `b` of `H` incident with at least two edges not in `X`.  For
`i = 1, 2` let `eᵢ ∈ Xᵢ` be incident with `b`, and let `e₃` be some third edge incident with `b`.
For `i = 1, 2, 3`, let `Bᵢ` be the branch of `H` containing `eᵢ`, and let `bᵢ` be its other
end."* -/
def BranchChoice {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n) : Prop :=
  -- *"There is a branch-vertex `b` of `H` incident with at least two edges not in `X`."*
  b ∈ branchVertices H ∧
  (∃ g₁ ∈ incidentEdges H b, ∃ g₂ ∈ incidentEdges H b, g₁ ≠ g₂ ∧
    g₁ ∉ completeEdges G H K φ Y ∧ g₂ ∉ completeEdges G H K φ Y) ∧
  -- *"For `i = 1, 2` let `eᵢ ∈ Xᵢ` be incident with `b`"*
  e₁ ∈ incidentEdges H b ∧ e₁ ∈ extraEdges G H K φ Y y₁ ∧
  e₂ ∈ incidentEdges H b ∧ e₂ ∈ extraEdges G H K φ Y y₂ ∧
  -- *"and let `e₃` be some third edge incident with `b`"*
  e₃ ∈ incidentEdges H b ∧ e₃ ≠ e₁ ∧ e₃ ≠ e₂ ∧
  -- *"let `Bᵢ` be the branch of `H` containing `eᵢ`, and let `bᵢ` be its other end"*
  IsBranch H B₁ ∧ e₁ ∈ trackEdges B₁ ∧ IsTrackFrom H B₁ b b₁ ∧
  IsBranch H B₂ ∧ e₂ ∈ trackEdges B₂ ∧ IsTrackFrom H B₂ b b₂ ∧
  IsBranch H B₃ ∧ e₃ ∈ trackEdges B₃ ∧ IsTrackFrom H B₃ b b₃

/-- One instance of the choice of the `fᵢ` (printed p. 30): *"let `fᵢ ∈ X` be incident with
`bᵢ`, chosen in addition such that `fᵢ ∉ E(Bᵢ)` if possible"*. -/
def ChosenOutside {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (B : List (Fin n)) (v : Fin n) (f : Sym2 (Fin n)) : Prop :=
  f ∈ completeEdges G H K φ Y ∧ f ∈ incidentEdges H v ∧
    ((∃ g ∈ completeEdges G H K φ Y, g ∈ incidentEdges H v ∧ g ∉ trackEdges B) →
      f ∉ trackEdges B)

/-- **The choice of `f₁, f₂, f₃`** (printed p. 30): *"If `Q` is odd, let `fᵢ ∈ X` be incident
with `bᵢ`, chosen in addition such that `fᵢ ∉ E(Bᵢ)` if possible (`1 ≤ i ≤ 3`).  (If `Q` is even
we choose the `fᵢ`'s a little differently, described later.)"* -/
def OddFChoice {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (Y : Set V)
    (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n) (f₁ f₂ f₃ : Sym2 (Fin n)) : Prop :=
  ChosenOutside G H K φ Y B₁ b₁ f₁ ∧
  ChosenOutside G H K φ Y B₂ b₂ f₂ ∧
  ChosenOutside G H K φ Y B₃ b₃ f₃

/-- **The configuration exists** (printed p. 30): *"There is a branch-vertex `b` of `H` incident
with at least two edges not in `X`.  For `i = 1, 2` let `eᵢ ∈ Xᵢ` be incident with `b`, and let
`e₃` be some third edge incident with `b`.  For `i = 1, 2, 3`, let `Bᵢ` be the branch of `H`
containing `eᵢ`, and let `bᵢ` be its other end."*

The branch-vertex `b` exists precisely because `X` does not saturate `L(H)`; the edges `e₁, e₂`
exist because `X ∪ X₁` and `X ∪ X₂` do saturate `L(H)` (`Thm61Setup.X_Xi_facts`); `e₃` exists
because `b` has degree `≥ 3`; and the branches exist because `H` is a subdivision of `J`. -/
theorem exists_branchChoice
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂) :
    ∃ (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n),
      BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ := by
  classical
  let X := completeEdges G H K φ Y
  let X₁ := extraEdges G H K φ Y y₁
  let X₂ := extraEdges G H K φ Y y₂
  obtain ⟨hXE, hX₁E, hX₂E, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  -- Since `X` does not saturate, some branch-vertex has two distinct incident edges outside it.
  have hex : ∃ b ∈ branchVertices H, (incidentEdges H b \ X).Nontrivial := by
    by_contra hc
    apply hnotsat
    intro b hb
    rw [← Set.not_nontrivial_iff]
    exact fun hnt => hc ⟨b, hb, hnt⟩
  obtain ⟨b, hb, g₁, hg₁, g₂, hg₂, hg₁g₂⟩ := hex
  obtain ⟨hg₁inc, hg₁X⟩ := hg₁
  obtain ⟨hg₂inc, hg₂X⟩ := hg₂
  -- Saturation by `X ∪ Xᵢ` forces an incident edge from each `Xᵢ` at `b`.
  have he₁ : ∃ e ∈ incidentEdges H b, e ∈ X₁ := by
    by_cases hg₁X₁ : g₁ ∈ X₁
    · exact ⟨g₁, hg₁inc, hg₁X₁⟩
    · have hg₂X₁ : g₂ ∈ X₁ := by
        by_contra hg₂X₁
        have heq := hsat₁ b hb
          ⟨hg₁inc, fun hg₁u => hg₁u.elim hg₁X hg₁X₁⟩
          ⟨hg₂inc, fun hg₂u => hg₂u.elim hg₂X hg₂X₁⟩
        exact hg₁g₂ heq
      exact ⟨g₂, hg₂inc, hg₂X₁⟩
  have he₂ : ∃ e ∈ incidentEdges H b, e ∈ X₂ := by
    by_cases hg₁X₂ : g₁ ∈ X₂
    · exact ⟨g₁, hg₁inc, hg₁X₂⟩
    · have hg₂X₂ : g₂ ∈ X₂ := by
        by_contra hg₂X₂
        have heq := hsat₂ b hb
          ⟨hg₁inc, fun hg₁u => hg₁u.elim hg₁X hg₁X₂⟩
          ⟨hg₂inc, fun hg₂u => hg₂u.elim hg₂X hg₂X₂⟩
        exact hg₁g₂ heq
      exact ⟨g₂, hg₂inc, hg₂X₂⟩
  obtain ⟨e₁, he₁inc, he₁X₁⟩ := he₁
  obtain ⟨e₂, he₂inc, he₂X₂⟩ := he₂
  have he₁e₂ : e₁ ≠ e₂ := by
    intro heq
    exact Set.disjoint_left.mp hX₁X₂ he₁X₁ (heq ▸ he₂X₂)
  -- A branch-vertex has at least three incident edges, so choose one different from both.
  have hinc3 : 3 ≤ (incidentEdges H b).ncard := by
    rw [Workspace.ProofLemmas.Thm84RungEndDictionary.incidentEdges_ncard]
    exact hb
  have hnsub : ¬ incidentEdges H b ⊆ ({e₁, e₂} : Set (Sym2 (Fin n))) := by
    intro hsub₁₂
    have hle := Set.ncard_le_ncard hsub₁₂ (Set.toFinite _)
    have hpairs : ({e₁, e₂} : Set (Sym2 (Fin n))).ncard ≤ 2 := by
      simpa using Set.ncard_insert_le e₁ ({e₂} : Set (Sym2 (Fin n)))
    omega
  obtain ⟨e₃, he₃inc, he₃not⟩ := Set.not_subset.mp hnsub
  have he₃e₁ : e₃ ≠ e₁ := by
    intro heq
    apply he₃not
    simp [heq]
  have he₃e₂ : e₃ ≠ e₂ := by
    intro heq
    apply he₃not
    simp [heq]
  -- The subdivision tracks are precisely the branches of `H` joining its branch-vertices.
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
  have hdegJ : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard := fun u =>
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hbv₁ : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisj hnew hdegJ
  have hbv₂ : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj hcover hedges
  have hTint : ∀ u v : Fin m, J.Adj u v → ∀ w ∈ trackInterior (T u v),
      w ∉ branchVertices H := fun u v huv w hw hbw => hnew u v huv w hw (hbv₂ hbw)
  have hTbranch : ∀ u v : Fin m, J.Adj u v → IsBranch H (T u v) := by
    intro u v huv
    exact Thm82BranchDelta.isBranch_of_ends_branch (htrack u v huv)
      (fun huvEq => huv.ne (hι huvEq)) (hTint u v huv)
      (hbv₁ ⟨u, rfl⟩) (hbv₁ ⟨v, rfl⟩)
  have hbranchFor : ∀ e : Sym2 (Fin n), e ∈ incidentEdges H b →
      ∃ (B : List (Fin n)) (b' : Fin n),
        IsBranch H B ∧ e ∈ trackEdges B ∧ IsTrackFrom H B b b' := by
    intro e he
    have heE : e ∈ H.edgeSet := he.1
    rw [hedges] at heE
    simp only [Set.mem_iUnion] at heE
    obtain ⟨u, v, huv, heT⟩ := heE
    have hbT : b ∈ T u v :=
      NaturalAppearanceStripSystemCore.endpoints_mem_of_mem_trackEdges heT he.2
    have hbnotint : b ∉ trackInterior (T u v) := fun hbint => hTint u v huv b hbint hb
    have hbends := SubdivisionCompose.mem_ends_of_mem
      (htrack u v huv).2.1 (htrack u v huv).2.2 hbT hbnotint
    rcases hbends with hbU | hbV
    · refine ⟨T u v, ι v, hTbranch u v huv, heT, ?_⟩
      rw [hbU]
      exact htrack u v huv
    · refine ⟨T v u, ι u, hTbranch v u huv.symm, ?_, ?_⟩
      · rw [hrev u v huv, SubdivisionCounting.trackEdges_reverse]
        exact heT
      · rw [hbV]
        exact htrack v u huv.symm
  obtain ⟨B₁, b₁, hB₁, he₁B₁, hfrom₁⟩ := hbranchFor e₁ he₁inc
  obtain ⟨B₂, b₂, hB₂, he₂B₂, hfrom₂⟩ := hbranchFor e₂ he₂inc
  obtain ⟨B₃, b₃, hB₃, he₃B₃, hfrom₃⟩ := hbranchFor e₃ he₃inc
  refine ⟨b, e₁, e₂, e₃, B₁, B₂, B₃, b₁, b₂, b₃, ?_⟩
  exact ⟨hb, ⟨g₁, hg₁inc, g₂, hg₂inc, hg₁g₂, hg₁X, hg₂X⟩,
    he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩

/-- **The printed consequence of the definition of a triad** (printed p. 30): *"It follows that
every triad has degree 3 in `H`, and is incident with exactly one edge in each of `X, X₁,
X₂`."* -/
theorem triad_facts
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (v : Fin n) (hv : Triad G H K φ Y v) :
    (H.neighborSet v).ncard = 3 ∧
    (∃! e : Sym2 (Fin n), e ∈ incidentEdges H v ∧ e ∈ completeEdges G H K φ Y) ∧
    (∃! e : Sym2 (Fin n), e ∈ incidentEdges H v ∧ e ∈ extraEdges G H K φ Y y₁) ∧
    (∃! e : Sym2 (Fin n), e ∈ incidentEdges H v ∧ e ∈ extraEdges G H K φ Y y₂) := by
  classical
  obtain ⟨hvbranch, htriad⟩ := hv
  obtain ⟨-, -, -, hdXA, hdXB, hdAB, hsatA, hsatB⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  have hdegree : 3 ≤ (H.neighborSet v).ncard := hvbranch
  have hneigh : (H.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨a, ha⟩ := hneigh
  have hdiff2 : 2 ≤ ((H.neighborSet v) \ {a}).ncard :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff hdegree
  obtain ⟨b, c, hb, hc, hbc⟩ :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.exists_two_mem hdiff2
  have hab : a ≠ b := by
    intro h
    exact hb.2 (by simpa [h])
  have hac : a ≠ c := by
    intro h
    exact hc.2 (by simpa [h])
  replace hb : b ∈ H.neighborSet v := hb.1
  replace hc : c ∈ H.neighborSet v := hc.1
  have hea : s(v, a) ∈ incidentEdges H v := ⟨H.mem_edgeSet.mpr ha, by simp⟩
  have heb : s(v, b) ∈ incidentEdges H v := ⟨H.mem_edgeSet.mpr hb, by simp⟩
  have hec : s(v, c) ∈ incidentEdges H v := ⟨H.mem_edgeSet.mpr hc, by simp⟩
  have heab : s(v, a) ≠ s(v, b) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> subst_vars <;> simp_all
  have heac : s(v, a) ≠ s(v, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> subst_vars <;> simp_all
  have hebc : s(v, b) ≠ s(v, c) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> subst_vars <;> simp_all
  have hsatA_pair : ∀ {e f : Sym2 (Fin n)}, e ∈ incidentEdges H v →
      f ∈ incidentEdges H v → e ≠ f →
      e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ ∨
        f ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    intro e f he hf hef
    by_contra h
    simp only [not_or] at h
    exact hef (hsatA v hvbranch ⟨he, h.1⟩ ⟨hf, h.2⟩)
  have hsatB_pair : ∀ {e f : Sym2 (Fin n)}, e ∈ incidentEdges H v →
      f ∈ incidentEdges H v → e ≠ f →
      e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ ∨
        f ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
    intro e f he hf hef
    by_contra h
    simp only [not_or] at h
    exact hef (hsatB v hvbranch ⟨he, h.1⟩ ⟨hf, h.2⟩)
  have hAab := hsatA_pair hea heb heab
  have hAac := hsatA_pair hea hec heac
  have hAbc := hsatA_pair heb hec hebc
  have hBab := hsatB_pair hea heb heab
  have hBac := hsatB_pair hea hec heac
  have hBbc := hsatB_pair heb hec hebc
  have hXab : ¬ (s(v, a) ∈ completeEdges G H K φ Y ∧
      s(v, b) ∈ completeEdges G H K φ Y) := by
    rintro ⟨hXa, hXb⟩
    exact heab (htriad ⟨hea, hXa⟩ ⟨heb, hXb⟩)
  have hXac : ¬ (s(v, a) ∈ completeEdges G H K φ Y ∧
      s(v, c) ∈ completeEdges G H K φ Y) := by
    rintro ⟨hXa, hXc⟩
    exact heac (htriad ⟨hea, hXa⟩ ⟨hec, hXc⟩)
  have hXbc : ¬ (s(v, b) ∈ completeEdges G H K φ Y ∧
      s(v, c) ∈ completeEdges G H K φ Y) := by
    rintro ⟨hXb, hXc⟩
    exact hebc (htriad ⟨heb, hXb⟩ ⟨hec, hXc⟩)
  have hABa : ¬ (s(v, a) ∈ extraEdges G H K φ Y y₁ ∧
      s(v, a) ∈ extraEdges G H K φ Y y₂) := by
    rintro ⟨hAa, hBa⟩
    exact (Set.disjoint_left.mp hdAB hAa) hBa
  have hABb : ¬ (s(v, b) ∈ extraEdges G H K φ Y y₁ ∧
      s(v, b) ∈ extraEdges G H K φ Y y₂) := by
    rintro ⟨hAb, hBb⟩
    exact (Set.disjoint_left.mp hdAB hAb) hBb
  have hABc : ¬ (s(v, c) ∈ extraEdges G H K φ Y y₁ ∧
      s(v, c) ∈ extraEdges G H K φ Y y₂) := by
    rintro ⟨hAc, hBc⟩
    exact (Set.disjoint_left.mp hdAB hAc) hBc
  have right_exists : ∀ {L₁ L₂ L₃ R₁ R₂ R₃ : Prop},
      ¬ (L₁ ∧ L₂) → ¬ (L₁ ∧ L₃) → ¬ (L₂ ∧ L₃) →
      ((L₁ ∨ R₁) ∨ (L₂ ∨ R₂)) → ((L₁ ∨ R₁) ∨ (L₃ ∨ R₃)) →
      ((L₂ ∨ R₂) ∨ (L₃ ∨ R₃)) → R₁ ∨ R₂ ∨ R₃ := by
    intro L₁ L₂ L₃ R₁ R₂ R₃ hL₁₂ hL₁₃ hL₂₃ h₁₂ h₁₃ h₂₃
    by_cases hR₁ : R₁
    · exact Or.inl hR₁
    by_cases hR₂ : R₂
    · exact Or.inr (Or.inl hR₂)
    by_cases hR₃ : R₃
    · exact Or.inr (Or.inr hR₃)
    simp only [hR₁, hR₂, hR₃, or_false] at h₁₂ h₁₃ h₂₃
    exfalso
    rcases h₁₂ with hL₁ | hL₂
    · rcases h₂₃ with hL₂ | hL₃
      · exact hL₁₂ ⟨hL₁, hL₂⟩
      · exact hL₁₃ ⟨hL₁, hL₃⟩
    · rcases h₁₃ with hL₁ | hL₃
      · exact hL₁₂ ⟨hL₁, hL₂⟩
      · exact hL₂₃ ⟨hL₂, hL₃⟩
  have left_exists : ∀ {X₁ X₂ X₃ A₁ A₂ A₃ B₁ B₂ B₃ : Prop},
      ¬ (A₁ ∧ B₁) → ¬ (A₂ ∧ B₂) → ¬ (A₃ ∧ B₃) →
      ((X₁ ∨ A₁) ∨ (X₂ ∨ A₂)) → ((X₁ ∨ A₁) ∨ (X₃ ∨ A₃)) →
      ((X₂ ∨ A₂) ∨ (X₃ ∨ A₃)) → ((X₁ ∨ B₁) ∨ (X₂ ∨ B₂)) →
      ((X₁ ∨ B₁) ∨ (X₃ ∨ B₃)) → ((X₂ ∨ B₂) ∨ (X₃ ∨ B₃)) →
      X₁ ∨ X₂ ∨ X₃ := by
    intro X₁ X₂ X₃ A₁ A₂ A₃ B₁ B₂ B₃ hAB₁ hAB₂ hAB₃
      hA₁₂ hA₁₃ hA₂₃ hB₁₂ hB₁₃ hB₂₃
    by_cases hX₁ : X₁
    · exact Or.inl hX₁
    by_cases hX₂ : X₂
    · exact Or.inr (Or.inl hX₂)
    by_cases hX₃ : X₃
    · exact Or.inr (Or.inr hX₃)
    simp only [hX₁, hX₂, hX₃, false_or] at hA₁₂ hA₁₃ hA₂₃ hB₁₂ hB₁₃ hB₂₃
    exfalso
    rcases hA₁₂ with hA₁ | hA₂
    · rcases hA₂₃ with hA₂ | hA₃
      · rcases hB₁₂ with hB₁ | hB₂
        · exact hAB₁ ⟨hA₁, hB₁⟩
        · exact hAB₂ ⟨hA₂, hB₂⟩
      · rcases hB₁₃ with hB₁ | hB₃
        · exact hAB₁ ⟨hA₁, hB₁⟩
        · exact hAB₃ ⟨hA₃, hB₃⟩
    · rcases hA₁₃ with hA₁ | hA₃
      · rcases hB₁₂ with hB₁ | hB₂
        · exact hAB₁ ⟨hA₁, hB₁⟩
        · exact hAB₂ ⟨hA₂, hB₂⟩
      · rcases hB₂₃ with hB₂ | hB₃
        · exact hAB₂ ⟨hA₂, hB₂⟩
        · exact hAB₃ ⟨hA₃, hB₃⟩
  have hAab' := (by simpa only [Set.mem_union] using hAab)
  have hAac' := (by simpa only [Set.mem_union] using hAac)
  have hAbc' := (by simpa only [Set.mem_union] using hAbc)
  have hBab' := (by simpa only [Set.mem_union] using hBab)
  have hBac' := (by simpa only [Set.mem_union] using hBac)
  have hBbc' := (by simpa only [Set.mem_union] using hBbc)
  have hXexists : s(v, a) ∈ completeEdges G H K φ Y ∨
      s(v, b) ∈ completeEdges G H K φ Y ∨
      s(v, c) ∈ completeEdges G H K φ Y :=
    left_exists hABa hABb hABc hAab' hAac' hAbc' hBab' hBac' hBbc'
  have hAexists : s(v, a) ∈ extraEdges G H K φ Y y₁ ∨
      s(v, b) ∈ extraEdges G H K φ Y y₁ ∨
      s(v, c) ∈ extraEdges G H K φ Y y₁ :=
    right_exists hXab hXac hXbc hAab' hAac' hAbc'
  have hBexists : s(v, a) ∈ extraEdges G H K φ Y y₂ ∨
      s(v, b) ∈ extraEdges G H K φ Y y₂ ∨
      s(v, c) ∈ extraEdges G H K φ Y y₂ :=
    right_exists hXab hXac hXbc hBab' hBac' hBbc'
  have hXnonempty : ∃ e : Sym2 (Fin n), e ∈ incidentEdges H v ∧
      e ∈ completeEdges G H K φ Y := by
    rcases hXexists with hXa | hXb | hXc
    · exact ⟨s(v, a), hea, hXa⟩
    · exact ⟨s(v, b), heb, hXb⟩
    · exact ⟨s(v, c), hec, hXc⟩
  have hAnonempty : ∃ e : Sym2 (Fin n), e ∈ incidentEdges H v ∧
      e ∈ extraEdges G H K φ Y y₁ := by
    rcases hAexists with hAa | hAb | hAc
    · exact ⟨s(v, a), hea, hAa⟩
    · exact ⟨s(v, b), heb, hAb⟩
    · exact ⟨s(v, c), hec, hAc⟩
  have hBnonempty : ∃ e : Sym2 (Fin n), e ∈ incidentEdges H v ∧
      e ∈ extraEdges G H K φ Y y₂ := by
    rcases hBexists with hBa | hBb | hBc
    · exact ⟨s(v, a), hea, hBa⟩
    · exact ⟨s(v, b), heb, hBb⟩
    · exact ⟨s(v, c), hec, hBc⟩
  obtain ⟨eX, heXD, heX⟩ := hXnonempty
  obtain ⟨eA, heAD, heA⟩ := hAnonempty
  obtain ⟨eB, heBD, heB⟩ := hBnonempty
  have heXA : eX ≠ eA := by
    intro h
    subst eA
    exact (Set.disjoint_left.mp hdXA heX) heA
  have heXB : eX ≠ eB := by
    intro h
    subst eB
    exact (Set.disjoint_left.mp hdXB heX) heB
  have heAB : eA ≠ eB := by
    intro h
    subst eB
    exact (Set.disjoint_left.mp hdAB heA) heB
  have heBnotUA : eB ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
    simp only [Set.mem_union, not_or]
    exact ⟨Set.disjoint_right.mp hdXB heB, Set.disjoint_right.mp hdAB heB⟩
  have heAnotUB : eA ∉ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
    simp only [Set.mem_union, not_or]
    exact ⟨Set.disjoint_right.mp hdXA heA, Set.disjoint_left.mp hdAB heA⟩
  have hcover : ∀ e : Sym2 (Fin n), e ∈ incidentEdges H v →
      e = eX ∨ e = eA ∨ e = eB := by
    intro e he
    by_cases heAeq : e = eA
    · exact Or.inr (Or.inl heAeq)
    by_cases heBeq : e = eB
    · exact Or.inr (Or.inr heBeq)
    have heUA : e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₁ := by
      by_contra h
      exact heBeq (hsatA v hvbranch ⟨he, h⟩ ⟨heBD, heBnotUA⟩)
    have heUB : e ∈ completeEdges G H K φ Y ∪ extraEdges G H K φ Y y₂ := by
      by_contra h
      exact heAeq (hsatB v hvbranch ⟨he, h⟩ ⟨heAD, heAnotUB⟩)
    simp only [Set.mem_union] at heUA heUB
    rcases heUA with heXcur | heAcur
    · exact Or.inl (htriad ⟨he, heXcur⟩ ⟨heXD, heX⟩)
    · rcases heUB with heXcur | heBcur
      · exact Or.inl (htriad ⟨he, heXcur⟩ ⟨heXD, heX⟩)
      · exact False.elim ((Set.disjoint_left.mp hdAB heAcur) heBcur)
  have hincident : incidentEdges H v = {eX, eA, eB} := by
    ext e
    constructor
    · intro he
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcover e he
    · intro he
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at he
      rcases he with h | h | h
      · rw [h]
        exact heXD
      · rw [h]
        exact heAD
      · rw [h]
        exact heBD
  have hincard : (incidentEdges H v).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨eX, eA, eB, heXA, heXB, heAB, hincident⟩
  have hcard : (H.neighborSet v).ncard = 3 := by
    have hequiv : (incidentEdges H v).ncard = (H.neighborSet v).ncard := by
      change (H.incidenceSet v).ncard = (H.neighborSet v).ncard
      exact Nat.card_congr (H.incidenceSetEquivNeighborSet v)
    omega
  refine ⟨hcard, ?_, ?_, ?_⟩
  · refine ⟨eX, ⟨heXD, heX⟩, ?_⟩
    intro e he
    exact htriad ⟨he.1, he.2⟩ ⟨heXD, heX⟩
  · refine ⟨eA, ⟨heAD, heA⟩, ?_⟩
    intro e he
    have heSet := he.1
    have heMem := he.2
    rw [hincident] at heSet
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heSet
    rcases heSet with h | h | h
    · rw [h]
      exact False.elim ((Set.disjoint_left.mp hdXA heX) (h ▸ heMem))
    · exact h
    · rw [h]
      exact False.elim ((Set.disjoint_left.mp hdAB (h ▸ heMem)) heB)
  · refine ⟨eB, ⟨heBD, heB⟩, ?_⟩
    intro e he
    have heSet := he.1
    have heMem := he.2
    rw [hincident] at heSet
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at heSet
    rcases heSet with h | h | h
    · rw [h]
      exact False.elim ((Set.disjoint_left.mp hdXB heX) (h ▸ heMem))
    · rw [h]
      exact False.elim ((Set.disjoint_left.mp hdAB heA) (h ▸ heMem))
    · exact h

/-- **The `fᵢ` exist** (printed p. 30): *"let `fᵢ ∈ X` be incident with `bᵢ`, chosen in addition
such that `fᵢ ∉ E(Bᵢ)` if possible (`1 ≤ i ≤ 3`)."*

That there is *some* edge of `X` incident with `bᵢ` is the printed remark *"every branch-vertex
is incident with at least one edge in `X`"* (used in claim (1)); once one exists, an edge outside
`E(Bᵢ)` is preferred. -/
theorem exists_oddFChoice
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃) :
    ∃ f₁ f₂ f₃ : Sym2 (Fin n), OddFChoice G H K φ Y B₁ B₂ B₃ b₁ b₂ b₃ f₁ f₂ f₃ := by
  classical
  rcases hbc with ⟨hb, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
    hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  have edge_forces_length : ∀ {B : List (Fin n)} {e : Sym2 (Fin n)},
      e ∈ trackEdges B → 1 ≤ trackLength B := by
    intro B e he
    obtain ⟨i, hi, rfl⟩ := he
    simp only [trackLength]
    omega
  have hlen₁ : 1 ≤ trackLength B₁ := edge_forces_length he₁B₁
  have hlen₂ : 1 ≤ trackLength B₂ := edge_forces_length he₂B₂
  have hlen₃ : 1 ≤ trackLength B₃ := edge_forces_length he₃B₃
  have hb₁v : b₁ ∈ branchVertices H :=
    (Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
      J hJ H hsub.1 B₁ b b₁ hB₁ hfrom₁ hlen₁).2
  have hb₂v : b₂ ∈ branchVertices H :=
    (Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
      J hJ H hsub.1 B₂ b b₂ hB₂ hfrom₂ hlen₂).2
  have hb₃v : b₃ ∈ branchVertices H :=
    (Workspace.ProofLemmas.Thm75BranchEnds.branchEnds_mem_branchVertices
      J hJ H hsub.1 B₃ b b₃ hB₃ hfrom₃ hlen₃).2
  have complete_incident : ∀ v : Fin n, v ∈ branchVertices H →
      ∃ e : Sym2 (Fin n), e ∈ incidentEdges H v ∧ e ∈ completeEdges G H K φ Y := by
    intro v hv
    by_cases htri : (incidentEdges H v ∩ completeEdges G H K φ Y).Subsingleton
    · obtain ⟨-, hX, -, -⟩ :=
        triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy v ⟨hv, htri⟩
      obtain ⟨e, he, -⟩ := hX
      exact ⟨e, he.1, he.2⟩
    · have hne : (incidentEdges H v ∩ completeEdges G H K φ Y).Nonempty := by
        by_contra hempty
        apply htri
        intro e he f hf
        exact False.elim (hempty ⟨e, he⟩)
      obtain ⟨e, he⟩ := hne
      exact ⟨e, he.1, he.2⟩
  have chooseOutside : ∀ (B : List (Fin n)) (v : Fin n), v ∈ branchVertices H →
      ∃ f : Sym2 (Fin n), ChosenOutside G H K φ Y B v f := by
    intro B v hv
    obtain ⟨f, hfinc, hfX⟩ := complete_incident v hv
    by_cases hout : ∃ g ∈ completeEdges G H K φ Y,
        g ∈ incidentEdges H v ∧ g ∉ trackEdges B
    · obtain ⟨g, hgX, hginc, hgout⟩ := hout
      exact ⟨g, hgX, hginc, fun _ => hgout⟩
    · exact ⟨f, hfX, hfinc, fun hex => False.elim (hout hex)⟩
  obtain ⟨f₁, hf₁⟩ := chooseOutside B₁ b₁ hb₁v
  obtain ⟨f₂, hf₂⟩ := chooseOutside B₂ b₂ hb₂v
  obtain ⟨f₃, hf₃⟩ := chooseOutside B₃ b₃ hb₃v
  exact ⟨f₁, f₂, f₃, hf₁, hf₂, hf₃⟩

end Workspace.ProofLemmas.Thm61BranchChoice
