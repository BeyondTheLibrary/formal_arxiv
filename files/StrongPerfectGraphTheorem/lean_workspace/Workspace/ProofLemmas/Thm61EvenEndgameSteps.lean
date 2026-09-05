import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.Thm61Setup
import Workspace.ProofLemmas.Thm61Conclusion
import Workspace.ProofLemmas.Thm61EvenClaims
import Workspace.ProofLemmas.Thm61BranchChoice
import Workspace.ProofLemmas.Thm61Claim1
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers
import Workspace.ProofLemmas.Thm61EvenEndgameRemaining

/-!
# 6.1, even case: the endgame, carved into the blocks the printed proof itself marks out

PAPER (proof of 6.1, printed pp. 32–33).  Everything after claim (10): the refinement of the
choice of `b`, claims (11), (12), (13) and the closing paragraph.

`Workspace.ProofLemmas.Thm61EvenEndgame.thm_6_1_even_endgame` is the *assembly* of this material.
This module holds the printed blocks, stated so that the assembly can be checked before any of
them is proved.  The carve is the paper's own:

| block | printed text |
|---|---|
| `exists_maximal_branchChoice` | *"Earlier (preceding (4)) we chose `b` such that at least two edges of `H` incident with `b` did not belong to `X`.  Let us refine this choice; now in addition we choose `b` such that `B₃` is as long as possible."* |
| `thm_6_1_claim_11` | *"(11) For `i = 1, 2` there is an edge `fᵢ ∈ X` incident with `bᵢ` that does not meet `e₃`."* |
| `thm_6_1_claim_12` | *"(12) If there exist `f₁, f₂` as in (11) with `f₁, f₂ ≠ b₁b₂` then the theorem holds."* |
| `thm_6_1_even_final` | *"From (11) and (12) we may therefore assume that `b₁, b₂` are adjacent, and the edge `b₁b₂ ∈ X`. …"* — the bridging paragraph, claim (13) and the closing paragraph, down to *"This proves 6.1"*. |

`branch_parity` is the one unargued sentence of the bridging paragraph: *"From the symmetry we
may assume that `B₁` is even and `B₂` is odd"* presupposes that exactly one of `B₁, B₂` is even,
which holds because `B₁`, the edge `b₁b₂` and `B₂` form a cycle of `H` and `H` is bipartite.  It
is stated here so that `thm_6_1_even_final` can quote it while performing the symmetry
internally.

## The configuration is **not** restated here

The configuration *"a branch-vertex `b` incident with at least two edges not in `X`; `eᵢ ∈ Xᵢ`
incident with `b`; a third edge `e₃`; `Bᵢ` the branch containing `eᵢ` and `bᵢ` its other end"* is
fixed by the paper on printed p. 30, **before** the odd/even split, and both halves of the proof
use it.  It is already named, once and for all, as
`Workspace.ProofLemmas.Thm61BranchChoice.BranchChoice`, with its existence lemma
`Thm61BranchChoice.exists_branchChoice`.  This module adds only the *refinement* of that choice
made on printed p. 32 (`BranchChoiceMaximal`), and reuses `BranchChoice` verbatim so that the odd
lane and the even lane agree byte-for-byte.  `Thm61BranchChoice.Triad` is likewise the paper's
*"triad"* and is used freely below.

**Status: statement only — every declaration below is a work item.**
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm61EvenEndgameSteps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm61Setup
open Workspace.ProofLemmas.Thm61Conclusion
open Workspace.ProofLemmas.Thm61EvenClaims
open Workspace.ProofLemmas.Thm61BranchChoice
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.Thm61EvenEndgameClaim12
open Workspace.ProofLemmas.Thm61EvenEndgameRemaining

/-- **The refinement of the choice of `b`** (printed p. 32, preceding (11)):

> *"Earlier (preceding (4)) we chose `b` such that at least two edges of `H` incident with `b`
> did not belong to `X`.  Let us refine this choice; now in addition we choose `b` such that
> `B₃` is as long as possible."*

`B₃` is as long as possible over **all** configurations, i.e. over all choices of `b`, of the
two edges `e₁ ∈ X₁`, `e₂ ∈ X₂` at `b`, and of the third edge `e₃` at `b` — this is the form the
printed proof of (11) uses when it says *"`b₂` and `B` contradict the choice of `b` and `B₃`"*,
where the competing configuration is centred at a different branch-vertex. -/
def BranchChoiceMaximal {V : Type*} (G : SimpleGraph V) {n : ℕ} (H : SimpleGraph (Fin n))
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) (Y : Set V) (y₁ y₂ : V)
    (B₃ : List (Fin n)) : Prop :=
  ∀ (b' : Fin n) (e₁' e₂' e₃' : Sym2 (Fin n)) (B₁' B₂' B₃' : List (Fin n))
      (b₁' b₂' b₃' : Fin n),
    BranchChoice G H K φ Y y₁ y₂ b' e₁' e₂' e₃' B₁' B₂' B₃' b₁' b₂' b₃' →
      trackLength B₃' ≤ trackLength B₃

/-- **The configuration exists with `B₃` as long as possible** (printed p. 32, preceding (11)).

Existence of *some* configuration is `Thm61BranchChoice.exists_branchChoice`; the refinement is
then a maximum of a set of natural numbers which is nonempty and bounded above (every `B₃` is a
`Nodup` list of vertices of `H`, so `trackLength B₃ < n`). -/
theorem exists_maximal_branchChoice
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
      BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ ∧
        BranchChoiceMaximal G H K φ Y y₁ y₂ B₃ := by
  classical
  obtain ⟨b₀, e₁₀, e₂₀, e₃₀, B₁₀, B₂₀, B₃₀, b₁₀, b₂₀, b₃₀, hchoice₀⟩ :=
    exists_branchChoice G m J hJ n H K hsub φ Y hYanti hnotsat hmin y₁ y₂ Q hQ hQY hy
  have branchChoice_nodup :
      ∀ {b : Fin n} {e₁ e₂ e₃ : Sym2 (Fin n)}
          {B₁ B₂ B₃ : List (Fin n)} {b₁ b₂ b₃ : Fin n},
        BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ →
          B₃.Nodup := by
    intro b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hchoice
    rcases hchoice with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hB₃, _, _⟩
    exact hB₃.1.2.1
  let P : ℕ → Prop := fun k =>
    ∃ (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n))
        (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n),
      BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ ∧
        trackLength B₃ = k
  let S : Finset ℕ := (Finset.range (n + 1)).filter P
  have hlength₀ : B₃₀.length ≤ n := by
    simpa using (branchChoice_nodup hchoice₀).length_le_card
  have hmem₀ : trackLength B₃₀ ∈ S := by
    change trackLength B₃₀ ∈ (Finset.range (n + 1)).filter P
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply Finset.mem_range.mpr
      unfold trackLength
      omega
    · exact ⟨b₀, e₁₀, e₂₀, e₃₀, B₁₀, B₂₀, B₃₀, b₁₀, b₂₀, b₃₀, hchoice₀, rfl⟩
  have hS : S.Nonempty := ⟨trackLength B₃₀, hmem₀⟩
  have hmaxmem : S.max' hS ∈ S := Finset.max'_mem S hS
  change S.max' hS ∈ (Finset.range (n + 1)).filter P at hmaxmem
  rcases Finset.mem_filter.mp hmaxmem with ⟨_, hmaxP⟩
  rcases hmaxP with
    ⟨b, e₁, e₂, e₃, B₁, B₂, B₃, b₁, b₂, b₃, hchoice, hlength⟩
  refine ⟨b, e₁, e₂, e₃, B₁, B₂, B₃, b₁, b₂, b₃, hchoice, ?_⟩
  intro b' e₁' e₂' e₃' B₁' B₂' B₃' b₁' b₂' b₃' hchoice'
  have hlength' : B₃'.length ≤ n := by
    simpa using (branchChoice_nodup hchoice').length_le_card
  have hmem' : trackLength B₃' ∈ S := by
    change trackLength B₃' ∈ (Finset.range (n + 1)).filter P
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · apply Finset.mem_range.mpr
      unfold trackLength
      omega
    · exact ⟨b', e₁', e₂', e₃', B₁', B₂', B₃', b₁', b₂', b₃', hchoice', rfl⟩
  rw [hlength]
  exact Finset.le_max' S (trackLength B₃') hmem'

private theorem claim11_one
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n))
    (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hmax : BranchChoiceMaximal G H K φ Y y₁ y₂ B₃) :
    ∃ f₁ ∈ completeEdges G H K φ Y, b₁ ∈ f₁ ∧ ¬ MeetEdges f₁ e₃ := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨f, hfX, hfinc, hfeq, hb₁tri, hB₃one, he₃eq, hB₁long⟩ :=
    claim11_failure_shape G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc hcon
  rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
    he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
    hB₃, he₃B₃, hfrom₃⟩
  have hbc' : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ :=
    ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc, he₃e₁, he₃e₂,
      hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂, hB₃, he₃B₃, hfrom₃⟩
  rcases branchChoice_basic G m J hJ n H K hsub φ Y hmin y₁ y₂ Q hQ hQY hy
      b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc' with
    ⟨hB₁pos, hB₂pos, hB₃pos, -, hb₁V, hb₂V, hb₃V, hbb₁, hbb₂, hbb₃,
      hb₁b₂, hb₁b₃, hb₂b₃⟩
  obtain ⟨-, -, -, hXX₁, hXX₂, hX₁X₂, hsat₁, hsat₂⟩ :=
    X_Xi_facts G H K φ Y hmin y₁ y₂ Q hQ hQY hy
  obtain ⟨hb₁deg, -, hX₁uniq, -⟩ :=
    triad_facts G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₁ hb₁tri
  obtain ⟨a₁, ha₁, -⟩ := hX₁uniq
  have ha₁e₂ : MeetEdges a₁ e₂ := h8 a₁ e₂ ha₁.2 he₂X₂
  have ha₁ne₁ : a₁ ≠ e₁ := by
    intro hae
    have hb₁e₁ : b₁ ∈ e₁ := hae ▸ ha₁.1.2
    have he₁eq : e₁ = s(b, b₁) :=
      Workspace.ProofLemmas.Thm84RungEndDictionary.eq_sym2_of_mem_mem hbb₁
        he₁inc.2 hb₁e₁
    have hadj : H.Adj b b₁ := by
      apply H.mem_edgeSet.mp
      rw [← he₁eq]
      exact he₁inc.1
    exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
      J hJ H hsub.1 B₁ b b₁ hB₁ hfrom₁ hB₁long).2.2.2 hadj
  obtain ⟨hB₂one, he₂eq, ha₁eq⟩ :=
    identify_cross_meeting J hJ H hsub.1 hB₂ hfrom₂ hB₁ hfrom₁
      hB₂pos hB₁pos hb₁V hbb₁.symm hb₁b₂ he₂B₂ he₂inc.2
      he₁B₁ he₁inc.2 ha₁.1.1 ha₁.1.2 ha₁ne₁ ha₁e₂
  have he₃X : e₃ ∈ completeEdges G H K φ Y :=
    other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
      he₃inc he₃e₁ he₃e₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
  have hbdeg : (H.neighborSet b).ncard = 3 := by
    by_contra hne3
    have hdeg4 : 4 ≤ (incidentEdges H b).ncard := by
      rw [Workspace.ProofLemmas.Thm84RungEndDictionary.incidentEdges_ncard]
      exact lt_of_le_of_ne hbV (Ne.symm hne3)
    have hnsub : ¬ incidentEdges H b ⊆ ({e₁, e₂, e₃} : Set (Sym2 (Fin n))) := by
      intro hs
      have hle := Set.ncard_le_ncard hs (Set.toFinite _)
      have hthree : ({e₁, e₂, e₃} : Set (Sym2 (Fin n))).ncard ≤ 3 := by
        have htwo := Set.ncard_insert_le e₂ ({e₃} : Set (Sym2 (Fin n)))
        calc
          ({e₁, e₂, e₃} : Set (Sym2 (Fin n))).ncard
              ≤ ({e₂, e₃} : Set (Sym2 (Fin n))).ncard + 1 := Set.ncard_insert_le _ _
          _ ≤ ({e₃} : Set (Sym2 (Fin n))).ncard + 1 + 1 := by omega
          _ = 3 := by simp
      omega
    obtain ⟨g, hginc, hgnot⟩ := Set.not_subset.mp hnsub
    have hgne₁ : g ≠ e₁ := fun h => hgnot (by simp [h])
    have hgne₂ : g ≠ e₂ := fun h => hgnot (by simp [h])
    have hgne₃ : g ≠ e₃ := fun h => hgnot (by simp [h])
    have hgX : g ∈ completeEdges G H K φ Y :=
      other_incident_is_complete φ Y y₁ y₂ hbV he₁inc he₁X₁ he₂inc he₂X₂
        hginc hgne₁ hgne₂ hXX₁ hXX₂ hX₁X₂ hsat₁ hsat₂
    obtain ⟨v, hgeq⟩ := Sym2.mem_iff_exists.mp hginc.2
    have hbv : b ≠ v := by
      have hadj : H.Adj b v := by
        apply H.mem_edgeSet.mp
        rw [← hgeq]
        exact hginc.1
      exact hadj.ne
    have hvb₁ : v ≠ b₁ := by
      intro hv
      have hadj : H.Adj b b₁ := by
        apply H.mem_edgeSet.mp
        have hgE : s(b, v) ∈ H.edgeSet := by rw [← hgeq]; exact hginc.1
        simpa [hv] using hgE
      exact (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
        J hJ H hsub.1 B₁ b b₁ hB₁ hfrom₁ hB₁long).2.2.2 hadj
    have hvb₂ : v ≠ b₂ := by
      intro hv
      apply hgne₂
      rw [hgeq, hv, he₂eq]
    have hvb₃ : v ≠ b₃ := by
      intro hv
      apply hgne₃
      rw [hgeq, hv, he₃eq]
    let P : List (Fin n) := [b₃, b₁, b₂, b, v]
    have hP : IsTrackList H P := by
      refine ⟨by simp [P], ?_, ?_⟩
      · simp only [P, List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
          or_false, not_or]
        exact ⟨⟨hb₁b₃.symm, hb₂b₃.symm, hbb₃.symm, hvb₃.symm⟩,
          ⟨⟨hb₁b₂, hbb₁.symm, hvb₁.symm⟩,
            ⟨⟨hbb₂.symm, hvb₂.symm⟩, ⟨hbv, by simp⟩⟩⟩⟩
      · intro i hi
        have hi' : i ≤ 3 := by simp only [P, List.length_cons, List.length_nil] at hi; omega
        interval_cases i <;> simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
        · apply H.mem_edgeSet.mp
          rw [Sym2.eq_swap, ← hfeq]
          exact hfX.1
        · apply H.mem_edgeSet.mp
          rw [← ha₁eq]
          exact ha₁.1.1
        · exact (H.mem_edgeSet.mp (he₂eq ▸ he₂inc.1)).symm
        · apply H.mem_edgeSet.mp
          rw [← hgeq]
          exact hginc.1
    have hPfirst :
        s(P[0]'(by simp [P]), P[1]'(by simp [P])) ∈ completeEdges G H K φ Y := by
      simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [Sym2.eq_swap, ← hfeq]
      exact hfX
    have hPlast :
        s(P[P.length - 2]'(by simp [P]), P[P.length - 1]'(by simp [P]))
          ∈ completeEdges G H K φ Y := by
      simpa only [P, List.length_cons, List.length_nil, List.getElem_cons_zero,
        List.getElem_cons_succ, hgeq] using hgX
    have hPint : ∀ i : ℕ, 1 ≤ i → ∀ _hi : i + 2 < P.length,
        s(P[i]'(by omega), P[i + 1]'(by omega)) ∉ completeEdges G H K φ Y := by
      intro i hi hi2
      have hi' : i ≤ 2 := by simp only [P, List.length_cons, List.length_nil] at hi2; omega
      interval_cases i
      · simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [← ha₁eq]
        exact Set.disjoint_right.mp hXX₁ ha₁.2
      · simp only [P, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [Sym2.eq_swap, ← he₂eq]
        exact Set.disjoint_right.mp hXX₂ he₂X₂
    obtain ⟨x, hxinc, hxX⟩ :=
      exists_complete_incident G n H K φ Y hmin y₁ y₂ Q hQ hQY hy b₂ hb₂V
    have hxb₁ : b₁ ∉ x := by
      intro hxb₁
      have hxeq : x = s(b₁, b₂) :=
        Workspace.ProofLemmas.Thm84RungEndDictionary.eq_sym2_of_mem_mem hb₁b₂ hxb₁ hxinc.2
      exact (Set.disjoint_left.mp hXX₁ hxX) (by rw [hxeq, ← ha₁eq]; exact ha₁.2)
    have hxb : b ∉ x := by
      intro hxb
      have hxeq : x = s(b, b₂) :=
        Workspace.ProofLemmas.Thm84RungEndDictionary.eq_sym2_of_mem_mem hbb₂ hxb hxinc.2
      exact (Set.disjoint_left.mp hXX₂ hxX) (by rw [hxeq, ← he₂eq]; exact he₂X₂)
    have hpen := h9 Y (Or.inl rfl) P hP (by simp [P]) (by
      refine ⟨2, ?_⟩
      simp [P, trackLength])
      hPfirst hPlast hPint x hxX
    rcases hpen with hpen | hpen
    · exact hxb₁ (by simpa [P] using hpen)
    · exact hxb (by simpa [P] using hpen)
  obtain ⟨ι, T, hι, htrack, hTlen, hrev, hdisj, hnew, hcover, hedges⟩ := hsub.1
  have hJdeg : ∀ u : Fin m, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  have hbrange : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range
      htrack hrev hdisj hcover hedges
  obtain ⟨u₀, hu₀⟩ := hbrange hbV
  obtain ⟨u₁, hu₁⟩ := hbrange hb₁V
  obtain ⟨u₂, hu₂⟩ := hbrange hb₂V
  obtain ⟨u₃, hu₃⟩ := hbrange hb₃V
  have h0 : b = ι u₀ := hu₀.symm
  have h1 : b₁ = ι u₁ := hu₁.symm
  have h2 : b₂ = ι u₂ := hu₂.symm
  have h3 : b₃ = ι u₃ := hu₃.symm
  have hu01 : u₀ ≠ u₁ := fun h => hbb₁ (by rw [h0, h1, h])
  have hu02 : u₀ ≠ u₂ := fun h => hbb₂ (by rw [h0, h2, h])
  have hu03 : u₀ ≠ u₃ := fun h => hbb₃ (by rw [h0, h3, h])
  have hu12 : u₁ ≠ u₂ := fun h => hb₁b₂ (by rw [h1, h2, h])
  have hu13 : u₁ ≠ u₃ := fun h => hb₁b₃ (by rw [h1, h3, h])
  have hu23 : u₂ ≠ u₃ := fun h => hb₂b₃ (by rw [h2, h3, h])
  have hH02 : H.Adj (ι u₀) (ι u₂) := by
    rw [← h0, ← h2]
    apply H.mem_edgeSet.mp
    rw [← he₂eq]
    exact he₂inc.1
  have hH03 : H.Adj (ι u₀) (ι u₃) := by
    rw [← h0, ← h3]
    apply H.mem_edgeSet.mp
    rw [← he₃eq]
    exact he₃inc.1
  have hH12 : H.Adj (ι u₁) (ι u₂) := by
    rw [← h1, ← h2]
    apply H.mem_edgeSet.mp
    rw [← ha₁eq]
    exact ha₁.1.1
  have hH13 : H.Adj (ι u₁) (ι u₃) := by
    rw [← h1, ← h3]
    apply H.mem_edgeSet.mp
    rw [← hfeq]
    exact hfX.1
  have hJ01 : J.Adj u₀ u₁ :=
    original_adj_of_branch_ends hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg
      hB₁ hfrom₁ hB₁pos h0 h1
  have hJ02 : J.Adj u₀ u₂ := original_adj_of_subdivision_adj hι htrack hnew hedges hH02
  have hJ03 : J.Adj u₀ u₃ := original_adj_of_subdivision_adj hι htrack hnew hedges hH03
  have hJ12 : J.Adj u₁ u₂ := original_adj_of_subdivision_adj hι htrack hnew hedges hH12
  have hJ13 : J.Adj u₁ u₃ := original_adj_of_subdivision_adj hι htrack hnew hedges hH13
  have hJdeg0 : (J.neighborSet u₀).ncard = 3 := by
    apply le_antisymm
    · calc
        (J.neighborSet u₀).ncard ≤ (H.neighborSet (ι u₀)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₀
        _ = 3 := by rw [← h0, hbdeg]
    · exact hJdeg u₀
  have hJdeg1 : (J.neighborSet u₁).ncard = 3 := by
    apply le_antisymm
    · calc
        (J.neighborSet u₁).ncard ≤ (H.neighborSet (ι u₁)).ncard :=
          original_degree_le_subdivision_degree hι htrack hTlen hdisj hnew u₁
        _ = 3 := by rw [← h1, hb₁deg]
    · exact hJdeg u₁
  have hall : ∀ x : Fin m, x = u₀ ∨ x = u₁ ∨ x = u₂ ∨ x = u₃ :=
    four_vertices_of_two_degree_three hJ hJ01 hJ02 hJ03 hJ12 hJ13 hu23 hJdeg0 hJdeg1
  have hJ23 : J.Adj u₂ u₃ := by
    by_contra hnot
    have hsubN : J.neighborSet u₂ ⊆ ({u₀, u₁} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl
      · simp
      · simp
      · exact False.elim (J.loopless.irrefl _ hx)
      · exact False.elim (hnot hx)
    have hle := Set.ncard_le_ncard hsubN (Set.toFinite _)
    rw [Set.ncard_pair hu01] at hle
    have hthree := hJdeg u₂
    omega
  let D : List (Fin n) := T u₂ u₃
  have hDfrom : IsTrackFrom H D b₂ b₃ := by
    dsimp [D]
    rw [h2, h3]
    exact htrack u₂ u₃ hJ23
  have hDpos : 1 ≤ trackLength D := hTlen u₂ u₃ hJ23
  have hDbranch : IsBranch H D :=
    subdivision_track_isBranch hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg hJ23
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
  have hcol02 : col (ι u₀) ≠ col (ι u₂) := col.valid hH02
  have hcol03 : col (ι u₀) ≠ col (ι u₃) := col.valid hH03
  have hcol23 : col b₂ = col b₃ := by
    rw [h2, h3]
    exact bool_eq_of_ne_ne (col (ι u₀)) (col (ι u₂)) (col (ι u₃)) hcol02 hcol03
  have hDeven : Even (trackLength D) :=
    (Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff
      (H := H) (q := D) (a := b₂) (b := b₃) col hDfrom).mpr hcol23
  have hDlong : 2 ≤ trackLength D := by
    rcases hDeven with ⟨k, hk⟩
    omega
  let C₁ : List (Fin n) := T u₂ u₁
  let C₂ : List (Fin n) := T u₂ u₀
  have hC₁from : IsTrackFrom H C₁ b₂ b₁ := by
    dsimp [C₁]
    rw [h2, h1]
    exact htrack u₂ u₁ hJ12.symm
  have hC₂from : IsTrackFrom H C₂ b₂ b := by
    dsimp [C₂]
    rw [h2, h0]
    exact htrack u₂ u₀ hJ02.symm
  have hC₁branch : IsBranch H C₁ :=
    subdivision_track_isBranch hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg hJ12.symm
  have hC₂branch : IsBranch H C₂ :=
    subdivision_track_isBranch hι htrack hTlen hrev hdisj hnew hcover hedges hJdeg hJ02.symm
  have hC₁len : C₁.length = 2 :=
    subdivision_track_length_two_of_adj hι htrack hrev hnew hedges hH12.symm
  have hC₂len : C₂.length = 2 :=
    subdivision_track_length_two_of_adj hι htrack hrev hnew hedges hH02.symm
  have ha₁C₁ : a₁ ∈ trackEdges C₁ := by
    rw [Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdges_of_len_two hC₁from hC₁len,
      ha₁eq, Sym2.eq_swap]
    exact Set.mem_singleton _
  have he₂C₂ : e₂ ∈ trackEdges C₂ := by
    rw [Workspace.ProofLemmas.Thm61Claim1Helpers.trackEdges_of_len_two hC₂from hC₂len,
      he₂eq, Sym2.eq_swap]
    exact Set.mem_singleton _
  have hDlen : 2 ≤ D.length := by simp only [trackLength] at hDpos; omega
  let d : Sym2 (Fin n) := s(D[0]'(by omega), D[1]'(by omega))
  have hdD : d ∈ trackEdges D := ⟨0, by omega, rfl⟩
  have hdE : d ∈ H.edgeSet := hDfrom.1.2.2 0 (by omega)
  have hD0 : D[0]'(by omega) = b₂ :=
    Workspace.ProofLemmas.Thm61Claim1Helpers.head_getElem hDfrom.2.1 (by omega)
  have hb₂d : b₂ ∈ d := by dsimp [d]; rw [← hD0]; simp
  have hdinc : d ∈ incidentEdges H b₂ := ⟨hdE, hb₂d⟩
  have hdne₁ : d ≠ a₁ := by
    intro h
    have hb₁d : b₁ ∈ d := h ▸ ha₁.1.2
    exact branch_edge_avoids_other_branchVertex hDbranch hDfrom hdD hb₁V
      hb₁b₂ hb₁b₃ hb₁d
  have hdne₂ : d ≠ e₂ := by
    intro h
    have hbd : b ∈ d := h ▸ he₂inc.2
    exact branch_edge_avoids_other_branchVertex hDbranch hDfrom hdD hbV
      hbb₂ hbb₃ hbd
  have ha₁ne₂ : a₁ ≠ e₂ := by
    intro h
    exact (Set.disjoint_left.mp hX₁X₂ ha₁.2) (h ▸ he₂X₂)
  have he₂atb₂ : e₂ ∈ incidentEdges H b₂ := by
    refine ⟨he₂inc.1, ?_⟩
    rw [he₂eq]
    simp
  have ha₁atb₂ : a₁ ∈ incidentEdges H b₂ := by
    refine ⟨ha₁.1.1, ?_⟩
    rw [ha₁eq]
    simp
  have hchoice₂ :
      BranchChoice G H K φ Y y₁ y₂ b₂ a₁ e₂ d C₁ C₂ D b₁ b b₃ := by
    exact ⟨hb₂V,
      ⟨a₁, ha₁atb₂, e₂, he₂atb₂, ha₁ne₂,
        Set.disjoint_right.mp hXX₁ ha₁.2, Set.disjoint_right.mp hXX₂ he₂X₂⟩,
      ha₁atb₂, ha₁.2, he₂atb₂, he₂X₂, hdinc, hdne₁, hdne₂,
      hC₁branch, ha₁C₁, hC₁from, hC₂branch, he₂C₂, hC₂from,
      hDbranch, hdD, hDfrom⟩
  have hleD := hmax b₂ a₁ e₂ d C₁ C₂ D b₁ b b₃ hchoice₂
  rw [hB₃one] at hleD
  omega

/-- **6.1(11)** *"For `i = 1, 2` there is an edge `fᵢ ∈ X` incident with `bᵢ` that does not meet
`e₃`."* -/
theorem thm_6_1_claim_11
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hmax : BranchChoiceMaximal G H K φ Y y₁ y₂ B₃) :
    (∃ f₁ ∈ completeEdges G H K φ Y, b₁ ∈ f₁ ∧ ¬ MeetEdges f₁ e₃) ∧
      (∃ f₂ ∈ completeEdges G H K φ Y, b₂ ∈ f₂ ∧ ¬ MeetEdges f₂ e₃) := by
  classical
  refine ⟨claim11_one G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
    y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc hmax, ?_⟩
  have hQrev : IsAntipathFrom G Q.reverse y₂ y₁ :=
    Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ
  have hQYrev : ∀ v : V, v ∈ Q.reverse ↔ v ∈ Y := by
    intro v
    simpa using hQY v
  have hQevenrev : Even (pathLength Q.reverse) := by
    simpa only [Workspace.ProofLemmas.PathBasics.pathLength_reverse] using hQeven
  have h8swap : Claim8 G H K φ Y y₂ y₁ := by
    intro a₂ a₁ ha₂ ha₁
    have hm := h8 a₁ a₂ ha₁ ha₂
    simpa only [MeetEdges, DisjointEdges, and_comm] using hm
  have h9swap : Claim9 G H K φ Y y₂ y₁ := by
    intro Y' hY' P hP hlen heven hfirst hlast hint f hf
    apply h9 Y' _ P hP hlen heven hfirst hlast hint f hf
    rcases hY' with rfl | hY' | hY'
    · exact Or.inl rfl
    · exact Or.inr (Or.inr hY')
    · exact Or.inr (Or.inl hY')
  have hbcswap :
      BranchChoice G H K φ Y y₂ y₁ b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ := by
    rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
    exact ⟨hbV, hnon, he₂inc, he₂X₂, he₁inc, he₁X₁, he₃inc,
      he₃e₂, he₃e₁, hB₂, he₂B₂, hfrom₂, hB₁, he₁B₁, hfrom₁,
      hB₃, he₃B₃, hfrom₃⟩
  have hmaxswap : BranchChoiceMaximal G H K φ Y y₂ y₁ B₃ := by
    intro b' e₂' e₁' e₃' B₂' B₁' B₃' b₂' b₁' b₃' hchoice
    apply hmax b' e₁' e₂' e₃' B₁' B₂' B₃' b₁' b₂' b₃'
    rcases hchoice with ⟨hbV, hnon, he₂inc, he₂X₂, he₁inc, he₁X₁, he₃inc,
      he₃e₂, he₃e₁, hB₂, he₂B₂, hfrom₂, hB₁, he₁B₁, hfrom₁,
      hB₃, he₃B₃, hfrom₃⟩
    exact ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
      he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
      hB₃, he₃B₃, hfrom₃⟩
  exact claim11_one G hG m J hJ n H K hsub φ Y hYanti hYmajor hnotsat hmin
    y₂ y₁ Q.reverse hQrev hQYrev hy.symm hQevenrev h8swap h9swap h10
    b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ hbcswap hmaxswap

/-- **6.1(12)** *"If there exist `f₁, f₂` as in (11) with `f₁, f₂ ≠ b₁b₂` then the theorem
holds."* -/
theorem thm_6_1_claim_12
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hmax : BranchChoiceMaximal G H K φ Y y₁ y₂ B₃)
    (f₁ f₂ : Sym2 (Fin n))
    (hf₁X : f₁ ∈ completeEdges G H K φ Y) (hf₁b : b₁ ∈ f₁) (hf₁e : ¬ MeetEdges f₁ e₃)
    (hf₂X : f₂ ∈ completeEdges G H K φ Y) (hf₂b : b₂ ∈ f₂) (hf₂e : ¬ MeetEdges f₂ e₃)
    (hf₁ne : f₁ ≠ s(b₁, b₂)) (hf₂ne : f₂ ≠ s(b₁, b₂)) :
    Thm61Concl G m J n H K φ Y := by
  classical
  obtain ⟨d₁, d₂, u, v, hd₁, hd₁X, hd₂, hd₂X, hf₁eq, hf₂eq,
      hd₁eq, hd₂eq, hu₁, hu₂, hv₁, hv₂, huv, hvdeg⟩ :=
    claim12_cross_skeleton_and_degree G m J hJ n H K hsub φ Y hmin y₁ y₂ Q
      hQ hQY hy h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂
      hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
  by_cases hvb₃ : v = b₃
  · exact claim12_v_eq_b3_conclusion G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃
      b₁ b₂ b₃ hbc f₁ f₂ d₁ d₂ u v hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e
      hf₁ne hf₂ne hd₁ hd₁X hd₂ hd₂X hf₁eq hf₂eq hd₁eq hd₂eq hu₁ hu₂ hv₁
      hv₂ huv hvdeg hvb₃
  · rcases hvdeg with hvdeg | hvdeg
    · exact claim12_degree_two_conclusion G m J hJ n H K hsub φ Y hYmajor hmin
        y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃
        hbc f₁ f₂ d₁ d₂ u v hf₁X hf₁b hf₁e hf₂X hf₂b hf₂e hf₁ne hf₂ne
        hd₁ hd₁X hd₂ hd₂X hf₁eq hf₂eq hd₁eq hd₂eq hu₁ hu₂ hv₁ hv₂ huv hvdeg
    · exact claim12_degree_three_conclusion G hG m J hJ n H K hsub φ Y hYanti
        hYmajor hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃
        B₁ B₂ B₃ b₁ b₂ b₃ hbc f₁ f₂ d₁ d₂ u v hf₁X hf₁b hf₁e hf₂X hf₂b
        hf₂e hf₁ne hf₂ne hd₁ hd₁X hd₂ hd₂X hf₁eq hf₂eq hd₁eq hd₂eq hu₁ hu₂
        hv₁ hv₂ huv hvb₃ hvdeg

/-- **Exactly one of `B₁`, `B₂` is even, once `b₁b₂` is an edge.**

This is what licenses the unargued *"From the symmetry we may assume that `B₁` is even and `B₂`
is odd"* of the paragraph following (12).  `B₁`, followed by the edge `b₁b₂`, followed by the
reverse of `B₂`, is a cycle of `H` through `b` of length `trackLength B₁ + trackLength B₂ + 1`;
since `H` is bipartite that length is even, so `trackLength B₁ + trackLength B₂` is odd. -/
theorem branch_parity
    {V : Type*} (G : SimpleGraph V)
    (m : ℕ) (J : SimpleGraph (Fin m))
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (y₁ y₂ : V)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hadj : H.Adj b₁ b₂) :
    (Even (trackLength B₁) ∧ Odd (trackLength B₂)) ∨
      (Odd (trackLength B₁) ∧ Even (trackLength B₂)) := by
  classical
  rcases hbc with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hfrom₁, _, _, hfrom₂, _, _, _⟩
  obtain ⟨col⟩ :=
    BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hsub.2
  have hcolne : col b₁ ≠ col b₂ := col.valid hadj
  have hpar₁ : Even (trackLength B₁) ↔ col b = col b₁ :=
    BipartiteClosedWalkEven.even_trackLength_iff col hfrom₁
  have hpar₂ : Even (trackLength B₂) ↔ col b = col b₂ :=
    BipartiteClosedWalkEven.even_trackLength_iff col hfrom₂
  rcases Nat.even_or_odd (trackLength B₁) with heven₁ | hodd₁
  · refine Or.inl ⟨heven₁, Nat.not_even_iff_odd.mp ?_⟩
    intro heven₂
    exact hcolne ((hpar₁.mp heven₁).symm.trans (hpar₂.mp heven₂))
  · refine Or.inr ⟨hodd₁, hpar₂.mpr ?_⟩
    have hcol₁ : col b ≠ col b₁ := fun heq =>
      (Nat.not_even_iff_odd.mpr hodd₁) (hpar₁.mpr heq)
    cases hb : col b <;> cases hb₁ : col b₁ <;> cases hb₂ : col b₂ <;>
      simp_all

/-- **6.1, even case: the bridging paragraph, claim (13) and the closing paragraph.**

> *"From (11) and (12) we may therefore assume that `b₁, b₂` are adjacent, and the edge
> `b₁b₂ ∈ X`.  From the symmetry we may assume that `B₁` is even and `B₂` is odd.  Let `T` be
> the track formed by `B₁` and the edges `e₃, b₁b₂` …"*

and everything down to *"But then the fourth outcome of the theorem holds.  This proves 6.1."*

The *"from the symmetry"* reduction is internal to this statement: exchanging the indices `1, 2`
exchanges `y₁, y₂` (reverse the antipath `Q`), `e₁, e₂`, `X₁, X₂`, `B₁, B₂` and `b₁, b₂`, and
`BranchChoice`, `BranchChoiceMaximal`, `Claim8` and `Claim9` are all invariant under that
exchange, while `Claim10` and the conclusion do not mention the indices at all.  `branch_parity`
supplies the parity dichotomy the symmetry is applied to. -/
theorem thm_6_1_even_final
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hG : Berge G)
    (m : ℕ) (J : SimpleGraph (Fin m)) (hJ : IsKConnected J 3)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (hsub : IsBipartiteSubdivision J H)
    (φ : H.lineGraph ≃g G.induce K)
    (Y : Set V) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForLineGraph G H K φ y)
    (hnotsat : ¬ SaturatesLineGraph H (completeEdges G H K φ Y))
    (hmin : ∀ Y₁ : Set V, Y₁ ⊂ Y → AnticonnectedSet G Y₁ →
      SaturatesLineGraph H (completeEdges G H K φ Y₁))
    (y₁ y₂ : V) (Q : List V) (hQ : IsAntipathFrom G Q y₁ y₂)
    (hQY : ∀ v : V, v ∈ Q ↔ v ∈ Y) (hy : y₁ ≠ y₂)
    (hQeven : Even (pathLength Q))
    (h8 : Claim8 G H K φ Y y₁ y₂)
    (h9 : Claim9 G H K φ Y y₁ y₂)
    (h10 : Claim10 G H K φ Y)
    (b : Fin n) (e₁ e₂ e₃ : Sym2 (Fin n)) (B₁ B₂ B₃ : List (Fin n)) (b₁ b₂ b₃ : Fin n)
    (hbc : BranchChoice G H K φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃ b₁ b₂ b₃)
    (hmax : BranchChoiceMaximal G H K φ Y y₁ y₂ B₃)
    (hadj : H.Adj b₁ b₂)
    (hXb : s(b₁, b₂) ∈ completeEdges G H K φ Y) :
    Thm61Concl G m J n H K φ Y := by
  classical
  rcases branch_parity G m J n H K hsub φ Y y₁ y₂ b e₁ e₂ e₃ B₁ B₂ B₃
      b₁ b₂ b₃ hbc hadj with hpar | hpar
  · exact even_final_oriented G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₁ y₂ Q hQ hQY hy hQeven h8 h9 h10 b e₁ e₂ e₃ B₁ B₂ B₃
      b₁ b₂ b₃ hbc hadj hXb hpar.1 hpar.2
  · have hQrev : IsAntipathFrom G Q.reverse y₂ y₁ :=
      Workspace.ProofLemmas.PathBasics.isAntipathFrom_reverse hQ
    have hQYrev : ∀ v : V, v ∈ Q.reverse ↔ v ∈ Y := by
      intro v
      simpa using hQY v
    have hQevenrev : Even (pathLength Q.reverse) := by
      simpa only [Workspace.ProofLemmas.PathBasics.pathLength_reverse] using hQeven
    have h8swap : Claim8 G H K φ Y y₂ y₁ := by
      intro a₂ a₁ ha₂ ha₁
      have hm := h8 a₁ a₂ ha₁ ha₂
      simpa only [MeetEdges, DisjointEdges, and_comm] using hm
    have h9swap : Claim9 G H K φ Y y₂ y₁ := by
      intro Y' hY' P hP hlen heven hfirst hlast hint f hf
      apply h9 Y' _ P hP hlen heven hfirst hlast hint f hf
      rcases hY' with rfl | hY' | hY'
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hY')
      · exact Or.inr (Or.inl hY')
    have hbcswap :
        BranchChoice G H K φ Y y₂ y₁ b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ := by
      rcases hbc with ⟨hbV, hnon, he₁inc, he₁X₁, he₂inc, he₂X₂, he₃inc,
        he₃e₁, he₃e₂, hB₁, he₁B₁, hfrom₁, hB₂, he₂B₂, hfrom₂,
        hB₃, he₃B₃, hfrom₃⟩
      exact ⟨hbV, hnon, he₂inc, he₂X₂, he₁inc, he₁X₁, he₃inc,
        he₃e₂, he₃e₁, hB₂, he₂B₂, hfrom₂, hB₁, he₁B₁, hfrom₁,
        hB₃, he₃B₃, hfrom₃⟩
    have hXbswap : s(b₂, b₁) ∈ completeEdges G H K φ Y := by
      simpa only [Sym2.eq_swap] using hXb
    exact even_final_oriented G hG m J hJ n H K hsub φ Y hYanti hYmajor
      hnotsat hmin y₂ y₁ Q.reverse hQrev hQYrev hy.symm hQevenrev h8swap h9swap
      h10 b e₂ e₁ e₃ B₂ B₁ B₃ b₂ b₁ b₃ hbcswap hadj.symm hXbswap hpar.2 hpar.1

end Workspace.ProofLemmas.Thm61EvenEndgameSteps
