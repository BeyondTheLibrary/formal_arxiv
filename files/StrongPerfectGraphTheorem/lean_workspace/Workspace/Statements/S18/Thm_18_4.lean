/-  Proof attempt for statement 18.4 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    THE PAPER'S PROOF (printed p. 111):

      "By 18.3, P contains an odd number of Y-complete edges, since an odd number of ends of
       P are Y-complete.  Suppose it only contains one, say p_i p_{i+1}.  Since p_2, p_n are
       not Y-complete it follows that 3 <= i <= n-2.  So there is an antipath joining
       p_i, p_{i+1} with interior in X, and by 15.4 applied to the path P, this antipath has
       length 2, that is, there exists x in X nonadjacent to both p_i, p_{i+1}.  Let C be a
       hole containing x, p_i, p_{i+1} and with C \ x contained in P.  Then (C,Y) is an odd
       wheel, since C contains the Y-complete vertices x, p_i, p_{i+1} and it also contains
       p_{i-1}, p_{i+2} which are not Y-complete, contrary to G in F7.  So at least three
       edges of P are Y-complete, and therefore P has length >= 6.  This proves 18.4."

    Two steps are compressed in the printed text; see AMBIGUITIES.md A28 and A28a.

    * 15.4 is used CONTRAPOSITIVELY: it concludes `Even n and m = 4`, and a pseudowheel's
      path has `m >= 5`, so no antipath with `n >= 2` interior vertices exists; `n >= 1`
      because `p_i, p_{i+1}` are adjacent in `G`.  Hence `n = 1`.
    * "(C,Y) is an odd wheel, since C contains the Y-complete vertices x, p_i, p_{i+1}" is an
      invocation of 2.3: `IsWheel` needs two DISJOINT Y-complete edges and only `p_i p_{i+1}`
      is visible (`x` is nonadjacent to both).  2.3's hole clause says the number of
      Y-complete edges of a hole is even unless there are exactly two Y-complete vertices and
      they are adjacent; three pairwise-nonadjacent ones kill that, so the count is even, so a
      second edge exists -- and it must be `x p_a` or `x p_b`, disjoint from `p_i p_{i+1}`.

    Indices below are 0-based, so the paper's `p_i` is `P[i-1]`; the `i` below is the paper's
    `i - 1`, and the paper's `3 <= i <= n-2` reads `2 <= i` and `i + 3 <= P.length`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Decompositions
import Workspace.Types.LongOddPrism
import Workspace.Types.Classes
import Workspace.Types.Wheels
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S15.Thm_15_4
import Workspace.Statements.S18.Thm_18_3
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleThroughGap
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.SegmentBasics

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000

namespace Workspace.Statements.S18

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

namespace SPGT

/-! ### Helper lemmas -/

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- Two adjacent vertices of an induced path occupy consecutive positions. -/
private theorem edge_index {W : Type*} {G : SimpleGraph W} {P : List W} (hP : IsPathList G P)
    {u v : W} (hu : u ∈ P) (hv : v ∈ P) (hadj : G.Adj u v) :
    ∃ (k : ℕ) (hk : k + 1 < P.length),
      (P[k]'(by omega) = u ∧ P[k + 1]'hk = v) ∨ (P[k]'(by omega) = v ∧ P[k + 1]'hk = u) := by
  obtain ⟨j, hj, hju⟩ := List.getElem_of_mem hu
  obtain ⟨j', hj', hjv⟩ := List.getElem_of_mem hv
  have h : j + 1 = j' ∨ j' + 1 = j :=
    (PathBasics.path_adj_iff hP hj hj').mp (by rw [hju, hjv]; exact hadj)
  rcases h with h | h
  · refine ⟨j, by omega, Or.inl ⟨hju, ?_⟩⟩
    rw [gidx P h (by omega) hj']
    exact hjv
  · refine ⟨j', by omega, Or.inr ⟨hjv, ?_⟩⟩
    rw [gidx P h (by omega) hj]
    exact hju

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **18.4** (printed p. 111).

PAPER: *"Let `(X,Y,P)` be a pseudowheel in a graph `G ∈ F₇`, where `P` is
`p₁`-`⋯`-`pₙ`.  Then `P` contains an odd number, at least `3`, of `Y`-complete
edges, and `P` has length `≥ 6`."* -/
theorem thm_18_4 (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V) (P : List V)
    (hpw : IsPseudowheel G X Y P) :
    (Odd {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard ∧
      3 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard) ∧
    6 ≤ pathLength P := by
  classical
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, p₁, p₂, pₙ,
    ⟨hPfrom, hp₂h, hPXY, hPlen⟩, hXuniq, hp₁Y, hother, hp₂Y, hpₙY⟩ := hpw
  have hP : IsPathList G P := hPfrom.1
  have hBerge : Berge G := hG.1.1.1.1
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hp₁eq : P[0]'(by omega) = p₁ :=
    PathBasics.getElem_zero_of_head? hPfrom.2.1 (by omega)
  have hpₙeq : P[P.length - 1]'(by omega) = pₙ :=
    PathBasics.getElem_last_of_getLast? hPfrom.2.2 (by omega)
  have hp₂eq : P[1]'(by omega) = p₂ := by
    have h := hp₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hPX : ∀ w ∈ P, w ∉ X := fun w hw => (hPXY w hw).1
  have hPY : ∀ w ∈ P, w ∉ Y := fun w hw => (hPXY w hw).2
  have hp₁mem : p₁ ∈ P := hp₁eq ▸ List.getElem_mem _
  have hpₙmem : pₙ ∈ P := hpₙeq ▸ List.getElem_mem _
  -- decoding membership of the `Y`-complete-edge set of `P`
  have hmemYE : ∀ e : Sym2 V,
      (e ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v}) ↔
      ∃ (k : ℕ) (hk : k + 1 < P.length), e = s(P[k]'(by omega), P[k + 1]'hk) ∧
        VertexComplete G (P[k]'(by omega)) Y ∧ VertexComplete G (P[k + 1]'hk) Y := by
    intro e
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hadj, huY, hvY⟩
      obtain ⟨k, hk, hcase⟩ := edge_index hP hu hv hadj
      rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨k, hk, by rw [e1, e2], by rw [e1]; exact huY, by rw [e2]; exact hvY⟩
      · exact ⟨k, hk, by rw [e1, e2, Sym2.eq_swap], by rw [e1]; exact hvY,
          by rw [e2]; exact huY⟩
    · rintro ⟨k, hk, rfl, h1, h2⟩
      exact ⟨_, List.getElem_mem _, _, List.getElem_mem _, rfl,
        PathBasics.path_adj_succ hP hk, h1, h2⟩
  -- every `Y`-complete edge sits strictly inside `P`
  have hrange : ∀ (k : ℕ) (hk : k + 1 < P.length),
      VertexComplete G (P[k]'(by omega)) Y → VertexComplete G (P[k + 1]'hk) Y →
      2 ≤ k ∧ k + 3 ≤ P.length := by
    intro k hk h1 h2
    constructor
    · by_contra hcon
      interval_cases k
      · exact hp₂Y (by rw [← hp₂eq]; exact h2)
      · exact hp₂Y (by rw [← hp₂eq]; exact h1)
    · by_contra hcon
      have hik : k + 1 = P.length - 1 := by omega
      exact hpₙY (by rw [← hpₙeq, ← gidx P hik hk (by omega)]; exact h2)
  -- ### Part 1: an odd number of `Y`-complete edges, by 18.3
  have h183 := thm_18_3 G hG X Y hXY hXne hYne hXanti hYanti hcompl P p₁ pₙ hP
    (fun w hw => by
      rintro (h | h)
      · exact hPX w hw h
      · exact hPY w hw h)
    hPlen hPfrom.2.1 hPfrom.2.2 hXuniq
  have h2vert : 2 ≤ {w : V | w ∈ P ∧ VertexComplete G w Y}.ncard := by
    obtain ⟨v, hvP, hvne, hvY⟩ := hother
    exact (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨p₁, ⟨hp₁mem, hp₁Y⟩, v, ⟨hvP, hvY⟩, fun h => hvne h.symm⟩
  have hendset : {w : V | (w = p₁ ∨ w = pₙ) ∧ VertexComplete G w Y} = {p₁} := by
    ext w
    constructor
    · rintro ⟨h | h, hY⟩
      · exact h
      · exact absurd (h ▸ hY) hpₙY
    · rintro rfl
      exact ⟨Or.inl rfl, hp₁Y⟩
  have hodd : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
      e = s(u, v) ∧ EdgeComplete G Y u v}.ncard % 2 = 1 := by
    have h := (h183.2 h2vert).2
    rw [hendset, Set.ncard_singleton] at h
    exact h
  -- ### Part 2: at least three, by the odd-wheel argument
  have h3 : 3 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
      e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := by
    by_contra hlt
    have hone : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
        e = s(u, v) ∧ EdgeComplete G Y u v}.ncard = 1 := by omega
    obtain ⟨e₀, he₀⟩ := Set.ncard_eq_one.mp hone
    have he₀mem : e₀ ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
        e = s(u, v) ∧ EdgeComplete G Y u v} := by rw [he₀]; rfl
    obtain ⟨i, hi, -, hPiY, hPi1Y⟩ := (hmemYE e₀).mp he₀mem
    obtain ⟨hi2, hi3⟩ := hrange i hi hPiY hPi1Y
    -- uniqueness of the index
    have huniq : ∀ (k : ℕ) (hk : k + 1 < P.length),
        VertexComplete G (P[k]'(by omega)) Y → VertexComplete G (P[k + 1]'hk) Y → k = i := by
      intro k hk h1 h2
      have hk' : s(P[k]'(by omega), P[k + 1]'hk) ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
          e = s(u, v) ∧ EdgeComplete G Y u v} := (hmemYE _).mpr ⟨k, hk, rfl, h1, h2⟩
      have hi' : s(P[i]'(by omega), P[i + 1]'hi) ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P,
          e = s(u, v) ∧ EdgeComplete G Y u v} := (hmemYE _).mpr ⟨i, hi, rfl, hPiY, hPi1Y⟩
      rw [he₀, Set.mem_singleton_iff] at hk' hi'
      have heq : s(P[k]'(by omega), P[k + 1]'hk) = s(P[i]'(by omega), P[i + 1]'hi) := by
        rw [hk', hi']
      rcases Sym2.eq_iff.mp heq with ⟨q1, -⟩ | ⟨q1, q2⟩
      · exact (List.Nodup.getElem_inj_iff hnd).mp q1
      · have r1 := (List.Nodup.getElem_inj_iff hnd).mp q1
        have r2 := (List.Nodup.getElem_inj_iff hnd).mp q2
        omega
    -- neither `P[i]` nor `P[i+1]` is `X`-complete
    have hnotX : ∀ (k : ℕ) (hk : k < P.length), 1 ≤ k → k + 2 ≤ P.length →
        ∃ z ∈ X, ¬ G.Adj (P[k]'hk) z := by
      intro k hk h1 h2
      by_contra hcon
      simp only [not_exists, not_and, not_not] at hcon
      have hc : VertexComplete G (P[k]'hk) X := fun z hz => hcon z hz
      rcases (hXuniq _ (List.getElem_mem hk)).mp hc with h | h
      · rw [← hp₁eq] at h
        have := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
      · rw [← hpₙeq] at h
        have := (List.Nodup.getElem_inj_iff hnd).mp h
        omega
    obtain ⟨z₁, hz₁X, hz₁⟩ := hnotX i (by omega) (by omega) (by omega)
    obtain ⟨z₂, hz₂X, hz₂⟩ := hnotX (i + 1) hi (by omega) (by omega)
    -- the antipath, and 15.4 used contrapositively (AMBIGUITIES A28a)
    obtain ⟨q, hq, hqint⟩ := InducedPathExtraction.exists_antipath_interior_in hXanti
      (hPX _ (List.getElem_mem (show i < P.length by omega)))
      (hPX _ (List.getElem_mem hi)) ⟨z₁, hz₁X, hz₁⟩ ⟨z₂, hz₂X, hz₂⟩
    have hq1 : 0 < q.length := PathBasics.path_length_pos hq.1
    have hqlen3 : 3 ≤ q.length := by
      rcases (show q.length = 1 ∨ q.length = 2 ∨ 3 ≤ q.length by omega) with h | h | h
      · exfalso
        obtain ⟨w, hw⟩ := List.length_eq_one_iff.mp h
        rw [hw] at hq
        have e1 : P[i]'(by omega) = w := (by simpa using hq.2.1 : w = P[i]'(by omega)).symm
        have e2 : P[i + 1]'hi = w := (by simpa using hq.2.2 : w = P[i + 1]'hi).symm
        exact PathBasics.path_ne_of_ne_index hP (by omega) hi (by omega) (e1.trans e2.symm)
      · exfalso
        obtain ⟨u, v, hw⟩ := PrismBasics.length_eq_two h
        have hadj : Gᶜ.Adj (q[0]'(by omega)) (q[1]'(by omega)) :=
          PathBasics.path_adj_succ hq.1 (show 0 + 1 < q.length by omega)
        have e1 : q[0]'(by omega) = P[i]'(by omega) := by
          have := hq.2.1
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < q.length by omega)] at this
          exact (Option.some_injective _ this)
        have e2 : q[1]'(by omega) = P[i + 1]'hi := by
          have := hq.2.2
          rw [List.getLast?_eq_getElem?, show q.length - 1 = 1 from by omega,
            List.getElem?_eq_getElem (show 1 < q.length by omega)] at this
          exact (Option.some_injective _ this)
        rw [e1, e2] at hadj
        exact hadj.2 (PathBasics.path_adj_succ hP hi)
      · exact h
    have hq3 : q.length = 3 := by
      by_contra hcon
      have hn2 : 2 ≤ q.length - 2 := by omega
      have h154 := _root_.Workspace.Statements.S15.SPGT.thm_15_4 G hG.1 P P.length hP rfl
        (i + 1) (by omega) (by omega)
        q (q.length - 2) (by omega) hn2
        (by
          have e1 : P[i + 1 - 1]'(by omega) = P[i]'(by omega) :=
            gidx P (by omega) (by omega) (by omega)
          have e2 : P[i + 1]'(by omega) = P[i + 1]'hi := rfl
          rw [e1, e2]
          exact hq)
        (by
          intro z hz
          have hzX : z ∈ X := hqint z hz
          refine ⟨?_, ?_⟩
          · rw [hp₁eq]
            exact (hXuniq p₁ hp₁mem).mpr (Or.inl rfl) z hzX
          · rw [hpₙeq]
            exact (hXuniq pₙ hpₙmem).mpr (Or.inr rfl) z hzX)
      omega
    -- the single interior vertex `x`
    obtain ⟨u₀, x, v₀, hqeq⟩ := PrismBasics.length_eq_three hq3
    have hxint : x ∈ SPGT.interior q := by
      rw [hqeq]; simp [SPGT.interior]
    have hxX : x ∈ X := hqint x hxint
    have hxi : ¬ G.Adj x (P[i]'(by omega)) := by
      have hadj : Gᶜ.Adj (q[0]'(by omega)) (q[1]'(by omega)) :=
        PathBasics.path_adj_succ hq.1 (show 0 + 1 < q.length by omega)
      have e1 : q[0]'(by omega) = P[i]'(by omega) := by
        have := hq.2.1
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < q.length by omega)] at this
        exact (Option.some_injective _ this)
      have e2 : q[1]'(by omega) = x := by
        have h1 : q[1]? = some x := by rw [hqeq]; rfl
        rw [List.getElem?_eq_getElem (show 1 < q.length by omega)] at h1
        exact Option.some_injective _ h1
      rw [e1, e2] at hadj
      exact fun h => hadj.2 h.symm
    have hxi1 : ¬ G.Adj x (P[i + 1]'hi) := by
      have hadj : Gᶜ.Adj (q[1]'(by omega)) (q[2]'(by omega)) :=
        PathBasics.path_adj_succ hq.1 (show 1 + 1 < q.length by omega)
      have e1 : q[1]'(by omega) = x := by
        have h1 : q[1]? = some x := by rw [hqeq]; rfl
        rw [List.getElem?_eq_getElem (show 1 < q.length by omega)] at h1
        exact Option.some_injective _ h1
      have e2 : q[2]'(by omega) = P[i + 1]'hi := by
        have := hq.2.2
        rw [List.getLast?_eq_getElem?, show q.length - 1 = 2 from by omega,
          List.getElem?_eq_getElem (show 2 < q.length by omega)] at this
        exact (Option.some_injective _ this)
      rw [e1, e2] at hadj
      exact hadj.2
    have hxP : x ∉ P := fun h => hPX x h hxX
    have hxne : ∀ (k : ℕ) (hk : k < P.length), x ≠ P[k]'hk :=
      fun k hk h => hxP (h ▸ List.getElem_mem hk)
    -- the hole `C = x :: (stretch of P)`
    have hxp₁ : G.Adj x (P[0]'(by omega)) := by
      rw [hp₁eq]
      exact ((hXuniq p₁ hp₁mem).mpr (Or.inl rfl) x hxX).symm
    have hxpₙ : G.Adj x (P[P.length - 1]'(by omega)) := by
      rw [hpₙeq]
      exact ((hXuniq pₙ hpₙmem).mpr (Or.inr rfl) x hxX).symm
    obtain ⟨a, b, ha, hbgap, hblen, hxa, hxb, hnone, hC, hClen⟩ :=
      HoleThroughGap.exists_hole_through_gap hP hxP hi hxi hxi1 (a₀ := 0) (by omega) hxp₁
        (b₀ := P.length - 1) (by omega) (by omega) hxpₙ
    have hxY : VertexComplete G x Y := hcompl x hxX
    have hxnotY : x ∉ Y := fun h => (Set.disjoint_left.mp hXY hxX) h
    have hSllen : ((P.drop a).take (b - a + 1)).length = b - a + 1 :=
      PathBasics.length_slice P (by omega) hblen
    have hCl : (x :: (P.drop a).take (b - a + 1)).length = b - a + 2 := by
      simp only [List.length_cons, hSllen]
    have hCmem : ∀ y : V, y ∈ (x :: (P.drop a).take (b - a + 1)) ↔
        (y = x ∨ ∃ (k : ℕ) (hk : k < P.length), a ≤ k ∧ k ≤ b ∧ P[k]'hk = y) := by
      intro y
      rw [List.mem_cons, PathBasics.mem_slice_iff P (by omega) hblen]
    have hCnotY : ∀ w ∈ (x :: (P.drop a).take (b - a + 1)), w ∉ Y := by
      intro w hw
      rcases (hCmem w).mp hw with rfl | ⟨k, hk, -, -, rfl⟩
      · exact hxnotY
      · exact hPY _ (List.getElem_mem hk)
    have hCget : ∀ (k : ℕ) (hk : k < P.length), a ≤ k → k ≤ b →
        (x :: (P.drop a).take (b - a + 1))[(k - a) + 1]? = some (P[k]'hk) := by
      intro k hk h1 h2
      have hlt : (k - a) + 1 < (x :: (P.drop a).take (b - a + 1)).length := by
        rw [hCl]; omega
      rw [List.getElem?_eq_getElem hlt]
      congr 1
      show ((P.drop a).take (b - a + 1))[k - a]'(by omega) = P[k]'hk
      exact PathBasics.getElem_slice' P (by omega) hk (by omega)
    have hCmemPi : P[i]'(by omega) ∈ (x :: (P.drop a).take (b - a + 1)) :=
      (hCmem _).mpr (Or.inr ⟨i, by omega, by omega, by omega, rfl⟩)
    have hCmemPi1 : P[i + 1]'hi ∈ (x :: (P.drop a).take (b - a + 1)) :=
      (hCmem _).mpr (Or.inr ⟨i + 1, hi, by omega, by omega, rfl⟩)
    have hCmemx : x ∈ (x :: (P.drop a).take (b - a + 1)) := List.mem_cons_self
    have hPiPi1 : P[i]'(by omega) ≠ P[i + 1]'hi :=
      PathBasics.path_ne_of_ne_index hP (by omega) hi (by omega)
    -- 2.3 supplies a second `Y`-complete edge (AMBIGUITIES A28)
    have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti (x :: (P.drop a).take (b - a + 1))
      (Or.inr hC) hCnotY).2 hC
    have hnotpair : ¬ ∃ c d : V, {w : V | w ∈ (x :: (P.drop a).take (b - a + 1)) ∧
        VertexComplete G w Y} = {c, d} ∧ c ≠ d ∧ G.Adj c d := by
      rintro ⟨c, d, hset, -, -⟩
      have m1 : x ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hCmemx, hxY⟩
      have m2 : P[i]'(by omega) ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hCmemPi, hPiY⟩
      have m3 : P[i + 1]'hi ∈ ({c, d} : Set V) := by rw [← hset]; exact ⟨hCmemPi1, hPi1Y⟩
      have hne1 : x ≠ P[i]'(by omega) := hxne _ _
      have hne2 : x ≠ P[i + 1]'hi := hxne _ _
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at m1 m2 m3
      rcases m1 with rfl | rfl <;> rcases m2 with h2 | h2 <;> rcases m3 with h3 | h3 <;>
        simp_all
    have heven := h23.resolve_right hnotpair
    have hmemedge : s(P[i]'(by omega), P[i + 1]'hi) ∈
        {e : Sym2 V | ∃ u ∈ (x :: (P.drop a).take (b - a + 1)),
          ∃ v ∈ (x :: (P.drop a).take (b - a + 1)),
          e = s(u, v) ∧ EdgeComplete G Y u v} :=
      ⟨_, hCmemPi, _, hCmemPi1, rfl, PathBasics.path_adj_succ hP hi, hPiY, hPi1Y⟩
    have hposC : 0 < {e : Sym2 V | ∃ u ∈ (x :: (P.drop a).take (b - a + 1)),
        ∃ v ∈ (x :: (P.drop a).take (b - a + 1)),
        e = s(u, v) ∧ EdgeComplete G Y u v}.ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨_, hmemedge⟩
    obtain ⟨n2, hn2⟩ := heven
    have h1lt : 1 < {e : Sym2 V | ∃ u ∈ (x :: (P.drop a).take (b - a + 1)),
        ∃ v ∈ (x :: (P.drop a).take (b - a + 1)),
        e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := by omega
    obtain ⟨e₁, he₁, e₂, he₂, hne₁₂⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp h1lt
    obtain ⟨e', he', hne'⟩ : ∃ e ∈ {e : Sym2 V | ∃ u ∈ (x :: (P.drop a).take (b - a + 1)),
        ∃ v ∈ (x :: (P.drop a).take (b - a + 1)),
        e = s(u, v) ∧ EdgeComplete G Y u v}, e ≠ s(P[i]'(by omega), P[i + 1]'hi) := by
      by_cases h : e₁ = s(P[i]'(by omega), P[i + 1]'hi)
      · exact ⟨e₂, he₂, fun hc => hne₁₂ (h.trans hc.symm)⟩
      · exact ⟨e₁, he₁, h⟩
    obtain ⟨u', hu'C, v', hv'C, rfl, hadj', hu'Y, hv'Y⟩ := he'
    -- the second edge is incident with `x`, hence disjoint from `s(P[i], P[i+1])`
    have honP : ∀ w : V, w ∈ (x :: (P.drop a).take (b - a + 1)) → w ≠ x →
        ∃ (k : ℕ) (hk : k < P.length), a ≤ k ∧ k ≤ b ∧ P[k]'hk = w := by
      intro w hw hwx
      rcases (hCmem w).mp hw with rfl | h
      · exact absurd rfl hwx
      · exact h
    have hdisj : u' ≠ P[i]'(by omega) ∧ u' ≠ P[i + 1]'hi ∧
        v' ≠ P[i]'(by omega) ∧ v' ≠ P[i + 1]'hi := by
      by_cases hux : u' = x
      · subst hux
        obtain ⟨k, hk, hk1, hk2, rfl⟩ := honP v' hv'C (fun h => hadj'.ne h.symm)
        have hkab : k = a ∨ k = b := by
          by_contra hcon
          exact hnone k hk (by omega) (by omega) hadj'
        exact ⟨hxne i (by omega), hxne (i + 1) hi,
          PathBasics.path_ne_of_ne_index hP hk (by omega) (by omega),
          PathBasics.path_ne_of_ne_index hP hk hi (by omega)⟩
      · by_cases hvx : v' = x
        · subst hvx
          obtain ⟨k, hk, hk1, hk2, rfl⟩ := honP u' hu'C hux
          have hkab : k = a ∨ k = b := by
            by_contra hcon
            exact hnone k hk (by omega) (by omega) hadj'.symm
          exact ⟨PathBasics.path_ne_of_ne_index hP hk (by omega) (by omega),
            PathBasics.path_ne_of_ne_index hP hk hi (by omega),
            hxne i (by omega), hxne (i + 1) hi⟩
        · exfalso
          obtain ⟨k, hk, hk1, hk2, rfl⟩ := honP u' hu'C hux
          obtain ⟨k', hk', hk'1, hk'2, rfl⟩ := honP v' hv'C hvx
          have hkk' : k + 1 = k' ∨ k' + 1 = k :=
            (PathBasics.path_adj_iff hP hk hk').mp hadj'
          rcases hkk' with h | h
          · have hklt : k + 1 < P.length := by omega
            have hv'Y' : VertexComplete G (P[k + 1]'hklt) Y := by
              rw [gidx P h hklt hk']; exact hv'Y
            have hki := huniq k hklt hu'Y hv'Y'
            refine hne' ?_
            rw [gidx P h.symm hk' hklt, gidx P hki hk (show i < P.length by omega),
              gidx P (show k + 1 = i + 1 by omega) hklt hi]
          · have hklt : k' + 1 < P.length := by omega
            have hu'Y' : VertexComplete G (P[k' + 1]'hklt) Y := by
              rw [gidx P h hklt hk]; exact hu'Y
            have hki := huniq k' hklt hv'Y hu'Y'
            refine hne' ?_
            rw [gidx P h.symm hk hklt, gidx P hki hk' (show i < P.length by omega),
              gidx P (show k' + 1 = i + 1 by omega) hklt hi]
            exact Sym2.eq_swap
    -- `(C, Y)` is a wheel
    have hwheel : Workspace.Types.Wheels.SPGT.IsWheel G
        (x :: (P.drop a).take (b - a + 1)) Y := by
      refine ⟨⟨hC, ?_⟩, ⟨hYne, hYanti, hCnotY⟩,
        P[i]'(by omega), P[i + 1]'hi, u', v', hCmemPi, hCmemPi1, hu'C, hv'C,
        ⟨PathBasics.path_adj_succ hP hi, hPiY, hPi1Y⟩, ⟨hadj', hu'Y, hv'Y⟩,
        fun h => hdisj.1 h.symm, fun h => hdisj.2.2.1 h.symm,
        fun h => hdisj.2.1 h.symm, fun h => hdisj.2.2.2 h.symm⟩
      have heven2 : Even (holeLength (x :: (P.drop a).take (b - a + 1))) := hBerge.1 _ hC
      obtain ⟨m, hm⟩ := heven2
      omega
    -- the `Y`-segment `P[i]-P[i+1]` has length one, so `(C, Y)` is an *odd* wheel
    have hcyc : ∀ (k : ℕ) (hk : k < P.length), a ≤ k → k ≤ b →
        (SegmentBasics.CycVert G Y (x :: (P.drop a).take (b - a + 1)) ((k - a) + 1) ↔
          VertexComplete G (P[k]'hk) Y) := by
      intro k hk h1 h2
      have hmod : ((k - a) + 1) % (x :: (P.drop a).take (b - a + 1)).length = (k - a) + 1 := by
        rw [hCl]; exact Nat.mod_eq_of_lt (by omega)
      constructor
      · rintro ⟨u, hu1, hu2⟩
        rw [hmod, hCget k hk h1 h2] at hu1
        rw [Option.some_injective _ hu1]
        exact hu2
      · intro h
        exact ⟨P[k]'hk, by rw [hmod]; exact hCget k hk h1 h2, h⟩
    have hoddwheel : Workspace.Types.Wheels.SPGT.IsOddWheel G
        (x :: (P.drop a).take (b - a + 1)) Y := by
      refine ⟨hwheel, ((x :: (P.drop a).take (b - a + 1)).rotate ((i - a) + 1)).take 2, ?_, ?_⟩
      · refine SegmentBasics.isSegment_of_run hC (by omega) (by rw [hCl]; omega) ?_ ?_ ?_
        · intro t ht
          interval_cases t
          · exact (hcyc i (by omega) (by omega) (by omega)).mpr hPiY
          · have he : (i - a) + 1 + 1 = ((i + 1) - a) + 1 := by omega
            rw [he]
            exact (hcyc (i + 1) hi (by omega) (by omega)).mpr hPi1Y
        · intro hcv
          have he : (i - a) + 1 + 2 = ((i + 2) - a) + 1 := by omega
          rw [he] at hcv
          have h2 := (hcyc (i + 2) (by omega) (by omega) (by omega)).mp hcv
          have := huniq (i + 1) (by omega) hPi1Y h2
          omega
        · intro hcv
          have hmodeq : ((i - a) + 1 + ((x :: (P.drop a).take (b - a + 1)).length - 1))
                % (x :: (P.drop a).take (b - a + 1)).length
              = ((i - 1) - a + 1) % (x :: (P.drop a).take (b - a + 1)).length := by
            have he : (i - a) + 1 + ((x :: (P.drop a).take (b - a + 1)).length - 1)
                = ((i - 1) - a + 1) + (x :: (P.drop a).take (b - a + 1)).length := by
              rw [hCl]; omega
            rw [he, Nat.add_mod_right]
          have hcv2 := (SegmentBasics.cycVert_congr hmodeq).mp hcv
          have h2 := (hcyc (i - 1) (by omega) (by omega) (by omega)).mp hcv2
          have hone : (i - 1) + 1 = i := by omega
          have := huniq (i - 1) (by omega) h2 (by rw [gidx P hone (by omega) (by omega)]; exact hPiY)
          omega
      · have hlen2 : (((x :: (P.drop a).take (b - a + 1)).rotate ((i - a) + 1)).take 2).length
            = 2 := by
          rw [List.length_take, List.length_rotate, hCl]
          omega
        rw [pathLength, hlen2]
        exact ⟨0, by omega⟩
    exact hG.2.1 ⟨_, Y, hoddwheel⟩
  -- ### Part 3: `P` has length at least six
  refine ⟨⟨Nat.odd_iff.mpr hodd, h3⟩, ?_⟩
  have hsub : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v} ⊆
      ↑((Finset.Ico 2 (P.length - 2)).image
        (fun k => s(P.getD k p₁, P.getD (k + 1) p₁))) := by
    intro e he
    obtain ⟨k, hk, rfl, h1, h2⟩ := (hmemYE e).mp he
    obtain ⟨hk2, hk3⟩ := hrange k hk h1 h2
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, Finset.mem_Ico.mpr ⟨hk2, by omega⟩, ?_⟩)
    rw [List.getD_eq_getElem P p₁ (show k < P.length by omega),
      List.getD_eq_getElem P p₁ hk]
  have hcard := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at hcard
  have hcard2 := Finset.card_image_le (s := Finset.Ico 2 (P.length - 2))
    (f := fun k => s(P.getD k p₁, P.getD (k + 1) p₁))
  rw [Nat.card_Ico] at hcard2
  rw [pathLength]
  omega


end SPGT

end Workspace.Statements.S18
