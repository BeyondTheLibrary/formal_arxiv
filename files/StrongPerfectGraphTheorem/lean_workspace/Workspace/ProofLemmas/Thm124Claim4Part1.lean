/-  **12.4, printed claim (4) — the first paragraph, complete and `sorry`-free.**

    PAPER (printed p. 75):

    *"(4) There is no edge `uv` of `G \ V(S)` such that `u` is a left-star, `v` is a right-star,
    and `u`, `v` are not `Q`-complete.*

    *For suppose `uv` is such an edge.  Since `u`, `v` have neighbours in `A ∪ B`, they do not
    belong to `R₀*`.  Since `u`, `v` have nonneighbours in `Q` and `Q` is anticonnected, there is
    an antipath `u-q₁-⋯-q_k-v` with `q₁, …, q_k ∈ Q`.  Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`.
    Then `a₁-b₂-u-q₁-⋯-q_k-v-a₁` is an antihole, so `k` is even.  Hence every `Q`-complete
    vertex `w` say is adjacent to one of `u`, `v`, for otherwise `w-u-q₁-⋯-q_k-v-w` would be an
    odd antihole.  In particular, there are no `Q`-complete vertices in `C`; and therefore
    `a₁-R₁-b₁` is an odd path with both ends `Q`-complete and no internal vertex `Q`-complete.
    Since `a₂` is `Q`-complete and has no neighbour in the interior of `R₁`, it follows from 2.2
    that `R₁` has length 1, and similarly `R₂` has length 1.  Since this step was arbitrary, and
    every vertex is in a step, it follows that `C = ∅.` …"*

    Everything down to and including `C = ∅` is proved here.  What is left of (4) is the second
    half of the printed paragraph (the two `R₀*` cases, the leap from 2.1 applied in `Ḡ`, and
    the complement staircase `((A ∪ {a}, ∅, B ∪ {b}), v-q_k-⋯-q₁-u)` contradicting strong
    maximality).  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.Thm151Core
import Workspace.ProofLemmas.Thm124Setup
import Workspace.ProofLemmas.Thm124Claims
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.Statements.S02.Thm_2_2

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace ProofAttempts.Thm124Claim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Generic bookkeeping -/

/-- A path whose two ends are adjacent has length `1`. -/
theorem pathLength_one_of_ends_adj {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hadj : G.Adj a b) : pathLength p = 1 := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hkey := (PathBasics.path_adj_iff hp.1 hpos (show p.length - 1 < p.length by omega)).mp
    (by rw [h0, hl]; exact hadj)
  have := PathBasics.pathLength_eq p
  omega

/-- A step is symmetric in its two rungs. -/
theorem step_symm {G : SimpleGraph V} {A C B : Set V} {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) : IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨hstep.2.1, hstep.1, ?_, ?_⟩
  · intro v hv hv2
    exact hstep.2.2.1 v hv2 hv
  · intro x hx y hy
    rw [SimpleGraph.adj_comm, hstep.2.2.2 y hy x hx]
    tauto

/-- Every vertex of a rung lies in `V(S) = A ∪ B ∪ C`. -/
theorem rung_subset {G : SimpleGraph V} {A C B : Set V} {a b : V} {R : List V}
    (hrung : IsRungOfStrip G A C B a R b) : ∀ w ∈ R, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (hwa ▸ hrung.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (hwb ▸ hrung.2.2.1))
  · exact Or.inr (hrung.2.2.2.2.2 w
      ((PathBasics.mem_interior_iff_of_pathFrom hrung.1).mpr ⟨hw, hwa, hwb⟩))

/-! ## The antipath `u-q₁-⋯-q_k-v` -/

/-- PAPER: *"Since `u`, `v` have nonneighbours in `Q` and `Q` is anticonnected, there is an
antipath `u-q₁-⋯-q_k-v` with `q₁, …, q_k ∈ Q`."*

This is `InducedPathExtraction.exists_antipath_interior_in` without its `u ∉ Q`, `v ∉ Q`
side conditions, which the printed proof does not establish. -/
theorem exists_antipath_through {G : SimpleGraph V} {Q : Set V} (hQ : AnticonnectedSet G Q)
    {u v : V} (hu : ∃ x ∈ Q, ¬ G.Adj u x) (hv : ∃ x ∈ Q, ¬ G.Adj v x) :
    ∃ q : List V, IsAntipathFrom G q u v ∧ ∀ z ∈ SPGT.interior q, z ∈ Q := by
  classical
  have key : ∀ (P : Set V) (w : V), ConnectedSet Gᶜ P → (∃ x ∈ P, ¬ G.Adj w x) →
      ConnectedSet Gᶜ (P ∪ {w}) := by
    intro P w hP hw
    by_cases hwP : w ∈ P
    · have hPw : P ∪ {w} = P := by
        ext y
        simp only [Set.mem_union, Set.mem_singleton_iff]
        constructor
        · rintro (hy | rfl); · exact hy
          · exact hwP
        · exact Or.inl
      rw [hPw]; exact hP
    · obtain ⟨x, hxP, hwx⟩ := hw
      refine ConnectedSetUnionAttach.connectedSet_union_singleton hP ⟨x, hxP, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨fun he => hwP (he ▸ hxP), hwx⟩
  have h1 : ConnectedSet Gᶜ (Q ∪ {u}) := key Q u hQ hu
  have h2 : ConnectedSet Gᶜ ((Q ∪ {u}) ∪ {v}) := by
    refine key _ v h1 ?_
    obtain ⟨x, hxQ, hvx⟩ := hv
    exact ⟨x, Or.inl hxQ, hvx⟩
  obtain ⟨q, hq, hqmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected (G := Gᶜ) h2
      (show u ∈ (Q ∪ {u}) ∪ {v} from Or.inl (Or.inr rfl))
      (show v ∈ (Q ∪ {u}) ∪ {v} from Or.inr rfl)
  refine ⟨q, hq, ?_⟩
  intro z hz
  rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hz
  obtain ⟨hzq, hzu, hzv⟩ := hz
  rcases hqmem z hzq with h | h
  · rcases h with h | h
    · exact h
    · exact absurd h hzu
  · exact absurd h hzv

/-! ## The parity of the antipath -/

/-- PAPER: *"Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`.  Then `a₁-b₂-u-q₁-⋯-q_k-v-a₁` is an antihole,
so `k` is even."*

`q = u-q₁-⋯-q_k-v` has `pathLength q = k + 1`, so *"`k` is even"* is `Odd (pathLength q)`. -/
theorem antipath_odd {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    {q : List V} (hq : IsAntipathFrom G q u v) (hqint : ∀ z ∈ SPGT.interior q, z ∈ Q) :
    Odd (pathLength q) := by
  classical
  -- PAPER: *"Choose a step `a₁-R₁-b₁`, `a₂-R₂-b₂`."*
  obtain ⟨a, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, -⟩ :=
    h.stepConnected.2.2.2.1 a (Or.inl (Or.inl haA))
  have hABd : Disjoint A B := h.stepConnected.1.1
  have ha₁A : a₁ ∈ A := hstep.1.2.1
  have hb₁B : b₁ ∈ B := hstep.1.2.2.1
  have ha₂A : a₂ ∈ A := hstep.2.1.2.1
  have hb₂B : b₂ ∈ B := hstep.2.1.2.2.1
  have ha₁R₁ : a₁ ∈ R₁ := (PathBasics.isPathFrom_ends_mem hstep.1.1).1
  have hb₂R₂ : b₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hstep.2.1.1).2
  have ha₁b₁ : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₁B)
  have ha₂b₂ : a₂ ≠ b₂ := fun he => Set.disjoint_left.mp hABd ha₂A (he ▸ hb₂B)
  have ha₁b₂ne : a₁ ≠ b₂ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₂B)
  -- the two rungs of a step meet only in the stepped edges, so `a₁` and `b₂` are nonadjacent
  have ha₁b₂ : ¬ G.Adj a₁ b₂ := by
    intro hadj
    rcases (hstep.2.2.2 a₁ ha₁R₁ b₂ hb₂R₂).mp hadj with ⟨-, he⟩ | ⟨he, -⟩
    · exact ha₂b₂ he.symm
    · exact ha₁b₁ he
  -- the `Q`-completeness of `A ∪ B` is claim (2)
  have ha₁Q : VertexComplete G a₁ Q := Thm124Claims.claim2 h a₁ (Or.inl ha₁A)
  have hb₂Q : VertexComplete G b₂ Q := Thm124Claims.claim2 h b₂ (Or.inr hb₂B)
  -- `u` is `A`-complete and anticomplete to `B ∪ C`; `v` is `B`-complete and anticomplete
  -- to `A ∪ C`
  have hua₁ : G.Adj u a₁ := hu.2.1 a₁ ha₁A
  have hvb₂ : G.Adj v b₂ := hv.2.1 b₂ hb₂B
  have hub₂ : ¬ G.Adj u b₂ := hu.2.2 b₂ (Or.inl hb₂B)
  have hva₁ : ¬ G.Adj v a₁ := hv.2.2 a₁ (Or.inl ha₁A)
  have huS : u ∉ A ∪ B ∪ C := hu.1
  have hvS : v ∉ A ∪ B ∪ C := hv.1
  have ha₁u : a₁ ≠ u := fun he => huS (he ▸ Or.inl (Or.inl ha₁A))
  have ha₁v : a₁ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inl ha₁A))
  have hb₂u : b₂ ≠ u := fun he => huS (he ▸ Or.inl (Or.inr hb₂B))
  have hb₂v : b₂ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inr hb₂B))
  have ha₁Qnot : a₁ ∉ Q := h.notMemQ_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
  have hb₂Qnot : b₂ ∉ Q := h.notMemQ_of_memStrip b₂ (Or.inl (Or.inr hb₂B))
  have ha₁q : a₁ ∉ q := by
    intro hm
    exact ha₁Qnot (hqint a₁ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, ha₁u, ha₁v⟩))
  have hb₂q : b₂ ∉ q := by
    intro hm
    exact hb₂Qnot (hqint b₂ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, hb₂u, hb₂v⟩))
  have hq3 : 3 ≤ q.length := AntiholeCompletion.three_le_length_of_antipath hq huv
  -- `a₁-b₂-u-q₁-⋯-q_k-v-a₁` is a hole of `Gᶜ`
  have hhole : IsHoleList Gᶜ (q ++ [a₁, b₂]) := by
    refine Thm151Core.hole_of_path_add_edge (G := Gᶜ) hq (by omega) ?_ ?_ ?_ ?_ ?_ ha₁q hb₂q ?_
    · exact ⟨ha₁b₂ne, ha₁b₂⟩
    · exact ⟨fun he => ha₁v he.symm, fun hadj => hva₁ hadj⟩
    · exact ⟨fun he => hb₂u he.symm, fun hadj => hub₂ hadj⟩
    · exact fun hcadj => hcadj.2 hua₁
    · exact fun hcadj => hcadj.2 hvb₂
    · intro x hx hxu hxv
      have hxQ : x ∈ Q :=
        hqint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hx, hxu, hxv⟩)
      exact ⟨fun hcadj => hcadj.2 (ha₁Q x hxQ).symm, fun hcadj => hcadj.2 (hb₂Q x hxQ).symm⟩
  have heven := h.berge.2 _ hhole
  have hlen : holeLength (q ++ [a₁, b₂]) = pathLength q + 3 :=
    Thm151Core.holeLength_add_edge a₁ b₂ (by omega)
  rw [hlen] at heven
  have := PathBasics.pathLength_eq q
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff]
  omega

/-! ## Every `Q`-complete vertex sees `u` or `v` -/

/-- PAPER: *"Hence every `Q`-complete vertex `w` say is adjacent to one of `u`, `v`, for
otherwise `w-u-q₁-⋯-q_k-v-w` would be an odd antihole."* -/
theorem Qcomplete_adj_u_or_v {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q)
    (w : V) (hw : VertexComplete G w Q) : G.Adj w u ∨ G.Adj w v := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨hwu, hwv⟩ := hcon
  -- the antipath of the printed proof
  have hunQ : ∃ x ∈ Q, ¬ G.Adj u x := by
    by_contra hno
    push_neg at hno
    exact hunc hno
  have hvnQ : ∃ x ∈ Q, ¬ G.Adj v x := by
    by_contra hno
    push_neg at hno
    exact hvnc hno
  obtain ⟨q, hq, hqint⟩ := exists_antipath_through h.anticonnQ hunQ hvnQ
  have hodd : Odd (pathLength q) := antipath_odd h huv hu hv hq hqint
  -- `w` is `Q`-complete and misses both ends, so `w-u-q-v-w` is an antihole and `q` is even
  have hwneu : w ≠ u := by
    rintro rfl; exact hunc hw
  have hwnev : w ≠ v := by
    rintro rfl; exact hvnc hw
  have heven : Even (pathLength q) :=
    AntiholeCompletion.even_pathLength_of_witness h.berge huv hw hwu hwv hwneu hwnev hq hqint
  exact (Nat.not_even_iff_odd.mpr hodd) heven

/-- PAPER: *"In particular, there are no `Q`-complete vertices in `C`."* -/
theorem no_Qcomplete_in_C {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∀ w ∈ C, ¬ VertexComplete G w Q := by
  intro w hwC hwQ
  rcases Qcomplete_adj_u_or_v h huv hu hv hunc hvnc w hwQ with hadj | hadj
  · exact hu.2.2 w (Or.inr hwC) hadj.symm
  · exact hv.2.2 w (Or.inr hwC) hadj.symm

/-! ## Every rung has length one, and `C = ∅` -/

/-- PAPER: *"therefore `a₁-R₁-b₁` is an odd path with both ends `Q`-complete and no internal
vertex `Q`-complete.  Since `a₂` is `Q`-complete and has no neighbour in the interior of `R₁`,
it follows from 2.2 that `R₁` has length 1."* -/
theorem rung_len_one {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (hCnc : ∀ w ∈ C, ¬ VertexComplete G w Q)
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V} (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    pathLength R₁ = 1 := by
  classical
  obtain ⟨-, -, hoddR₁, -⟩ :=
    StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism G A C B a₀ b₀ a₁ b₁ a₂ b₂
      R₀ R₁ R₂ h.staircase hstep h.berge h.noPrism
  have hrung₁ := hstep.1
  have hrung₂ := hstep.2.1
  have hR₁path : IsPathFrom G R₁ a₁ b₁ := hrung₁.1
  have ha₁A : a₁ ∈ A := hrung₁.2.1
  have hb₁B : b₁ ∈ B := hrung₁.2.2.1
  have ha₂A : a₂ ∈ A := hrung₂.2.1
  have ha₂R₂ : a₂ ∈ R₂ := (PathBasics.isPathFrom_ends_mem hrung₂.1).1
  have hR₁Q : ∀ x ∈ R₁, x ∉ Q :=
    fun x hx => h.notMemQ_of_memStrip x (rung_subset hrung₁ x hx)
  -- the interior of `R₁` lies in `C`, so no internal vertex is `Q`-complete
  have hncint : ∀ x ∈ R₁, x ≠ a₁ → x ≠ b₁ → ¬ VertexComplete G x Q := by
    intro x hx hxa hxb
    exact hCnc x (hrung₁.2.2.2.2.2 x
      ((PathBasics.mem_interior_iff_of_pathFrom hR₁path).mpr ⟨hx, hxa, hxb⟩))
  by_contra hne
  have hnoedge : ¬ ∃ x ∈ R₁, ∃ y ∈ R₁, EdgeComplete G Q x y := by
    rintro ⟨x, hx, y, hy, hadj, hxc, hyc⟩
    have hx' : x = a₁ ∨ x = b₁ := by
      by_contra hc
      push_neg at hc
      exact hncint x hx hc.1 hc.2 hxc
    have hy' : y = a₁ ∨ y = b₁ := by
      by_contra hc
      push_neg at hc
      exact hncint y hy hc.1 hc.2 hyc
    have hab : G.Adj a₁ b₁ := by
      rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
      · exact absurd hadj (G.irrefl)
      · exact hadj
      · exact hadj.symm
      · exact absurd hadj (G.irrefl)
    exact hne (pathLength_one_of_ends_adj hR₁path hab)
  obtain ⟨x, hxint, hadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G h.berge Q h.anticonnQ R₁ a₁ b₁ hR₁path hR₁Q
      hoddR₁ (Thm124Claims.claim2 h a₁ (Or.inl ha₁A)) (Thm124Claims.claim2 h b₁ (Or.inr hb₁B))
      hnoedge a₂ (Thm124Claims.claim2 h a₂ (Or.inl ha₂A))
  obtain ⟨hxR₁, hxa, hxb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hR₁path).mp hxint
  rcases (hstep.2.2.2 x hxR₁ a₂ ha₂R₂).mp hadj.symm with ⟨he, -⟩ | ⟨he, -⟩
  · exact hxa he
  · exact hxb he

/-- PAPER: *"Since this step was arbitrary, and every vertex is in a step, it follows that
`C = ∅`."* -/
theorem C_eq_empty {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (hCnc : ∀ w ∈ C, ¬ VertexComplete G w Q) :
    C = ∅ := by
  classical
  have hACd : Disjoint A C := h.stepConnected.1.2.1
  have hBCd : Disjoint B C := h.stepConnected.1.2.2
  ext w
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hwC
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hmem⟩ :=
    h.stepConnected.2.2.2.1 w (Or.inr hwC)
  rcases hmem with hw | hw
  · have hlen : pathLength R₁ = 1 := rung_len_one h hCnc hstep
    rcases PathGlue.mem_of_pathLength_one hstep.1.1 hlen w hw with rfl | rfl
    · exact Set.disjoint_left.mp hACd hstep.1.2.1 hwC
    · exact Set.disjoint_left.mp hBCd hstep.1.2.2.1 hwC
  · have hlen : pathLength R₂ = 1 := rung_len_one h hCnc (step_symm hstep)
    rcases PathGlue.mem_of_pathLength_one hstep.2.1.1 hlen w hw with rfl | rfl
    · exact Set.disjoint_left.mp hACd hstep.2.1.2.1 hwC
    · exact Set.disjoint_left.mp hBCd hstep.2.1.2.2.1 hwC

/-- The first paragraph of claim (4), assembled: on the printed hypotheses, `C = ∅`. -/
theorem claim4_C_empty {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    C = ∅ :=
  C_eq_empty h (no_Qcomplete_in_C h huv hu hv hunc hvnc)

/-! ## What `C = ∅` buys: the complement half of strong maximality

The printed proof of (4) finishes *"…contrary to the hypothesis that `K` is strongly maximal"*
with a staircase of **`Ḡ`** (`pdftotext` drops the overline).  That is legitimate exactly
because `C = ∅` has just been derived: `StronglyMaximalStaircase` is
`MaximalStaircase ∧ (C.Nonempty ∨ ¬ ∃ staircase of Gᶜ properly containing V(S))`, so killing
`C` selects the second disjunct. -/

/-- With `C = ∅`, strong maximality of `K` says outright that no staircase of `Gᶜ` properly
contains `V(S)`. -/
theorem no_compl_staircase {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) (hC : C = ∅) :
    ¬ ∃ (A' C' B' : Set V) (a₀' : V) (R' : List V) (b₀' : V),
        IsStaircase Gᶜ A' C' B' a₀' R' b₀' ∧ (A ∪ B ∪ C) ⊂ (A' ∪ B' ∪ C') := by
  rcases h.stronglyMaximal.2 with hne | hno
  · exact absurd (hC ▸ hne) (by simp)
  · exact hno

/-- With `C = ∅` every rung of the strip is a single edge: PAPER *"`R₁` has length 1"* read
back over the whole strip, which is what makes the pairs `a-b₁`, `a₁-b` of the final paragraph
of (4) rungs of `(A ∪ {a}, ∅, B ∪ {b})`. -/
theorem rung_is_edge {G : SimpleGraph V} {A C B : Set V} {a b : V} {R : List V}
    (hrung : IsRungOfStrip G A C B a R b) (hC : C = ∅) (hab : a ≠ b) :
    G.Adj a b ∧ R = [a, b] := by
  have hint : ∀ w ∈ SPGT.interior R, w ∈ C := hrung.2.2.2.2.2
  have hlen : pathLength R = 1 := by
    by_contra hne
    have hpos : 0 < R.length := PathBasics.path_length_pos hrung.1.1
    have hlen2 : 2 ≤ R.length := by
      rcases Nat.lt_or_ge R.length 2 with h1 | h1
      · exfalso
        have := PathBasics.pathLength_eq R
        have hR1 : R.length = 1 := by omega
        have ha : R[0]'hpos = a := PathBasics.getElem_zero_of_head? hrung.1.2.1 hpos
        have hb : R[R.length - 1]'(by omega) = b :=
          PathBasics.getElem_last_of_getLast? hrung.1.2.2 hpos
        refine hab ?_
        rw [← ha, ← hb]
        congr 1
        omega
      · exact h1
    have hplen : pathLength R = R.length - 1 := PathBasics.pathLength_eq R
    have hgt : 2 ≤ pathLength R := by omega
    -- a path of length `≥ 2` has an interior vertex, which would lie in `C = ∅`
    have h1 : 1 < R.length := by omega
    exact absurd (hC ▸ hint (R[1]'h1)
      (PathBasics.getElem_mem_interior hrung.1.1 h1 (by omega) (by omega)))
      (Set.notMem_empty _)
  have hpos : 0 < R.length := PathBasics.path_length_pos hrung.1.1
  have hR2 : R.length = 2 := by
    have := PathBasics.pathLength_eq R; omega
  obtain ⟨c, d, hcd⟩ := PathGlue.length_eq_two hR2
  subst hcd
  have ha : c = a := by simpa using hrung.1.2.1
  have hb : d = b := by simpa using hrung.1.2.2
  subst ha; subst hb
  refine ⟨?_, rfl⟩
  simpa using PathBasics.path_adj_succ hrung.1.1 (i := 0) (by simp)

/-! ## *"So `u` has a neighbour in `R₀*`"* -/

/-- `Q ∪ {v}` is anticonnected as soon as `v` has a nonneighbour in the anticonnected `Q`
(no `v ∉ Q` side condition: if `v ∈ Q` the union is `Q`). -/
theorem anticonn_union_singleton {G : SimpleGraph V} {Q : Set V} (hQ : AnticonnectedSet G Q)
    {v : V} (hv : ∃ x ∈ Q, ¬ G.Adj v x) : AnticonnectedSet G (Q ∪ {v}) := by
  classical
  by_cases hvQ : v ∈ Q
  · have hQv : Q ∪ {v} = Q := by
      ext y
      simp only [Set.mem_union, Set.mem_singleton_iff]
      constructor
      · rintro (hy | rfl)
        · exact hy
        · exact hvQ
      · exact Or.inl
    rw [hQv]; exact hQ
  · obtain ⟨x, hxQ, hvx⟩ := hv
    refine ConnectedSetUnionAttach.connectedSet_union_singleton hQ ⟨x, hxQ, ?_⟩
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hvQ (he ▸ hxQ), hvx⟩

/-- PAPER: *"Suppose that `u` has no neighbour in `R₀*`.  Then all `Q`-complete vertices in
`R₀*` are adjacent to `v`.  In particular, `v` is adjacent to `s`, `t` and hence does not belong
to `R₀` (because `v` is a right-star); and `s-S-a₀-a₁-b₁` is an odd path, its ends are
`(Q ∪ {v})`-complete, its internal vertices are not, and the `(Q ∪ {v})`-complete `t` has no
neighbour in its interior, contrary to 2.2.  So `u` has a neighbour in `R₀*`."*

The path is written from the far end, `b₁-a₁-a₀-S-s`; 2.2 does not care about direction. -/
theorem left_star_has_neighbour_in_interior {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V}
    (huv : G.Adj u v) (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∃ z ∈ SPGT.interior R₀, G.Adj u z := by
  classical
  by_contra hcon
  push_neg at hcon
  have hCempty : C = ∅ := claim4_C_empty h huv hu hv hunc hvnc
  have hABd : Disjoint A B := h.stepConnected.1.1
  have hlen := h.lengthGe
  obtain ⟨iS, iT, hiS, hiT, hiS0, hiTlast, hlt, hsQ, htQ, hminS, hmaxT, hoddS, hoddT⟩ :=
    Thm124Setup.claim1 h
  set s : V := R₀[iS]'hiS with hsdef
  set t : V := R₀[iT]'hiT with htdef
  have hsint : s ∈ SPGT.interior R₀ :=
    PathBasics.getElem_mem_interior h.pathList hiS (by omega) (by omega)
  have htint : t ∈ SPGT.interior R₀ :=
    PathBasics.getElem_mem_interior h.pathList hiT (by omega) (by omega)
  -- PAPER: *"Then all `Q`-complete vertices in `R₀*` are adjacent to `v`."*
  have hsv : G.Adj s v := by
    rcases Qcomplete_adj_u_or_v h huv hu hv hunc hvnc s hsQ with hadj | hadj
    · exact absurd hadj.symm (hcon s hsint)
    · exact hadj
  have htv : G.Adj t v := by
    rcases Qcomplete_adj_u_or_v h huv hu hv hunc hvnc t htQ with hadj | hadj
    · exact absurd hadj.symm (hcon t htint)
    · exact hadj
  -- PAPER: *"and hence does not belong to `R₀` (because `v` is a right-star)"*
  obtain ⟨bne, hbneB⟩ := h.stepConnected.2.1.2
  have hvR₀ : v ∉ R₀ := by
    intro hmem
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hmem
    have h1 := (PathBasics.path_adj_iff h.pathList hj hiS).mp (by rw [hjv]; exact hsv.symm)
    have h2 := (PathBasics.path_adj_iff h.pathList hj hiT).mp (by rw [hjv]; exact htv.symm)
    -- the only surviving case puts `v` in the interior of `R₀`, which is anticomplete to `B`
    have hjint : 1 ≤ j ∧ j + 2 ≤ R₀.length := by omega
    refine h.interiorAnti v ?_ bne (Or.inl (Or.inr hbneB)) (hv.2.1 bne hbneB)
    rw [← hjv]
    exact PathBasics.getElem_mem_interior h.pathList hj hjint.1 hjint.2
  -- PAPER: *"Choose a step `a₁-R₁-b₁` …"* — with `C = ∅` its rung is a single edge `a₁b₁`
  obtain ⟨aA, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨a₁, R₁, b₁, hrung, -⟩ := h.stepConnected.2.2.1 aA (Or.inl (Or.inl haA))
  have ha₁A : a₁ ∈ A := hrung.2.1
  have hb₁B : b₁ ∈ B := hrung.2.2.1
  have ha₁b₁ne : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₁B)
  have ha₁b₁ : G.Adj a₁ b₁ := (rung_is_edge hrung hCempty ha₁b₁ne).1
  -- the stretch `a₀-S-s` of `R₀`
  set SS : List V := (R₀.drop 0).take (iS - 0 + 1) with hSSdef
  have hSSlen : SS.length = iS - 0 + 1 := PathBasics.length_slice R₀ (by omega) hiS
  have hSSpath : IsPathFrom G SS a₀ s := by
    have hx := PathBasics.isPathFrom_slice h.pathList (show (0 : ℕ) < iS from hiS0) hiS
    rwa [h.getElem_zero] at hx
  have hSSmem : ∀ x ∈ SS, ∃ (k : ℕ) (hk : k < R₀.length), k ≤ iS ∧ (R₀[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, -, hki, hkx⟩ := (PathBasics.mem_slice_iff R₀ (by omega) hiS).mp hx
    exact ⟨k, hk, hki, hkx⟩
  have hSSsub : ∀ x ∈ SS, x ∈ R₀ := by
    intro x hx
    obtain ⟨k, hk, -, hkx⟩ := hSSmem x hx
    exact hkx ▸ List.getElem_mem hk
  -- `a₁-a₀-S-s`
  have ha₁SS : a₁ ∉ SS := fun hm =>
    h.notMemR₀_of_memStrip a₁ (Or.inl (Or.inl ha₁A)) (hSSsub a₁ hm)
  have hP1 : IsPathFrom G (a₁ :: SS) a₁ s := by
    refine PathAttach.isPathFrom_cons hSSpath ((h.leftStar.2.1 a₁ ha₁A).symm) ha₁SS ?_
    intro x hx hxa₀ hadj
    obtain ⟨k, hk, -, hkx⟩ := hSSmem x hx
    subst hkx
    have hk0 := (h.adj_mem_A_iff ha₁A k hk).mp hadj
    subst hk0
    exact hxa₀ h.getElem_zero
  -- `b₁-a₁-a₀-S-s`
  have hb₁P1 : b₁ ∉ (a₁ :: SS) := by
    intro hm
    rcases List.mem_cons.mp hm with he | hm'
    · exact ha₁b₁ne he.symm
    · exact h.notMemR₀_of_memStrip b₁ (Or.inl (Or.inr hb₁B)) (hSSsub b₁ hm')
  have hP2 : IsPathFrom G (b₁ :: a₁ :: SS) b₁ s := by
    refine PathAttach.isPathFrom_cons hP1 ha₁b₁.symm hb₁P1 ?_
    rintro x hx hxa₁ hadj
    rcases List.mem_cons.mp hx with he | hx'
    · exact hxa₁ he
    · obtain ⟨k, hk, hki, hkx⟩ := hSSmem x hx'
      have := (h.adj_mem_B_iff hb₁B k hk).mp (by rw [hkx]; exact hadj)
      omega
  -- lengths and parity
  have hP2len : (b₁ :: a₁ :: SS).length = iS + 3 := by
    simp only [List.length_cons]
    omega
  have hP2odd : Odd (pathLength (b₁ :: a₁ :: SS)) := by
    have := PathBasics.pathLength_eq (b₁ :: a₁ :: SS)
    obtain ⟨m, hm⟩ := hoddS
    exact ⟨m + 1, by omega⟩
  -- the set `Q ∪ {v}`
  have hvnQex : ∃ x ∈ Q, ¬ G.Adj v x := by
    by_contra hno
    push_neg at hno
    exact hvnc hno
  have hQ₀ : AnticonnectedSet G (Q ∪ {v}) := anticonn_union_singleton h.anticonnQ hvnQex
  have hcompl : ∀ w : V, VertexComplete G w Q → G.Adj w v → VertexComplete G w (Q ∪ {v}) := by
    intro w hwQ hwv x hx
    rcases hx with hx | hx
    · exact hwQ x hx
    · rw [Set.mem_singleton_iff] at hx; exact hx ▸ hwv
  have hvS : v ∉ A ∪ B ∪ C := hv.1
  have hP2Q : ∀ w ∈ (b₁ :: a₁ :: SS), w ∉ Q ∪ {v} := by
    intro w hw
    rintro (hq | hq)
    · rcases List.mem_cons.mp hw with rfl | hw'
      · exact h.notMemQ_of_memStrip w (Or.inl (Or.inr hb₁B)) hq
      · rcases List.mem_cons.mp hw' with rfl | hw''
        · exact h.notMemQ_of_memStrip w (Or.inl (Or.inl ha₁A)) hq
        · exact h.notMemQ_of_mem w (hSSsub w hw'') hq
    · rw [Set.mem_singleton_iff] at hq
      subst hq
      rcases List.mem_cons.mp hw with he | hw'
      · exact hvS (he ▸ Or.inl (Or.inr hb₁B))
      · rcases List.mem_cons.mp hw' with he | hw''
        · exact hvS (he ▸ Or.inl (Or.inl ha₁A))
        · exact hvR₀ (hSSsub w hw'')
  -- PAPER: *"its ends are `(Q ∪ {v})`-complete, its internal vertices are not"*
  have hb₁Q₀ : VertexComplete G b₁ (Q ∪ {v}) :=
    hcompl b₁ (Thm124Claims.claim2 h b₁ (Or.inr hb₁B)) (hv.2.1 b₁ hb₁B).symm
  have hsQ₀ : VertexComplete G s (Q ∪ {v}) := hcompl s hsQ hsv
  have htQ₀ : VertexComplete G t (Q ∪ {v}) := hcompl t htQ htv
  have honly : ∀ w ∈ (b₁ :: a₁ :: SS), VertexComplete G w (Q ∪ {v}) → w = b₁ ∨ w = s := by
    intro w hw hwc
    rcases List.mem_cons.mp hw with he | hw'
    · exact Or.inl he
    rcases List.mem_cons.mp hw' with he | hw''
    · -- `a₁ ∈ A` is not adjacent to the right-star `v`
      exact absurd (hwc v (Or.inr rfl)) (by rw [he]; exact fun hadj => hv.2.2 a₁ (Or.inl ha₁A) hadj.symm)
    · obtain ⟨k, hk, hki, hkx⟩ := hSSmem w hw''
      rcases Nat.lt_or_ge k iS with hklt | hkge
      · exact absurd (fun x hx => hwc x (Or.inl hx)) (by rw [← hkx]; exact hminS k hk hklt)
      · have : k = iS := by omega
        exact Or.inr (by rw [← hkx, hsdef]; congr 1)
  have hnoedge : ¬ ∃ x ∈ (b₁ :: a₁ :: SS), ∃ y ∈ (b₁ :: a₁ :: SS),
      EdgeComplete G (Q ∪ {v}) x y := by
    rintro ⟨x, hx, y, hy, hadj, hxc, hyc⟩
    have hbs : ¬ G.Adj b₁ s := fun hadj' =>
      h.interiorAnti s hsint b₁ (Or.inl (Or.inr hb₁B)) hadj'.symm
    rcases honly x hx hxc with rfl | rfl <;> rcases honly y hy hyc with rfl | rfl
    · exact G.irrefl hadj
    · exact hbs hadj
    · exact hbs hadj.symm
    · exact G.irrefl hadj
  -- PAPER: *"the `(Q ∪ {v})`-complete `t` has no neighbour in its interior, contrary to 2.2"*
  obtain ⟨w, hwint, hwadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G h.berge (Q ∪ {v}) hQ₀ (b₁ :: a₁ :: SS) b₁ s
      hP2 hP2Q hP2odd hb₁Q₀ hsQ₀ hnoedge t htQ₀
  obtain ⟨hwP2, hwb₁, hws⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP2).mp hwint
  rcases List.mem_cons.mp hwP2 with he | hw'
  · exact hwb₁ he
  rcases List.mem_cons.mp hw' with he | hw''
  · -- `t` is not adjacent to `a₁ ∈ A`, whose only neighbour on `R₀` is `a₀`
    have := (h.adj_mem_A_iff ha₁A iT hiT).mp (by rw [← htdef]; rw [he] at hwadj; exact hwadj.symm)
    omega
  · obtain ⟨k, hk, hki, hkx⟩ := hSSmem w hw''
    have hkne : k ≠ iS := by
      intro he
      exact hws (by rw [← hkx, hsdef]; congr 1)
    have := (PathBasics.path_adj_iff h.pathList hiT hk).mp (by rw [hkx]; exact hwadj)
    omega

/-- PAPER: *"So `u` has a neighbour in `R₀*`, and **similarly so does `v`**."*  The printed
*"similarly"* is the left–right exchange `Thm124Setup.Setup.swap`, under which a left-star of
`(A, C, B)` is a right-star of `(B, C, A)` and vice versa. -/
theorem right_star_has_neighbour_in_interior {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V}
    {R₀ : List V} {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V}
    (huv : G.Adj u v) (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∃ z ∈ SPGT.interior R₀, G.Adj v z := by
  have hUnion : B ∪ A ∪ C = A ∪ B ∪ C := by rw [Set.union_comm B A]
  have hv' : IsLeftStar G B C A v := ⟨hUnion ▸ hv.1, hv.2.1, hv.2.2⟩
  have hu' : IsRightStar G B C A u := ⟨hUnion ▸ hu.1, hu.2.1, hu.2.2⟩
  obtain ⟨z, hz, hadj⟩ :=
    left_star_has_neighbour_in_interior (Thm124Setup.Setup.swap h) huv.symm hv' hu' hvnc hunc
  exact ⟨z, PathBasics.mem_interior_reverse.mp hz, hadj⟩

/-! ## *"Now `b₁-u-Q-v-a₁` is an odd antipath …"* -/

/-- PAPER: *"Now `b₁-u-Q-v-a₁` is an odd antipath, all its internal vertices have neighbours in
the connected set `R₀*`, and its ends do not."*

This is the exact input to *"By 2.1 applied in `Ḡ`, there is a leap; that is, there exist
adjacent `a, b ∈ R₀*`, both `Q`-complete, such that `b-u-Q-v-a` is an antipath."*  The vertex
`a₁ ∈ A` and `b₁ ∈ B` are the two ends of an arbitrary rung, which `C = ∅` has just made a
single edge. -/
theorem odd_antipath_for_leap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : Thm124Setup.Setup G A C B a₀ R₀ b₀ Q) {u v : V} (huv : G.Adj u v)
    (hu : IsLeftStar G A C B u) (hv : IsRightStar G A C B v)
    (hunc : ¬ VertexComplete G u Q) (hvnc : ¬ VertexComplete G v Q) :
    ∃ (a₁ b₁ : V) (q : List V), a₁ ∈ A ∧ b₁ ∈ B ∧ G.Adj a₁ b₁ ∧
      IsAntipathFrom G (b₁ :: (q ++ [a₁])) b₁ a₁ ∧
      Odd (pathLength (b₁ :: (q ++ [a₁]))) ∧
      (∀ w ∈ SPGT.interior (b₁ :: (q ++ [a₁])), ∃ z ∈ SPGT.interior R₀, G.Adj w z) ∧
      (∀ z ∈ SPGT.interior R₀, ¬ G.Adj b₁ z ∧ ¬ G.Adj a₁ z) := by
  classical
  have hCempty : C = ∅ := claim4_C_empty h huv hu hv hunc hvnc
  have hABd : Disjoint A B := h.stepConnected.1.1
  -- the antipath `u-q₁-⋯-q_k-v` and its (odd) length
  have hunQ : ∃ x ∈ Q, ¬ G.Adj u x := by
    by_contra hno; push_neg at hno; exact hunc hno
  have hvnQ : ∃ x ∈ Q, ¬ G.Adj v x := by
    by_contra hno; push_neg at hno; exact hvnc hno
  obtain ⟨q, hq, hqint⟩ := exists_antipath_through h.anticonnQ hunQ hvnQ
  have hqodd : Odd (pathLength q) := antipath_odd h huv hu hv hq hqint
  -- an arbitrary rung, a single edge because `C = ∅`
  obtain ⟨aA, haA⟩ := h.stepConnected.2.1.1
  obtain ⟨a₁, R₁, b₁, hrung, -⟩ := h.stepConnected.2.2.1 aA (Or.inl (Or.inl haA))
  have ha₁A : a₁ ∈ A := hrung.2.1
  have hb₁B : b₁ ∈ B := hrung.2.2.1
  have ha₁b₁ne : a₁ ≠ b₁ := fun he => Set.disjoint_left.mp hABd ha₁A (he ▸ hb₁B)
  have ha₁b₁ : G.Adj a₁ b₁ := (rung_is_edge hrung hCempty ha₁b₁ne).1
  have ha₁Q : VertexComplete G a₁ Q := Thm124Claims.claim2 h a₁ (Or.inl ha₁A)
  have hb₁Q : VertexComplete G b₁ Q := Thm124Claims.claim2 h b₁ (Or.inr hb₁B)
  have huS : u ∉ A ∪ B ∪ C := hu.1
  have hvS : v ∉ A ∪ B ∪ C := hv.1
  have ha₁u : a₁ ≠ u := fun he => huS (he ▸ Or.inl (Or.inl ha₁A))
  have ha₁v : a₁ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inl ha₁A))
  have hb₁u : b₁ ≠ u := fun he => huS (he ▸ Or.inl (Or.inr hb₁B))
  have hb₁v : b₁ ≠ v := fun he => hvS (he ▸ Or.inl (Or.inr hb₁B))
  have ha₁q : a₁ ∉ q := fun hm =>
    h.notMemQ_of_memStrip a₁ (Or.inl (Or.inl ha₁A))
      (hqint a₁ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, ha₁u, ha₁v⟩))
  have hb₁q : b₁ ∉ q := fun hm =>
    h.notMemQ_of_memStrip b₁ (Or.inl (Or.inr hb₁B))
      (hqint b₁ ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hm, hb₁u, hb₁v⟩))
  -- `b₁-u-q₁-⋯-q_k-v-a₁` is a path of `Gᶜ`
  have hpath : IsAntipathFrom G (b₁ :: (q ++ [a₁])) b₁ a₁ := by
    refine PathAttach.isPathFrom_cons_concat (G := Gᶜ) hq ?_ ?_ ?_ (Ne.symm ha₁b₁ne)
      hb₁q ha₁q ?_ ?_
    · exact ⟨hb₁u, fun hadj => hu.2.2 b₁ (Or.inl hb₁B) hadj.symm⟩
    · exact ⟨ha₁v, fun hadj => hv.2.2 a₁ (Or.inl ha₁A) hadj.symm⟩
    · exact fun hcadj => hcadj.2 ha₁b₁.symm
    · intro x hx hxu hcadj
      by_cases hxv : x = v
      · exact hcadj.2 (by rw [hxv]; exact (hv.2.1 b₁ hb₁B).symm)
      · exact hcadj.2 (hb₁Q x
          (hqint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hx, hxu, hxv⟩)))
    · intro x hx hxv hcadj
      by_cases hxu : x = u
      · exact hcadj.2 (by rw [hxu]; exact (hu.2.1 a₁ ha₁A).symm)
      · exact hcadj.2 (ha₁Q x
          (hqint x ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr ⟨hx, hxu, hxv⟩)))
  -- PAPER: *"is an odd antipath"*
  have hqpos : 0 < q.length := PathBasics.path_length_pos hq.1
  have hlen : (b₁ :: (q ++ [a₁])).length = q.length + 2 := by
    simp only [List.length_cons, List.length_append, List.length_nil]
  have hodd : Odd (pathLength (b₁ :: (q ++ [a₁]))) := by
    have h1 := PathBasics.pathLength_eq (b₁ :: (q ++ [a₁]))
    have h2 := PathBasics.pathLength_eq q
    obtain ⟨m, hm⟩ := hqodd
    exact ⟨m + 1, by omega⟩
  -- PAPER: *"all its internal vertices have neighbours in the connected set `R₀*`"*
  obtain ⟨iS, iT, hiS, hiT, hiS0, hiTlast, hlt, hsQ, htQ, -, -, -, -⟩ := Thm124Setup.claim1 h
  have hsint : (R₀[iS]'hiS) ∈ SPGT.interior R₀ :=
    PathBasics.getElem_mem_interior h.pathList hiS (by omega) (by omega)
  obtain ⟨zu, hzu, hzuadj⟩ := left_star_has_neighbour_in_interior h huv hu hv hunc hvnc
  obtain ⟨zv, hzv, hzvadj⟩ := right_star_has_neighbour_in_interior h huv hu hv hunc hvnc
  refine ⟨a₁, b₁, q, ha₁A, hb₁B, ha₁b₁, hpath, hodd, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwmem, hwb₁, hwa₁⟩ := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hw
    have hwq : w ∈ q := by
      rcases List.mem_cons.mp hwmem with he | hw'
      · exact absurd he hwb₁
      · rcases List.mem_append.mp hw' with h1 | h1
        · exact h1
        · exact absurd (by simpa using h1) hwa₁
    by_cases hwu : w = u
    · exact ⟨zu, hzu, by rw [hwu]; exact hzuadj⟩
    by_cases hwv : w = v
    · exact ⟨zv, hzv, by rw [hwv]; exact hzvadj⟩
    · -- an internal vertex of the antipath lies in `Q`, hence sees the `Q`-complete `s ∈ R₀*`
      exact ⟨R₀[iS]'hiS, hsint,
        (hsQ w (hqint w ((PathBasics.mem_interior_iff_of_pathFrom hq).mpr
          ⟨hwq, hwu, hwv⟩))).symm⟩
  · -- PAPER: *"and its ends do not"* — `V(S)` is anticomplete to the interior of `R₀`
    intro z hz
    exact ⟨fun hadj => h.interiorAnti z hz b₁ (Or.inl (Or.inr hb₁B)) hadj.symm,
      fun hadj => h.interiorAnti z hz a₁ (Or.inl (Or.inl ha₁A)) hadj.symm⟩

end ProofAttempts.Thm124Claim4
