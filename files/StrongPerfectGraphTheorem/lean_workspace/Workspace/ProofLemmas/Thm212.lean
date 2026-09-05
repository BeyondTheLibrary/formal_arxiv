import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Pseudowheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.TwoPathsHole
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm203Prelim
import Workspace.ProofLemmas.Thm203AntipathTools
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm212Claim3Tools
import Workspace.ProofLemmas.Thm212EndgameTools
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_10
import Workspace.ProofLemmas.Thm212RunParity
import Workspace.ProofLemmas.Thm212OnlyTwoComplete
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S20.Thm_20_1
import Workspace.Statements.S21.Thm_21_1
import Workspace.Statements.S15.Thm_15_7
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm212Claim5Antipath

/-!
# 21.2 — the named steps of the printed proof

The printed proof of **21.2** (`paper/proofs/21_2.md`, printed pp. 131–135) is one of the
longest in the paper.  It runs:

* an unnumbered opening claim **(1)**;
* the construction of the path `x_{t+1}-p₁-⋯-p_m`, with the extremal choice *"choose such a
  path such that if possible, every member of `Y` has a neighbour in
  `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`"*;
* claims **(2)** and **(3)**;
* the extension of that path to `x_{t+1}-p₁-⋯-p_n` containing neighbours of all of `X_t`,
  and the choice of the indices `i` and `s`;
* claims **(4)**–**(9)** and the concluding paragraph.

This module carves that narrative into the six pieces the printed proof itself marks out, so
that `Workspace.Statements.S21.Thm_21_2` is the paper's own chaining of them.  Every
definition below records the printed sentence it renders.

Encoding conventions (`paper/spec/CONVENTIONS.md`): a path is the list of its vertices, the
paper's `p₁,…,p_m` are the entries of the list `p` (so `p_k` is `p[k-1]`), and the printed
path `x_{t+1}-p₁-⋯-p_m` is the Lean list `x (t + 1) :: p`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm212

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio.SPGT Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The standing hypothesis package of **21.2**, verbatim from the frozen statement:
*"Let `G ∈ F₇`, and let `Y ⊆ V(G)`, such that there do not exist `X, P` so that `(X, Y, P)` is
a pseudowheel.  Let `(z, A₀)` be a frame, and let `x₀,…,x_{t+1}` be a wheel system with hub
`Y`, and with `t ≥ 2`.  Define `Xᵢ, Aᵢ` as usual.  Suppose that `x_{t+1}` has no neighbour in
`A_{t−1}`; and moreover that at most one member of `Y` has no neighbour in
`A_{t−1} ∪ {x_{t+1}}`, and any such vertex has a neighbour in `A_t`."* -/
def Setup (G : SimpleGraph V) (Y : Set V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) : Prop :=
  InF7 G ∧
  (¬ ∃ (X : Set V) (P : List V), IsPseudowheel G X Y P) ∧
  IsFrame G z A₀ ∧
  2 ≤ t ∧
  IsHubForWheelSystem G z A₀ x (t + 1) Y ∧
  VertexAnticomplete G (x (t + 1)) (wheelSystemA G z A₀ x (t - 1)) ∧
  Set.Subsingleton
    {y ∈ Y | VertexAnticomplete G y
      (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)})} ∧
  (∀ y ∈ Y,
    VertexAnticomplete G y (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)}) →
      ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj y a)

/-- The conclusion of **21.2**: *"Then there is a wheel in `G` with hub `Y`."* -/
def Concl (G : SimpleGraph V) (Y : Set V) : Prop := ∃ C : List V, IsWheel G C Y

/-- The path built in the paragraph after claim (1):

PAPER: *"Since `x_{t+1}` has a neighbour in `A_t` and none in `A_{t−1}`, there is a path from
`x_{t+1}` to `A_{t−1}` with interior in `A_t \ A_{t−1}`.  Hence there is a path
`x_{t+1}-p₁-⋯-p_m` such that `p₁,…,p_m ∈ A_t \ A_{t−1}` and `p_m` is the unique vertex of this
path with a neighbour in `A_{t−1}`.  (Hence `m ≥ 1`, and `p_m` is `X_{t−1}`-complete.)"*

The printed path is the Lean list `x (t + 1) :: p`; *"`p_m` is the unique vertex of this path
with a neighbour in `A_{t−1}`"* is the last clause (`x_{t+1}` itself has no such neighbour by
the hypothesis of 21.2, so quantifying over the entries of `p` is the whole content). -/
def GoodPath (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) (p : List V) :
    Prop :=
  IsPathList G (x (t + 1) :: p) ∧ p ≠ [] ∧
  (∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t ∧ v ∉ wheelSystemA G z A₀ x (t - 1)) ∧
  (∀ (k : ℕ) (hk : k < p.length),
    (∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (p[k]'hk) a) ↔ k + 1 = p.length)

/-- *"every member of `Y` has a neighbour in `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`"* — the property
by which the path of `GoodPath` is chosen *"if possible"*, and the content of claim (3). -/
def SpanY (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) (Y : Set V)
    (p : List V) : Prop :=
  ∀ y ∈ Y, ∃ a : V,
    (a ∈ wheelSystemA G z A₀ x (t - 1) ∨ a = x (t + 1) ∨ a ∈ p) ∧ G.Adj y a

/-- Claim **(1)**: *"There do not exist `xᵢ, x_j ∈ X_t` joined by an odd path
`xᵢ-x_{t+1}-P-x_j` of length ≥ 5 such that `xᵢ, x_j ∈ X_t` and `P` has interior in `A_t`."*

The printed path is `x i :: x (t+1) :: P` where `P` lists `p₁,…,p_n, x j`; *"`P` has interior
in `A_t`"* is therefore *"every entry of `P` other than `x j` lies in `A_t`"*. -/
def NoOddLeapPath (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) : Prop :=
  ¬ ∃ (i j : ℕ) (P : List V), i ≤ t ∧ j ≤ t ∧
      IsPathFrom G (x i :: x (t + 1) :: P) (x i) (x j) ∧
      Odd (pathLength (x i :: x (t + 1) :: P)) ∧
      5 ≤ pathLength (x i :: x (t + 1) :: P) ∧
      (∀ v ∈ P, v ≠ x j → v ∈ wheelSystemA G z A₀ x t)

/-- Claim **(2)**: *"We may assume that one of `x₀,…,x_t` is nonadjacent to both
`x_{t+1}, p₁`."* -/
def Claim2 (G : SimpleGraph V) (x : ℕ → V) (t : ℕ) (p : List V) : Prop :=
  ∃ s ≤ t, ¬ G.Adj (x s) (x (t + 1)) ∧ ∃ p₁ : V, p.head? = some p₁ ∧ ¬ G.Adj (x s) p₁

/-- The paragraph after claim (3):

PAPER: *"Since `x_t, p_m` have neighbours in `A_{t−1}` and none of `x_{t+1}, p₁,…,p_{m−1}` have
neighbours in `A_{t−1}`, we can extend the path `x_{t+1}-p₁-⋯-p_m` to a path
`x_{t+1}-p₁-⋯-p_m-p_{m+1}-⋯-p_n` containing neighbours of all members of `X_t`.  By (2), we can
choose `i` with `2 ≤ i ≤ n` maximum such that some vertex of `X_t` is nonadjacent to all of
`x_{t+1}, p₁,…,p_{i−1}`; and choose `s` with `0 ≤ s ≤ t` such that `x_s` is nonadjacent to all
of `x_{t+1}, p₁,…,p_{i−1}`.  Since every vertex in `X_t` has a neighbour in
`{x_{t+1}, p₁,…,p_n}`, it follows from the maximality of `i` that every vertex in `X_t` is
adjacent to one of `x_{t+1}, p₁,…,p_i`."*

Here `q` is the extended list `p₁,…,p_n` (so `p <+: q`), and
`(x (t + 1) :: q).take i = [x_{t+1}, p₁,…,p_{i−1}]`,
`(x (t + 1) :: q).take (i + 1) = [x_{t+1}, p₁,…,p_i]`. -/
def Extended (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (p q : List V) (i s : ℕ) : Prop :=
  p <+: q ∧
  IsPathList G (x (t + 1) :: q) ∧
  (∀ v ∈ q, v ∈ wheelSystemA G z A₀ x t) ∧
  (∀ j ≤ t, ∃ w ∈ x (t + 1) :: q, G.Adj (x j) w) ∧
  2 ≤ i ∧ i ≤ q.length ∧ s ≤ t ∧
  (∀ w ∈ (x (t + 1) :: q).take i, ¬ G.Adj (x s) w) ∧
  (∀ j ≤ t, ∃ w ∈ (x (t + 1) :: q).take (i + 1), G.Adj (x j) w)

/-- Auxiliary: the family of *candidate* paths minimised over in `exists_goodPath_aux`.  A
candidate is an induced path `x_{t+1}-p₁-⋯-p_k` with all of `p₁,…,p_k` in `A_t`, whose last
vertex either lies in `A_{t−1}` or has a neighbour there. -/
private def Cand (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ) (p : List V) :
    Prop :=
  IsPathList G (x (t + 1) :: p) ∧ p ≠ [] ∧
  (∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t) ∧
  (∃ a ∈ wheelSystemA G z A₀ x (t - 1), ∃ v : V,
    p.getLast? = some v ∧ (v = a ∨ G.Adj v a))

private theorem getLast?_take_succ (l : List V) (k : ℕ) (hk : k < l.length) :
    (l.take (k + 1)).getLast? = some (l[k]'hk) := by
  simpa using PathBasics.getLast?_slice l (i := 0) (j := k) (Nat.zero_le _) hk

/-- **Existence of the path of the paragraph after claim (1)**, without the extremal clause:

PAPER: *"Since `x_{t+1}` has a neighbour in `A_t` and none in `A_{t−1}`, there is a path from
`x_{t+1}` to `A_{t−1}` with interior in `A_t \ A_{t−1}`.  Hence there is a path
`x_{t+1}-p₁-⋯-p_m` such that `p₁,…,p_m ∈ A_t \ A_{t−1}` and `p_m` is the unique vertex of this
path with a neighbour in `A_{t−1}`."*

Implemented as the paper's *"hence"*: take a shortest candidate path.  A candidate exists
because `A_t` is connected, contains `A_{t−1} ⊇ A₀ ≠ ∅` and a neighbour of `x_{t+1}`, while
`x_{t+1} ∉ A_t` (it is adjacent to `z`).  Minimality then forces both *"`p₁,…,p_m ∉ A_{t−1}`"*
and *"`p_m` is the unique vertex with a neighbour in `A_{t−1}`"*: any earlier vertex with a
neighbour in `A_{t−1}` would give a strictly shorter candidate. -/
private theorem exists_goodPath_aux {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) :
    ∃ p : List V, GoodPath G z A₀ x t p := by
  classical
  obtain ⟨-, -, hframe, ht, hhub, hxt1, -, -⟩ := h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hcond2 := hws.2.2.2.2.1
  have hcond4 := hws.2.2.2.2.2.2
  -- `A₀ ⊆ A_{t−1}`, by condition 2 of the wheel system at index `t`.
  obtain ⟨B, hB0, hBcon, -, hBz, hBX⟩ := hcond2 t ht (by omega)
  have hA₀A1 : A₀ ⊆ wheelSystemA G z A₀ x (t - 1) := fun v hv =>
    WheelSystemBasics.mem_wheelSystemA_of_witness hB0 hBcon hBz hBX (hB0 hv)
  obtain ⟨c, hcA₀⟩ := hframe.1
  have hcA1 : c ∈ wheelSystemA G z A₀ x (t - 1) := hA₀A1 hcA₀
  have hcAt : c ∈ wheelSystemA G z A₀ x t :=
    WheelSystemBasics.wheelSystemA_mono (by omega) hcA1
  -- *"`x_{t+1}` has a neighbour in `A_t`"*, by condition 2 at index `t + 1`.
  obtain ⟨B', hB'0, hB'con, ⟨b, hbB', hxb⟩, hB'z, hB'X⟩ := hcond2 (t + 1) (by omega) le_rfl
  simp only [Nat.add_sub_cancel] at hB'X
  have hbAt : b ∈ wheelSystemA G z A₀ x t :=
    WheelSystemBasics.mem_wheelSystemA_of_witness hB'0 hB'con hB'z hB'X hbB'
  -- `x_{t+1} ∉ A_t`, since `z` is adjacent to it and `A_t` has no neighbour of `z`.
  have hxnotAt : x (t + 1) ∉ wheelSystemA G z A₀ x t := fun hm =>
    WheelSystemBasics.wheelSystemA_no_nbr hm (hcond4 (t + 1) le_rfl)
  -- An induced path from `x_{t+1}` to `c ∈ A_{t−1}` through `A_t`.
  have hAtcon : ConnectedSet G (wheelSystemA G z A₀ x t) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hScon : ConnectedSet G (wheelSystemA G z A₀ x t ∪ {x (t + 1)}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hAtcon ⟨b, hbAt, hxb⟩
  obtain ⟨q, hq, hqS⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hScon
    (Set.mem_union_right _ rfl) (Set.mem_union_left _ hcAt)
  -- Split off the head `x_{t+1}`.
  obtain ⟨r, hr⟩ : ∃ r : List V, q = x (t + 1) :: r := by
    rcases q with _ | ⟨w, l⟩
    · exact absurd hq.2.1 (by simp)
    · exact ⟨l, by rw [show w = x (t + 1) by simpa using hq.2.1]⟩
  subst hr
  have hrne : r ≠ [] := by
    rintro rfl
    have hcx : x (t + 1) = c := by simpa using hq.2.2
    exact hxnotAt (hcx ▸ hcAt)
  have hrlast : r.getLast? = some c := by
    have hgl := hq.2.2
    rwa [List.getLast?_cons_of_ne_nil hrne] at hgl
  -- `r` is a candidate.
  have hcandr : Cand G z A₀ x t r := by
    refine ⟨hq.1, hrne, ?_, c, hcA1, c, hrlast, Or.inl rfl⟩
    intro v hv
    rcases hqS v (List.mem_cons_of_mem _ hv) with hvAt | hvx
    · exact hvAt
    · exact absurd (by simpa using hq.1.2.1) (by
        simp only [Set.mem_singleton_iff] at hvx
        subst hvx
        simp only [List.nodup_cons, not_and, not_not]
        exact fun hcon => absurd hv hcon)
  -- Choose a candidate of minimum length.
  have hexn : ∃ n : ℕ, ∃ p : List V, Cand G z A₀ x t p ∧ p.length = n :=
    ⟨r.length, r, hcandr, rfl⟩
  obtain ⟨p, hpc, hpn⟩ := Nat.find_spec hexn
  have hmin : ∀ w : List V, Cand G z A₀ x t w → p.length ≤ w.length := by
    intro w hw
    rw [hpn]
    exact Nat.find_min' hexn ⟨w, hw, rfl⟩
  obtain ⟨hppath, hpne, hpAt, a₀, ha₀, v₀, hv₀last, hv₀⟩ := hpc
  have hplen0 : 0 < p.length := by
    rcases p with _ | ⟨w, l⟩
    · exact absurd rfl hpne
    · simp
  -- Adjacency along `x_{t+1} :: p`.
  have hadj0 : G.Adj (x (t + 1)) (p[0]'hplen0) := by
    have := PathBasics.path_adj_succ hppath (i := 0) (by simpa using hplen0)
    simpa using this
  have hadjp : ∀ (k : ℕ) (hk : k + 1 < p.length),
      G.Adj (p[k]'(by omega)) (p[k + 1]'hk) := by
    intro k hk
    have := PathBasics.path_adj_succ hppath (i := k + 1) (by simp; omega)
    simpa using this
  have hlastgen : ∀ (k : ℕ) (hk : k < p.length), k + 1 = p.length →
      p.getLast? = some (p[k]'hk) := by
    intro k hk hkeq
    have hgl := getLast?_take_succ p k hk
    rwa [hkeq, List.take_length] at hgl
  -- Truncating a candidate at any position where the next vertex is in `A_{t−1}`.
  have htrunc : ∀ (k : ℕ) (hk : k < p.length),
      (∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (p[k]'hk) a) → k + 1 = p.length := by
    intro k hk ha
    by_contra hne
    obtain ⟨a, haA1, hpa⟩ := ha
    have hlt : k + 1 < p.length := by omega
    have hcandw : Cand G z A₀ x t (p.take (k + 1)) := by
      refine ⟨?_, ?_, ?_, a, haA1, p[k]'hk, getLast?_take_succ p k hk, Or.inr hpa⟩
      · exact PathBasics.isPathList_take hppath (k := k + 2) (by omega)
      · simp only [ne_eq, List.take_eq_nil_iff, not_or]
        exact ⟨by omega, hpne⟩
      · exact fun w hw => hpAt w (List.take_subset _ _ hw)
    have := hmin _ hcandw
    rw [List.length_take] at this
    omega
  -- No vertex of `p` lies in `A_{t−1}`.
  have hnotA1 : ∀ (k : ℕ) (hk : k < p.length),
      (p[k]'hk) ∉ wheelSystemA G z A₀ x (t - 1) := by
    intro k hk hmem
    rcases k with _ | k'
    · exact hxt1 _ hmem hadj0
    · have hadjk : G.Adj (p[k']'(by omega)) (p[k' + 1]'hk) := hadjp k' hk
      have := htrunc k' (by omega) ⟨_, hmem, hadjk⟩
      omega
  -- Hence the last vertex of `p` genuinely has a neighbour in `A_{t−1}`.
  have hlastnbr : ∀ (k : ℕ) (hk : k < p.length), k + 1 = p.length →
      ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (p[k]'hk) a := by
    intro k hk hkeq
    have hveq : v₀ = p[k]'hk := by
      have hgl := hlastgen k hk hkeq
      rw [hgl] at hv₀last
      exact (Option.some.inj hv₀last).symm
    rcases hv₀ with heq | hadj
    · exact absurd (by rw [← hveq, heq]; exact ha₀ : (p[k]'hk) ∈ _) (hnotA1 k hk)
    · exact ⟨a₀, ha₀, by rw [← hveq]; exact hadj⟩
  refine ⟨p, hppath, hpne, ?_, ?_⟩
  · intro w hw
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
    exact ⟨hpAt _ hw, hnotA1 k hk⟩
  · intro k hk
    exact ⟨htrunc k hk, hlastnbr k hk⟩

/-- **Construction of the path, with its extremal choice** (printed p. 131, the paragraph
following claim (1)):

*"Since `x_{t+1}` has a neighbour in `A_t` and none in `A_{t−1}`, there is a path from
`x_{t+1}` to `A_{t−1}` with interior in `A_t \ A_{t−1}`.  Hence there is a path
`x_{t+1}-p₁-⋯-p_m` such that `p₁,…,p_m ∈ A_t \ A_{t−1}` and `p_m` is the unique vertex of this
path with a neighbour in `A_{t−1}`. …  Choose such a path such that if possible, every member
of `Y` has a neighbour in `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`."*

The *"if possible"* is discharged by cases: if some good path spans `Y` in that sense, take
it; otherwise the extremal clause is vacuous and any good path (`exists_goodPath_aux`) will
do. -/
theorem exists_goodPath {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (h : Setup G Y z A₀ x t) :
    ∃ p : List V, GoodPath G z A₀ x t p ∧
      ((∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q) →
        SpanY G z A₀ x t Y p) := by
  by_cases hex : ∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q
  · obtain ⟨q, hq, hs⟩ := hex
    exact ⟨q, hq, fun _ => hs⟩
  · obtain ⟨p, hp⟩ := exists_goodPath_aux h
    exact ⟨p, hp, fun hc => absurd hc hex⟩

/-- **Claim (1)** of the printed proof (printed p. 131). -/
theorem claim1 {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (h : Setup G Y z A₀ x t) :
    NoOddLeapPath G z A₀ x t := by
  classical
  rintro ⟨i, j, P, hi, hj, hL, hLodd, hL5, hPAt⟩
  obtain ⟨hG, -, hframe, ht, hhub, hxt₁A, -, -⟩ := h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hG.1.1.1.1
  let A := wheelSystemA G z A₀ x (t - 1)
  have hAcon : ConnectedSet G A :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hxiA : ∃ a ∈ A, G.Adj (x i) a :=
    Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
  have hxjA : ∃ a ∈ A, G.Adj (x j) a :=
    Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
  have hxiNotA : x i ∉ A := Thm203Prelim.x_notMem_wheelSystemA hws (by omega)
  have hxjNotA : x j ∉ A := Thm203Prelim.x_notMem_wheelSystemA hws (by omega)
  have hEndsNe : x i ≠ x j := PathBasics.isPathFrom_ends_ne hL (by omega)
  have hEndsNonadj : ¬ G.Adj (x i) (x j) := by
    have hlen : 3 ≤ (x i :: x (t + 1) :: P).length := by
      rw [PathBasics.pathLength_eq] at hL5
      omega
    have hn := PathBasics.path_ends_not_adj hL.1 hlen
    have hpos : 0 < (x i :: x (t + 1) :: P).length := by simp
    have hzero : (x i :: x (t + 1) :: P)[0]'hpos = x i := by simp
    have hlast : (x i :: x (t + 1) :: P)[(x i :: x (t + 1) :: P).length - 1]'(by omega) =
        x j := PathBasics.getElem_last_of_getLast? hL.2.2 hpos
    rw [hzero, hlast] at hn
    exact hn
  obtain ⟨S, hS, hSint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hAcon hxiNotA hxjNotA hxiA hxjA
  have hS3 : 3 ≤ S.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hS hEndsNe hEndsNonadj
  have hzS : z ∉ S := by
    intro hz
    by_cases hzi : z = x i
    · exact (hws.2.2.1 i (by omega)).2 hzi.symm
    by_cases hzj : z = x j
    · exact (hws.2.2.1 j (by omega)).2 hzj.symm
    have hzint : z ∈ SPGT.interior S :=
      (PathBasics.mem_interior_iff_of_pathFrom hS).2 ⟨hz, hzi, hzj⟩
    exact Thm203Prelim.z_notMem_wheelSystemA hws (by omega) (hSint z hzint)
  have hSeven : Even (pathLength S) := by
    by_cases hS4 : 4 ≤ S.length
    · have hclose : Even (S.length + 1) :=
        PrismBasics.even_of_path_closed_by_vertex hBerge hS hS4 hzS
          (hws.2.2.2.2.2.2 i (by omega)) (hws.2.2.2.2.2.2 j (by omega))
          (fun v hv => WheelSystemBasics.wheelSystemA_no_nbr (hSint v hv))
      obtain ⟨r, hr⟩ := hclose
      refine ⟨r - 1, ?_⟩
      rw [PathBasics.pathLength_eq]
      omega
    · have hlen : S.length = 3 := by omega
      rw [PathBasics.pathLength_eq, hlen]
      decide
  have hpar : ¬ Even (pathLength (x i :: x (t + 1) :: P) + pathLength S) := by
    intro he
    obtain ⟨a, ha⟩ := hLodd
    obtain ⟨b, hb⟩ := hSeven
    obtain ⟨c, hc⟩ := he
    omega
  have hlinked := TwoPathsHole.interiors_linked hBerge hL hS (by
      rw [PathBasics.pathLength_eq] at hL5
      omega) hS3 hpar
  have hPpath : IsPathList G P := by
    have hpos : 0 < P.length := by
      rw [PathBasics.pathLength_eq] at hL5
      simp only [List.length_cons] at hL5
      omega
    have hd := PathBasics.isPathList_drop hL.1 (k := 2) (by simpa using hpos)
    simpa using hd
  have hPlen : 4 ≤ P.length := by
    rw [PathBasics.pathLength_eq] at hL5
    simp only [List.length_cons] at hL5
    omega
  have hPne : P ≠ [] := by intro he; rw [he] at hPlen; simp at hPlen
  have hPlast : P.getLast? = some (x j) := by
    have hlast := hL.2.2
    simpa [List.getLast?_cons_of_ne_nil hPne] using hlast
  have hxjLast : P[P.length - 1]'(by omega) = x j :=
    PathBasics.getElem_last_of_getLast? hPlast (by omega)
  have hxt₁NotA : x (t + 1) ∉ A :=
    Thm203Prelim.x_notMem_wheelSystemA hws (by omega)
  have hBridge :
      (∃ v ∈ P, v ≠ x j ∧ v ∈ A) ∨
        ∃ v ∈ P, v ≠ x j ∧ ∃ a ∈ A, G.Adj v a := by
    rcases hlinked with ⟨v, hvL, hvS⟩ | ⟨v, hvL, a, haS, hva⟩
    · have hvA := hSint v hvS
      have hvEnds := (PathBasics.mem_interior_iff_of_pathFrom hL).1 hvL
      rcases List.mem_cons.mp hvEnds.1 with hvi | hvrest
      · exact absurd hvi hvEnds.2.1
      rcases List.mem_cons.mp hvrest with hvt | hvP
      · exact absurd (hvt.symm ▸ hvA) hxt₁NotA
      exact Or.inl ⟨v, hvP, hvEnds.2.2, hvA⟩
    · have haA := hSint a haS
      have hvEnds := (PathBasics.mem_interior_iff_of_pathFrom hL).1 hvL
      rcases List.mem_cons.mp hvEnds.1 with hvi | hvrest
      · exact absurd hvi hvEnds.2.1
      rcases List.mem_cons.mp hvrest with hvt | hvP
      · subst hvt
        exact absurd hva (hxt₁A a haA)
      exact Or.inr ⟨v, hvP, hvEnds.2.2, a, haA, hva⟩
  have hLink :
      ({v : V | v ∈ P} ∩ A).Nonempty ∨
        ∃ v ∈ ({v : V | v ∈ P} : Set V), ∃ a ∈ A, G.Adj v a := by
    rcases hBridge with ⟨v, hvP, -, hvA⟩ | ⟨v, hvP, -, a, haA, hva⟩
    · exact Or.inl ⟨v, hvP, hvA⟩
    · exact Or.inr ⟨v, hvP, a, haA, hva⟩
  have hPcon : ConnectedSet G {v : V | v ∈ P} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPpath
  have hFcon : ConnectedSet G (({v : V | v ∈ P} : Set V) ∪ A) :=
    ConnectedSetUnionAttach.connectedSet_union hPcon hAcon hLink
  have hp₁A : P[0]'(by omega) ∉ A := by
    intro hpA
    have hadj := PathBasics.path_adj_succ hL.1 (i := 1) (by simp; omega)
    have hadj' : G.Adj (x (t + 1)) (P[0]'(by omega)) := by simpa using hadj
    exact hxt₁A _ hpA hadj'
  have hexk : ∃ k : ℕ, ∃ hk : k + 1 < P.length,
      ((P[k]'(by omega)) ∈ A ∨ ∃ a ∈ A, G.Adj (P[k]'(by omega)) a) := by
    rcases hBridge with ⟨v, hvP, hvj, hvA⟩ | ⟨v, hvP, hvj, a, haA, hva⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hvP
      have hk' : k + 1 < P.length := by
        have hklt : k < P.length := by get_elem_tactic
        by_contra hnot
        have hkeq : k = P.length - 1 := by omega
        apply hvj
        rw [← hxjLast]
        exact hPpath.2.1.getElem_inj_iff.mpr hkeq
      exact ⟨k, hk', Or.inl hvA⟩
    · obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hvP
      have hk' : k + 1 < P.length := by
        have hklt : k < P.length := by get_elem_tactic
        by_contra hnot
        have hkeq : k = P.length - 1 := by omega
        apply hvj
        rw [← hxjLast]
        exact hPpath.2.1.getElem_inj_iff.mpr hkeq
      exact ⟨k, hk', Or.inr ⟨a, haA, hva⟩⟩
  let k := Nat.find hexk
  obtain ⟨hkBound, hkSpec⟩ := Nat.find_spec hexk
  have hkMin : ∀ r < k, ¬ (∃ hr : r + 1 < P.length,
      ((P[r]'(by omega)) ∈ A ∨ ∃ a ∈ A, G.Adj (P[r]'(by omega)) a)) := by
    intro r hr
    exact Nat.find_min hexk hr
  have hpkNotA : P[k]'(by omega) ∉ A := by
    intro hpkA
    have hkpos : 0 < k := by
      by_contra hk0
      have hkeq : k = 0 := by omega
      exact hp₁A (by simpa only [hkeq] using hpkA)
    have hpred : k - 1 + 1 < P.length := by omega
    have hadj := PathBasics.path_adj_succ hPpath (i := k - 1) (by omega)
    have hidx : k - 1 + 1 = k := by omega
    have hadj' : G.Adj (P[k - 1]'(by omega)) (P[k]'(by omega)) := by
      simpa only [hidx] using hadj
    exact hkMin (k - 1) (by omega) ⟨hpred, Or.inr ⟨P[k]'(by omega), hpkA, hadj'⟩⟩
  obtain ⟨a, haA, hpka⟩ := hkSpec.resolve_left hpkNotA
  have hpkNeXj : P[k]'(by omega) ≠ x j := by
    rw [← hxjLast]
    exact PathBasics.path_ne_of_ne_index hPpath (by omega) (by omega) (by omega)
  have hpkAt : P[k]'(by omega) ∈ wheelSystemA G z A₀ x t :=
    (hPAt _ (List.getElem_mem (by omega)) hpkNeXj)
  have hpkComplete : VertexComplete G (P[k]'(by omega)) (wheelSystemX x (t - 1)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega)
      (WheelSystemBasics.wheelSystemA_no_nbr hpkAt) hpkNotA ⟨a, haA, hpka⟩
  have hit : i = t := by
    by_contra hne
    have hadj := hpkComplete (x i) ⟨i, by omega, rfl⟩
    have hnadj := PathBasics.path_not_adj_of_gap hL.1
      (i := 0) (j := k + 2) (by simp) (by simp; omega) (by omega) (by omega)
    apply hnadj
    simpa using hadj.symm
  have hjlt : j ≤ t - 1 := by
    by_contra hne
    have hjt : j = t := by omega
    exact hEndsNe (by rw [hit, hjt])
  have hpkxj := hpkComplete (x j) ⟨j, hjlt, rfl⟩
  have hkLast : k + 2 = P.length := by
    have hadj : G.Adj (P[k]'(by omega)) (P[P.length - 1]'(by omega)) := by
      rwa [hxjLast]
    rcases (PathBasics.path_adj_iff hPpath (by omega) (by omega)).1 hadj with hh | hh
    · omega
    · omega
  have hxtxt₁ : G.Adj (x t) (x (t + 1)) := by
    have hadj := PathBasics.path_adj_succ hL.1 (i := 0) (by simp)
    simpa [hit] using hadj
  have hp₁NeXj : P[0]'(by omega) ≠ x j := by
    rw [← hxjLast]
    exact PathBasics.path_ne_of_ne_index hPpath (by omega) (by omega) (by omega)
  have hp₁NonadjXj : ¬ G.Adj (P[0]'(by omega)) (x j) := by
    rw [← hxjLast]
    exact PathBasics.path_not_adj_of_gap hPpath (by omega) (by omega) (by omega) (by omega)
  have hp₁NonadjXt : ¬ G.Adj (P[0]'(by omega)) (x t) := by
    have hn := PathBasics.path_not_adj_of_gap hL.1
      (i := 0) (j := 2) (by simp) (by simp; omega) (by omega) (by omega)
    intro hadj
    apply hn
    simpa [hit] using hadj.symm
  have hxjNonadjXt : ¬ G.Adj (x j) (x t) := by
    have hn := PathBasics.path_ends_not_adj hL.1 (by simp; omega)
    have hlast : (x i :: x (t + 1) :: P)[(x i :: x (t + 1) :: P).length - 1]'(by simp) =
        x j := PathBasics.getElem_last_of_getLast? hL.2.2 (by simp)
    intro hadj
    apply hn
    have hadj' : G.Adj (x i) (x j) := by
      rw [hit]
      exact hadj.symm
    simpa only [List.getElem_cons_zero, hlast] using hadj'
  let T : Set V := {z, x (t + 1), x t}
  let F : Set V := {v : V | v ∈ P} ∪ A
  have hTtri : IsTriangle G T := by
    have hzne1 : z ≠ x (t + 1) := (hws.2.2.1 (t + 1) le_rfl).2.symm
    have hznet : z ≠ x t := (hws.2.2.1 t (by omega)).2.symm
    have hne12 : x (t + 1) ≠ x t := hxtxt₁.ne.symm
    refine ⟨Set.ncard_eq_three.mpr ⟨z, x (t + 1), x t, hzne1, hznet, hne12, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (huv rfl).elim
    · exact hws.2.2.2.2.2.2 (t + 1) le_rfl
    · exact hws.2.2.2.2.2.2 t (by omega)
    · exact (hws.2.2.2.2.2.2 (t + 1) le_rfl).symm
    · exact (huv rfl).elim
    · exact hxtxt₁.symm
    · exact (hws.2.2.2.2.2.2 t (by omega)).symm
    · exact hxtxt₁
    · exact (huv rfl).elim
  have hFTA : F ⊆ Tᶜ := by
    intro v hv hvT
    rcases hv with hvP | hvA
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hvT
      rcases hvT with hvz | hvxt₁ | hvxt
      · have hzP : z ∈ P := hvz ▸ hvP
        by_cases he : z = x j
        · exact (hws.2.2.1 j (by omega)).2 he.symm
        · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
            ((hPAt z hzP he))
      · have hxt₁P : x (t + 1) ∈ P := hvxt₁ ▸ hvP
        exact (List.nodup_cons.mp (List.nodup_cons.mp hL.1.2.1).2).1 hxt₁P
      · have hn := (List.nodup_cons.mp hL.1.2.1).1
        rw [hit] at hn
        have hxtP : x t ∈ P := hvxt ▸ hvP
        exact hn (List.mem_cons_of_mem _ hxtP)
    · simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hvT
      rcases hvT with hvz | hvxt₁ | hvxt
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (by omega) (hvz ▸ hvA)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws le_rfl (hvxt₁ ▸ hvA)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (by omega) (hvxt ▸ hvA)
  have hzUnique : ∀ f ∈ F, G.Adj z f → f = x j := by
    intro f hf hzf
    rcases hf with hfP | hfA
    · by_cases he : f = x j
      · exact he
      · exact absurd hzf (WheelSystemBasics.wheelSystemA_no_nbr (hPAt f hfP he))
    · exact absurd hzf (WheelSystemBasics.wheelSystemA_no_nbr hfA)
  have hxt₁Unique : ∀ f ∈ F, G.Adj (x (t + 1)) f → f = P[0]'(by omega) := by
    intro f hf hadj
    rcases hf with hfP | hfA
    · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hfP
      have hadj' : G.Adj
          ((x i :: x (t + 1) :: P)[1]'(by simp))
          ((x i :: x (t + 1) :: P)[r + 2]'(by simp; omega)) := by simpa using hadj
      rcases (PathBasics.path_adj_iff hL.1 (by simp) (by simp; omega)).1 hadj' with he | he
      · have : r = 0 := by omega
        subst r
        rfl
      · omega
    · exact absurd hadj (hxt₁A f hfA)
  have hxtNoP : ∀ f ∈ P, ¬ G.Adj (x t) f := by
    intro f hfP
    obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hfP
    have hn := PathBasics.path_not_adj_of_gap hL.1
      (i := 0) (j := r + 2) (by simp) (by simp; omega) (by omega) (by omega)
    simpa [hit] using hn
  have hcatch : Catches G F T := by
    refine ⟨hTtri, hFcon, Set.disjoint_left.mpr hFTA, ?_⟩
    intro v hv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨x j, Or.inl (PathBasics.getLast_mem hPlast),
        hws.2.2.2.2.2.2 j (by omega)⟩
    · have hadj := PathBasics.path_adj_succ hL.1 (i := 1) (by simp; omega)
      exact ⟨P[0]'(by omega), Or.inl (List.getElem_mem _), by simpa using hadj⟩
    · obtain ⟨a, ha, hxa⟩ :=
        Thm203Prelim.exists_nbr_wheelSystemA hframe hws (i := t) (k := t - 1)
          (by omega) (by omega) (by omega)
      exact ⟨a, Or.inr ha, hxa⟩
  have hAtMostOne : ∀ f ∈ F, (G.neighborSet f ∩ T).ncard ≤ 1 := by
    intro f hf
    apply (Set.ncard_le_one (Set.toFinite _)).2
    intro u hu v hv
    obtain ⟨hfu, huT⟩ := hu
    obtain ⟨hfv, hvT⟩ := hv
    have hfu' : G.Adj f u := by simpa only [SimpleGraph.mem_neighborSet] using hfu
    have hfv' : G.Adj f v := by simpa only [SimpleGraph.mem_neighborSet] using hfv
    simp only [T, Set.mem_insert_iff, Set.mem_singleton_iff] at huT hvT
    rcases hf with hfP | hfA
    · have hft : ¬ G.Adj (x t) f := hxtNoP f hfP
      rcases huT with rfl | rfl | rfl <;> rcases hvT with rfl | rfl | rfl
      · rfl
      · have he1 := hzUnique f (Or.inl hfP) hfu'.symm
        have he2 := hxt₁Unique f (Or.inl hfP) hfv'.symm
        exact absurd (he1.symm.trans he2) hp₁NeXj.symm
      · exact (hft (by simpa using hfv'.symm)).elim
      · have he1 := hxt₁Unique f (Or.inl hfP) hfu'.symm
        have he2 := hzUnique f (Or.inl hfP) hfv'.symm
        exact absurd (he1.symm.trans he2) hp₁NeXj
      · rfl
      · exact (hft (by simpa using hfv'.symm)).elim
      · exact (hft (by simpa using hfu'.symm)).elim
      · exact (hft (by simpa using hfu'.symm)).elim
      · rfl
    · have hnz : ¬ G.Adj z f := WheelSystemBasics.wheelSystemA_no_nbr hfA
      have hnx : ¬ G.Adj (x (t + 1)) f := hxt₁A f hfA
      rcases huT with rfl | rfl | rfl <;> rcases hvT with rfl | rfl | rfl
      · rfl
      · exact (hnz hfu'.symm).elim
      · exact (hnz hfu'.symm).elim
      · exact (hnz hfv'.symm).elim
      · rfl
      · exact (hnx hfu'.symm).elim
      · exact (hnz hfv'.symm).elim
      · exact (hnx hfv'.symm).elim
      · rfl
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG T hTtri F hFTA hcatch with
    href | htwo
  · obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hTeq, hbF, href⟩ := href
    have hzT : z ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hTeq]; simp [T]
    have hxT : x (t + 1) ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hTeq]; simp [T]
    obtain ⟨bz, hbz, bx, hbx, hzbz, hxbx, hbzbx⟩ :=
      Scratch203.reflection_pair href hzT hxT
        (hws.2.2.1 (t + 1) le_rfl).2.symm
    have hbzj := hzUnique bz (hbF hbz) hzbz
    have hbxp := hxt₁Unique bx (hbF hbx) hxbx
    exact hp₁NonadjXj (by simpa [hbzj, hbxp] using hbzbx.symm)
  · obtain ⟨f, hfF, hf2⟩ := htwo
    have hf1 := hAtMostOne f hfF
    omega

/-- **Claim (2)** of the printed proof (printed p. 132): *"We may assume that one of
`x₀,…,x_t` is nonadjacent to both `x_{t+1}, p₁`."*  The *"we may assume"* is the printed
alternative that *"`x₀,…,x_{t+1}` is a `Y`-square, and the theorem holds by 20.1"*, i.e. the
conclusion of 21.2 itself. -/
theorem claim2 {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (h : Setup G Y z A₀ x t) {p : List V} (hp : GoodPath G z A₀ x t p) :
    Concl G Y ∨ Claim2 G x t p := by
  classical
  obtain ⟨hG, -, hframe, ht, hhub, hxt₁A, -, -⟩ := h
  obtain ⟨hppath, hpne, hpAt, hpattach⟩ := hp
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hG.1.1.1.1
  let A := wheelSystemA G z A₀ x (t - 1)
  let X := wheelSystemX x t
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  let p₁ : V := p[0]'hplen
  have hp₁head : p.head? = some p₁ := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hplen]
  have hp₁mem : p₁ ∈ p := List.getElem_mem hplen
  have hp₁At : p₁ ∈ wheelSystemA G z A₀ x t := (hpAt p₁ hp₁mem).1
  have hp₁NotA : p₁ ∉ A := (hpAt p₁ hp₁mem).2
  have hxt₁p₁ : G.Adj (x (t + 1)) p₁ := by
    have hadj := PathBasics.path_adj_succ hppath (i := 0) (by simp [hplen])
    simpa [p₁] using hadj
  have hXanti : AnticonnectedSet G X :=
    Thm203Prelim.anticonnected_wheelSystemX hws t (by omega)
  have hxt₁NotX : x (t + 1) ∉ X := by
    rintro ⟨j, hj, he⟩
    exact KiteTailBasics.hub_last_ne hhub hj he
  have hp₁NotX : p₁ ∉ X := by
    rintro ⟨j, hj, he⟩
    exact WheelSystemBasics.wheelSystemA_no_nbr hp₁At
      (by simpa [he] using hws.2.2.2.2.2.2 j (by omega))
  have hxt₁NC : ¬ VertexComplete G (x (t + 1)) X :=
    hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl
  have hp₁NC : ¬ VertexComplete G p₁ X :=
    WheelSystemBasics.wheelSystemA_no_complete hp₁At
  have hxt₁NC' : ∃ w ∈ X, ¬ G.Adj (x (t + 1)) w := by
    by_contra hn
    apply hxt₁NC
    intro w hw
    by_contra hnadj
    exact hn ⟨w, hw, hnadj⟩
  have hp₁NC' : ∃ w ∈ X, ¬ G.Adj p₁ w := by
    by_contra hn
    apply hp₁NC
    intro w hw
    by_contra hnadj
    exact hn ⟨w, hw, hnadj⟩
  obtain ⟨Q, hQ, hQint⟩ :=
    InducedPathExtraction.exists_antipath_interior_in hXanti hxt₁NotX hp₁NotX
      hxt₁NC' hp₁NC'
  have hQNotA : ∀ w ∈ Q, w ∉ A := by
    intro w hw hwA
    by_cases hw₁ : w = x (t + 1)
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl (hw₁ ▸ hwA)
    by_cases hwp : w = p₁
    · exact hp₁NotA (hwp ▸ hwA)
    have hwint : w ∈ SPGT.interior Q :=
      (PathBasics.mem_interior_iff_of_pathFrom hQ).2 ⟨hw, by simpa [hw₁] using hQ.2.1,
        by simpa [hwp] using hQ.2.2⟩
    obtain ⟨j, hj, he⟩ := hQint w hwint
    exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (he ▸ hwA)
  have hQintA : ∀ w ∈ SPGT.interior Q, ∃ a ∈ A, G.Adj w a := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := hQint w hw
    exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
  have hQintz : ∀ w ∈ SPGT.interior Q, G.Adj z w := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := hQint w hw
    exact hws.2.2.2.2.2.2 j (by omega)
  rcases Nat.even_or_odd (pathLength Q) with hQeven | hQodd
  · have hzNotP₁ : z ≠ p₁ := by
      intro he
      exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (he ▸ hp₁At)
    have hzQ : ∀ w ∈ Q, w ≠ p₁ → G.Adj z w := by
      intro w hw hwp
      by_cases hwxt : w = x (t + 1)
      · simpa [hwxt] using hws.2.2.2.2.2.2 (t + 1) le_rfl
      · exact hQintz w ((PathBasics.mem_interior_iff_of_pathFrom hQ).2
          ⟨hw, by simpa [hwxt] using hQ.2.1, by simpa [hwp] using hQ.2.2⟩)
    have hzNotQ : z ∉ Q := by
      intro hzQmem
      exact G.irrefl (hzQ z hzQmem hzNotP₁)
    let R := z :: Q.reverse
    have hR : IsAntipathFrom G R z (x (t + 1)) := by
      have hQr := PathBasics.isAntipathFrom_reverse hQ
      apply PathAttach.isPathFrom_cons hQr
      · rw [SimpleGraph.compl_adj]
        exact ⟨hzNotP₁, WheelSystemBasics.wheelSystemA_no_nbr hp₁At⟩
      · simpa [R] using hzNotQ
      · intro w hw hwp
        rw [SimpleGraph.compl_adj]
        intro hc
        exact hc.2 (hzQ w (by simpa using hw) hwp)
    let T : Set V := A ∪ {w : V | w ∈ p.tail}
    have hMemTail : ∀ {w : V}, w ∈ p.tail →
        ∃ j : ℕ, ∃ hj : j < p.length, 1 ≤ j ∧ p[j]'hj = w := by
      intro w hw
      cases p with
      | nil => exact absurd hw (by simp)
      | cons a l =>
          simp only [List.tail_cons] at hw
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
          exact ⟨j + 1, by simp; omega, by omega, by simp⟩
    have hGetElemTail : ∀ (j : ℕ) (hj : j < p.length), 1 ≤ j → p[j]'hj ∈ p.tail := by
      intro j hj hj1
      cases p with
      | nil => simp at hj
      | cons a l =>
          cases j with
          | zero => omega
          | succ k =>
              simpa using (List.getElem_mem (l := l) (i := k) (by simpa using hj))
    have hAcon : ConnectedSet G A :=
      WheelSystemBasics.connectedSet_wheelSystemA hframe.1
    have hTcon : ConnectedSet G T := by
      by_cases htail : p.tail = []
      · simpa [T, htail] using hAcon
      · have htailpos : 0 < p.tail.length := List.length_pos_of_ne_nil htail
        have htailPath : IsPathList G p.tail := by
          have hd := PathBasics.isPathList_drop hppath (k := 2) (by simpa using htailpos)
          simpa using hd
        have htailCon : ConnectedSet G {w : V | w ∈ p.tail} :=
          InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htailPath
        have hlen2 : 2 ≤ p.length := by
          simpa [List.length_tail] using htailpos
        let pm : V := p[p.length - 1]'(by omega)
        have hpmTail : pm ∈ p.tail := by
          exact hGetElemTail (p.length - 1) (by omega) (by omega)
        obtain ⟨a, ha, hpma⟩ := (hpattach (p.length - 1) (by omega)).mpr (by omega)
        exact ConnectedSetUnionAttach.connectedSet_union hAcon htailCon
          (Or.inr ⟨a, ha, pm, hpmTail, hpma.symm⟩)
    have hzT : z ∉ T := by
      rintro (hzA | hzTail)
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (by omega) hzA
      · have hzp : z ∈ p := List.mem_of_mem_tail hzTail
        exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
          ((hpAt z hzp).1)
    have hzTAnti : ∀ a ∈ T, ¬ G.Adj z a := by
      intro a ha
      rcases ha with ha | ha
      · exact WheelSystemBasics.wheelSystemA_no_nbr ha
      · exact WheelSystemBasics.wheelSystemA_no_nbr
          ((hpAt a (List.mem_of_mem_tail ha)).1)
    have hxt₁TAnti : ∀ a ∈ T, ¬ G.Adj (x (t + 1)) a := by
      intro a ha
      rcases ha with ha | ha
      · exact hxt₁A a ha
      · obtain ⟨j, hj, hj1, hje⟩ := hMemTail ha
        have hn := PathBasics.path_not_adj_of_gap hppath
          (i := 0) (j := j + 1) (by simp) (by simp; omega) (by omega) (by omega)
        intro hadj
        apply hn
        simpa only [List.getElem_cons_zero, List.getElem_cons_succ, hje] using hadj
    have hp₁NotTail : p₁ ∉ p.tail := by
      intro hpTail
      obtain ⟨j, hj, hj1, hje⟩ := hMemTail hpTail
      have hpNodup : p.Nodup := (List.nodup_cons.mp hppath.2.1).2
      have hje' : p[j]'hj = p[0]'hplen := by simpa [p₁] using hje
      have : j = 0 := hpNodup.getElem_inj_iff.mp hje'
      omega
    have hQTails : ∀ w ∈ Q, w ∉ p.tail := by
      intro w hw hwTail
      by_cases hwp : w = p₁
      · exact hp₁NotTail (hwp ▸ hwTail)
      · have hwAt := (hpAt w (List.mem_of_mem_tail hwTail)).1
        exact WheelSystemBasics.wheelSystemA_no_nbr hwAt (hzQ w hw hwp)
    have hRT : ∀ w ∈ R, w ∉ T := by
      intro w hw hwT
      rcases hwT with hwA | hwTail
      · rcases List.mem_cons.mp hw with hwz | hwQ
        · exact Thm203Prelim.z_notMem_wheelSystemA hws (by omega) (hwz ▸ hwA)
        · exact hQNotA w (by simpa using hwQ) hwA
      · rcases List.mem_cons.mp hw with hwz | hwQ
        · exact hzT (Or.inr (hwz ▸ hwTail))
        · exact hQTails w (by simpa using hwQ) hwTail
    have hRintT : ∀ w ∈ SPGT.interior R, ∃ a ∈ T, G.Adj w a := by
      intro w hw
      have hwdata := (PathBasics.mem_interior_iff_of_pathFrom hR).1 hw
      have hwQ : w ∈ Q := by
        rcases List.mem_cons.mp hwdata.1 with hwz | hwQr
        · exact absurd hwz hwdata.2.1
        · simpa using hwQr
      by_cases hwp : w = p₁
      · subst w
        by_cases hlen : p.length = 1
        · obtain ⟨a, ha, hadj⟩ := (hpattach 0 hplen).mpr (by omega)
          exact ⟨a, Or.inl ha, by simpa [p₁] using hadj⟩
        · have hlen2 : 2 ≤ p.length := by omega
          let p₂ : V := p[1]'(by omega)
          have hp₂Tail : p₂ ∈ p.tail := hGetElemTail 1 (by omega) (by omega)
          have hadj := PathBasics.path_adj_succ hppath (i := 1) (by simp; omega)
          exact ⟨p₂, Or.inr hp₂Tail, by simpa [p₁, p₂] using hadj⟩
      · have hwint : w ∈ SPGT.interior Q :=
          (PathBasics.mem_interior_iff_of_pathFrom hQ).2
            ⟨hwQ, by simpa using hwdata.2.2, by simpa [hwp] using hQ.2.2⟩
        obtain ⟨a, ha, hadj⟩ := hQintA w hwint
        exact ⟨a, Or.inl ha, hadj⟩
    have hRodd : Odd (pathLength R) := by
      obtain ⟨d, hd⟩ := hQeven
      refine ⟨d, ?_⟩
      rw [PathBasics.pathLength_cons, List.length_reverse, PathBasics.pathLength_eq] at *
      have hQpos := PathBasics.path_length_pos hQ.1
      omega
    have hRlen : pathLength R = 3 :=
      Thm203AntipathTools.antipath_length_three_of_odd hG.1.1 hTcon hR hRodd
        (hws.2.2.2.2.2.2 (t + 1) le_rfl) hRT hzTAnti hxt₁TAnti hRintT
    have hQlen : pathLength Q = 2 := by
      have hrevlen : Q.reverse.length = 3 := by
        simpa only [R, PathBasics.pathLength_cons] using hRlen
      rw [List.length_reverse] at hrevlen
      rw [PathBasics.pathLength_eq]
      have hQpos := PathBasics.path_length_pos hQ.1
      omega
    have hQlength : Q.length = 3 := by
      rw [PathBasics.pathLength_eq] at hQlen
      omega
    let q : V := Q[1]'(by omega)
    have hQzero : Q[0]'(by omega) = x (t + 1) :=
      PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hQtwo : Q[2]'(by omega) = p₁ := by
      have hh := PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
      simpa [hQlength] using hh
    have hqInt : q ∈ SPGT.interior Q := by
      apply (PathBasics.mem_interior_iff_of_pathFrom hQ).2
      refine ⟨List.getElem_mem (by omega), ?_, ?_⟩
      · intro he
        have he' : Q[0]'(by omega) = Q[1]'(by omega) := by
          rw [hQzero]
          simpa [q] using he.symm
        exact (by omega : (0 : ℕ) ≠ 1) (hQ.1.2.1.getElem_inj_iff.mp he')
      · intro he
        have he' : Q[1]'(by omega) = Q[2]'(by omega) := by
          rw [hQtwo]
          simpa [q] using he
        exact (by omega : (1 : ℕ) ≠ 2) (hQ.1.2.1.getElem_inj_iff.mp he')
    obtain ⟨s, hs, hq⟩ := hQint q hqInt
    have hqxt₁ : ¬ G.Adj q (x (t + 1)) := by
      have hadj := PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
      rw [SimpleGraph.compl_adj] at hadj
      exact fun h => hadj.2 (by simpa only [hQzero, q] using h.symm)
    have hqp₁ : ¬ G.Adj q p₁ := by
      have hadj := PathBasics.path_adj_succ hQ.1 (i := 1) (by omega)
      rw [SimpleGraph.compl_adj] at hadj
      exact fun h => hadj.2 (by simpa only [q, hQtwo] using h)
    exact Or.inr ⟨s, hs, by simpa [← hq] using hqxt₁,
      p₁, hp₁head, by simpa [← hq] using hqp₁⟩
  · have hp₁Nbr : ∃ a ∈ A, G.Adj p₁ a := by
      rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hBerge
          (WheelSystemBasics.connectedSet_wheelSystemA hframe.1)
          (Thm203Prelim.z_notMem_wheelSystemA hws (by omega))
          (fun a ha => WheelSystemBasics.wheelSystemA_no_nbr ha)
          hQ hQodd hxt₁p₁ hQNotA hQintA hQintz with hleft | hright
      · obtain ⟨a, ha, hadj⟩ := hleft
        exact (hxt₁A a ha hadj).elim
      · exact hright
    have hplen1 : p.length = 1 := by
      have hh := (hpattach 0 hplen).mp (by simpa [p₁] using hp₁Nbr)
      omega
    have hp₁Complete : VertexComplete G p₁ (wheelSystemX x (t - 1)) :=
      Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega)
        (WheelSystemBasics.wheelSystemA_no_nbr hp₁At) hp₁NotA hp₁Nbr
    have hp₁xt : ¬ G.Adj p₁ (x t) := by
      intro hadj
      apply WheelSystemBasics.wheelSystemA_no_complete hp₁At
      rintro w ⟨j, hj, rfl⟩
      by_cases hjt : j = t
      · simpa [hjt] using hadj
      · exact hp₁Complete (x j) ⟨j, by omega, rfl⟩
    by_cases htxt₁ : G.Adj (x t) (x (t + 1))
    · left
      have hYSquare : IsYSquare G z A₀ x (t + 1) Y := by
        refine ⟨hws, hhub.2.1, hhub.2.2.1, ⟨?_, ?_⟩,
          hhub.2.2.2.2.2.1, hhub.2.2.2.2.2.2, by omega, ?_, ?_, ?_⟩
        · intro hzY
          exact (hhub.2.2.2.1 z hzY).2 rfl
        · intro i hi hxiY
          by_cases hie : i = t + 1
          · exact KiteTailBasics.hub_last_notMem hhub (hie ▸ hxiY)
          · exact G.irrefl (hhub.2.2.2.2.2.1 i (by omega) (x i) hxiY)
        · simpa only [Nat.add_sub_cancel] using htxt₁.symm
        · simpa only [Nat.add_sub_cancel] using hxt₁A
        · refine ⟨p₁, ?_, hxt₁p₁.symm, ?_⟩
          · simpa only [Nat.add_sub_cancel] using hp₁At
          · simpa only [Nat.add_sub_cancel] using hp₁Nbr
      exact (_root_.Workspace.Statements.S20.SPGT.thm_20_1 G hG z A₀ hframe Y
        hhub.2.2.2.1 hhub.2.1 hhub.2.2.1
        (Or.inr ⟨x, t + 1, hYSquare⟩)).2
    · exact Or.inr ⟨t, le_rfl, htxt₁, p₁, hp₁head, fun hadj => hp₁xt hadj.symm⟩

/-- PAPER (21.2(3), p. 132): the set `A_{t-1} ∪ {p_j,…,p_m}` is
connected, since the last vertex of the path has a neighbour in `A_{t-1}`. -/
theorem goodPath_suffix_connected {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p) (k : ℕ) :
    ConnectedSet G (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p.drop k}) := by
  have hA : ConnectedSet G (wheelSystemA G z A₀ x (t - 1)) :=
    WheelSystemBasics.connectedSet_wheelSystemA h.2.2.1.1
  by_cases hk : k < p.length
  · have hpath : IsPathList G (p.drop k) := by
      have hh := PathBasics.isPathList_drop hp.1 (k := k + 1) (by simp; omega)
      simpa using hh
    have hlast : (p.drop k).getLast? = some (p[p.length - 1]'(by omega)) := by
      rw [List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)]
    obtain ⟨a, ha, hadj⟩ := (hp.2.2.2 (p.length - 1) (by omega)).mpr (by omega)
    exact ConnectedSetUnionAttach.connectedSet_union hA
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hpath)
      (Or.inr ⟨a, ha, _, PathBasics.getLast_mem hlast, hadj.symm⟩)
  · simpa [List.drop_eq_nil_of_le (by omega : p.length ≤ k)] using hA

/-- PAPER (21.2(3), p. 132): "all other members of `Y` have neighbours
in `{x_{t+1}} ∪ A_{t-1}`." Thus a path meeting the exceptional `y` meets all of `Y`. -/
theorem spanY_of_exceptional_neighbor {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {y : V} (hy : y ∈ Y)
    (hyno : VertexAnticomplete G y (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)}))
    {r : List V} (hyr : ∃ a ∈ r, G.Adj y a) : SpanY G z A₀ x t Y r := by
  classical
  intro w hw
  by_cases hwe : w = y
  · obtain ⟨a, ha, hya⟩ := hyr
    exact ⟨a, Or.inr (Or.inr ha), by simpa [hwe] using hya⟩
  · have hn : ¬ VertexAnticomplete G w
        (wheelSystemA G z A₀ x (t - 1) ∪ {x (t + 1)}) := by
      intro hn
      exact hwe (h.2.2.2.2.2.2.1 ⟨hw, hn⟩ ⟨hy, hyno⟩)
    simp only [VertexAnticomplete, not_forall, not_not, exists_prop] at hn
    obtain ⟨a, ha, hwa⟩ := hn
    exact ⟨a, by rcases ha with ha | ha; exact Or.inl ha; exact Or.inr (Or.inl ha), hwa⟩

/-- A rotation of a list with no repeated vertex is determined by its first vertex. -/
private theorem rotate_index_eq {H : List V} (hnd : H.Nodup)
    {i j : ℕ} (hj : j < H.length) {w : V}
    (hhead : (H.rotate i).head? = some w) (hjw : H[j]'hj = w) :
    H.rotate i = H.rotate j := by
  have hpos : 0 < H.length := by omega
  have hmod : i % H.length < H.length := Nat.mod_lt _ hpos
  have hg : (H.rotate i).head? = H[(0 + i) % H.length]? := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate hpos]
  rw [hg, Nat.zero_add, List.getElem?_eq_getElem hmod] at hhead
  have heq : H[i % H.length]'hmod = w := Option.some.inj hhead
  have hij : i % H.length = j := hnd.getElem_inj_iff.mp (heq.trans hjw.symm)
  rw [← List.rotate_mod H i, hij]

/-- Labelled gap: the first paragraph of 21.2(3), p. 132.
PAPER: "Since `y` has no neighbour in `A_{t-1} ∪ {p₁,…,p_m}`, it follows
from the minimality of `F` that `y` has a unique neighbour in `F`, say `f` ...
So `R` has length 2, and therefore `x_{t+1}` is adjacent to `f`."
Only the common neighbour furnished by this paragraph is retained. -/
theorem claim3_common_neighbor_gap {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p)
    (hc1 : NoOddLeapPath G z A₀ x t) {y : V} (hy : y ∈ Y)
    (hyno : ∀ a : V,
      (a ∈ wheelSystemA G z A₀ x (t - 1) ∨ a = x (t + 1) ∨ a ∈ p) →
        ¬ G.Adj y a) :
    ∃ f ∈ wheelSystemA G z A₀ x t, G.Adj y f ∧ G.Adj (x (t + 1)) f := by
  classical
  obtain ⟨hG, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hG.1.1.1.1
  -- `S = A_{t-1} ∪ {p₁,…,p_m}` is connected and lies in `A_t`.
  have hScon : ConnectedSet G
      (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) := by
    simpa using goodPath_suffix_connected h hp 0
  have hSAt : (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ⊆
      wheelSystemA G z A₀ x t := by
    rintro v (hv | hv)
    · exact WheelSystemBasics.wheelSystemA_mono (by omega) hv
    · exact (hp.2.2.1 v hv).1
  have hyAt : y ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (j := t) (by omega) hy
  have hyS : y ∉ (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) :=
    fun hm => hyAt (hSAt hm)
  have hynbrAt : ∃ a ∈ wheelSystemA G z A₀ x t, G.Adj y a := by
    refine hyA y hy ?_
    intro a ha
    rcases ha with ha | ha
    · exact hyno a (Or.inl ha)
    · exact hyno a (Or.inr (Or.inl ha))
  have hp0 : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hAtS : (wheelSystemA G z A₀ x t ∩
      (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p})).Nonempty :=
    ⟨p[0], (hp.2.2.1 _ (List.getElem_mem hp0)).1, Or.inr (List.getElem_mem hp0)⟩
  obtain ⟨pt, hptAtS, P, hP, hPpos, hPAt, hPS⟩ :=
    FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G
      (wheelSystemA G z A₀ x t) (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) y
      (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) hynbrAt hAtS hyS
  have hPlen2 : 2 ≤ P.length := by
    have := PathBasics.pathLength_eq P
    omega
  have hPnd : P.Nodup := PathBasics.path_nodup hP.1
  have hP0 : P[0]'(by omega) = y := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hPlast : P[P.length - 1]'(by omega) = pt :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  -- The vertices of `P` other than `y`, as the list `P.drop 1`.
  have hDpath : IsPathList G (P.drop 1) := PathBasics.isPathList_drop hP.1 (by omega)
  have hDidx : ∀ w ∈ P.drop 1, ∃ (j : ℕ) (hj : j + 1 < P.length), P[j + 1]'hj = w := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    simp only [List.length_drop] at hj
    exact ⟨j, by omega, by simp only [List.getElem_drop]; ring_nf⟩
  have hDne : ∀ w ∈ P.drop 1, w ≠ y := by
    intro w hw he
    obtain ⟨j, hj, rfl⟩ := hDidx w hw
    have := hPnd.getElem_inj_iff.mp (he.trans hP0.symm)
    omega
  have hDAt : ∀ w ∈ P.drop 1, w ∈ wheelSystemA G z A₀ x t :=
    fun w hw => hPAt w (List.mem_of_mem_drop hw) (hDne w hw)
  have hptD : pt ∈ P.drop 1 := by
    have : P.drop 1 ≠ [] := by
      intro he
      have := congrArg List.length he
      simp only [List.length_drop, List.length_nil] at this
      omega
    have hidx : P.length - 2 < (P.drop 1).length := by
      simp only [List.length_drop]; omega
    have he : (P.drop 1)[P.length - 2]'hidx = pt := by
      simp only [List.getElem_drop]
      rw [← hPlast]
      exact hPnd.getElem_inj_iff.mpr (by omega)
    exact he ▸ List.getElem_mem hidx
  have hfD : P[1]'(by omega) ∈ P.drop 1 := by
    have hidx : 0 < (P.drop 1).length := by simp only [List.length_drop]; omega
    have he : (P.drop 1)[0]'hidx = P[1]'(by omega) := by
      simp only [List.getElem_drop]
    exact he ▸ List.getElem_mem hidx
  have hyf : G.Adj y (P[1]'(by omega)) := by
    have := PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
    simpa only [hP0] using this
  have hDuniq : ∀ w ∈ P.drop 1, G.Adj y w → w = P[1]'(by omega) := by
    intro w hw hadj
    obtain ⟨j, hj, rfl⟩ := hDidx w hw
    rw [← hP0] at hadj
    have := (PathBasics.path_adj_iff hP.1 (show 0 < P.length by omega) hj).mp hadj
    have hj0 : j = 0 := by omega
    exact hPnd.getElem_inj_iff.mpr (by omega)
  -- The connected set `F` of the printed proof.
  have hFcon : ConnectedSet G
      ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪ {w : V | w ∈ P.drop 1}) :=
    ConnectedSetUnionAttach.connectedSet_union hScon
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hDpath)
      (Or.inl ⟨pt, (hPS pt (List.mem_of_mem_drop hptD)).mpr rfl, hptD⟩)
  have hFAt : ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}) ⊆ wheelSystemA G z A₀ x t := by
    rintro v (hv | hv)
    · exact hSAt hv
    · exact hDAt v hv
  have hyF : y ∉ ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}) := fun hm => hyAt (hFAt hm)
  have hfF : (P[1]'(by omega)) ∈ ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}) := Or.inr hfD
  -- The unique neighbour of `y` in `F`.
  have hFuniq : ∀ w ∈ ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}), G.Adj y w → w = P[1]'(by omega) := by
    rintro w (hw | hw) hadj
    · rcases hw with hw | hw
      · exact absurd hadj (hyno w (Or.inl hw))
      · exact absurd hadj (hyno w (Or.inr (Or.inr hw)))
    · exact hDuniq w hw hadj
  have hxt1At : x (t + 1) ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
  have hxt1F : x (t + 1) ∉ ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}) := fun hm => hxt1At (hFAt hm)
  have hxt1p0 : G.Adj (x (t + 1)) (p[0]'hp0) := by
    have := PathBasics.path_adj_succ hp.1 (i := 0) (by simp; omega)
    simpa using this
  have hxt1nbr : ∃ w ∈ ((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
      {w : V | w ∈ P.drop 1}), G.Adj (x (t + 1)) w :=
    ⟨p[0], Or.inl (Or.inr (List.getElem_mem hp0)), hxt1p0⟩
  obtain ⟨R, hR, hRint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFcon hyF hxt1F ⟨_, hfF, hyf⟩ hxt1nbr
  have hzy : G.Adj z y := hhub.2.2.2.2.1 y hy
  have hyXt : VertexComplete G y (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    exact (hhub.2.2.2.2.2.1 j (by omega) y hy).symm
  have hxt1notXt : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x t) := by
    have hh := hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl
    simpa only [Nat.add_sub_cancel] using hh
  have hyne : y ≠ x (t + 1) := fun he => hxt1notXt (he ▸ hyXt)
  have hynadjx : ¬ G.Adj y (x (t + 1)) := hyno _ (Or.inr (Or.inl rfl))
  have hR3 : 3 ≤ R.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hR hyne hynadjx
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hzint : ∀ w ∈ SPGT.interior R, ¬ G.Adj z w := by
    intro w hw
    exact WheelSystemBasics.wheelSystemA_no_nbr (hFAt (hRint w hw))
  have hzR : z ∉ R := by
    intro hz
    by_cases hzy' : z = y
    · exact (hhub.2.2.2.1 y hy).2 hzy'.symm
    by_cases hzx' : z = x (t + 1)
    · exact (hws.2.2.1 (t + 1) le_rfl).2 hzx'.symm
    exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
      (hFAt (hRint z ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hz, hzy', hzx'⟩)))
  have hRlen2 : 2 ≤ pathLength R := by
    have := PathBasics.pathLength_eq R
    omega
  have hC : IsHoleList G (z :: R) :=
    PrismBasics.isHoleList_of_path_add_vertex hR hRlen2 hzy hzxt1 hzR hzint
  have hCeven : Even (pathLength R + 2) := by
    have hh := hBerge.1 _ hC
    rwa [PrismBasics.holeLength_cons z (PathBasics.path_ne_nil hR.1)] at hh
  have hReven : Even (pathLength R) := by
    obtain ⟨d, hd⟩ := hCeven
    exact ⟨d - 1, by omega⟩
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  have hR0 : R[0]'(by omega) = y := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hRlast : R[R.length - 1]'(by omega) = x (t + 1) :=
    PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  rcases (show pathLength R = 2 ∨ 4 ≤ pathLength R by
      obtain ⟨d, hd⟩ := hReven; omega) with hR2 | hR4
  · -- *"So `R` has length 2, and therefore `x_{t+1}` is adjacent to `f`."*
    have hRlen3 : R.length = 3 := by
      have := PathBasics.pathLength_eq R
      omega
    have h1lt : 1 < R.length := by omega
    have hyR1 : G.Adj y (R[1]'h1lt) := by
      have hh := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
      simpa only [hR0] using hh
    have hR1x : G.Adj (R[1]'h1lt) (x (t + 1)) := by
      have hh := PathBasics.path_adj_succ hR.1 (i := 1) (by omega)
      have he : R[1 + 1]'(by omega) = x (t + 1) := by
        rw [← hRlast]; exact hRnd.getElem_inj_iff.mpr (by omega)
      simpa only [he] using hh
    have hR1int : (R[1]'h1lt) ∈ SPGT.interior R := by
      refine (PathBasics.mem_interior_iff_of_pathFrom hR).mpr
        ⟨List.getElem_mem h1lt, ?_, ?_⟩
      · rw [← hR0]; exact fun he => by simpa using hRnd.getElem_inj_iff.mp he
      · rw [← hRlast]; exact fun he => by
          have := hRnd.getElem_inj_iff.mp he; omega
    exact ⟨R[1]'h1lt, hFAt (hRint _ hR1int), hyR1, hR1x.symm⟩
  · -- *"Suppose it has length ≥ 4."*  We derive a contradiction.
    exfalso
    have hR5 : 5 ≤ R.length := by
      have := PathBasics.pathLength_eq R
      omega
    have h1lt : 1 < R.length := by omega
    -- the second vertex `f` of `R` is the unique neighbour of `y` in `F`
    have hyR1 : G.Adj y (R[1]'h1lt) := by
      have hh := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
      simpa only [hR0] using hh
    have hR1int : (R[1]'h1lt) ∈ SPGT.interior R := by
      refine (PathBasics.mem_interior_iff_of_pathFrom hR).mpr
        ⟨List.getElem_mem h1lt, ?_, ?_⟩
      · rw [← hR0]; exact fun he => by simpa using hRnd.getElem_inj_iff.mp he
      · rw [← hRlast]; exact fun he => by
          have := hRnd.getElem_inj_iff.mp he; omega
    have hR1F := hRint _ hR1int
    have hR1x : ¬ G.Adj (x (t + 1)) (R[1]'h1lt) := by
      rw [← hRlast]
      intro hadj
      exact PathBasics.path_not_adj_of_gap hR.1 (i := 1) (j := R.length - 1)
        h1lt (by omega) (by omega) (by omega) hadj.symm
    -- the hole `C = z-y-r₁-⋯-x_{t+1}-z`
    have hcX : ∀ w ∈ (z :: R), w ∉ wheelSystemX x t := by
      rintro w hw ⟨j, hj, rfl⟩
      rcases List.mem_cons.mp hw with he | hw
      · exact (hws.2.2.1 j (by omega)).2 he
      · by_cases hjy : x j = y
        · exact G.irrefl (hjy ▸ hyXt (x j) ⟨j, hj, rfl⟩)
        by_cases hjx : x j = x (t + 1)
        · have := hws.2.1 j (by omega) (t + 1) le_rfl hjx
          omega
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (i := t) (by omega)
            (hFAt (hRint _ ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr
              ⟨hw, hjy, hjx⟩)))
    have hzXt : VertexComplete G z (wheelSystemX x t) := by
      rintro w ⟨j, hj, rfl⟩
      exact hws.2.2.2.2.2.2 j (by omega)
    have honly : ∀ w ∈ (z :: R), VertexComplete G w (wheelSystemX x t) →
        w = z ∨ w = y := by
      intro w hw hwc
      rcases List.mem_cons.mp hw with he | hw
      · exact Or.inl he
      · by_cases hwy : w = y
        · exact Or.inr hwy
        by_cases hwx : w = x (t + 1)
        · exact absurd (hwx ▸ hwc) hxt1notXt
        · exact absurd hwc (WheelSystemBasics.wheelSystemA_no_complete
            (hFAt (hRint _ ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr
              ⟨hw, hwy, hwx⟩))))
    have hholeLen : holeLength (z :: R) = pathLength R + 2 :=
      PrismBasics.holeLength_cons z (PathBasics.path_ne_nil hR.1)
    have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge
      (wheelSystemX x t) (Thm203Prelim.anticonnected_wheelSystemX hws t (by omega))
      (z :: R) hC hcX (by rw [hholeLen]; omega) z y (by simp)
      (List.mem_cons_of_mem _ (PathBasics.head_mem hR.2.1)) hzy hzXt hyXt honly
    rcases h210 with ⟨w0, hw0X, hhat⟩ | ⟨a, haX, b, hbX, hleap⟩
    · -- *"there exists `x ∈ X_t` with no neighbours in `C` except `y, z`"*
      obtain ⟨j0, hj0, rfl⟩ := hw0X
      have hnoC := hhat.2.2.2.2.2.2
      have hxj0z : G.Adj z (x j0) := hws.2.2.2.2.2.2 j0 (by omega)
      have hxj0y : G.Adj (x j0) y := hhat.2.2.2.2.2.1
      have hxj0At : x j0 ∉ wheelSystemA G z A₀ x t :=
        Thm203Prelim.x_notMem_wheelSystemA hws (i := t) (by omega)
      have hxj0ne : x j0 ≠ x (t + 1) := by
        intro he
        have := hws.2.1 j0 (by omega) (t + 1) le_rfl he
        omega
      have hR1mem : (R[1]'h1lt) ∈ (z :: R) := List.mem_cons_of_mem _ (List.getElem_mem h1lt)
      have hR1nez : (R[1]'h1lt) ≠ z := fun he => hzR (he ▸ List.getElem_mem h1lt)
      have hR1ney : (R[1]'h1lt) ≠ y := by
        rw [← hR0]; exact fun he => by simpa using hRnd.getElem_inj_iff.mp he
      have hxt1mem : x (t + 1) ∈ (z :: R) :=
        List.mem_cons_of_mem _ (PathBasics.getLast_mem hR.2.2)
      have hxt1nez : x (t + 1) ≠ z := (hws.2.2.1 (t + 1) le_rfl).2
      have hxt1ney : x (t + 1) ≠ y := fun he => hyne he.symm
      -- the catching set `F ∪ {x_{t+1}}` and the triangle `{x_{j₀}, y, z}`
      have hFxcon : ConnectedSet G
          (((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
            {w : V | w ∈ P.drop 1}) ∪ {x (t + 1)}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hFcon hxt1nbr
      have hTtri : IsTriangle G ({x j0, y, z} : Set V) := by
        refine ⟨Set.ncard_eq_three.mpr ⟨x j0, y, z, hxj0y.ne, hxj0z.ne', hzy.ne', rfl⟩, ?_⟩
        intro u hu v hv huv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
        · exact (huv rfl).elim
        · exact hxj0y
        · exact hxj0z.symm
        · exact hxj0y.symm
        · exact (huv rfl).elim
        · exact hzy.symm
        · exact hxj0z
        · exact hzy
        · exact (huv rfl).elim
      have hFxT : ∀ v ∈ (((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
          {w : V | w ∈ P.drop 1}) ∪ {x (t + 1)}), v ∉ ({x j0, y, z} : Set V) := by
        rintro v (hv | hv) hvT <;>
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hvT
        · rcases hvT with rfl | rfl | rfl
          · exact hxj0At (hFAt hv)
          · exact hyF hv
          · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (hFAt hv)
        · rw [Set.mem_singleton_iff] at hv
          subst hv
          rcases hvT with he | he | he
          · exact hxj0ne he.symm
          · exact hxt1ney he
          · exact hxt1nez he
      have hcatch : Catches G
          (((wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p}) ∪
            {w : V | w ∈ P.drop 1}) ∪ {x (t + 1)}) ({x j0, y, z} : Set V) := by
        refine ⟨hTtri, hFxcon, Set.disjoint_left.mpr hFxT, ?_⟩
        intro v hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
        rcases hv with rfl | rfl | rfl
        · obtain ⟨c, hc, hxc⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
            (i := j0) (k := t - 1) (by omega) (by omega) (by omega)
          exact ⟨c, Or.inl (Or.inl (Or.inl hc)), hxc⟩
        · exact ⟨P[1], Or.inl hfF, hyf⟩
        · exact ⟨x (t + 1), Or.inr rfl, hzxt1⟩
      refine Thm212Claim3Tools.catch_obstruction hG hcatch
        (u := z) (v := y) (z := x (t + 1)) (by simp) (by simp) hzy.ne ?_ ?_ ?_
      · rintro w (hw | hw) hadj
        · exact absurd hadj (WheelSystemBasics.wheelSystemA_no_nbr (hFAt hw))
        · rw [Set.mem_singleton_iff] at hw; exact hw
      · rintro w (hw | hw) hadj hyw
        · have he := hFuniq w hw hyw
          have he2 : w = R[1]'h1lt := by
            have := hFuniq _ hR1F hyR1
            rw [he, this]
          exact hR1x (he2 ▸ hadj)
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          exact G.irrefl hadj
      · intro w hw
        refine (Set.ncard_le_one (Set.toFinite _)).2 ?_
        rintro u ⟨hwu, huT⟩ v ⟨hwv, hvT⟩
        simp only [SimpleGraph.mem_neighborSet] at hwu hwv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at huT hvT
        rcases hw with hw | hw
        · -- `w ∈ F`: not adjacent to `z`; adjacent to `y` only if `w = R[1]`,
          -- and then not adjacent to the hat.
          have hnz : ¬ G.Adj w z :=
            fun hc => WheelSystemBasics.wheelSystemA_no_nbr (hFAt hw) hc.symm
          have hkey : ¬ (G.Adj w y ∧ G.Adj w (x j0)) := by
            rintro ⟨h1, h2⟩
            have he : w = R[1]'h1lt := by
              have := hFuniq _ hR1F hyR1
              rw [hFuniq w hw h1.symm, this]
            exact hnoC _ hR1mem hR1nez hR1ney (he ▸ h2).symm
          rcases huT with rfl | rfl | rfl <;> rcases hvT with rfl | rfl | rfl
          · rfl
          · exact absurd ⟨hwv, hwu⟩ hkey
          · exact (hnz hwv).elim
          · exact absurd ⟨hwu, hwv⟩ hkey
          · rfl
          · exact (hnz hwv).elim
          · exact (hnz hwu).elim
          · exact (hnz hwu).elim
          · rfl
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          have hny : ¬ G.Adj (x (t + 1)) y := fun hc => hynadjx hc.symm
          have hnh : ¬ G.Adj (x (t + 1)) (x j0) :=
            fun hc => hnoC _ hxt1mem hxt1nez hxt1ney hc.symm
          rcases huT with rfl | rfl | rfl <;> rcases hvT with rfl | rfl | rfl
          · rfl
          · exact (hnh hwu).elim
          · exact (hnh hwu).elim
          · exact (hnh hwv).elim
          · rfl
          · exact (hny hwu).elim
          · exact (hnh hwv).elim
          · exact (hny hwv).elim
          · rfl
    · -- *"By (1) there is no leap."*
      obtain ⟨M, hReq⟩ : ∃ M : List V, R = y :: M := by
        cases hRc : R with
        | nil => rw [hRc] at hR3; simp at hR3
        | cons c M =>
            refine ⟨M, ?_⟩
            have := hR.2.1
            rw [hRc] at this
            simp only [List.head?_cons, Option.some.injEq] at this
            rw [this]
      have hMlen : M.length = R.length - 1 := by rw [hReq]; simp
      have hMne : M ≠ [] := by
        intro he; rw [he] at hMlen; simp at hMlen; omega
      have hMpath : IsPathList G M := by
        have hh := PathBasics.isPathList_drop hR.1 (k := 1) (by omega)
        rw [hReq] at hh
        simpa using hh
      have hMlast : M.getLast? = some (x (t + 1)) := by
        have := hR.2.2
        rw [hReq, List.getLast?_cons_of_ne_nil hMne] at this
        exact this
      have hnd : (z :: y :: M).Nodup := by rw [← hReq]; exact hC.2.1
      have hcXeq : ∀ w ∈ (z :: y :: M), w ∉ wheelSystemX x t := by
        rw [← hReq]; exact hcX
      have haH : a ∉ (z :: y :: M) := fun hm => hcXeq a hm haX
      have hbH : b ∉ (z :: y :: M) := fun hm => hcXeq b hm hbX
      have haz : a ≠ z := by rintro rfl; exact haH (by simp)
      have hay : a ≠ y := by rintro rfl; exact haH (by simp)
      have hbz : b ≠ z := by rintro rfl; exact hbH (by simp)
      have hby : b ≠ y := by rintro rfl; exact hbH (by simp)
      have haM : a ∉ M := fun hm => haH (by simp [hm])
      have hbM : b ∉ M := fun hm => hbH (by simp [hm])
      have hMlen4 : 4 ≤ M.length := by omega
      have hCeq : (z :: R) = z :: y :: M := by rw [hReq]
      rcases hleap with hleap | hleap
      · obtain ⟨-, i, hhd, hlst, hpl, hplen2, hab, hnab, hAdjA, hAdjB⟩ := hleap
        rw [hCeq] at hhd hlst hpl hAdjA hAdjB
        have hrot : (z :: y :: M).rotate i = (z :: y :: M).rotate 1 :=
          rotate_index_eq hnd (j := 1) (by simp) hhd (by simp)
        rw [hrot] at hAdjA hAdjB
        have hProt : (z :: y :: M).rotate 1 = y :: (M ++ [z]) := by
          rw [List.rotate_cons_succ]; simp
        rw [hProt] at hAdjA hAdjB
        have hPlen : (y :: (M ++ [z])).length = M.length + 2 := by simp
        have hbridge : ∀ (c w : V), c ≠ z → c ≠ y →
            ((G.deleteEdges {s(z, y)}).Adj c w ↔ G.Adj c w) := by
          intro c w hcz hcy
          rw [SimpleGraph.deleteEdges_adj]
          refine ⟨fun hq => hq.1, fun hq => ⟨hq, ?_⟩⟩
          simp only [Set.mem_singleton_iff, Sym2.eq_iff]
          rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · exact hcz h1
          · exact hcy h1
        have hPmid : ∀ (m : ℕ) (hm : m < M.length) (h2 : m + 1 < (y :: (M ++ [z])).length),
            (y :: (M ++ [z]))[m + 1]'h2 = M[m]'hm := by
          intro m hm h2
          simp only [List.getElem_cons_succ]
          exact List.getElem_append_left hm
        have hM0lt : (0 : ℕ) < M.length := by omega
        have hMklt : M.length - 1 < M.length := by omega
        have hAM : G.Adj a (M[0]'hM0lt) := by
          have hi1 : (0 : ℕ) + 1 < (y :: (M ++ [z])).length := by rw [hPlen]; omega
          have hq := (hAdjA (0 + 1) hi1).mpr (Or.inr (Or.inl rfl))
          rw [hPmid 0 hM0lt hi1] at hq
          exact (hbridge a _ haz hay).mp hq
        have hAother : ∀ w ∈ M, w ≠ (M[0]'hM0lt) → ¬ G.Adj a w := by
          intro w hw hw0 hcontra
          obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
          have hi1 : m + 1 < (y :: (M ++ [z])).length := by rw [hPlen]; omega
          have hq := (hAdjA (m + 1) hi1).mp
            (by rw [hPmid m hm hi1]; exact (hbridge a _ haz hay).mpr hcontra)
          rw [hPlen] at hq
          have hm0 : m = 0 := by omega
          exact hw0 (by subst hm0; rfl)
        have hBM : G.Adj b (M[M.length - 1]'hMklt) := by
          have hi1 : (M.length - 1) + 1 < (y :: (M ++ [z])).length := by rw [hPlen]; omega
          have hq := (hAdjB ((M.length - 1) + 1) hi1).mpr
            (Or.inr (Or.inl (by rw [hPlen]; omega)))
          rw [hPmid (M.length - 1) hMklt hi1] at hq
          exact (hbridge b _ hbz hby).mp hq
        have hBother : ∀ w ∈ M, w ≠ (M[M.length - 1]'hMklt) → ¬ G.Adj b w := by
          intro w hw hwk hcontra
          obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
          have hi1 : m + 1 < (y :: (M ++ [z])).length := by rw [hPlen]; omega
          have hq := (hAdjB (m + 1) hi1).mp
            (by rw [hPmid m hm hi1]; exact (hbridge b _ hbz hby).mpr hcontra)
          rw [hPlen] at hq
          have hmk : m = M.length - 1 := by omega
          exact hwk (by subst hmk; rfl)
        have hnab' : ¬ G.Adj a b := fun hq => hnab ((hbridge a b haz hay).mpr hq)
        have hMhead : M.head? = some (M[0]'hM0lt) := by
          rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hM0lt]
        have hMlast' : M.getLast? = some (M[M.length - 1]'hMklt) := by
          rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hMklt]
        have hMfrom : IsPathFrom G M (M[0]'hM0lt) (M[M.length - 1]'hMklt) :=
          ⟨hMpath, hMhead, hMlast'⟩
        have hL : IsPathFrom G (a :: (M ++ [b])) a b :=
          PathAttach.isPathFrom_cons_concat hMfrom hAM hBM hnab' hab haM hbM hAother hBother
        -- reverse the path and feed it to claim (1)
        have hxt1eq : M[M.length - 1]'hMklt = x (t + 1) := by
          rw [hMlast'] at hMlast
          exact (Option.some.inj hMlast)
        have hLrev : IsPathFrom G (a :: (M ++ [b])).reverse b a :=
          PathBasics.isPathFrom_reverse hL
        have hrevshape : (a :: (M ++ [b])).reverse = b :: (M.reverse ++ [a]) := by
          simp
        have hMrev : M.reverse = x (t + 1) :: M.reverse.tail := by
          have : M.reverse.head? = some (x (t + 1)) := by
            rw [List.head?_reverse]; exact hMlast
          exact (List.cons_head?_tail this).symm
        obtain ⟨P0, hP0eq⟩ : ∃ P0 : List V,
            (a :: (M ++ [b])).reverse = b :: x (t + 1) :: P0 :=
          ⟨M.reverse.tail ++ [a], by rw [hrevshape, hMrev]; simp⟩
        obtain ⟨ja, hja, rfl⟩ := haX
        obtain ⟨jb, hjb, rfl⟩ := hbX
        rw [hP0eq] at hLrev
        have hlen0 : pathLength (x jb :: x (t + 1) :: P0) = M.length + 1 := by
          rw [← hP0eq, PathBasics.pathLength_reverse,
            PathAttach.pathLength_cons_append_singleton]
        have hMeven : Even M.length := by
          have : M.length = pathLength R := by
            rw [PathBasics.pathLength_eq]; omega
          rw [this]; exact hReven
        have hndrev : (x jb :: x (t + 1) :: P0).Nodup := by
          rw [← hP0eq]; exact List.nodup_reverse.mpr (PathBasics.path_nodup hL.1)
        refine hc1 ⟨jb, ja, P0, hjb, hja, hLrev, ?_, ?_, ?_⟩
        · rw [hlen0]; obtain ⟨d, hd⟩ := hMeven; exact ⟨d, by omega⟩
        · rw [hlen0]; omega
        · intro v hv hvne
          have hvL : v ∈ (x ja :: (M ++ [x jb])).reverse := by
            rw [hP0eq]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hv)
          have hvL' : v ∈ (x ja :: (M ++ [x jb])) := List.mem_reverse.mp hvL
          have hvb : v ≠ x jb := by
            intro he; exact (List.nodup_cons.mp hndrev).1 (he ▸
              List.mem_cons_of_mem _ hv)
          have hvx : v ≠ x (t + 1) := by
            intro he
            exact (List.nodup_cons.mp (List.nodup_cons.mp hndrev).2).1 (he ▸ hv)
          have hvM : v ∈ M := by
            rcases List.mem_cons.mp hvL' with he | hq
            · exact absurd he hvne
            · rcases List.mem_append.mp hq with hq | hq
              · exact hq
              · exact absurd (by simpa using hq) hvb
          have hvR : v ∈ R := by rw [hReq]; exact List.mem_cons_of_mem _ hvM
          have hvy : v ≠ y := by
            intro he
            exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (he ▸ hvM)
          exact hFAt (hRint v ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr
            ⟨hvR, hvy, hvx⟩))
      · -- the impossible orientation
        obtain ⟨-, i, hhd, hlst, -⟩ := hleap
        rw [hCeq] at hhd hlst
        have hrot : (z :: y :: M).rotate i = (z :: y :: M).rotate 0 :=
          rotate_index_eq hnd (j := 0) (by simp) hhd (by simp)
        rw [hrot, List.rotate_zero] at hlst
        have hlenH : (z :: y :: M).length = M.length + 2 := by simp
        rw [List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (show (z :: y :: M).length - 1 <
            (z :: y :: M).length by omega)] at hlst
        have hy1 : (z :: y :: M)[1]'(by omega) = y := by simp
        have hidx := hnd.getElem_inj_iff.mp ((Option.some.inj hlst).trans hy1.symm)
        omega


/-- PAPER (21.2(3), p. 132): "it follows that `f` has no neighbours in
`A_{t-1}`", since otherwise `x_{t+1}-f` would be a better path. -/
theorem claim3_common_neighbor_avoids_prev {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V}
    (hopt : (∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q) →
      SpanY G z A₀ x t Y p)
    {y f : V} (hy : y ∈ Y)
    (hyno : ∀ a : V,
      (a ∈ wheelSystemA G z A₀ x (t - 1) ∨ a = x (t + 1) ∨ a ∈ p) →
        ¬ G.Adj y a)
    (hf : f ∈ wheelSystemA G z A₀ x t) (hyf : G.Adj y f)
    (huf : G.Adj (x (t + 1)) f) :
    VertexAnticomplete G f (wheelSystemA G z A₀ x (t - 1)) := by
  intro a ha hfa
  have hfnot : f ∉ wheelSystemA G z A₀ x (t - 1) :=
    fun hfA => h.2.2.2.2.2.1 f hfA huf
  have hg : GoodPath G z A₀ x t [f] := by
    refine ⟨PathBasics.isPathList_pair huf, by simp, ?_, ?_⟩
    · intro w hw
      have he : w = f := by simpa using hw
      simpa [he] using And.intro hf hfnot
    · intro k hk
      have he : k = 0 := by simpa using hk
      subst k
      simpa using (show ∃ b ∈ wheelSystemA G z A₀ x (t - 1), G.Adj f b from ⟨a, ha, hfa⟩)
  have hs : SpanY G z A₀ x t Y [f] :=
    spanY_of_exceptional_neighbor h hy
      (fun w hw => hyno w (by rcases hw with hw | hw; exact Or.inl hw; exact Or.inr (Or.inl hw)))
      ⟨f, by simp, hyf⟩
  obtain ⟨b, hb, hyb⟩ := hopt ⟨[f], hg, hs⟩ y hy
  exact hyno b hb hyb

/-- A replacement `x_{t+1}-f-p_j-⋯-p_m`, with `j ≥ 2`, remains a good path
when `p_j` is the last neighbour of `f` on the old path. -/
theorem goodPath_prepend_suffix {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p) {f : V}
    (hf : f ∈ wheelSystemA G z A₀ x t) (hfp : f ∉ p)
    (huf : G.Adj (x (t + 1)) f)
    (hfA : VertexAnticomplete G f (wheelSystemA G z A₀ x (t - 1)))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k < p.length) (hfk : G.Adj f p[k])
    (hafter : ∀ j (hj : j < p.length), k < j → ¬ G.Adj f p[j]) :
    GoodPath G z A₀ x t (f :: p.drop k) := by
  have hP : IsPathList G (p.drop k) := by
    have hh := PathBasics.isPathList_drop hp.1 (k := k + 1) (by simp; omega)
    simpa using hh
  have hPfrom : IsPathFrom G (p.drop k) p[k] p[p.length - 1] := by
    refine ⟨hP, ?_, ?_⟩
    · simp only [List.head?_drop, List.getElem?_eq_getElem hk]
    · rw [List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega)]
  have hffrom : IsPathFrom G (f :: p.drop k) f p[p.length - 1] := by
    apply PathAttach.isPathFrom_cons hPfrom hfk (fun hm => hfp (List.mem_of_mem_drop hm))
    intro w hw hne
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hkj : k + j < p.length := by
      simp only [List.length_drop] at hj
      omega
    simp only [List.getElem_drop] at *
    apply hafter (k + j) hkj
    by_contra hn
    have he : j = 0 := by omega
    subst j
    exact hne rfl
  have huP : ∀ w ∈ p.drop k, ¬ G.Adj (x (t + 1)) w := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hkj : k + j < p.length := by
      simp only [List.length_drop] at hj
      omega
    have hn := PathBasics.path_not_adj_of_gap hp.1
      (i := 0) (j := k + j + 1) (by simp) (by simp; omega) (by omega) (by omega)
    simpa only [List.getElem_drop, List.getElem_cons_zero, List.getElem_cons_succ] using hn
  have hufrom : IsPathFrom G (x (t + 1) :: f :: p.drop k) (x (t + 1)) p[p.length - 1] := by
    apply PathAttach.isPathFrom_cons hffrom huf
    · intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact huf.ne he
      · exact (List.nodup_cons.mp hp.1.2.1).1 (List.mem_of_mem_drop hm)
    · intro w hw hne
      rcases List.mem_cons.mp hw with he | hw
      · exact (hne he).elim
      · exact huP w hw
  refine ⟨hufrom.1, by simp, ?_, ?_⟩
  · intro w hw
    rcases List.mem_cons.mp hw with he | hw
    · subst w
      exact ⟨hf, fun hfprev => h.2.2.2.2.2.1 f hfprev huf⟩
    · exact hp.2.2.1 w (List.mem_of_mem_drop hw)
  · intro j hj
    cases j with
    | zero =>
        simp only [List.getElem_cons_zero, List.length_cons, List.length_drop]
        constructor
        · rintro ⟨a, ha, hadj⟩
          exact (hfA a ha hadj).elim
        · omega
    | succ j =>
        have hkj : k + j < p.length := by
          simp only [List.length_cons, List.length_drop] at hj
          omega
        simp only [List.getElem_cons_succ, List.getElem_drop,
          hp.2.2.2 (k + j) hkj, List.length_cons, List.length_drop]
        omega

/-- PAPER (21.2(3), p. 132): "`f` is nonadjacent to `p₂,…,p_m`, since
otherwise there would be a better choice of path using `f`." -/
theorem claim3_common_neighbor_avoids_tail {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p)
    (hopt : (∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q) →
      SpanY G z A₀ x t Y p)
    {y f : V} (hy : y ∈ Y)
    (hyno : ∀ a : V,
      (a ∈ wheelSystemA G z A₀ x (t - 1) ∨ a = x (t + 1) ∨ a ∈ p) →
        ¬ G.Adj y a)
    (hf : f ∈ wheelSystemA G z A₀ x t) (hyf : G.Adj y f)
    (huf : G.Adj (x (t + 1)) f)
    (hfA : VertexAnticomplete G f (wheelSystemA G z A₀ x (t - 1))) :
    ∀ w ∈ p.tail, ¬ G.Adj f w := by
  classical
  intro w hw hfw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have hjp : j + 1 < p.length := by
    simp only [List.length_tail] at hj
    omega
  have hcontact : G.Adj f p[j + 1] := by simpa only [List.getElem_tail] using hfw
  let R : ℕ → Prop := fun k => ∃ hk : k < p.length, G.Adj f p[k]
  let k := Nat.findGreatest R (p.length - 1)
  have hRj : R (j + 1) := ⟨hjp, hcontact⟩
  have hjk : j + 1 ≤ k := Nat.le_findGreatest (by omega) hRj
  obtain ⟨hk, hfk⟩ : R k := Nat.findGreatest_spec (by omega : j + 1 ≤ p.length - 1) hRj
  have hafter : ∀ l (hl : l < p.length), k < l → ¬ G.Adj f p[l] := by
    intro l hl hkl hfl
    exact Nat.findGreatest_is_greatest (P := R) (n := p.length - 1) hkl
      (by omega) ⟨hl, hfl⟩
  have hg := goodPath_prepend_suffix h hp hf
    (fun hfp => hyno f (Or.inr (Or.inr hfp)) hyf) huf hfA (by omega) hk hfk hafter
  have hs : SpanY G z A₀ x t Y (f :: p.drop k) :=
    spanY_of_exceptional_neighbor h hy
      (fun w hw => hyno w (by rcases hw with hw | hw; exact Or.inl hw; exact Or.inr (Or.inl hw)))
      ⟨f, by simp, hyf⟩
  obtain ⟨b, hb, hyb⟩ := hopt ⟨f :: p.drop k, hg, hs⟩ y hy
  exact hyno b hb hyb

/-- **Labelled gap for the counterexample argument in Claim (3)** (printed pp. 132–133).

PAPER: *"For suppose some `y ∈ Y` has no such neighbour. ... Consequently,
`{z,y,x,p₂,…,p_m} ∪ A_{t−1}` catches the triangle `{x_{t+1},f,p₁}`. ... By 17.1,
`F'` contains a reflection of the triangle ... a contradiction.  This proves (3)."*

The conclusion is stated as the impossibility of the single counterexample `y`.  Thus the gap
contains exactly the minimal-connected-set, antipath, and final reflection argument in that
quoted paragraph; the outer quantifier bookkeeping remains in `claim3`. -/
theorem claim3_counterexample_reflection_gap {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p)
    (hopt : (∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q) →
      SpanY G z A₀ x t Y p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc2 : Claim2 G x t p)
    {y : V} (hy : y ∈ Y)
    (hyno : ∀ a : V,
      (a ∈ wheelSystemA G z A₀ x (t - 1) ∨ a = x (t + 1) ∨ a ∈ p) →
        ¬ G.Adj y a) : False := by
  classical
  obtain ⟨hG, _, hframe, ht, hhub, huA, _, _⟩ := id h
  have hws := hhub.1
  obtain ⟨s, hst, hsu, p₁, hp₁, hs₁⟩ := hc2
  obtain ⟨r, hpform⟩ : ∃ r, p = p₁ :: r := by
    cases p with
    | nil => simp at hp₁
    | cons a r =>
        exact ⟨r, by simpa using congrArg (fun v => v :: r) (Option.some.inj hp₁)⟩
  have hp₁mem : p₁ ∈ p := by simp [hpform]
  have hp₁At := (hp.2.2.1 p₁ hp₁mem).1
  have hp₁NotA := (hp.2.2.1 p₁ hp₁mem).2
  have hp₁NotTail : p₁ ∉ p.tail := by
    have hnd := (List.nodup_cons.mp hp.1.2.1).2
    simpa [hpform] using (List.nodup_cons.mp (show (p₁ :: r).Nodup by rwa [← hpform])).1
  have hu₁ : G.Adj (x (t + 1)) p₁ := by
    have hh := PathBasics.path_adj_succ hp.1 (i := 0) (by simp [hpform])
    simpa [hpform] using hh
  obtain ⟨f, hfAt, hyf, huf⟩ := claim3_common_neighbor_gap h hp hc1 hy hyno
  have hfA := claim3_common_neighbor_avoids_prev h hopt hy hyno hfAt hyf huf
  have hfTail := claim3_common_neighbor_avoids_tail h hp hopt hy hyno hfAt hyf huf hfA
  have hfNotP : f ∉ p := fun hm => hyno f (Or.inr (Or.inr hm)) hyf
  have hBAt : (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) ⊆
      wheelSystemA G z A₀ x t := by
    rintro w (hw | hw)
    · exact WheelSystemBasics.wheelSystemA_mono (by omega) hw
    · exact (hp.2.2.1 w hw).1
  have hzB : z ∉ (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) :=
    fun hm => Thm203Prelim.z_notMem_wheelSystemA hws (by omega) (hBAt hm)
  have hzAnti : VertexAnticomplete G z
      (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) :=
    fun w hw => WheelSystemBasics.wheelSystemA_no_nbr (hBAt hw)
  have hzU := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hzY := hhub.2.2.2.2.1 y hy
  have hzX : VertexComplete G z (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hyX : VertexComplete G y (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    exact (hhub.2.2.2.2.2.1 j (by omega) y hy).symm
  have huNotB : x (t + 1) ∉ (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) :=
    fun hm => hzAnti _ hm hzU
  have hyNotB : y ∉ (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) :=
    fun hm => hzAnti _ hm hzY
  have hfNotA : f ∉ wheelSystemA G z A₀ x (t - 1) := fun hm => huA f hm huf
  have hfNotB : f ∉ (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}) := by
    rintro (hm | hm)
    · exact hfNotA hm
    · exact hfNotP hm
  have huNotX : x (t + 1) ∉ wheelSystemX x t := by
    rintro ⟨j, hj, he⟩
    exact KiteTailBasics.hub_last_ne hhub hj he
  have hfNotX : f ∉ wheelSystemX x t :=
    fun hm => WheelSystemBasics.wheelSystemA_no_nbr hfAt (hzX f hm)
  have hXNbr : ∀ w ∈ wheelSystemX x t,
      ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj w a := by
    rintro w ⟨j, hj, rfl⟩
    exact Thm203Prelim.exists_nbr_wheelSystemA hframe hws (by omega) (by omega) (by omega)
  have hBNbr : ∃ b ∈ (wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p}), G.Adj f b :=
    Thm212Claim3Tools.neighbor_of_two_antipaths hG.1.1.1.1
      (WheelSystemBasics.connectedSet_wheelSystemA hframe.1)
      (by simpa using goodPath_suffix_connected h hp 0) Set.subset_union_left
      (Thm203Prelim.anticonnected_wheelSystemX hws t (by omega))
      hzB hzAnti hzX hyX hzU huNotB hfNotB huNotX hfNotX
      (hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl)
      (WheelSystemBasics.wheelSystemA_no_complete hfAt)
      huf hyf (hyno _ (Or.inr (Or.inl rfl))) hyNotB
      (fun w hw => hyno w (by rcases hw with hw | hw; exact Or.inl hw; exact Or.inr (Or.inr hw)))
      huA hfA ⟨p₁, Or.inr hp₁mem, hu₁⟩ hXNbr
  have hf₁ : G.Adj f p₁ := by
    obtain ⟨b, hb, hfb⟩ := hBNbr
    rcases hb with hb | hb
    · exact (hfA b hb hfb).elim
    · rw [hpform] at hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hfb
      · exact (hfTail b (by simpa [hpform] using hb) hfb).elim
  let B : Set V := wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p.tail}
  let F : Set V := ((B ∪ {x s}) ∪ {z}) ∪ {y}
  let T : Set V := {x (t + 1), f, p₁}
  have hBsub : B ⊆ wheelSystemA G z A₀ x (t - 1) ∪ {v | v ∈ p} := by
    rintro w (hw | hw)
    · exact Or.inl hw
    · exact Or.inr (List.mem_of_mem_tail hw)
  have hBcon : ConnectedSet G B := by simpa [B] using goodPath_suffix_connected h hp 1
  have hsX : x s ∈ wheelSystemX x t := ⟨s, hst, rfl⟩
  have hzS := hzX (x s) hsX
  have hFcon : ConnectedSet G F :=
    ConnectedSetUnionAttach.connectedSet_union_singleton
      (ConnectedSetUnionAttach.connectedSet_union_singleton
        (ConnectedSetUnionAttach.connectedSet_union_singleton hBcon
          (by obtain ⟨a, ha, hsa⟩ := hXNbr _ hsX; exact ⟨a, Or.inl ha, hsa⟩))
        ⟨x s, Or.inr rfl, hzS⟩)
      ⟨z, Or.inr rfl, hzY.symm⟩
  have hT : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr ⟨_, _, _, huf.ne, hu₁.ne, hf₁.ne, rfl⟩, ?_⟩
    intro a ha b hb hab
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    · exact (hab rfl).elim
    · exact huf
    · exact hu₁
    · exact huf.symm
    · exact (hab rfl).elim
    · exact hf₁
    · exact hu₁.symm
    · exact hf₁.symm
    · exact (hab rfl).elim
  have huTail : ∀ w ∈ p.tail, ¬ G.Adj (x (t + 1)) w := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hjp : j + 1 < p.length := by simp only [List.length_tail] at hj; omega
    have hh := PathBasics.path_not_adj_of_gap hp.1 (i := 0) (j := j + 2)
      (by simp) (by simp; omega) (by omega) (by omega)
    simpa [List.getElem_tail] using hh
  have huB : VertexAnticomplete G (x (t + 1)) B := by
    rintro w (hw | hw)
    · exact huA w hw
    · exact huTail w hw
  have hfB : VertexAnticomplete G f B := by
    rintro w (hw | hw)
    · exact hfA w hw
    · exact hfTail w hw
  have hBnot : ∀ v ∈ B, v ∉ T := by
    intro v hv hvT
    rcases hvT with he | he | he
    · exact huNotB (he ▸ hBsub hv)
    · exact hfNotB (he ▸ hBsub hv)
    · rcases hv with hv | hv
      · exact hp₁NotA (he ▸ hv)
      · exact hp₁NotTail (he ▸ hv)
  have hrestNot : ∀ v ∈ ({x s, z, y} : Set V), v ∉ T := by
    intro v hv hvT
    rcases hv with rfl | rfl | rfl
    · rcases hvT with he | he | he
      · exact huNotX (he ▸ hsX)
      · exact WheelSystemBasics.wheelSystemA_no_nbr hfAt (by rwa [← he])
      · exact WheelSystemBasics.wheelSystemA_no_nbr hp₁At (by rwa [← he])
    · rcases hvT with he | he | he
      · exact hzU.ne he
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (he.symm ▸ hfAt)
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (he.symm ▸ hp₁At)
    · rcases hvT with he | he | he
      · exact KiteTailBasics.hub_last_notMem hhub (he ▸ hy)
      · exact hyf.ne he
      · exact WheelSystemBasics.wheelSystemA_no_nbr hp₁At (by rwa [← he])
  have hdis : Disjoint F T := by
    apply Set.disjoint_left.mpr
    intro v hv hvT
    rcases hv with ((hv | hv) | hv) | hv
    · exact hBnot v hv hvT
    · exact hrestNot v (Or.inl hv) hvT
    · exact hrestNot v (Or.inr (Or.inl hv)) hvT
    · exact hrestNot v (Or.inr (Or.inr hv)) hvT
  have hp₁B : ∃ b ∈ B, G.Adj p₁ b := by
    cases r with
    | nil =>
        have hattach := (hp.2.2.2 0 (by simp [hpform])).mpr (by simp [hpform])
        obtain ⟨b, hb, hadj⟩ := hattach
        exact ⟨b, Or.inl hb, by simpa [hpform] using hadj⟩
    | cons b r =>
        have hh := PathBasics.path_adj_succ hp.1 (i := 1) (by simp [hpform])
        exact ⟨b, Or.inr (by simp [hpform]), by simpa [hpform] using hh⟩
  have hcatch : Catches G F T := by
    refine ⟨hT, hFcon, hdis, ?_⟩
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨z, Or.inl (Or.inr rfl), hzU.symm⟩
    · exact ⟨y, Or.inr rfl, hyf.symm⟩
    · obtain ⟨b, hb, h₁b⟩ := hp₁B
      exact ⟨b, Or.inl (Or.inl (Or.inl hb)), h₁b⟩
  have hunique : ∀ w ∈ F, G.Adj (x (t + 1)) w → w = z := by
    intro w hw huw
    rcases hw with ((hw | hw) | hw) | hw
    · exact (huB w hw huw).elim
    · exact (hsu (by simpa only [Set.mem_singleton_iff.mp hw] using huw.symm)).elim
    · exact hw
    · exact (hyno _ (Or.inr (Or.inl rfl)) (by simpa only [Set.mem_singleton_iff.mp hw] using huw.symm)).elim
  have hcommon : ∀ w ∈ F, G.Adj z w → ¬ G.Adj p₁ w := by
    intro w hw hzw h₁w
    rcases hw with ((hw | hw) | hw) | hw
    · exact hzAnti w (hBsub hw) hzw
    · exact hs₁ (by simpa only [Set.mem_singleton_iff.mp hw] using h₁w.symm)
    · exact G.irrefl (by simpa only [Set.mem_singleton_iff.mp hw] using hzw)
    · exact hyno p₁ (Or.inr (Or.inr hp₁mem))
        (by simpa only [Set.mem_singleton_iff.mp hw] using h₁w.symm)
  have hpair : ∀ w ∈ F, ¬ (G.Adj w f ∧ G.Adj w p₁) := by
    intro w hw ⟨hwf, hw₁⟩
    rcases hw with ((hw | hw) | hw) | hw
    · exact hfB w hw hwf.symm
    · exact hs₁ (by simpa only [Set.mem_singleton_iff.mp hw] using hw₁)
    · exact WheelSystemBasics.wheelSystemA_no_nbr hfAt
        (by simpa only [Set.mem_singleton_iff.mp hw] using hwf)
    · exact hyno p₁ (Or.inr (Or.inr hp₁mem))
        (by simpa only [Set.mem_singleton_iff.mp hw] using hw₁)
  apply Thm212Claim3Tools.catch_obstruction hG hcatch
    (show x (t + 1) ∈ T from Or.inl rfl) (show p₁ ∈ T from Or.inr (Or.inr rfl))
    hu₁.ne hunique hcommon
  intro w hw
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  rintro a ⟨hwa, ha⟩ b ⟨hwb, hb⟩
  have hwa' : G.Adj w a := hwa
  have hwb' : G.Adj w b := hwb
  have hwu : G.Adj w (x (t + 1)) → w = z := fun hh => hunique w hw hh.symm
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · rfl
  · exact (WheelSystemBasics.wheelSystemA_no_nbr hfAt (hwu hwa' ▸ hwb')).elim
  · exact (WheelSystemBasics.wheelSystemA_no_nbr hp₁At (hwu hwa' ▸ hwb')).elim
  · exact (WheelSystemBasics.wheelSystemA_no_nbr hfAt (hwu hwb' ▸ hwa')).elim
  · rfl
  · exact (hpair w hw ⟨hwa', hwb'⟩).elim
  · exact (WheelSystemBasics.wheelSystemA_no_nbr hp₁At (hwu hwb' ▸ hwa')).elim
  · exact (hpair w hw ⟨hwb', hwa'⟩).elim
  · rfl

/-- **Claim (3)** of the printed proof (printed pp. 132–133): *"Every vertex in `Y` has a
neighbour in `A_{t−1} ∪ {x_{t+1}, p₁,…,p_m}`."* -/
theorem claim3 {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (h : Setup G Y z A₀ x t) {p : List V} (hp : GoodPath G z A₀ x t p)
    (hopt : (∃ q : List V, GoodPath G z A₀ x t q ∧ SpanY G z A₀ x t Y q) →
      SpanY G z A₀ x t Y p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc2 : Claim2 G x t p) :
    SpanY G z A₀ x t Y p := by
  intro y hy
  by_contra hn
  apply claim3_counterexample_reflection_gap h hp hopt hc1 hc2 hy
  intro a ha hadj
  exact hn ⟨a, ha, hadj⟩

/-- **Extension of the path and choice of `i`, `s`** (printed p. 133, the paragraph after
claim (3)). -/
theorem exists_extended_with_support {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V} (hp : GoodPath G z A₀ x t p)
    (hc2 : Claim2 G x t p) (hc3 : SpanY G z A₀ x t Y p) :
    ∃ (q : List V) (i s : ℕ), Extended G z A₀ x t p q i s ∧
      ∀ v ∈ q, v ∈ p ∨ v ∈ wheelSystemA G z A₀ x (t - 1) := by
  classical
  obtain ⟨-, -, hframe, ht, hhub, hxt1, -, -⟩ := h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hcond2 := hws.2.2.2.2.1
  have hcond4 := hws.2.2.2.2.2.2
  obtain ⟨hppath, hpne, hpAt, hpattach⟩ := hp
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hpne
  let pm : V := p[p.length - 1]'(by omega)
  have hpmmem : pm ∈ p := by
    dsimp [pm]
    exact List.getElem_mem (by omega)
  have hpmAt : pm ∈ wheelSystemA G z A₀ x t := (hpAt pm hpmmem).1
  have hpmnotA1 : pm ∉ wheelSystemA G z A₀ x (t - 1) := (hpAt pm hpmmem).2
  have hpmlast : p.getLast? = some pm := by
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
  have hpmlastnbr :
      ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj pm a := by
    have hidx : p.length - 1 + 1 = p.length := by omega
    have ha := (hpattach (p.length - 1) (by omega)).mpr hidx
    simpa [pm] using ha
  obtain ⟨B, hB0, hBcon, hBxt, hBz, hBX⟩ := hcond2 t ht (by omega)
  have hA0A1 : A₀ ⊆ wheelSystemA G z A₀ x (t - 1) := fun v hv =>
    WheelSystemBasics.mem_wheelSystemA_of_witness hB0 hBcon hBz hBX (hB0 hv)
  have hA1con : ConnectedSet G (wheelSystemA G z A₀ x (t - 1)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hpmcomplete : VertexComplete G pm (wheelSystemX x (t - 1)) := by
    by_contra hnc
    have hUcon :
        ConnectedSet G (wheelSystemA G z A₀ x (t - 1) ∪ {pm}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton hA1con hpmlastnbr
    have hpmA1 : pm ∈ wheelSystemA G z A₀ x (t - 1) :=
      WheelSystemBasics.mem_wheelSystemA_of_witness
        (B := wheelSystemA G z A₀ x (t - 1) ∪ {pm}) (i := t - 1)
        (fun v hv => Or.inl (hA0A1 hv)) hUcon
        (by
          intro v hv
          rcases hv with hv | rfl
          · exact WheelSystemBasics.wheelSystemA_no_nbr hv
          · exact WheelSystemBasics.wheelSystemA_no_nbr hpmAt)
        (by
          intro v hv
          rcases hv with hv | rfl
          · exact WheelSystemBasics.wheelSystemA_no_complete hv
          · exact hnc)
        (Or.inr rfl)
    exact hpmnotA1 hpmA1
  have hxtpm : ¬ G.Adj (x t) pm := by
    intro htp
    apply (WheelSystemBasics.wheelSystemA_no_complete hpmAt)
    intro v hv
    obtain ⟨j, hj, rfl⟩ := hv
    by_cases hje : j = t
    · subst j
      exact htp.symm
    · exact hpmcomplete (x j) ⟨j, by omega, rfl⟩
  have hxtA1 :
      ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (x t) a :=
    WheelSystemBasics.exists_adj_wheelSystemA_of_witness
      (i := t - 1) hB0 hBcon hBz hBX hBxt
  have hzxt : G.Adj z (x t) := hcond4 t (by omega)
  have hzxt1 : G.Adj z (x (t + 1)) := hcond4 (t + 1) le_rfl
  have hpmne : pm ≠ x t := by
    intro he
    rw [← he] at hzxt
    exact (WheelSystemBasics.wheelSystemA_no_nbr hpmAt) hzxt
  have hxtnotA1 : x t ∉ wheelSystemA G z A₀ x (t - 1) := by
    intro hm
    exact (WheelSystemBasics.wheelSystemA_no_nbr hm) hzxt
  have hxt1notA1 : x (t + 1) ∉ wheelSystemA G z A₀ x (t - 1) := by
    intro hm
    exact (WheelSystemBasics.wheelSystemA_no_nbr hm) hzxt1
  have hxt1nepm : x (t + 1) ≠ pm := by
    intro he
    rw [he] at hzxt1
    exact (WheelSystemBasics.wheelSystemA_no_nbr hpmAt) hzxt1
  have glue_path_local :
      ∀ {R S : List V} {u₀ u₁ w₀ w₁ : V},
        IsPathFrom G R u₀ u₁ →
        IsPathFrom G S w₀ w₁ →
        (∀ v ∈ R, v ∉ S) →
        (∀ v ∈ R, ∀ w ∈ S, (G.Adj v w ↔ (v = u₁ ∧ w = w₀))) →
        IsPathFrom G (R ++ S) u₀ w₁ := by
    intro R S u₀ u₁ w₀ w₁ hR hS hdisj hcross
    obtain ⟨hRl, hRh, hRt⟩ := hR
    obtain ⟨hSl, hSh, hSt⟩ := hS
    have hm : 0 < R.length := PathBasics.path_length_pos hRl
    have hn : 0 < S.length := PathBasics.path_length_pos hSl
    have hRne : R ≠ [] := PathBasics.path_ne_nil hRl
    have hSne : S ≠ [] := PathBasics.path_ne_nil hSl
    have hRm : R[R.length - 1]'(by omega) = u₁ :=
      PathBasics.getElem_last_of_getLast? hRt hm
    have hS0 : S[0]'hn = w₀ := PathBasics.getElem_zero_of_head? hSh hn
    have hRnd : R.Nodup := hRl.2.1
    have hSnd : S.Nodup := hSl.2.1
    have cross : ∀ (i j : ℕ) (hiR : i < R.length) (hjR : R.length ≤ j)
        (hi : i < (R ++ S).length) (hj : j < (R ++ S).length),
        (G.Adj ((R ++ S)[i]'hi) ((R ++ S)[j]'hj) ↔
          (i + 1 = j ∨ j + 1 = i)) := by
      intro i j hiR hjR hi hj
      have hiL : i < R.length + S.length := by simpa using hi
      have hjL : j < R.length + S.length := by simpa using hj
      have hjS : j - R.length < S.length := by omega
      rw [List.getElem_append_left hiR, List.getElem_append_right hjR,
        hcross (R[i]'hiR) (List.getElem_mem hiR)
          (S[j - R.length]'hjS) (List.getElem_mem hjS)]
      have e1 : (R[i]'hiR = u₁) ↔ i = R.length - 1 := by
        rw [← hRm]
        exact hRnd.getElem_inj_iff
      have e2 : (S[j - R.length]'hjS = w₀) ↔ j - R.length = 0 := by
        rw [← hS0]
        exact hSnd.getElem_inj_iff
      rw [e1, e2]
      omega
    refine ⟨⟨by simp [hRne], ?_, ?_⟩, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨hRnd, hSnd, fun a ha b hb => by rintro rfl; exact hdisj a ha hb⟩
    · intro i j hi hj
      have hiL : i < R.length + S.length := by simpa using hi
      have hjL : j < R.length + S.length := by simpa using hj
      rcases lt_or_ge i R.length with hiR | hiR
      · rcases lt_or_ge j R.length with hjR | hjR
        · rw [List.getElem_append_left hiR, List.getElem_append_left hjR,
            PathBasics.path_adj_iff hRl hiR hjR]
        · exact cross i j hiR hjR hi hj
      · rcases lt_or_ge j R.length with hjR | hjR
        · rw [SimpleGraph.adj_comm, cross j i hjR hiR hj hi]
          constructor <;> (intro h; omega)
        · have hiS : i - R.length < S.length := by omega
          have hjS : j - R.length < S.length := by omega
          rw [List.getElem_append_right hiR, List.getElem_append_right hjR,
            PathBasics.path_adj_iff hSl hiS hjS]
          omega
    · rw [List.head?_append, hRh]
      rfl
    · rw [List.getLast?_append_of_ne_nil _ hSne]
      exact hSt
  obtain ⟨q, hpref, hqpath, hqAt, hqall, hqlen, hqextra⟩ :
      ∃ q : List V,
        p <+: q ∧
        IsPathList G (x (t + 1) :: q) ∧
        (∀ v ∈ q, v ∈ wheelSystemA G z A₀ x t) ∧
        (∀ j ≤ t, ∃ w ∈ x (t + 1) :: q, G.Adj (x j) w) ∧
        2 ≤ q.length ∧
        (∀ v ∈ q, v ∈ p ∨ v ∈ wheelSystemA G z A₀ x (t - 1)) := by
    by_cases htp : ∃ v ∈ p, G.Adj (x t) v
    · refine ⟨p, ⟨[], by simp⟩, hppath, (fun v hv => (hpAt v hv).1), ?_, ?_, fun v hv => Or.inl hv⟩
      · intro j hj
        by_cases hje : j = t
        · subst j
          obtain ⟨v, hv, hadj⟩ := htp
          exact ⟨v, List.mem_cons_of_mem _ hv, hadj⟩
        · exact ⟨pm, List.mem_cons_of_mem _ hpmmem,
            (hpmcomplete (x j) ⟨j, by omega, rfl⟩).symm⟩
      · by_contra hlen
        have hpone : p.length = 1 := by omega
        obtain ⟨v, hv, hadj⟩ := htp
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
        have hk0 : k = 0 := by omega
        subst k
        have he : p[0]'hk = pm := by simp [pm, hpone]
        rw [he] at hadj
        exact hxtpm hadj
    · have h1 :
          ConnectedSet G (wheelSystemA G z A₀ x (t - 1) ∪ {pm}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hA1con hpmlastnbr
      have h2 :
          ConnectedSet G
            ((wheelSystemA G z A₀ x (t - 1) ∪ {pm}) ∪ {x t}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton h1
          (by
            obtain ⟨a, ha, hxa⟩ := hxtA1
            exact ⟨a, Or.inl ha, hxa⟩)
      obtain ⟨R, hR, hRmem⟩ :=
        InducedPathExtraction.exists_isPathFrom_of_connected h2
          (Or.inl (Or.inr rfl)) (Or.inr rfl)
      have hRint :
          ∀ w ∈ SPGT.interior R, w ∈ wheelSystemA G z A₀ x (t - 1) := by
        intro w hw
        have hwi := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hw
        obtain ⟨hwR, hwpm, hwxt⟩ := hwi
        rcases hRmem w hwR with (hwA | hweq) | hweq
        · exact hwA
        · exact False.elim (hwpm hweq)
        · exact False.elim (hwxt hweq)
      have hpmxt : ¬ G.Adj pm (x t) := fun hadj => hxtpm hadj.symm
      have hR3 : 3 ≤ R.length := by
        rcases R with _ | ⟨a, _ | ⟨b, _ | ⟨c, r⟩⟩⟩
        · exfalso
          simpa using hR.2.1
        · have ha0 : a = pm := by simpa using hR.2.1
          have hat : a = x t := by simpa using hR.2.2
          exfalso
          exact hpmne (ha0.symm.trans hat)
        · have ha0 : a = pm := by simpa using hR.2.1
          have hbt : b = x t := by simpa using hR.2.2
          have hab : G.Adj a b :=
            (hR.1.2.2 0 1 (by simp) (by simp)).mpr (Or.inl rfl)
          exfalso
          apply hpmxt
          simpa [ha0, hbt] using hab
        · simp
      have hRpos : 0 < R.length := by omega
      have hR0 : R[0]'hRpos = pm :=
        PathBasics.getElem_zero_of_head? hR.2.1 hRpos
      have hRlast : R[R.length - 1]'(by omega) = x t :=
        PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
      have hIfrom :
          IsPathFrom G (SPGT.interior R)
            (R[1]'(by omega)) (R[R.length - 2]'(by omega)) := by
        have hd : IsPathList G (R.drop 1) :=
          PathBasics.isPathList_drop hR.1 (by omega)
        have htI : IsPathList G ((R.drop 1).take (R.length - 2)) :=
          PathBasics.isPathList_take hd (by omega)
        have hkey : R.length - 2 - 1 + 1 = R.length - 2 := by omega
        have hh := PathBasics.head?_slice R (i := 1) (j := R.length - 2)
          (by omega) (by omega)
        have hl := PathBasics.getLast?_slice R (i := 1) (j := R.length - 2)
          (by omega) (by omega)
        rw [hkey] at hh hl
        exact ⟨by
            rw [PathBasics.interior_eq_drop_take]
            exact htI,
          by
            rw [PathBasics.interior_eq_drop_take]
            exact hh,
          by
            rw [PathBasics.interior_eq_drop_take]
            exact hl⟩
      have hPfrom :
          IsPathFrom G (x (t + 1) :: p) (x (t + 1)) pm := by
        exact ⟨hppath, rfl, by
          rw [List.getLast?_cons_of_ne_nil hpne]
          exact hpmlast⟩
      have hpmI : ∀ w ∈ SPGT.interior R,
          (G.Adj pm w ↔ w = R[1]'(by omega)) := by
        intro w hw
        obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
          PathBasics.exists_getElem_of_mem_interior hR.1 hw
        constructor
        · intro hadj
          have hadj0k : G.Adj (R[0]'hRpos) (R[k]'hk) := by
            simpa only [hR0] using hadj
          rcases (PathBasics.path_adj_iff hR.1 hRpos hk).mp hadj0k with hki | hki
          · have hke : k = 1 := by omega
            subst k
            rfl
          · omega
        · intro heq
          have hke : k = 1 := (hR.1.2.1.getElem_inj_iff).mp heq
          subst k
          simpa only [hR0] using
            (PathBasics.path_adj_succ hR.1 (i := 0) (by omega))
      have hpIcross : ∀ v ∈ p, ∀ w ∈ SPGT.interior R,
          (G.Adj v w ↔ (v = pm ∧ w = R[1]'(by omega))) := by
        intro v hv w hw
        constructor
        · intro hadj
          obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
          have hlastidx : k + 1 = p.length :=
            (hpattach k hk).mp ⟨w, hRint w hw, hadj⟩
          have hke : k = p.length - 1 := by omega
          subst k
          have hvpm : p[p.length - 1]'hk = pm := by simp [pm]
          rw [hvpm] at hadj
          exact ⟨hvpm, (hpmI w hw).mp hadj⟩
        · rintro ⟨rfl, rfl⟩
          exact (hpmI _ hw).mpr rfl
      have hdisj : ∀ v ∈ x (t + 1) :: p, v ∉ SPGT.interior R := by
        intro v hv hvI
        have hvA1 := hRint v hvI
        rcases List.mem_cons.mp hv with rfl | hvp
        · exact hxt1notA1 hvA1
        · exact (hpAt v hvp).2 hvA1
      have hcross : ∀ v ∈ x (t + 1) :: p, ∀ w ∈ SPGT.interior R,
          (G.Adj v w ↔ (v = pm ∧ w = R[1]'(by omega))) := by
        intro v hv w hw
        rcases List.mem_cons.mp hv with rfl | hvp
        · exact iff_of_false (hxt1 w (hRint w hw))
            (fun hs => hxt1nepm hs.1)
        · exact hpIcross v hvp w hw
      have hglued :
          IsPathFrom G ((x (t + 1) :: p) ++ SPGT.interior R)
            (x (t + 1)) (R[R.length - 2]'(by omega)) :=
        glue_path_local hPfrom hIfrom hdisj hcross
      have hqpath' :
          IsPathList G (x (t + 1) :: (p ++ SPGT.interior R)) := by
        simpa using hglued.1
      refine ⟨p ++ SPGT.interior R, ⟨SPGT.interior R, rfl⟩,
        hqpath', ?_, ?_, ?_, ?_⟩
      · intro v hv
        rcases List.mem_append.mp hv with hvp | hvI
        · exact (hpAt v hvp).1
        · exact WheelSystemBasics.wheelSystemA_mono (by omega) (hRint v hvI)
      · intro j hj
        by_cases hje : j = t
        · subst j
          have hrmem :
              R[R.length - 2]'(by omega) ∈ SPGT.interior R :=
            PathBasics.getElem_mem_interior hR.1 (by omega) (by omega) (by omega)
          have hadj :=
            PathBasics.path_adj_succ hR.1 (i := R.length - 2) (by omega)
          have hidx : R.length - 2 + 1 = R.length - 1 := by omega
          have hadj' :
              G.Adj (R[R.length - 2]'(by omega))
                (R[R.length - 1]'(by omega)) := by
            simpa only [hidx] using hadj
          rw [hRlast] at hadj'
          exact ⟨R[R.length - 2]'(by omega),
            List.mem_cons_of_mem _ (List.mem_append_right p hrmem), hadj'.symm⟩
        · exact ⟨pm, List.mem_cons_of_mem _
              (List.mem_append_left _ hpmmem),
            (hpmcomplete (x j) ⟨j, by omega, rfl⟩).symm⟩
      · rw [List.length_append, PathBasics.interior_length]
        omega
      · intro v hv
        rcases List.mem_append.mp hv with hv | hv
        · exact Or.inl hv
        · exact Or.inr (hRint v hv)
  obtain ⟨s₀, hs₀t, hs₀x, p₁, hp₁head, hs₀p₁⟩ := hc2
  have htake2 : (x (t + 1) :: q).take 2 = [x (t + 1), p₁] := by
    obtain ⟨p', hpform⟩ : ∃ p', p = p₁ :: p' := by
      rcases p with _ | ⟨a, r⟩
      · simp at hp₁head
      · simp only [List.head?_cons, Option.some.injEq] at hp₁head
        exact ⟨r, by rw [hp₁head]⟩
    obtain ⟨r, hr⟩ := hpref
    rw [← hr, hpform]
    simp
  let P : ℕ → Prop := fun k =>
    2 ≤ k ∧ ∃ j ≤ t,
      ∀ w ∈ (x (t + 1) :: q).take k, ¬ G.Adj (x j) w
  have hP2 : P 2 := by
    refine ⟨le_rfl, s₀, hs₀t, ?_⟩
    intro w hw
    rw [htake2] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hs₀x
    · exact hs₀p₁
  let i := Nat.findGreatest P q.length
  have hPi : P i := by
    dsimp [i]
    exact Nat.findGreatest_spec hqlen hP2
  have hiq : i ≤ q.length := by
    dsimp [i]
    exact Nat.findGreatest_le q.length
  obtain ⟨hi2, s, hst, hsnon⟩ := hPi
  have hmax :
      ∀ j ≤ t, ∃ w ∈ (x (t + 1) :: q).take (i + 1), G.Adj (x j) w := by
    intro j hj
    by_cases hieq : i = q.length
    · obtain ⟨w, hw, hadj⟩ := hqall j hj
      refine ⟨w, ?_, hadj⟩
      have htakeall :
          (x (t + 1) :: q).take (i + 1) = x (t + 1) :: q := by
        rw [hieq]
        simp
      rw [htakeall]
      exact hw
    · have hilt : i < q.length := lt_of_le_of_ne hiq hieq
      have hnotP : ¬ P (i + 1) := by
        apply Nat.findGreatest_is_greatest (P := P) (n := q.length)
        · dsimp [i]
          omega
        · omega
      by_contra hex
      push Not at hex
      apply hnotP
      refine ⟨by omega, j, hj, ?_⟩
      intro w hw
      exact hex w hw
  exact ⟨q, i, s, ⟨hpref, hqpath, hqAt, hqall, hi2, hiq, hst, hsnon, hmax⟩, hqextra⟩

/-- The extension and choice of indices from the paragraph after 21.2(3). -/
theorem exists_extended {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V} (hp : GoodPath G z A₀ x t p)
    (hc2 : Claim2 G x t p) (hc3 : SpanY G z A₀ x t Y p) :
    ∃ (q : List V) (i s : ℕ), Extended G z A₀ x t p q i s := by
  obtain ⟨q, i, s, hext, _⟩ := exists_extended_with_support h hp hc2 hc3
  exact ⟨q, i, s, hext⟩

/-- The complete input package for Theorem 21.1.  Naming this package makes the exact output
still missing from the printed Claims (4)–(9) visible in the type of the labelled gap below. -/
def Thm211Witness (G : SimpleGraph V) (X Y : Set V) : Prop :=
  ∃ (P : List V) (p₁ pₙ : V),
    Disjoint X Y ∧ X.Nonempty ∧ Y.Nonempty ∧
    AnticonnectedSet G X ∧ AnticonnectedSet G Y ∧ Complete G X Y ∧
    IsPathList G P ∧ (∀ v ∈ P, v ∉ X ∧ v ∉ Y) ∧
    4 ≤ pathLength P ∧ P.head? = some p₁ ∧ P.getLast? = some pₙ ∧
    (∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ)) ∧
    ((∀ v ∈ P.take 3, VertexComplete G v Y) ∨
      (∃ (j : ℕ) (_h1 : 1 ≤ j) (_h2 : j ≤ P.length - 3),
        VertexComplete G P[j - 1] Y ∧ VertexComplete G P[j] Y ∧
          VertexComplete G P[j + 1] Y ∧ VertexComplete G P[j + 2] Y) ∨
      (∃ (j : ℕ) (_h1 : 1 ≤ j) (_h2 : j ≤ P.length - 3),
        VertexComplete G P[j] Y ∧ VertexComplete G P[j + 1] Y ∧
          ¬ VertexComplete G P[j - 1] Y ∧ ¬ VertexComplete G P[j + 2] Y))

/-- The path `z-x_{t+1}-p₁-⋯-p_k` has the common hypotheses of 21.1
when `p_k` is the first `X_{t-1}`-complete vertex after `z`. -/
theorem prefix_pathFor211 {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p : List V} (hp : GoodPath G z A₀ x t p)
    {k : ℕ} (hk3 : 3 ≤ k) (hkm : k ≤ p.length)
    (hunc : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)))
    (hkc : VertexComplete G p[k - 1] (wheelSystemX x (t - 1)))
    (hfirst : ∀ j (hj : j < p.length), j + 1 < k →
      ¬ VertexComplete G p[j] (wheelSystemX x (t - 1))) :
    Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1] := by
  classical
  obtain ⟨_, _, hframe, ht, hhub, _, _, _⟩ := id h
  have hws := hhub.1
  have hlast : (x (t + 1) :: p.take k).getLast? = some p[k - 1] := by
    have he : k - 1 + 1 = k := by omega
    have hh := getLast?_take_succ p (k - 1) (by omega)
    rw [he] at hh
    have htakepos : 0 < (p.take k).length := by simp only [List.length_take]; omega
    rw [List.getLast?_cons_of_ne_nil (List.ne_nil_of_length_pos htakepos)]
    exact hh
  have hpath : IsPathFrom G (x (t + 1) :: p.take k) (x (t + 1)) p[k - 1] := by
    refine ⟨?_, rfl, hlast⟩
    simpa using PathBasics.isPathList_take hp.1 (k := k + 1) (by omega)
  have hzP : z ∉ x (t + 1) :: p.take k := by
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
    · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
        ((hp.2.2.1 z (List.take_subset _ _ hm)).1)
  have hpath' : IsPathFrom G (z :: x (t + 1) :: p.take k) z p[k - 1] := by
    apply PathAttach.isPathFrom_cons hpath (hws.2.2.2.2.2.2 (t + 1) le_rfl) hzP
    intro w hw hwu
    rcases List.mem_cons.mp hw with he | hw
    · exact (hwu he).elim
    · exact WheelSystemBasics.wheelSystemA_no_nbr
        ((hp.2.2.1 w (List.take_subset _ _ hw)).1)
  have hXY : Complete G (wheelSystemX x (t - 1)) Y := by
    rintro w ⟨j, hj, rfl⟩ y hy
    exact hhub.2.2.2.2.2.1 j (by omega) y hy
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  refine ⟨?_, ⟨x 0, 0, by omega, rfl⟩, hhub.2.1,
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega),
    hhub.2.2.1, hXY, hpath', ?_, ?_, ?_⟩
  · exact Set.disjoint_left.mpr (fun v hvX hvY => G.irrefl (hXY v hvX v hvY))
  · intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · subst v
      exact ⟨fun hvX => G.irrefl (hzX z hvX),
        fun hvY => G.irrefl (hhub.2.2.2.2.1 z hvY)⟩
    · rcases List.mem_cons.mp hv with he | hv
      · subst v
        refine ⟨?_, KiteTailBasics.hub_last_notMem hhub⟩
        rintro ⟨j, hj, he⟩
        exact KiteTailBasics.hub_last_ne hhub (by omega) he
      · have hvAt := (hp.2.2.1 v (List.take_subset _ _ hv)).1
        refine ⟨?_, ?_⟩
        · rintro ⟨j, hj, he⟩
          exact WheelSystemBasics.wheelSystemA_no_nbr hvAt
            (by simpa only [he] using hws.2.2.2.2.2.2 j (by omega))
        · intro hvY
          exact Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (by omega) hvY hvAt
  · simp only [pathLength, List.length_cons, List.length_take]
    omega
  · intro v hv
    constructor
    · intro hvc
      rcases List.mem_cons.mp hv with he | hv
      · exact Or.inl he
      · rcases List.mem_cons.mp hv with he | hv
        · exact (hunc (he ▸ hvc)).elim
        · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
          have hjp : j < p.length := by simp only [List.length_take] at hj; omega
          have hjk : j < k := by simp only [List.length_take] at hj; omega
          simp only [List.getElem_take] at hvc ⊢
          have he : j = k - 1 := by
            by_contra hne
            exact hfirst j hjp (by omega) hvc
          subst j
          exact Or.inr rfl
    · rintro (he | he)
      · exact he ▸ hzX
      · exact he ▸ hkc

/-- PAPER (21.2(5), pp. 133–134): the odd return paths from `x_t` to the
first `X_{t-1}`-complete vertex. -/
def OddReturnPaths (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V)
    (t : ℕ) (p : List V) : Prop :=
  ∀ (R : List V) (r : V), IsPathFrom G R (x t) r →
    (∀ v ∈ R, VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = r) →
    (∀ v ∈ R, v ≠ x t → v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p) →
    Odd (pathLength R) ∧ 3 ≤ pathLength R

/-- PAPER (21.2(4), p. 133): "`z-x_{t+1}-p₁-⋯-p_i-x_s-z` is a hole ...
and so `i` is odd." This part uses only the induced path and the choice of `s`. -/
theorem extended_index_odd {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ}
    (hext : Extended G z A₀ x t p q i s) : Odd i := by
  obtain ⟨_, hq, hqAt, _, hi2, hiq, hst, hsnone, hcover⟩ := hext
  have hws := h.2.2.2.2.1.1
  have hwhole : i < (x (t + 1) :: q).length := by simp; omega
  have helem : (x (t + 1) :: q)[i] = q[i - 1] := by
    cases i with
    | zero => omega
    | succ i => rfl
  have hspi : G.Adj (x s) q[i - 1] := by
    obtain ⟨w, hw, hsw⟩ := hcover s hst
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact (hsnone w hw hsw).elim
    · have he : w = (x (t + 1) :: q)[i] := by simpa using hw
      simpa only [he, helem] using hsw
  have hpre : IsPathFrom G ((x (t + 1) :: q).take (i + 1))
      (x (t + 1)) q[i - 1] := by
    refine ⟨PathBasics.isPathList_take hq (by omega), by simp, ?_⟩
    simpa only [helem] using getLast?_take_succ (x (t + 1) :: q) i hwhole
  have hsNot : x s ∉ (x (t + 1) :: q).take (i + 1) := by
    intro hm
    have hm' := List.take_subset _ _ hm
    rcases List.mem_cons.mp hm' with he | hm'
    · have hi := hws.2.1 s (by omega) (t + 1) le_rfl he
      omega
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := s) (by omega) (hqAt _ hm')
  have hpath : IsPathFrom G (((x (t + 1) :: q).take (i + 1)) ++ [x s])
      (x (t + 1)) (x s) := by
    apply PathAttach.isPathFrom_concat hpre hspi hsNot
    intro w hw hne
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hsnone w hw
    · exact (hne (by simpa only [List.mem_singleton, helem] using hw)).elim
  have hzNot : z ∉ ((x (t + 1) :: q).take (i + 1)) ++ [x s] := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_cons.mp (List.take_subset _ _ hm) with he | hm
      · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (hqAt _ hm)
    · exact (hws.2.2.1 s (by omega)).2 (by simpa using (show z = x s by simpa using hm).symm)
  have hzI : ∀ w ∈ SPGT.interior (((x (t + 1) :: q).take (i + 1)) ++ [x s]),
      ¬ G.Adj z w := by
    intro w hw
    have hd := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hw
    rcases List.mem_append.mp hd.1 with hw | hw
    · rcases List.mem_cons.mp (List.take_subset _ _ hw) with he | hw
      · exact (hd.2.1 he).elim
      · exact WheelSystemBasics.wheelSystemA_no_nbr (hqAt _ hw)
    · exact (hd.2.2 (by simpa using hw)).elim
  have hlen : (((x (t + 1) :: q).take (i + 1)) ++ [x s]).length = i + 2 := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  have heven := PrismBasics.even_of_path_closed_by_vertex h.1.1.1.1.1 hpath
    (by rw [hlen]; omega) hzNot
    (hws.2.2.2.2.2.2 (t + 1) le_rfl) (hws.2.2.2.2.2.2 s (by omega)) hzI
  rw [hlen] at heven
  obtain ⟨d, hd⟩ := heven
  exact ⟨d - 2, by omega⟩

/-- Shared hole construction for the hat argument of 21.2(4), printed p. 133.

PAPER: *"let `p_i-r₁-⋯-r_k-y` be a path from `p_i` to `y` with interior in
`A_{t−1} ∪ {p_{i+1},…,p_m}`.  Then `z-x_{t+1}-p₁-⋯-p_i-r₁-⋯-r_k-y-z` is a hole of length `≥ 6`,
and the only `X_t`-complete vertices in this hole are `z, y`.  By 2.10 `X_t` contains a hat or
a leap for this hole."*

The conclusion packages the outcome of 2.10 for `J = min(i, m)`: some `x_j ∈ X_t` has no
neighbour in `{x_{t+1}, p₁,…,p_J}`, and moreover either it also misses the whole connecting
path `r₁-⋯-r_k` (the hat case) or some member of `X_t` is adjacent to `x_{t+1}` and not to
`p_J` (the leap case). -/
theorem claim4_hat_outcome {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p q : List V} {i s : ℕ} (hp : GoodPath G z A₀ x t p)
    (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s)
    {y : V} (hy : y ∈ Y) (hyx : ¬ G.Adj y (x (t + 1)))
    (hyp : ∀ w ∈ q.take i, ¬ G.Adj y w) :
    ∃ hJ : min i p.length - 1 < p.length, ∃ j ≤ t,
      (∀ w ∈ x (t + 1) :: p.take (min i p.length), ¬ G.Adj (x j) w) ∧
      ((∃ R : Set V, ConnectedSet G R ∧ R ⊆ wheelSystemA G z A₀ x t ∧
          (∃ r ∈ R, G.Adj (p[min i p.length - 1]'hJ) r) ∧ (∃ r ∈ R, G.Adj y r) ∧
          (∀ r ∈ R, ¬ G.Adj (x j) r)) ∨
        (∃ j' ≤ t, G.Adj (x j') (x (t + 1)) ∧
          ¬ G.Adj (x j') (p[min i p.length - 1]'hJ))) := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  obtain ⟨hpref, hqpath, hqAt, hcov0, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  have hpm : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hppath : IsPathList G p := by
    have := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using this
  have hpnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpA1 : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  -- the paper's `min(i, m)`
  set J : ℕ := min i p.length with hJdef
  have hJ1 : 1 ≤ J := by omega
  have hJp : J ≤ p.length := by omega
  have hJi : J ≤ i := by omega
  have hJ1p : J - 1 < p.length := by omega
  -- `hyp` transported to `p`
  have hypp : ∀ (l : ℕ) (hl : l < p.length), l < i → ¬ G.Adj y (p[l]'hl) := by
    intro l hl hli
    have hlq : l < q.length := by have := hpref.length_le; omega
    have hmem : q[l]'hlq ∈ q.take i := by
      have hlt : l < (q.take i).length := by simp only [List.length_take]; omega
      have hh := List.getElem_mem hlt
      rwa [List.getElem_take] at hh
    have he : q[l]'hlq = p[l]'hl := (hpref.getElem hl).symm
    rw [← he]
    exact hyp _ hmem
  -- the prefix `z-x_{t+1}-p₁-⋯-p_J` of the hole
  have hpretake : (x (t + 1) :: p).take (J + 1) = x (t + 1) :: p.take J := by simp
  have hpre0 : IsPathList G (x (t + 1) :: p.take J) := by
    rw [← hpretake]
    exact PathBasics.isPathList_take hp.1 (by omega)
  have hprelast : (x (t + 1) :: p.take J).getLast? = some (p[J - 1]'hJ1p) := by
    have hh := PathBasics.getLast?_slice (x (t + 1) :: p) (i := 0) (j := J)
      (Nat.zero_le _) (by simp only [List.length_cons]; omega)
    simp only [List.drop_zero, Nat.sub_zero] at hh
    rw [hpretake] at hh
    rw [hh]
    congr 1
    rw [HoleArithmetic.getElem_congr_idx (x (t + 1) :: p)
      (show J < (x (t + 1) :: p).length by simp only [List.length_cons]; omega)
      (show J - 1 + 1 < (x (t + 1) :: p).length by simp only [List.length_cons]; omega)
      (show J = J - 1 + 1 by omega)]
    rfl
  have hpre : IsPathFrom G (x (t + 1) :: p.take J) (x (t + 1)) (p[J - 1]'hJ1p) :=
    ⟨hpre0, by simp, hprelast⟩
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hznotp : ∀ v ∈ p, z ≠ v := by
    intro v hv he
    exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (he ▸ hpA v hv)
  have hznot : z ∉ (x (t + 1) :: p.take J) := by
    intro hm
    rcases List.mem_cons.mp hm with he | hm
    · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
    · exact hznotp _ (List.mem_of_mem_take hm) rfl
  have hzother : ∀ w ∈ (x (t + 1) :: p.take J), w ≠ x (t + 1) → ¬ G.Adj z w := by
    intro w hw hne
    rcases List.mem_cons.mp hw with he | hw
    · exact (hne he).elim
    · exact WheelSystemBasics.wheelSystemA_no_nbr (hpA w (List.mem_of_mem_take hw))
  have hPpath : IsPathFrom G (z :: x (t + 1) :: p.take J) z (p[J - 1]'hJ1p) :=
    PathAttach.isPathFrom_cons hpre hzxt1 hznot hzother
  -- the connected set `A_{t-1} ∪ {p_{J+1},…,p_m}`
  set B : Set V := wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop J} with hBdef
  have hBcon : ConnectedSet G B := goodPath_suffix_connected h hp J
  have hBAt : B ⊆ wheelSystemA G z A₀ x t := by
    rintro v (hv | hv)
    · exact WheelSystemBasics.wheelSystemA_mono (by omega) hv
    · exact hpA v (List.mem_of_mem_drop hv)
  have hdropmem : ∀ (l : ℕ) (hl : l < p.length), J ≤ l → (p[l]'hl) ∈ p.drop J := by
    intro l hl hJl
    have hidx : l - J < (p.drop J).length := by simp only [List.length_drop]; omega
    have hh := List.getElem_mem hidx
    rw [List.getElem_drop] at hh
    rwa [HoleArithmetic.getElem_congr_idx p (show J + (l - J) < p.length by omega) hl
      (by omega)] at hh
  have hdropidx : ∀ w ∈ p.drop J, ∃ (l : ℕ) (hl : l < p.length), J ≤ l ∧ (p[l]'hl) = w := by
    intro w hw
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hw
    simp only [List.length_drop] at hn
    exact ⟨J + n, by omega, by omega, by simp only [List.getElem_drop]⟩
  have hstartB : (p[J - 1]'hJ1p) ∉ B := by
    rintro (hv | hv)
    · exact hpA1 _ (List.getElem_mem hJ1p) hv
    · obtain ⟨l, hl, hJl, he⟩ := hdropidx _ hv
      have := hpnd.getElem_inj_iff.mp he
      omega
  have hyAt : y ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (j := t) (by omega) hy
  have hyB : y ∉ B := fun hm => hyAt (hBAt hm)
  have hstartnbr : ∃ b ∈ B, G.Adj (p[J - 1]'hJ1p) b := by
    rcases Nat.lt_or_ge J p.length with hlt | hge
    · refine ⟨p[J]'hlt, Or.inr (hdropmem J hlt le_rfl), ?_⟩
      have hh := PathBasics.path_adj_succ hppath (i := J - 1) (by omega)
      rwa [HoleArithmetic.getElem_congr_idx p (show J - 1 + 1 < p.length by omega) hlt
        (by omega)] at hh
    · have hJe : J = p.length := by omega
      obtain ⟨a, ha, hadj⟩ := (hp.2.2.2 (p.length - 1) (by omega)).mpr (by omega)
      exact ⟨a, Or.inl ha, by rw [HoleArithmetic.getElem_congr_idx p hJ1p
        (show p.length - 1 < p.length by omega) (by omega)]; exact hadj⟩
  have hynbr : ∃ b ∈ B, G.Adj y b := by
    obtain ⟨a, ha, hya⟩ := hc3 y hy
    rcases ha with ha | ha | ha
    · exact ⟨a, Or.inl ha, hya⟩
    · exact absurd (ha ▸ hya) hyx
    · obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem ha
      have hli : ¬ l < i := fun hc => hypp l hl hc hya
      exact ⟨_, Or.inr (hdropmem l hl (by omega)), hya⟩
  obtain ⟨W, hW, hWint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hBcon hstartB hyB hstartnbr hynbr
  have hstarty : ¬ G.Adj (p[J - 1]'hJ1p) y := fun hc =>
    hypp (J - 1) hJ1p (by omega) hc.symm
  have hstartney : (p[J - 1]'hJ1p) ≠ y := fun he => hyAt (he ▸ hpA _ (List.getElem_mem hJ1p))
  have hW3 : 3 ≤ W.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hW hstartney hstarty
  -- the second half of the hole, `r₁-⋯-r_k-y`
  have hWnd : W.Nodup := PathBasics.path_nodup hW.1
  have hW0 : W[0]'(by omega) = (p[J - 1]'hJ1p) :=
    PathBasics.getElem_zero_of_head? hW.2.1 (by omega)
  have hWlast : W[W.length - 1]'(by omega) = y :=
    PathBasics.getElem_last_of_getLast? hW.2.2 (by omega)
  have hRpath : IsPathList G (W.drop 1) := PathBasics.isPathList_drop hW.1 (by omega)
  have hRhead : (W.drop 1).head? = some (W[1]'(by omega)) := by
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < (W.drop 1).length by simp only [List.length_drop]; omega)]
    congr 1
    simp only [List.getElem_drop]
  have hRlast : (W.drop 1).getLast? = some y := by
    rw [List.getLast?_drop, if_neg (by omega), List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show W.length - 1 < W.length by omega), hWlast]
  have hR : IsPathFrom G (W.drop 1) (W[1]'(by omega)) y := ⟨hRpath, hRhead, hRlast⟩
  have hRidx : ∀ v ∈ W.drop 1, ∃ (n : ℕ) (hn : n < W.length), 1 ≤ n ∧ W[n]'hn = v := by
    intro v hv
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hv
    simp only [List.length_drop] at hn
    exact ⟨1 + n, by omega, by omega, by simp only [List.getElem_drop]⟩
  have hRmem : ∀ v ∈ W.drop 1, v = y ∨ v ∈ B := by
    intro v hv
    by_cases hvy : v = y
    · exact Or.inl hvy
    refine Or.inr (hWint v ?_)
    rw [PathBasics.mem_interior_iff_of_pathFrom hW]
    refine ⟨List.mem_of_mem_drop hv, ?_, hvy⟩
    obtain ⟨n, hn, hn1, rfl⟩ := hRidx v hv
    intro he
    rw [← hW0] at he
    have := hWnd.getElem_inj_iff.mp he
    omega
  -- the first half of the hole
  set Pl : List V := z :: x (t + 1) :: p.take J with hPldef
  have hPllen : Pl.length = J + 2 := by
    simp only [hPldef, List.length_cons, List.length_take]
    omega
  have hPlmem : ∀ v ∈ Pl, v = z ∨ v = x (t + 1) ∨
      ∃ (l : ℕ) (hl : l < p.length), l < J ∧ (p[l]'hl) = v := by
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · exact Or.inl he
    rcases List.mem_cons.mp hv with he | hv
    · exact Or.inr (Or.inl he)
    · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem hv
      simp only [List.length_take] at hn
      exact Or.inr (Or.inr ⟨n, by omega, by omega, by simp only [List.getElem_take]⟩)
  have hzy : G.Adj z y := hhub.2.2.2.2.1 y hy
  have hxt1notY : x (t + 1) ∉ Y := KiteTailBasics.hub_last_notMem hhub
  have hxt1At : x (t + 1) ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
  have hzAt : z ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
  have hdisj : ∀ v ∈ Pl, v ∉ W.drop 1 := by
    intro v hv hvR
    rcases hRmem v hvR with rfl | hvB
    · rcases hPlmem v hv with rfl | rfl | ⟨l, hl, hlJ, he⟩
      · exact G.irrefl hzy
      · exact hxt1notY hy
      · exact hyAt (he ▸ hpA _ (List.getElem_mem hl))
    · rcases hPlmem v hv with rfl | rfl | ⟨l, hl, hlJ, he⟩
      · exact hzAt (hBAt hvB)
      · exact hxt1At (hBAt hvB)
      · rcases hvB with hvB | hvB
        · exact hpA1 _ (List.getElem_mem hl) (he ▸ hvB)
        · obtain ⟨l', hl', hJl', he'⟩ := hdropidx _ hvB
          have := hpnd.getElem_inj_iff.mp (he.trans he'.symm)
          omega
  have hWadj01 : G.Adj (W[0]'(by omega)) (W[1]'(by omega)) :=
    PathBasics.path_adj_succ hW.1 (i := 0) (by omega)
  have hWuniq : ∀ v ∈ W.drop 1, G.Adj (p[J - 1]'hJ1p) v → v = W[1]'(by omega) := by
    intro v hv hadj
    obtain ⟨n, hn, hn1, rfl⟩ := hRidx v hv
    rw [← hW0] at hadj
    have hnn := (PathBasics.path_adj_iff hW.1 (show 0 < W.length by omega) hn).mp hadj
    have : n = 1 := by omega
    exact HoleArithmetic.getElem_congr_idx W hn (by omega) this
  have hcross : ∀ v ∈ Pl, ∀ w ∈ W.drop 1,
      (G.Adj v w ↔ (v = (p[J - 1]'hJ1p) ∧ w = W[1]'(by omega)) ∨ (v = z ∧ w = y)) := by
    intro v hv w hw
    constructor
    · intro hadj
      rcases hPlmem v hv with rfl | rfl | ⟨l, hl, hlJ, rfl⟩
      · rcases hRmem w hw with rfl | hwB
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd hadj (WheelSystemBasics.wheelSystemA_no_nbr (hBAt hwB))
      · exfalso
        rcases hRmem w hw with rfl | hwB
        · exact hyx hadj.symm
        · rcases hwB with hwB | hwB
          · exact hxt1A w hwB hadj
          · obtain ⟨l', hl', hJl', rfl⟩ := hdropidx _ hwB
            have hcons : G.Adj ((x (t + 1) :: p)[0]'(by simp)) ((x (t + 1) :: p)[l' + 1]'(by
              simp only [List.length_cons]; omega)) := hadj
            have := (PathBasics.path_adj_iff hp.1 (show 0 < (x (t + 1) :: p).length by simp)
              (show l' + 1 < (x (t + 1) :: p).length by simp only [List.length_cons]; omega)).mp
              hcons
            omega
      · by_cases hlJ1 : l = J - 1
        · refine Or.inl ⟨HoleArithmetic.getElem_congr_idx p hl hJ1p hlJ1, ?_⟩
          exact hWuniq w hw (by rwa [← HoleArithmetic.getElem_congr_idx p hl hJ1p hlJ1])
        · exfalso
          rcases hRmem w hw with rfl | hwB
          · exact hypp l hl (by omega) hadj.symm
          · rcases hwB with hwB | hwB
            · have := (hp.2.2.2 l hl).mp ⟨w, hwB, hadj⟩
              omega
            · obtain ⟨l', hl', hJl', rfl⟩ := hdropidx _ hwB
              have := (PathBasics.path_adj_iff hppath hl hl').mp hadj
              omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · rw [← hW0]; exact hWadj01
      · exact hzy
  have hC : IsHoleList G (Pl ++ W.drop 1) :=
    PathGlue.glue_hole hPpath hR hdisj hcross (by simp only [List.length_drop]; omega)
  set C : List V := Pl ++ W.drop 1 with hCdef
  have hPlsubC : ∀ w ∈ Pl, w ∈ C := fun w hw => List.mem_append_left _ hw
  have hClen : C.length = J + 2 + (W.length - 1) := by
    simp only [hCdef, List.length_append, hPllen, List.length_drop]
  have hC5 : 5 ≤ C.length := by omega
  have hymem : y ∈ C := List.mem_append_right _ (PathBasics.getLast_mem hRlast)
  have hzmem : z ∈ C := hPlsubC z (by simp [hPldef])
  have hyPl : y ∉ Pl := fun hm => hdisj y hm (PathBasics.getLast_mem hRlast)
  have hW1ney : (W[1]'(by omega)) ≠ y := by
    rw [← hWlast]
    exact fun he => by have := hWnd.getElem_inj_iff.mp he; omega
  have hCne_y : ∀ v ∈ Pl, G.Adj y v → v = z := by
    intro v hv hadj
    rcases (hcross v hv y (PathBasics.getLast_mem hRlast)).mp hadj.symm with ⟨-, he⟩ | ⟨he, -⟩
    · exact absurd he.symm hW1ney
    · exact he
  -- the only `X_t`-complete vertices of the hole are `z` and `y`
  have hCmem : ∀ w ∈ C, w = y ∨ w ∈ Pl ∨ w ∈ B := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact Or.inr (Or.inl hw)
    · rcases hRmem w hw with rfl | hwB
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hwB)
  have hCX : ∀ w ∈ C, w ∉ wheelSystemX x t := by
    intro w hw hwX
    obtain ⟨j, hj, rfl⟩ := hwX
    rcases hCmem _ hw with he | hw' | hwB
    · exact G.irrefl (he ▸ hhub.2.2.2.2.2.1 j (by omega) y hy)
    · rcases hPlmem _ hw' with he | he | ⟨l, hl, hlJ, he⟩
      · exact (hws.2.2.1 j (by omega)).2 he
      · have := hws.2.1 j (by omega) (t + 1) le_rfl he
        omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega)
          (he ▸ hpA _ (List.getElem_mem hl))
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hBAt hwB)
  have hzX : VertexComplete G z (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hyX : VertexComplete G y (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    exact (hhub.2.2.2.2.2.1 j (by omega) y hy).symm
  have honly : ∀ w ∈ C, VertexComplete G w (wheelSystemX x t) → w = z ∨ w = y := by
    intro w hw hwc
    rcases hCmem w hw with rfl | hw' | hwB
    · exact Or.inr rfl
    · rcases hPlmem _ hw' with he | he | ⟨l, hl, hlJ, he⟩
      · exact Or.inl he
      · exfalso
        have hh := hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl
        simp only [Nat.add_sub_cancel] at hh
        exact hh (he ▸ hwc)
      · exact absurd hwc (WheelSystemBasics.wheelSystemA_no_complete
          (he ▸ hpA _ (List.getElem_mem hl)))
    · exact absurd hwc (WheelSystemBasics.wheelSystemA_no_complete (hBAt hwB))
  have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge (wheelSystemX x t)
    (Thm203Prelim.anticonnected_wheelSystemX hws t (by omega)) C hC hCX
    (by simp only [holeLength]; omega) z y hzmem hymem hzy hzX hyX honly
  -- in every case some `x_j ∈ X_t` has no neighbour in `{x_{t+1}, p₁,…,p_J}`
  have hleaphelp : ∀ (c : V) (D : List V) (e : ℕ) (he : e < D.length),
      (∀ w ∈ Pl, w ∈ D) → G.Adj y (D[e]'he) →
      (∀ (n : ℕ) (hn : n < D.length), G.Adj c (D[n]'hn) → (n = 0 ∨ n = e ∨ n = D.length - 1)) →
      (∀ (n : ℕ) (hn : n < D.length), (n = 0 ∨ n = D.length - 1) →
        ((D[n]'hn) = z ∨ (D[n]'hn) = y)) →
      ∀ w ∈ Pl, w ≠ z → ¬ G.Adj c w := by
    intro c D e he hPD hye hnb hends w hw hwz hadj
    obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem (hPD w hw)
    rw [← hnw] at hadj hwz hw
    rcases hnb n hn hadj with h0 | h1 | h2
    · rcases hends n hn (Or.inl h0) with hc | hc
      · exact hwz hc
      · exact hyPl (hc ▸ hw)
    · have hde : (D[n]'hn) = D[e]'he := HoleArithmetic.getElem_congr_idx D hn he h1
      exact hwz (hCne_y _ hw (by rw [hde]; exact hye))
    · rcases hends n hn (Or.inr h2) with hc | hc
      · exact hwz hc
      · exact hyPl (hc ▸ hw)
  have hpmmem : (p[J - 1]'hJ1p) ∈ Pl := by
    simp only [hPldef]
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    have hlt : J - 1 < (p.take J).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hpmC : (p[J - 1]'hJ1p) ∈ C := hPlsubC _ hpmmem
  have hpmz : (p[J - 1]'hJ1p) ≠ z := fun he => hznotp _ (List.getElem_mem hJ1p) he.symm
  have hpmx : (p[J - 1]'hJ1p) ≠ x (t + 1) :=
    fun he => hxt1At (he ▸ hpA _ (List.getElem_mem hJ1p))
  have hzC : ∀ w ∈ C, G.Adj z w → w = x (t + 1) ∨ w = y := by
    intro w hw hadj
    rcases List.mem_append.mp hw with hw | hw
    · refine Or.inl ?_
      obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem hw
      have hz0 : Pl[0]'(by omega) = z := rfl
      rw [← hnw] at hadj ⊢
      rw [← hz0] at hadj
      have := (PathBasics.path_adj_iff hPpath.1 (show 0 < Pl.length by omega) hn).mp hadj
      have hn1 : n = 1 := by omega
      rw [HoleArithmetic.getElem_congr_idx Pl hn (show 1 < Pl.length by omega) hn1]
      rfl
    · rcases (hcross z (by simp only [hPldef]; exact List.mem_cons_self) w hw).mp hadj with
        ⟨he, -⟩ | ⟨-, he⟩
      · exact absurd he hpmz.symm
      · exact Or.inr he
  have hleaphelp : ∀ (c : V) (D : List V) (e : ℕ) (he : e < D.length),
      (∀ w ∈ Pl, w ∈ D) → G.Adj y (D[e]'he) →
      (∀ (n : ℕ) (hn : n < D.length), G.Adj c (D[n]'hn) → (n = 0 ∨ n = e ∨ n = D.length - 1)) →
      (∀ (n : ℕ) (hn : n < D.length), (n = 0 ∨ n = D.length - 1) →
        ((D[n]'hn) = z ∨ (D[n]'hn) = y)) →
      ∀ w ∈ Pl, w ≠ z → ¬ G.Adj c w := by
    intro c D e he hPD hye hnb hends w hw hwz hadj
    obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem (hPD w hw)
    rw [← hnw] at hadj hwz hw
    rcases hnb n hn hadj with h0 | h1 | h2
    · rcases hends n hn (Or.inl h0) with hc | hc
      · exact hwz hc
      · exact hyPl (hc ▸ hw)
    · have hde : (D[n]'hn) = D[e]'he := HoleArithmetic.getElem_congr_idx D hn he h1
      exact hwz (hCne_y _ hw (by rw [hde]; exact hye))
    · rcases hends n hn (Or.inr h2) with hc | hc
      · exact hwz hc
      · exact hyPl (hc ▸ hw)
  have hleapextra : ∀ (c : V) (D : List V) (e : ℕ) (he : e < D.length),
      (∀ w ∈ C, w ∈ D) → (D[e]'he) = x (t + 1) →
      (∀ (n : ℕ) (hn : n < D.length), G.Adj c (D[n]'hn) ↔ (n = 0 ∨ n = e ∨ n = D.length - 1)) →
      (∀ (n : ℕ) (hn : n < D.length), (n = 0 ∨ n = D.length - 1) →
        ((D[n]'hn) = z ∨ (D[n]'hn) = y)) →
      G.Adj c (x (t + 1)) ∧ ¬ G.Adj c (p[J - 1]'hJ1p) := by
    intro c D e he hCD hDe hnb hends
    refine ⟨by rw [← hDe]; exact (hnb e he).mpr (Or.inr (Or.inl rfl)), ?_⟩
    intro hadj
    obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem (hCD _ hpmC)
    rw [← hnw] at hadj
    rcases (hnb n hn).mp hadj with h0 | h1 | h2
    · rcases hends n hn (Or.inl h0) with hc | hc
      · exact hpmz (by rw [← hnw, hc])
      · exact hstartney (by rw [← hnw, hc])
    · exact hpmx (by rw [← hnw, HoleArithmetic.getElem_congr_idx D hn he h1, hDe])
    · rcases hends n hn (Or.inr h2) with hc | hc
      · exact hpmz (by rw [← hnw, hc])
      · exact hstartney (by rw [← hnw, hc])
  have hbad : ∃ j ≤ t, (∀ w ∈ Pl, w ≠ z → ¬ G.Adj (x j) w) ∧
      ((∀ w ∈ C, w ≠ z → w ≠ y → ¬ G.Adj (x j) w) ∨
        ∃ j' ≤ t, G.Adj (x j') (x (t + 1)) ∧ ¬ G.Adj (x j') (p[J - 1]'hJ1p)) := by
    rcases h210 with ⟨hh, hhX, hhat⟩ | ⟨a, haX, b, hbX, hleap⟩
    · obtain ⟨j, hj, rfl⟩ := hhX
      have hfull : ∀ w ∈ C, w ≠ z → w ≠ y → ¬ G.Adj (x j) w :=
        fun w hw hwz hwy => hhat.2.2.2.2.2.2 w hw hwz hwy
      exact ⟨j, by omega, fun w hw hwz => hfull w (hPlsubC w hw) hwz
        (fun he => hyPl (he ▸ hw)), Or.inl hfull⟩
    · have hbridge : ∀ (u v c w : V), c ≠ u → c ≠ v →
          ((G.deleteEdges {s(u, v)}).Adj c w ↔ G.Adj c w) := by
        intro u v c w hcu hcv
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨fun hq => hq.1, fun hq => ⟨hq, ?_⟩⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact hcu h1
        · exact hcv h1
      have hXne : ∀ c ∈ wheelSystemX x t, c ≠ z ∧ c ≠ y := by
        rintro c ⟨j, hj, rfl⟩
        exact ⟨(hws.2.2.1 j (by omega)).2,
          fun he => G.irrefl (he ▸ hhub.2.2.2.2.2.1 j (by omega) y hy)⟩
      rcases hleap with hl | hl
      · -- the rotation runs from `y` to `z`: `a` avoids `Pl`, and `b` is adjacent to `x_{t+1}`
        obtain ⟨-, idx, hhead, hlast, hlp⟩ := hl
        obtain ⟨hDpath, hDlen2, -, -, hAdjA, hAdjB⟩ := hlp
        have haz : a ≠ z := (hXne a haX).1
        have hay : a ≠ y := (hXne a haX).2
        have hbz : b ≠ z := (hXne b hbX).1
        have hby : b ≠ y := (hXne b hbX).2
        obtain ⟨j, hj, rfl⟩ := haX
        obtain ⟨jb, hjb, rfl⟩ := hbX
        have hDlen : (C.rotate idx).length = C.length := List.length_rotate ..
        have hD0 : (C.rotate idx)[0]'(by omega) = y :=
          PathBasics.getElem_zero_of_head? hhead (by omega)
        have hDl : (C.rotate idx)[(C.rotate idx).length - 1]'(by omega) = z :=
          PathBasics.getElem_last_of_getLast? hlast (by omega)
        have hends : ∀ (n : ℕ) (hn : n < (C.rotate idx).length), (n = 0 ∨
            n = (C.rotate idx).length - 1) →
            (((C.rotate idx)[n]'hn) = z ∨ ((C.rotate idx)[n]'hn) = y) := by
          intro n hn hcase
          rcases hcase with hc | hc
          · exact Or.inr (by rw [HoleArithmetic.getElem_congr_idx _ hn (by omega) hc]; exact hD0)
          · exact Or.inl (by rw [HoleArithmetic.getElem_congr_idx _ hn (by omega) hc]; exact hDl)
        refine ⟨j, by omega, ?_, Or.inr ⟨jb, by omega, ?_⟩⟩
        · refine hleaphelp _ (C.rotate idx) 1 (by omega)
            (fun w hw => List.mem_rotate.mpr (hPlsubC w hw)) ?_ ?_ hends
          · have hh := PathBasics.path_adj_succ hDpath (i := 0) (by omega)
            rw [hD0] at hh
            exact (SimpleGraph.deleteEdges_adj.mp hh).1
          · intro n hn hadj
            exact (hAdjA n hn).mp ((hbridge z y _ _ haz hay).mpr hadj)
        · -- `D[len-2]` is a neighbour of `z = D[len-1]` other than `y = D[0]`, hence `x_{t+1}`
          have he2 : (C.rotate idx).length - 2 < (C.rotate idx).length := by omega
          have hadj2 : G.Adj z ((C.rotate idx)[(C.rotate idx).length - 2]'he2) := by
            have hh := PathBasics.path_adj_succ hDpath
              (i := (C.rotate idx).length - 2) (by omega)
            rw [HoleArithmetic.getElem_congr_idx _ (show (C.rotate idx).length - 2 + 1 <
              (C.rotate idx).length by omega) (show (C.rotate idx).length - 1 <
              (C.rotate idx).length by omega) (by omega), hDl] at hh
            exact ((SimpleGraph.deleteEdges_adj.mp hh).1).symm
          have hmem2 : ((C.rotate idx)[(C.rotate idx).length - 2]'he2) ∈ C :=
            List.mem_rotate.mp (List.getElem_mem he2)
          have hDe : ((C.rotate idx)[(C.rotate idx).length - 2]'he2) = x (t + 1) := by
            rcases hzC _ hmem2 hadj2 with hc | hc
            · exact hc
            · exfalso
              rw [← hD0] at hc
              have := (List.nodup_rotate.mpr hC.2.1).getElem_inj_iff.mp hc
              omega
          exact hleapextra _ (C.rotate idx) _ he2
            (fun w hw => List.mem_rotate.mpr hw) hDe
            (fun n hn => (hbridge z y _ _ hbz hby).symm.trans (hAdjB n hn)) hends
      · -- the rotation runs from `z` to `y`: `b` avoids `Pl`, and `a` is adjacent to `x_{t+1}`
        obtain ⟨-, idx, hhead, hlast, hlp⟩ := hl
        obtain ⟨hDpath, hDlen2, -, -, hAdjA, hAdjB⟩ := hlp
        have haz : a ≠ z := (hXne a haX).1
        have hay : a ≠ y := (hXne a haX).2
        have hbz : b ≠ z := (hXne b hbX).1
        have hby : b ≠ y := (hXne b hbX).2
        obtain ⟨j, hj, rfl⟩ := hbX
        obtain ⟨ja, hja, rfl⟩ := haX
        have hDlen : (C.rotate idx).length = C.length := List.length_rotate ..
        have hD0 : (C.rotate idx)[0]'(by omega) = z :=
          PathBasics.getElem_zero_of_head? hhead (by omega)
        have hDl : (C.rotate idx)[(C.rotate idx).length - 1]'(by omega) = y :=
          PathBasics.getElem_last_of_getLast? hlast (by omega)
        have hends : ∀ (n : ℕ) (hn : n < (C.rotate idx).length), (n = 0 ∨
            n = (C.rotate idx).length - 1) →
            (((C.rotate idx)[n]'hn) = z ∨ ((C.rotate idx)[n]'hn) = y) := by
          intro n hn hcase
          rcases hcase with hc | hc
          · exact Or.inl (by rw [HoleArithmetic.getElem_congr_idx _ hn (by omega) hc]; exact hD0)
          · exact Or.inr (by rw [HoleArithmetic.getElem_congr_idx _ hn (by omega) hc]; exact hDl)
        refine ⟨j, by omega, ?_, Or.inr ⟨ja, by omega, ?_⟩⟩
        · refine hleaphelp _ (C.rotate idx) ((C.rotate idx).length - 2) (by omega)
            (fun w hw => List.mem_rotate.mpr (hPlsubC w hw)) ?_ ?_ hends
          · have hh := PathBasics.path_adj_succ hDpath
              (i := (C.rotate idx).length - 2) (by omega)
            rw [HoleArithmetic.getElem_congr_idx _ (show (C.rotate idx).length - 2 + 1 <
              (C.rotate idx).length by omega) (show (C.rotate idx).length - 1 <
              (C.rotate idx).length by omega) (by omega), hDl] at hh
            exact ((SimpleGraph.deleteEdges_adj.mp hh).1).symm
          · intro n hn hadj
            exact (hAdjB n hn).mp ((hbridge y z _ _ hby hbz).mpr hadj)
        · have he2 : 1 < (C.rotate idx).length := by omega
          have hadj2 : G.Adj z ((C.rotate idx)[1]'he2) := by
            have hh := PathBasics.path_adj_succ hDpath (i := 0) (by omega)
            rw [hD0] at hh
            exact (SimpleGraph.deleteEdges_adj.mp hh).1
          have hmem2 : ((C.rotate idx)[1]'he2) ∈ C :=
            List.mem_rotate.mp (List.getElem_mem he2)
          have hDe : ((C.rotate idx)[1]'he2) = x (t + 1) := by
            rcases hzC _ hmem2 hadj2 with hc | hc
            · exact hc
            · exfalso
              rw [← hDl] at hc
              have := (List.nodup_rotate.mpr hC.2.1).getElem_inj_iff.mp hc
              omega
          exact hleapextra _ (C.rotate idx) 1 he2
            (fun w hw => List.mem_rotate.mpr hw) hDe
            (fun n hn => (hbridge y z _ _ hay haz).symm.trans (hAdjA n hn)) hends
  obtain ⟨j, hj, hjbad, hjmore⟩ := hbad
  refine ⟨hJ1p, j, hj, fun w hw => hjbad w (List.mem_cons_of_mem _ hw)
    (fun he => hznot (he ▸ hw)), ?_⟩
  rcases hjmore with hfull | hlp
  · refine Or.inl ⟨{v : V | v ∈ SPGT.interior W},
      MinimalConnectedIsPath.connectedSet_interior hW, ?_, ?_, ?_, ?_⟩
    · intro v hv
      exact hBAt (hWint v hv)
    · refine ⟨W[1]'(by omega), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        rw [PathBasics.mem_interior_iff_of_pathFrom hW]
        refine ⟨List.getElem_mem _, ?_, ?_⟩
        · rw [← hW0]; exact fun he => by have := hWnd.getElem_inj_iff.mp he; omega
        · rw [← hWlast]; exact fun he => by have := hWnd.getElem_inj_iff.mp he; omega
      · rw [← hW0]; exact hWadj01
    · refine ⟨W[W.length - 2]'(by omega), ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        rw [PathBasics.mem_interior_iff_of_pathFrom hW]
        refine ⟨List.getElem_mem _, ?_, ?_⟩
        · rw [← hW0]; exact fun he => by have := hWnd.getElem_inj_iff.mp he; omega
        · rw [← hWlast]; exact fun he => by have := hWnd.getElem_inj_iff.mp he; omega
      · have hh := PathBasics.path_adj_succ hW.1 (i := W.length - 2) (by omega)
        rw [HoleArithmetic.getElem_congr_idx W (show W.length - 2 + 1 < W.length by omega)
          (show W.length - 1 < W.length by omega) (by omega), hWlast] at hh
        exact hh.symm
    · intro r hr
      refine hfull r ?_ (fun he => hzAt (he ▸ hBAt (hWint r hr)))
        ((PathBasics.mem_interior_iff_of_pathFrom hW).mp hr).2.2
      refine List.mem_append_right _ ?_
      have hr' := (PathBasics.mem_interior_iff_of_pathFrom hW).mp hr
      obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem hr'.1
      have hn0 : n ≠ 0 := by
        intro he
        exact hr'.2.1 (by rw [← hnw, HoleArithmetic.getElem_congr_idx W hn (by omega) he, hW0])
      have hidx : n - 1 < (W.drop 1).length := by simp only [List.length_drop]; omega
      have hh := List.getElem_mem hidx
      rw [List.getElem_drop, HoleArithmetic.getElem_congr_idx W
        (show 1 + (n - 1) < W.length by omega) hn (by omega), hnw] at hh
      exact hh
  · exact Or.inr hlp

/-- Labelled gap for the **second** case of the hat argument of 21.2(4), printed p. 133.

PAPER: *"Now suppose that `i > m`, and so `s = t`.  Let `p_m-r₁-⋯-r_k-y` be a path from `p_m`
to `y` with interior in `A_{t−1}`.  Again, `z-x_{t+1}-p₁-⋯-p_m-r₁-⋯-r_k-y-z` is a hole of
length `≥ 6`, and its only `X_t`-complete vertices are `z, y`.  By 2.10 `X_t` contains a hat or
leap.  By (1) it contains no leap, so there exists `x ∈ X_t` nonadjacent to all
`x_{t+1}, p₁,…,p_m, r₁,…,r_k`.  Since `p_m` is `X_{t−1}`-complete, it follows that `x = x_t`.
Now `{x_{t+1}, p₁,…,p_i, r₁,…,r_k}` (`= F` say) is connected, and catches the triangle
`{y, z, x_t}`; the only neighbour of `z` in `F` is `x_{t+1}`; the only neighbour of `y` in `F`
is `r_k` (because `y` is nonadjacent to `x_{t+1}, p₁,…,p_i`); and the only neighbour of `x_t`
in `F` is `p_i` (because `x_t` is a hat).  Since `x_{t+1}` is not adjacent to `p_i`, this
contradicts 17.1."*

The hypothesis `hbig` is the printed *"suppose that `i > m`"*; the case `i ≤ m` of the same
paragraph is proved in `claim4_hat_gap`. -/
theorem claim4_hat_large_index_gap {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p q : List V} {i s : ℕ} (hp : GoodPath G z A₀ x t p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s) (hiodd : Odd i)
    {y : V} (hy : y ∈ Y) (hyx : ¬ G.Adj y (x (t + 1)))
    (hyp : ∀ w ∈ q.take i, ¬ G.Adj y w) (hbig : p.length < i) : False := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  obtain ⟨hpref, hqpath, hqAt, hcov0, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hpm0 : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hJm : min i p.length = p.length := by omega
  obtain ⟨hJ1p, j, hj, hjbad, hjmore⟩ := claim4_hat_outcome h hp hc3 hext hy hyx hyp
  set m1 : ℕ := min i p.length - 1 with hm1def
  set pm : V := p[m1]'hJ1p with hpmdef
  have hm1e : m1 = p.length - 1 := by omega
  have hpmA : pm ∈ wheelSystemA G z A₀ x t := hpA _ (List.getElem_mem hJ1p)
  have hpmc : VertexComplete G pm (wheelSystemX x (t - 1)) := by
    refine Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (i := t - 1) (by omega)
      (WheelSystemBasics.wheelSystemA_no_nbr hpmA)
      (hp.2.2.1 _ (List.getElem_mem hJ1p)).2 ?_
    exact (hp.2.2.2 m1 hJ1p).mpr (by omega)
  have hqJ1 : m1 < q.length := by have := hpref.length_le; omega
  have hpmq : q[m1]'hqJ1 = pm := (hpref.getElem hJ1p).symm
  have hjbadp : ∀ w ∈ p, ¬ G.Adj (x j) w := by
    intro w hw
    refine hjbad w (List.mem_cons_of_mem _ ?_)
    rw [hJm]; simpa using hw
  have hjbadx : ¬ G.Adj (x j) (x (t + 1)) := hjbad _ List.mem_cons_self
  have hmemtakei : ∀ (l : ℕ) (hl : l < q.length), l + 1 < i →
      (q[l]'hl) ∈ (x (t + 1) :: q).take i := by
    intro l hl hli
    have hsplit : (x (t + 1) :: q).take i = x (t + 1) :: q.take (i - 1) := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp
    rw [hsplit]
    refine List.mem_cons_of_mem _ ?_
    have hlt : l < (q.take (i - 1)).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hspm : ¬ G.Adj (x s) pm := by
    have hmem := hmemtakei m1 hqJ1 (by omega)
    rw [hpmq] at hmem
    exact hsnone _ hmem
  have hs : s = t := by
    by_contra hne
    exact hspm (hpmc (x s) ⟨s, by omega, rfl⟩).symm
  have hxtxt1 : ¬ G.Adj (x s) (x (t + 1)) := by
    refine hsnone _ ?_
    have hsplit : (x (t + 1) :: q).take i = x (t + 1) :: q.take (i - 1) := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp
    rw [hsplit]; exact List.mem_cons_self
  have hjt : j = t := by
    by_contra hne
    exact hjbadp pm (List.getElem_mem hJ1p) (hpmc (x j) ⟨j, by omega, rfl⟩).symm
  obtain ⟨R, hRcon, hRA, ⟨r0, hr0R, hr0adj⟩, ⟨r1, hr1R, hr1adj⟩, hRbad⟩ :
      ∃ R : Set V, ConnectedSet G R ∧ R ⊆ wheelSystemA G z A₀ x t ∧
        (∃ r ∈ R, G.Adj pm r) ∧ (∃ r ∈ R, G.Adj y r) ∧ (∀ r ∈ R, ¬ G.Adj (x j) r) := by
    rcases hjmore with hf | ⟨j', hj', hadj', hnadj'⟩
    · exact hf
    · exfalso
      have hj't : j' = t := by
        by_contra hne
        exact hnadj' (hpmc (x j') ⟨j', by omega, rfl⟩).symm
      rw [hj't] at hadj'
      exact hxtxt1 (by rw [hs]; exact hadj')
  -- the triangle `{y, z, x_t}`
  have hzy : G.Adj z y := hhub.2.2.2.2.1 y hy
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hzxt : G.Adj z (x t) := hws.2.2.2.2.2.2 t (by omega)
  have hxty : G.Adj (x t) y := hhub.2.2.2.2.2.1 t (by omega) y hy
  have hxt1notY : x (t + 1) ∉ Y := KiteTailBasics.hub_last_notMem hhub
  have hxt1At : x (t + 1) ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
  have hzAt : z ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
  have hyAt : y ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (j := t) (by omega) hy
  have hxtnotAt : x t ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
  set TT : Set V := ({y, z, x t} : Set V) with hTTdef
  have hTri : IsTriangle G TT := by
    refine ⟨Set.ncard_eq_three.mpr ⟨y, z, x t, hzy.ne', hxty.ne', hzxt.ne, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact absurd rfl huv
    · exact hzy.symm
    · exact hxty.symm
    · exact hzy
    · exact absurd rfl huv
    · exact hzxt
    · exact hxty
    · exact hzxt.symm
    · exact absurd rfl huv
  set T : List V := (x (t + 1) :: q).take (i + 1) with hTdef
  set F : Set V := {v : V | v ∈ T} ∪ R with hFdef
  have hTpath : IsPathList G T := PathBasics.isPathList_take hqpath (by omega)
  have hTmem : ∀ w ∈ T, w = x (t + 1) ∨ ∃ (l : ℕ) (hl : l < q.length), l < i ∧
      (q[l]'hl) = w := by
    intro w hw
    have hsplit : T = x (t + 1) :: q.take i := by simp only [hTdef]; simp
    rw [hsplit] at hw
    rcases List.mem_cons.mp hw with he | hw
    · exact Or.inl he
    · obtain ⟨l, hl, hlw⟩ := List.mem_iff_getElem.mp hw
      have hli : l < i := by simp only [List.length_take] at hl; omega
      refine Or.inr ⟨l, by simp only [List.length_take] at hl; omega, hli, ?_⟩
      rw [← hlw, List.getElem_take]
  have hmemtake1 : ∀ (l : ℕ) (hl : l < q.length), l < i → (q[l]'hl) ∈ T := by
    intro l hl hli
    have hsplit : T = x (t + 1) :: q.take i := by simp only [hTdef]; simp
    rw [hsplit]
    refine List.mem_cons_of_mem _ ?_
    have hlt : l < (q.take i).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hpmT : pm ∈ T := by
    rw [← hpmq]; exact hmemtake1 m1 hqJ1 (by omega)
  have hFAt : ∀ w ∈ F, w = x (t + 1) ∨ w ∈ wheelSystemA G z A₀ x t := by
    rintro w (hw | hw)
    · rcases hTmem w hw with he | ⟨l, hl, -, he⟩
      · exact Or.inl he
      · exact Or.inr (he ▸ hqAt _ (List.getElem_mem hl))
    · exact Or.inr (hRA hw)
  have hFcon : ConnectedSet G F :=
    ConnectedSetUnionAttach.connectedSet_union
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hTpath) hRcon
      (Or.inr ⟨pm, hpmT, r0, hr0R, hr0adj⟩)
  have hFdisj : Disjoint F TT := by
    rw [Set.disjoint_left]
    intro w hwF hwT
    simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hwT
    rcases hFAt w hwF with he | hwA
    · rcases hwT with rfl | rfl | rfl
      · exact hxt1notY (he ▸ hy)
      · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
      · have := hws.2.1 (t + 1) le_rfl t (by omega) he.symm
        omega
    · rcases hwT with rfl | rfl | rfl
      · exact hyAt hwA
      · exact hzAt hwA
      · exact hxtnotAt hwA
  have hxt1T : x (t + 1) ∈ T := by
    simp only [hTdef]
    exact List.mem_of_mem_head? (by simp)
  have hFcatch : Catches G F TT := by
    refine ⟨hTri, hFcon, hFdisj, ?_⟩
    intro a ha
    simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨r1, Or.inr hr1R, hr1adj⟩
    · exact ⟨x (t + 1), Or.inl hxt1T, hzxt1⟩
    · obtain ⟨w, hw, hadjw⟩ := hcover t le_rfl
      exact ⟨w, Or.inl hw, hadjw⟩
  have hunique : ∀ w ∈ F, G.Adj z w → w = x (t + 1) := by
    intro w hwF hadj
    rcases hFAt w hwF with he | hwA
    · exact he
    · exact absurd hadj (WheelSystemBasics.wheelSystemA_no_nbr hwA)
  have hxt1q : ∀ (l : ℕ) (hl : l < q.length), G.Adj (x (t + 1)) (q[l]'hl) → l = 0 := by
    intro l hl hadj
    have hcons : G.Adj ((x (t + 1) :: q)[0]'(by simp))
        ((x (t + 1) :: q)[l + 1]'(by simp only [List.length_cons]; omega)) := hadj
    have := (PathBasics.path_adj_iff hqpath (show 0 < (x (t + 1) :: q).length by simp)
      (show l + 1 < (x (t + 1) :: q).length by simp only [List.length_cons]; omega)).mp hcons
    omega
  have hcommon : ∀ w ∈ F, G.Adj (x (t + 1)) w → ¬ G.Adj (x t) w := by
    rintro w (hw | hw) hadj1 hadj2
    · rcases hTmem w hw with he | ⟨l, hl, hli, he⟩
      · exact G.irrefl (he ▸ hadj1)
      · have hl0 : l = 0 := hxt1q l hl (he ▸ hadj1)
        exact hsnone _ (hmemtakei l hl (by omega)) (by rw [hs]; exact he ▸ hadj2)
    · exact hRbad w hw (by rw [hjt]; exact hadj2)
  have honesub : ∀ (w c : V), (∀ a ∈ TT, G.Adj w a → a = c) →
      (G.neighborSet w ∩ TT).ncard ≤ 1 := by
    intro w c hsub
    have hss : (G.neighborSet w ∩ TT) ⊆ ({c} : Set V) := by
      rintro a ⟨ha1, ha2⟩
      exact hsub a ha2 ha1
    calc (G.neighborSet w ∩ TT).ncard ≤ ({c} : Set V).ncard :=
          Set.ncard_le_ncard hss (Set.toFinite _)
      _ = 1 := Set.ncard_singleton _
  have hone : ∀ w ∈ F, (G.neighborSet w ∩ TT).ncard ≤ 1 := by
    rintro w (hw | hw)
    · rcases hTmem w hw with he | ⟨l, hl, hli, he⟩
      · subst he
        refine honesub _ z ?_
        intro a ha hadj
        simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · exact absurd hadj.symm hyx
        · rfl
        · exact absurd (by rw [hs]; exact hadj.symm) hxtxt1
      · refine honesub _ (x t) ?_
        intro a ha hadj
        simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rcases ha with rfl | rfl | rfl
        · refine absurd (he ▸ hadj.symm) (hyp _ ?_)
          have hlt : l < (q.take i).length := by simp only [List.length_take]; omega
          have hh := List.getElem_mem hlt
          rw [List.getElem_take] at hh
          exact he ▸ hh
        · exact absurd hadj.symm
            (WheelSystemBasics.wheelSystemA_no_nbr (he ▸ hqAt _ (List.getElem_mem hl)))
        · rfl
    · refine honesub _ y ?_
      intro a ha hadj
      simp only [hTTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · rfl
      · exact absurd hadj.symm (WheelSystemBasics.wheelSystemA_no_nbr (hRA hw))
      · exact absurd hadj.symm (fun hc => hRbad w hw (by rw [hjt]; exact hc))
  exact Thm212Claim3Tools.catch_obstruction hGF (F := F) (T := TT) (u := z) (v := x t)
    (z := x (t + 1)) hFcatch (by simp [hTTdef]) (by simp [hTTdef]) hzxt.ne
    hunique hcommon hone

/-- Labelled gap for the *hat* case of 21.2(4), p. 133.

PAPER: *"So `Y` contains a hat, that is, there exists `y ∈ Y` nonadjacent to
`x_{t+1}, p₁,…,p_i`.  By (3), `y` has a neighbour in `A_{t−1} ∪ {p_j : i+1 ≤ j ≤ m}`.
Suppose first that `i ≤ m`, and let `p_i-r₁-⋯-r_k-y` be a path from `p_i` to `y` with interior
in `A_{t−1} ∪ {p_{i+1},…,p_m}`.  Then `z-x_{t+1}-p₁-⋯-p_i-r₁-⋯-r_k-y-z` is a hole of length
`≥ 6`, and the only `X_t`-complete vertices in this hole are `z, y`. … so some `x ∈ X_t` has
no neighbour in `{x_{t+1},p₁,…,p_i}`, contrary to the choice of `i`.  Now suppose that
`i > m`, and so `s = t`. … Since `x_{t+1}` is not adjacent to `p_i`, this contradicts 17.1.
This proves (4)."*

`hyp` is *"`y` is nonadjacent to `p₁,…,p_i`"* (the entries of `q.take i` are `p₁,…,p_i`). -/
theorem claim4_hat_gap {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p q : List V} {i s : ℕ} (hp : GoodPath G z A₀ x t p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s) (hiodd : Odd i)
    {y : V} (hy : y ∈ Y) (hyx : ¬ G.Adj y (x (t + 1)))
    (hyp : ∀ w ∈ q.take i, ¬ G.Adj y w) : False := by
  classical
  obtain ⟨hpref, hqpath, hqAt, hcov0, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  rcases Nat.lt_or_ge p.length i with hbig | hsmall
  · exact claim4_hat_large_index_gap h hp hc1 hc3 hext hiodd hy hyx hyp hbig
  · obtain ⟨hJ1p, j, hj, hjbad, -⟩ := claim4_hat_outcome h hp hc3 hext hy hyx hyp
    obtain ⟨w, hw, hadjw⟩ := hcover j hj
    have hsplit : (x (t + 1) :: q).take (i + 1) = x (t + 1) :: q.take i := by simp
    rw [hsplit] at hw
    refine hjbad w ?_ hadjw
    rcases List.mem_cons.mp hw with he | hw
    · rw [he]; exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      obtain ⟨l, hl, hlw⟩ := List.mem_iff_getElem.mp hw
      have hli : l < i := by simp only [List.length_take] at hl; omega
      have hlp : l < p.length := by omega
      have hlq : l < q.length := by simp only [List.length_take] at hl; omega
      have hwq : q[l]'hlq = w := by rw [← hlw, List.getElem_take]
      have hwp : (p[l]'hlp) = w := by rw [← hwq]; exact hpref.getElem hlp
      rw [← hwp]
      have hlt : l < (p.take (min i p.length)).length := by simp only [List.length_take]; omega
      have hh := List.getElem_mem hlt
      rwa [List.getElem_take] at hh

/-- Labelled gap for the second assertion of 21.2(4), p. 133.
PAPER: "Suppose `p_i` is not `Y`-complete ... This proves (4)."
The remaining argument excludes the leap and the two hat cases. -/
theorem endgame_claim4_hub_complete_gap {G : SimpleGraph V} {Y : Set V} {z : V}
    {A₀ : Set V} {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t)
    {p q : List V} {i s : ℕ} (hp : GoodPath G z A₀ x t p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s) (hiodd : Odd i) :
    ∃ hi : i - 1 < q.length, VertexComplete G q[i - 1] Y := by
  classical
  obtain ⟨hpref, hq, hqAt, hcov0, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  obtain ⟨hG, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hG.1.1.1.1
  have hi3 : 3 ≤ i := by obtain ⟨d, hd⟩ := hiodd; omega
  refine ⟨by omega, ?_⟩
  by_contra hnc
  -- the hole `C = z-x_{t+1}-p₁-⋯-p_i-x_s-z`
  have hwhole : i < (x (t + 1) :: q).length := by simp; omega
  have helem : (x (t + 1) :: q)[i] = q[i - 1] := by
    cases i with
    | zero => omega
    | succ i => rfl
  have hspi : G.Adj (x s) q[i - 1] := by
    obtain ⟨w, hw, hsw⟩ := hcover s hst
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact (hsnone w hw hsw).elim
    · have he : w = (x (t + 1) :: q)[i] := by simpa using hw
      simpa only [he, helem] using hsw
  have hpre : IsPathFrom G ((x (t + 1) :: q).take (i + 1)) (x (t + 1)) q[i - 1] := by
    refine ⟨PathBasics.isPathList_take hq (by omega), by simp, ?_⟩
    simpa only [helem] using getLast?_take_succ (x (t + 1) :: q) i hwhole
  have hsNot : x s ∉ (x (t + 1) :: q).take (i + 1) := by
    intro hm
    have hm' := List.take_subset _ _ hm
    rcases List.mem_cons.mp hm' with he | hm'
    · have hi := hws.2.1 s (by omega) (t + 1) le_rfl he
      omega
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := s) (by omega) (hqAt _ hm')
  have hpath : IsPathFrom G (((x (t + 1) :: q).take (i + 1)) ++ [x s]) (x (t + 1)) (x s) := by
    apply PathAttach.isPathFrom_concat hpre hspi hsNot
    intro w hw hne
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact hsnone w hw
    · exact (hne (by simpa only [List.mem_singleton, helem] using hw)).elim
  have hzNot : z ∉ ((x (t + 1) :: q).take (i + 1)) ++ [x s] := by
    intro hm
    rcases List.mem_append.mp hm with hm | hm
    · rcases List.mem_cons.mp (List.take_subset _ _ hm) with he | hm
      · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
      · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (hqAt _ hm)
    · exact (hws.2.2.1 s (by omega)).2 (by simpa using (show z = x s by simpa using hm).symm)
  have hzI : ∀ w ∈ SPGT.interior (((x (t + 1) :: q).take (i + 1)) ++ [x s]), ¬ G.Adj z w := by
    intro w hw
    have hd := (PathBasics.mem_interior_iff_of_pathFrom hpath).mp hw
    rcases List.mem_append.mp hd.1 with hw | hw
    · rcases List.mem_cons.mp (List.take_subset _ _ hw) with he | hw
      · exact (hd.2.1 he).elim
      · exact WheelSystemBasics.wheelSystemA_no_nbr (hqAt _ hw)
    · exact (hd.2.2 (by simpa using hw)).elim
  have hlen : (((x (t + 1) :: q).take (i + 1)) ++ [x s]).length = i + 2 := by
    simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
    omega
  have hplen : pathLength (((x (t + 1) :: q).take (i + 1)) ++ [x s]) = i + 1 := by
    rw [PathBasics.pathLength_eq, hlen]
    omega
  have hC : IsHoleList G (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) :=
    PrismBasics.isHoleList_of_path_add_vertex hpath (by rw [hplen]; omega)
      (hws.2.2.2.2.2.2 (t + 1) le_rfl) (hws.2.2.2.2.2.2 s (by omega)) hzNot hzI
  have hClen : (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).length = i + 3 := by
    simp only [List.length_cons, hlen]
  have hzY : VertexComplete G z Y := hhub.2.2.2.2.1
  have hxsY : VertexComplete G (x s) Y := hhub.2.2.2.2.2.1 s (by omega)
  have hzxs : G.Adj z (x s) := hws.2.2.2.2.2.2 s (by omega)
  have htakeS : ∀ w ∈ (x (t + 1) :: q).take (i + 1),
      w ∈ (x (t + 1) :: q).take i ∨ w = q[i - 1] := by
    intro w hw
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact Or.inl hw
    · exact Or.inr (by simpa only [List.mem_singleton, helem] using hw)
  have hCY : ∀ w ∈ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])), w ∉ Y := by
    intro w hw hwY
    rcases List.mem_cons.mp hw with he | hw
    · exact G.irrefl (he ▸ hzY w hwY)
    rcases List.mem_append.mp hw with hw | hw
    · rcases List.mem_cons.mp (List.take_subset _ _ hw) with he | hw'
      · exact KiteTailBasics.hub_last_notMem hhub (he ▸ hwY)
      · exact Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (j := t) (by omega)
          hwY (hqAt w hw')
    · have he : w = x s := by simpa using hw
      exact G.irrefl (he ▸ hxsY w hwY)
  have hnbr : ∀ w ∈ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])),
      (G.Adj w z ∨ G.Adj w (x s)) → VertexComplete G w Y → w = z ∨ w = x s := by
    intro w hw hadjw hcw
    rcases List.mem_cons.mp hw with he | hw
    · exact Or.inl he
    rcases List.mem_append.mp hw with hw | hw
    · rcases htakeS w hw with hw' | he
      · rcases List.mem_cons.mp (List.take_subset _ _ hw') with he | hw''
        · exact absurd (he ▸ hcw) hhub.2.2.2.2.2.2
        · rcases hadjw with hadjw | hadjw
          · exact absurd hadjw.symm (WheelSystemBasics.wheelSystemA_no_nbr (hqAt w hw''))
          · exact absurd hadjw.symm (hsnone w hw')
      · exact absurd (he ▸ hcw) hnc
    · exact Or.inr (by simpa using hw)
  have honly := Thm212OnlyTwoComplete.only_two_complete hBerge hG.2.1 hC
    (by rw [hClen]; omega) hhub.2.1 hhub.2.2.1 hCY (by simp)
    (by simp) hzxs hzY hxsY hnbr
  have h210 := _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge Y hhub.2.2.1
    (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) hC hCY
    (by simp only [holeLength, hClen]; omega) z (x s) (by simp) (by simp) hzxs hzY hxsY honly
  rcases h210 with ⟨w0, hw0Y, hhat⟩ | ⟨a, haY, b, hbY, hleap⟩
  · -- *"So `Y` contains a hat, that is, there exists `y ∈ Y` nonadjacent to
    -- `x_{t+1}, p₁,…,p_i`."*
    have hnoC := hhat.2.2.2.2.2.2
    have hxt1mem : x (t + 1) ∈ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) := by
      refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
      exact List.mem_of_mem_head? (by simp)
    have hxt1nez : x (t + 1) ≠ z := (hws.2.2.1 (t + 1) le_rfl).2
    have hxt1nes : x (t + 1) ≠ x s := by
      intro he
      have := hws.2.1 (t + 1) le_rfl s (by omega) he
      omega
    refine claim4_hat_gap h hp hc1 hc3 hext hiodd hw0Y
      (hnoC (x (t + 1)) hxt1mem hxt1nez hxt1nes) ?_
    intro w hw hadj
    have hwmem : w ∈ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) := by
      refine List.mem_cons_of_mem _ (List.mem_append_left _ ?_)
      have : (x (t + 1) :: q).take (i + 1) = x (t + 1) :: q.take i := by
        simp [List.take_succ_cons]
      rw [this]
      exact List.mem_cons_of_mem _ hw
    have hwq : w ∈ q := List.mem_of_mem_take hw
    refine hnoC w hwmem ?_ ?_ hadj
    · intro he
      exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (he ▸ hqAt w hwq)
    · intro he
      exact Thm203Prelim.x_notMem_wheelSystemA hws (j := s) (by omega) (he ▸ hqAt w hwq)
  · -- *"Suppose it contains a leap; then there are nonadjacent `y₁,y₂ ∈ Y` such that
    -- `y₁-x_{t+1}-p₁-⋯-p_i-y₂` is a path."*
    exfalso
    have hnd : (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).Nodup := hC.2.1
    have hMideq : (x (t + 1) :: q).take (i + 1) = x (t + 1) :: q.take i := by
      simp [List.take_succ_cons]
    have hMidlen : ((x (t + 1) :: q).take (i + 1)).length = i + 1 := by
      simp only [List.length_take, List.length_cons]; omega
    have haC : a ∉ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) :=
      fun hm => hCY a hm haY
    have hbC : b ∉ (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) :=
      fun hm => hCY b hm hbY
    have haz : a ≠ z := fun he => haC (by rw [he]; simp)
    have hbz : b ≠ z := fun he => hbC (by rw [he]; simp)
    have has : a ≠ x s := fun he => haC (by rw [he]; simp)
    have hbs : b ≠ x s := fun he => hbC (by rw [he]; simp)
    have haMid : a ∉ (x (t + 1) :: q).take (i + 1) :=
      fun hm => haC (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    have hbMid : b ∉ (x (t + 1) :: q).take (i + 1) :=
      fun hm => hbC (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    have hxsidx : (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s]))[i + 2]'(by omega) = x s := by
      simp only [List.getElem_cons_succ]
      rw [List.getElem_append_right (by omega)]
      simp [hMidlen]
    have hgood : IsLeapForPath (G.deleteEdges {s(x s, z)})
        (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])) a b := by
      rcases hleap with hl | hl
      · -- head `x s`, last `z`: impossible, the rotation at `x s` ends at `p_i`
        exfalso
        obtain ⟨-, k, hhd, hlst, -⟩ := hl
        have hrot := rotate_index_eq hnd (j := i + 2) (by omega) hhd hxsidx
        rw [hrot] at hlst
        have hlen' : ((z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).rotate (i + 2)).length
            = i + 3 := by rw [List.length_rotate]; omega
        rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlst
        have hg : ((z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).rotate (i + 2))[
            ((z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).rotate (i + 2)).length - 1]'
            (by omega) = z := Option.some.inj hlst
        rw [List.getElem_rotate] at hg
        have hidx : (((z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).rotate (i + 2)).length
            - 1 + (i + 2)) % (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).length
            = i + 1 := by
          rw [hlen']
          rw [show (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).length = i + 3 by omega]
          have : i + 3 - 1 + (i + 2) = (i + 1) + (i + 3) := by omega
          rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
        rw [HoleArithmetic.getElem_congr_idx _ _ (show i + 1 <
          (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).length by omega) hidx] at hg
        have hz0 : (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s]))[0]'(by omega) = z := rfl
        have := hnd.getElem_inj_iff.mp (hg.trans hz0.symm)
        omega
      · obtain ⟨-, k, hhd, hlst, hlp⟩ := hl
        have hrot := rotate_index_eq hnd (j := 0) (by omega) hhd rfl
        rw [hrot, List.rotate_zero] at hlp
        exact hlp
    obtain ⟨-, -, hab, hnab0, hAdjA, hAdjB⟩ := hgood
    have hbridge : ∀ (c w : V), c ≠ x s → c ≠ z →
        ((G.deleteEdges {s(x s, z)}).Adj c w ↔ G.Adj c w) := by
      intro c w hcz hcy
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨fun hq => hq.1, fun hq => ⟨hq, ?_⟩⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hcz h1
      · exact hcy h1
    have hCidx : ∀ (m : ℕ) (hm : m < ((x (t + 1) :: q).take (i + 1)).length)
        (h2 : m + 1 < (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s])).length),
        (z :: (((x (t + 1) :: q).take (i + 1)) ++ [x s]))[m + 1]'h2 =
          ((x (t + 1) :: q).take (i + 1))[m]'hm := by
      intro m hm h2
      simp only [List.getElem_cons_succ]
      exact List.getElem_append_left hm
    have hnab : ¬ G.Adj a b := fun hq => hnab0 ((hbridge a b has haz).mpr hq)
    have hM0 : ((x (t + 1) :: q).take (i + 1))[0]'(by omega) = x (t + 1) :=
      PathBasics.getElem_zero_of_head? hpre.2.1 (by omega)
    have hMi : ((x (t + 1) :: q).take (i + 1))[i]'(by omega) = q[i - 1] := by
      have hh := PathBasics.getElem_last_of_getLast? hpre.2.2 (show 0 < _ by omega)
      rw [HoleArithmetic.getElem_congr_idx _ (show i < ((x (t + 1) :: q).take (i + 1)).length
        by omega) (show ((x (t + 1) :: q).take (i + 1)).length - 1 <
        ((x (t + 1) :: q).take (i + 1)).length by omega) (by omega)]
      exact hh
    have hAM : G.Adj a (x (t + 1)) := by
      have hq0 := (hAdjA 1 (by omega)).mpr (Or.inr (Or.inl rfl))
      rw [hCidx 0 (by omega) (by omega), hM0] at hq0
      exact (hbridge a _ has haz).mp hq0
    have hAother : ∀ w ∈ (x (t + 1) :: q).take (i + 1), w ≠ x (t + 1) → ¬ G.Adj a w := by
      intro w hw hwne hcon
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
      have hq0 := (hAdjA (m + 1) (by omega)).mp
        (by rw [hCidx m hm (by omega)]; exact (hbridge a _ has haz).mpr hcon)
      have hm0 : m = 0 := by
        simp only [List.length_cons, List.length_append, hMidlen] at hq0
        omega
      subst hm0
      exact hwne hM0
    have hBM : G.Adj b q[i - 1] := by
      have hq0 := (hAdjB (i + 1) (by omega)).mpr (Or.inr (Or.inl (by rw [hClen]; omega)))
      rw [hCidx i (by omega) (by omega), hMi] at hq0
      exact (hbridge b _ hbs hbz).mp hq0
    have hBother : ∀ w ∈ (x (t + 1) :: q).take (i + 1), w ≠ q[i - 1] → ¬ G.Adj b w := by
      intro w hw hwne hcon
      obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hw
      have hq0 := (hAdjB (m + 1) (by omega)).mp
        (by rw [hCidx m hm (by omega)]; exact (hbridge b _ hbs hbz).mpr hcon)
      have hmi : m = i := by
        simp only [List.length_cons, List.length_append, hMidlen] at hq0
        omega
      subst hmi
      exact hwne hMi
    have hL : IsPathFrom G (a :: (((x (t + 1) :: q).take (i + 1)) ++ [b])) a b :=
      PathAttach.isPathFrom_cons_concat hpre hAM hBM hnab hab haMid hbMid hAother hBother
    have hLlen : pathLength (a :: (((x (t + 1) :: q).take (i + 1)) ++ [b])) = i + 2 := by
      rw [PathAttach.pathLength_cons_append_singleton, hMidlen]
    -- 13.6 applied to this odd path with ends `X_t`-complete
    have hXcomp : ∀ w : V, w ∈ Y → VertexComplete G w (wheelSystemX x t) := by
      rintro w hwY u ⟨j, hj, rfl⟩
      exact (hhub.2.2.2.2.2.1 j (by omega) w hwY).symm
    have hLcomplete : ∀ w ∈ (a :: (((x (t + 1) :: q).take (i + 1)) ++ [b])),
        VertexComplete G w (wheelSystemX x t) → w = a ∨ w = b := by
      intro w hw hwc
      rcases List.mem_cons.mp hw with he | hw
      · exact Or.inl he
      rcases List.mem_append.mp hw with hw | hw
      · rcases List.mem_cons.mp (by rwa [hMideq] at hw) with he | hw'
        · exfalso
          have hh := hws.2.2.2.2.2.1 (t + 1) (by omega) le_rfl
          simp only [Nat.add_sub_cancel] at hh
          exact hh (he ▸ hwc)
        · exact absurd hwc (WheelSystemBasics.wheelSystemA_no_complete
            (hqAt w (List.mem_of_mem_take hw')))
      · exact Or.inr (by simpa using hw)
    have hXP : wheelSystemX x t ⊆
        {v : V | v ∈ (a :: (((x (t + 1) :: q).take (i + 1)) ++ [b]))}ᶜ := by
      rintro u ⟨j, hj, rfl⟩ hmem
      simp only [Set.mem_setOf_eq] at hmem
      rcases List.mem_cons.mp hmem with he | hmem
      · exact G.irrefl (he ▸ hhub.2.2.2.2.2.1 j (by omega) a haY)
      rcases List.mem_append.mp hmem with hmem | hmem
      · rcases List.mem_cons.mp (by rwa [hMideq] at hmem) with he | hmem'
        · have := hws.2.1 j (by omega) (t + 1) le_rfl he
          omega
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega)
            (hqAt _ (List.mem_of_mem_take hmem'))
      · exact G.irrefl ((by simpa using hmem : x j = b) ▸
          hhub.2.2.2.2.2.1 j (by omega) b hbY)
    have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1
      (a :: (((x (t + 1) :: q).take (i + 1)) ++ [b])) a b hL
      (by rw [hLlen]; obtain ⟨d, hd⟩ := hiodd; exact ⟨d + 1, by omega⟩)
      (wheelSystemX x t) hXP (Thm203Prelim.anticonnected_wheelSystemX hws t (by omega))
      (hXcomp a haY) (hXcomp b hbY)
    rcases h136 with ⟨u, hu, v, hv, hedge⟩ | ⟨h3, -⟩
    · rcases hLcomplete u hu hedge.2.1 with rfl | rfl <;>
        rcases hLcomplete v hv hedge.2.2 with he | he
      · exact G.irrefl (he ▸ hedge.1)
      · exact hnab (he ▸ hedge.1)
      · exact hnab (he ▸ hedge.1).symm
      · exact G.irrefl (he ▸ hedge.1)
    · rw [hLlen] at h3
      omega


/-- Labelled gap for 21.2(4), p. 133.
PAPER: "`i` is odd, and `p_i` is `Y`-complete."
The hole, hat, and leap argument in that claim proves these two assertions. -/
theorem endgame_claim4_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ}
    (hp : GoodPath G z A₀ x t p) (hc1 : NoOddLeapPath G z A₀ x t)
    (hc3 : SpanY G z A₀ x t Y p) (hext : Extended G z A₀ x t p q i s) :
    Odd i ∧ ∃ hi : i - 1 < q.length, VertexComplete G q[i - 1] Y := by
  have hi := extended_index_odd h hext
  exact ⟨hi, endgame_claim4_hub_complete_gap h hp hc1 hc3 hext hi⟩

/-- The first case of the middle-vertex analysis in the proof of 21.2(5), printed p. 133.

PAPER: *"Suppose first that `q ∈ {p₁,…,p_m}`; then it follows that `q = p_{m−1}`.  Hence
`q-Q-x_t-p_m` is an even antipath of length `≥ 4`; `q` is its only vertex that is anticomplete
to `A_{t−1}`, and `p_m` is its only vertex that is anticomplete to
`{z, x_{t+1}, p₁,…,p_{m−2}}`.  Since the sets `A_{t−1}`, `{z, x_{t+1}, p₁,…,p_{m−2}}` are each
connected and anticomplete to each other, this contradicts 13.7 applied in `Ḡ`."*

Here `qm` is the paper's `q`, `pm` its `p_m`, and `Q` the odd antipath produced by 13.6. -/
theorem claim5_even_middle_in_path {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V}
    (hp : GoodPath G z A₀ x t p) {pm qm : V} {Q : List V}
    (hpmlast : p.getLast? = some pm)
    (hpmc : VertexComplete G pm (wheelSystemX x (t - 1)))
    (hxtpm : ¬ G.Adj (x t) pm) (hpmqm : G.Adj pm qm)
    (hqmp : qm ∈ p)
    (hxtqm : G.Adj (x t) qm)
    (hqmnc : ¬ VertexComplete G qm (wheelSystemX x (t - 1)))
    (hQ : IsAntipathFrom G Q (x t) qm) (hQodd : Odd (pathLength Q))
    (hQ3 : 3 ≤ pathLength Q)
    (hQint : ∀ u ∈ SPGT.interior Q, u ∈ wheelSystemX x (t - 1)) : False := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hpne : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hMlt : p.length - 1 < p.length := by omega
  have hpmeq : pm = p[p.length - 1]'hMlt := by
    have hh := hpmlast
    rw [List.getLast?_eq_some_getLast hp.2.1, List.getLast_eq_getElem] at hh
    exact (Option.some.inj hh).symm
  have hppath : IsPathList G p := by
    have hh := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using hh
  have hpnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpA1 : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  have hxt1p : ∀ (j : ℕ) (hj : j < p.length), G.Adj (x (t + 1)) (p[j]'hj) ↔ j = 0 := by
    intro j hj
    have hh := hp.1.2.2 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
    have h0 : (x (t + 1) :: p)[0]'(by simp) = x (t + 1) := rfl
    have hj1 : (x (t + 1) :: p)[j + 1]'(by simp only [List.length_cons]; omega) = p[j]'hj := rfl
    rw [h0, hj1] at hh
    rw [hh]; omega
  -- `A_{t-1}` is nonempty and every `x_j`, `j ≤ t`, has a neighbour in it
  obtain ⟨B, hB0, hBcon, hBadj, hBz, hBX⟩ := hws.2.2.2.2.1 t (by omega) (by omega)
  have hBsub : ∀ v ∈ B, v ∈ wheelSystemA G z A₀ x (t - 1) :=
    fun v hv => WheelSystemBasics.mem_wheelSystemA_of_witness hB0 hBcon hBz hBX hv
  obtain ⟨a0, ha0⟩ := hframe.1
  have hA1ne : (wheelSystemA G z A₀ x (t - 1)).Nonempty := ⟨a0, hBsub a0 (hB0 ha0)⟩
  have hxA : ∀ j ≤ t, ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (x j) a := by
    intro j hj
    rcases Nat.lt_or_ge j 2 with hj2 | hj2
    · have hb : ∃ b ∈ A₀, G.Adj (x j) b := by
        interval_cases j
        · exact hws.2.2.2.1.1
        · exact hws.2.2.2.1.2.1
      obtain ⟨b, hb, hadj⟩ := hb
      exact ⟨b, hBsub b (hB0 hb), hadj⟩
    · obtain ⟨B', hB0', hBcon', hBadj', hBz', hBX'⟩ := hws.2.2.2.2.1 j hj2 (by omega)
      obtain ⟨a, ha, hadj⟩ := WheelSystemBasics.exists_adj_wheelSystemA_of_witness
        (i := j - 1) hB0' hBcon' hBz' hBX' hBadj'
      exact ⟨a, WheelSystemBasics.wheelSystemA_mono (by omega) ha, hadj⟩
  -- `q = p_{m-1}`
  obtain ⟨l, hl, hlq⟩ := List.getElem_of_mem hqmp
  have hdisj0 := (hppath.2.2 l (p.length - 1) hl hMlt).mp (by rw [hlq, ← hpmeq]; exact hpmqm.symm)
  have hlM : l = p.length - 2 := by omega
  have hM2 : 2 ≤ p.length := by omega
  obtain ⟨n, hn⟩ : ∃ n, p.length = n + 2 := ⟨p.length - 2, by omega⟩
  -- the set `{z, x_{t+1}, p₁, …, p_{m−2}}`
  set Yc : Set V := {z, x (t + 1)} ∪ {v : V | v ∈ p.take n} with hYcdef
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hzAt : z ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
  have hznotp : ∀ v ∈ p, z ≠ v := fun v hv he => hzAt (he ▸ hpA v hv)
  have hzA1 : z ∉ wheelSystemA G z A₀ x (t - 1) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t - 1) (by omega)
  have hxt1A1 : x (t + 1) ∉ wheelSystemA G z A₀ x (t - 1) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
  have hmid : IsPathList G (x (t + 1) :: p.take n) := by
    have hh := PathBasics.isPathList_take hp.1 (k := n + 1) (Nat.succ_pos n)
    rw [List.take_succ_cons] at hh
    exact hh
  have hmidF : IsPathFrom G (x (t + 1) :: p.take n) (x (t + 1))
      ((x (t + 1) :: p.take n).getLast (List.cons_ne_nil _ _)) :=
    ⟨hmid, rfl, List.getLast?_eq_some_getLast _⟩
  have hzmid : z ∉ (x (t + 1) :: p.take n) := by
    intro hz
    rcases List.mem_cons.mp hz with he | he
    · exact (hws.2.2.1 (t + 1) le_rfl).2 he.symm
    · exact hznotp z (List.mem_of_mem_take he) rfl
  have hPz : IsPathList G (z :: x (t + 1) :: p.take n) :=
    (PathAttach.isPathFrom_cons hmidF hzxt1 hzmid (by
      intro w hw hwne
      rcases List.mem_cons.mp hw with he | he
      · exact absurd he hwne
      · exact WheelSystemBasics.wheelSystemA_no_nbr (hpA w (List.mem_of_mem_take he)))).1
  have hYcmem : Yc = {v : V | v ∈ (z :: x (t + 1) :: p.take n)} := by
    ext w
    simp only [hYcdef, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, List.mem_cons]
    tauto
  have hYccon : ConnectedSet G Yc := by
    rw [hYcmem]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPz
  -- `A_{t-1}` is anticomplete to `Yc`, and disjoint from it
  have hsep : ∀ a ∈ wheelSystemA G z A₀ x (t - 1), ∀ w ∈ Yc, a ≠ w ∧ ¬ G.Adj a w := by
    intro a ha w hw
    have haAt : a ∈ wheelSystemA G z A₀ x t := WheelSystemBasics.wheelSystemA_mono (by omega) ha
    simp only [hYcdef, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq] at hw
    rcases hw with (rfl | rfl) | hw
    · exact ⟨fun he => hzA1 (he ▸ ha),
        fun hadj => WheelSystemBasics.wheelSystemA_no_nbr haAt hadj.symm⟩
    · exact ⟨fun he => hxt1A1 (he ▸ ha), fun hadj => hxt1A a ha hadj.symm⟩
    · obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
      simp only [List.length_take] at hj
      have hjp : j < p.length := by omega
      have hjw' : (p[j]'hjp) = w := by rw [← hjw, List.getElem_take]
      refine ⟨fun he => hpA1 w (hjw' ▸ List.getElem_mem hjp) (he ▸ ha), fun hadj => ?_⟩
      exact (hp.2.2.2 j hjp).not.mpr (by omega) ⟨a, ha, by rw [hjw']; exact hadj.symm⟩
  -- the antipath `q-Q-x_t-p_m`
  have hpmc' := hpmc
  have hpmAt : pm ∈ wheelSystemA G z A₀ x t := hpmeq ▸ hpA _ (List.getElem_mem hMlt)
  have hpmqmne : pm ≠ qm := fun he => hqmnc (he ▸ hpmc)
  have hpmxt : pm ≠ x t :=
    fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (he ▸ hpmAt)
  have hQmem : ∀ w ∈ Q, w = x t ∨ w = qm ∨ w ∈ wheelSystemX x (t - 1) := by
    intro w hw
    rcases eq_or_ne w (x t) with he | hwa
    · exact Or.inl he
    rcases eq_or_ne w qm with he | hwb
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (hQint w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, hwa, hwb⟩)))
  have hpmQ : pm ∉ Q := by
    intro hmem
    rcases hQmem _ hmem with he | he | he
    · exact hpmxt he
    · exact hpmqmne he
    · obtain ⟨j, hj, hje⟩ := he
      exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hje ▸ hpmAt)
  have hQrev : IsAntipathFrom G Q.reverse qm (x t) := PathBasics.isAntipathFrom_reverse hQ
  have hAP : IsPathFrom Gᶜ (Q.reverse ++ [pm]) qm pm := by
    refine PathAttach.isPathFrom_concat hQrev
      (SimpleGraph.compl_adj .. |>.mpr ⟨hpmxt, fun hc => hxtpm hc.symm⟩)
      (by simpa using hpmQ) ?_
    intro w hw hwne
    have hw' : w ∈ Q := List.mem_reverse.mp hw
    rcases hQmem w hw' with he | he | he
    · exact absurd he hwne
    · exact fun hc => (SimpleGraph.compl_adj .. |>.mp hc).2 (he ▸ hpmqm)
    · obtain ⟨j, hj, hje⟩ := he
      exact fun hc => (SimpleGraph.compl_adj .. |>.mp hc).2 (hje ▸ hpmc (x j) ⟨j, hj, rfl⟩)
  have hAPlen : pathLength (Q.reverse ++ [pm]) = pathLength Q + 1 := by
    have hQ0 : 0 < Q.length := PathBasics.path_length_pos hQ.1
    simp only [pathLength, List.length_append, List.length_reverse, List.length_singleton]
    omega
  have hAPmem : ∀ w ∈ (Q.reverse ++ [pm]), w = pm ∨ w = x t ∨ w = qm ∨
      w ∈ wheelSystemX x (t - 1) := by
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · rcases hQmem w (List.mem_reverse.mp hw) with he | he | he
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inl he))
      · exact Or.inr (Or.inr (Or.inr he))
    · exact Or.inl (by simpa using hw)
  -- `q` is the only vertex of the antipath anticomplete to `A_{t-1}`
  have hqmA1 : qm ∉ wheelSystemA G z A₀ x (t - 1) := hpA1 qm hqmp
  have hqmno : ¬ ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj qm a := by
    rw [← hlq]
    exact (hp.2.2.2 l hl).not.mpr (by omega)
  have hXuniq : ∀ u ∈ (Q.reverse ++ [pm]),
      (VertexComplete Gᶜ u (wheelSystemA G z A₀ x (t - 1)) ↔ u = qm) := by
    intro u hu
    constructor
    · intro hc
      rcases hAPmem u hu with he | he | he | he
      · exfalso
        obtain ⟨a, ha, hadj⟩ : ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj pm a := by
          rw [hpmeq]; exact (hp.2.2.2 (p.length - 1) hMlt).mpr (by omega)
        exact (SimpleGraph.compl_adj .. |>.mp (he ▸ hc a ha)).2 hadj
      · exfalso
        obtain ⟨a, ha, hadj⟩ := hxA t (by omega)
        exact (SimpleGraph.compl_adj .. |>.mp (he ▸ hc a ha)).2 hadj
      · exact he
      · exfalso
        obtain ⟨j, hj, hje⟩ := he
        obtain ⟨a, ha, hadj⟩ := hxA j (by omega)
        exact (SimpleGraph.compl_adj .. |>.mp (hje ▸ hc a ha)).2 hadj
    · rintro rfl
      intro a ha
      refine SimpleGraph.compl_adj .. |>.mpr ⟨fun he => hqmA1 (he ▸ ha), fun hadj => ?_⟩
      exact hqmno ⟨a, ha, hadj⟩
  -- `p_m` is the only vertex of the antipath anticomplete to `{z, x_{t+1}, p₁,…,p_{m−2}}`
  have hzYc : z ∈ Yc := by simp [hYcdef]
  have hxt1Yc : x (t + 1) ∈ Yc := by simp [hYcdef]
  have hYuniq : ∀ u ∈ (Q.reverse ++ [pm]), (VertexComplete Gᶜ u Yc ↔ u = pm) := by
    intro u hu
    constructor
    · intro hc
      rcases hAPmem u hu with he | he | he | he
      · exact he
      · exfalso
        exact (SimpleGraph.compl_adj .. |>.mp (he ▸ hc z hzYc)).2
          (hws.2.2.2.2.2.2 t (by omega)).symm
      · exfalso
        rcases Nat.eq_zero_or_pos n with hn0 | hn0
        · refine (SimpleGraph.compl_adj .. |>.mp (he ▸ hc (x (t + 1)) hxt1Yc)).2 ?_
          rw [← hlq]
          exact ((hxt1p l hl).mpr (by omega)).symm
        · have hprev : (p[l - 1]'(by omega)) ∈ p.take n := by
            have hlt : l - 1 < (p.take n).length := by
              simp only [List.length_take]; omega
            have hh := List.getElem_mem hlt
            rwa [List.getElem_take] at hh
          refine (SimpleGraph.compl_adj .. |>.mp
            (he ▸ hc (p[l - 1]'(by omega)) (by simp only [hYcdef]; exact Or.inr hprev))).2 ?_
          rw [← hlq]
          exact (hppath.2.2 l (l - 1) hl (by omega)).mpr (by omega)
      · exfalso
        obtain ⟨j, hj, hje⟩ := he
        exact (SimpleGraph.compl_adj .. |>.mp (hje ▸ hc z hzYc)).2
          (hws.2.2.2.2.2.2 j (by omega)).symm
    · rintro rfl
      intro w hw
      simp only [hYcdef, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff,
        Set.mem_setOf_eq] at hw
      rcases hw with (rfl | rfl) | hw
      · exact SimpleGraph.compl_adj .. |>.mpr
          ⟨fun he => hzAt (he ▸ hpmAt),
            fun hadj => WheelSystemBasics.wheelSystemA_no_nbr hpmAt hadj.symm⟩
      · refine SimpleGraph.compl_adj .. |>.mpr ⟨?_, ?_⟩
        · exact fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
            (he ▸ hpmAt)
        · rw [hpmeq]
          exact fun hadj => by
            have := (hxt1p (p.length - 1) hMlt).mp hadj.symm
            omega
      · obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
        simp only [List.length_take] at hj
        have hjp : j < p.length := by omega
        have hjw' : (p[j]'hjp) = w := by rw [← hjw, List.getElem_take]
        refine SimpleGraph.compl_adj .. |>.mpr ⟨?_, ?_⟩
        · rw [hpmeq, ← hjw']
          exact fun he => by have := hpnd.getElem_inj_iff.mp he; omega
        · rw [hpmeq, ← hjw']
          exact fun hadj => by
            have := (hppath.2.2 (p.length - 1) j hMlt hjp).mp hadj
            omega
  -- 13.7 applied in the complement
  have h137 := Workspace.Statements.S13.SPGT.thm_13_7 Gᶜ
    (ClassLemmas.inF5_compl.mpr hGF.1.1)
    (wheelSystemA G z A₀ x (t - 1)) Yc
    (by
      rw [Set.disjoint_left]
      intro a ha hw
      exact (hsep a ha a hw).1 rfl)
    hA1ne ⟨z, hzYc⟩
    (by
      show ConnectedSet (Gᶜ)ᶜ _
      rw [compl_compl]
      exact WheelSystemBasics.connectedSet_wheelSystemA hframe.1)
    (by
      show ConnectedSet (Gᶜ)ᶜ _
      rw [compl_compl]
      exact hYccon)
    (by
      intro a ha w hw
      exact SimpleGraph.compl_adj .. |>.mpr (hsep a ha w hw))
    (Q.reverse ++ [pm]) qm pm hAP.1
    (by
      obtain ⟨dd, hdd⟩ := hQodd
      exact ⟨dd + 1, by omega⟩)
    (by omega)
    hAP.2.1 hAP.2.2 hXuniq hYuniq
  omega

/-- The second case of the middle-vertex analysis in the proof of 21.2(5), printed p. 134.

PAPER: *"So `q ∈ A_{t−1}`, and in particular `x_t` is nonadjacent to `p_m, p_{m−1}`.  Let `R'`
be a path between `x_t, p_m` with interior in `{z, x_{t+1}, p₁,…,p_m}`; then
`x_t-R-p_m-R'-x_t` is a hole of length `≥ 6` sharing the vertices `x_t, q, p_m` with the
antihole `q-Q-x_t-p_m-z-q`, contrary to 15.7."*

Here `qm` is the paper's `q`, `pm` its `p_m`, and `Q` the odd antipath produced by 13.6.  The
companion case `q ∈ {p₁,…,p_m}` is discharged by `claim5_even_middle_in_path`.

Two remarks on the printed argument.  First, *"a hole of length ≥ 6"* is exactly *"`R'` has
length ≥ 3"*, and the only middle vertices a length-2 `R'` could have are `p_{m−1}` and
`x_{t+1}`.  The first is excluded by the printed remark *"and in particular `x_t` is
nonadjacent to `p_m, p_{m−1}`"*, which is proved here without circularity: `x_t ∼ p_{m−1}`
makes `z-x_t-p_{m−1}-p_m` an odd path whose ends are `X_{t−1}`-complete and whose internal
vertices are not, so 13.6 (`Thm212Claim5Antipath.exists_odd_antipath`) yields an odd antipath
between `x_t` and `p_{m−1}` with interior in `X_{t−1}`, and `claim5_even_middle_in_path`
applies to it.  Second, the vertex `x_{t+1}` is a possible middle vertex only when `m = 1` and
`x_t` is adjacent to `x_{t+1}`, which is why the hypothesis `hc2` — claim (2) of the printed
proof, available at this point of the paper — is needed: with `m = 1` the vertex `x_s` it
provides is nonadjacent to `p₁ = p_m`, which is `X_{t−1}`-complete, so `s = t` and
`x_t` is nonadjacent to `x_{t+1}`. -/
theorem claim5_even_middle_in_A_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V}
    (hp : GoodPath G z A₀ x t p) (hc2 : Claim2 G x t p) {pm qm : V} {Q : List V}
    (hpmlast : p.getLast? = some pm)
    (hpmc : VertexComplete G pm (wheelSystemX x (t - 1)))
    (hxtpm : ¬ G.Adj (x t) pm) (hpmqm : G.Adj pm qm)
    (hqmA : qm ∈ wheelSystemA G z A₀ x (t - 1))
    (hxtqm : G.Adj (x t) qm)
    (hqmnc : ¬ VertexComplete G qm (wheelSystemX x (t - 1)))
    (hQ : IsAntipathFrom G Q (x t) qm) (hQodd : Odd (pathLength Q))
    (hQ3 : 3 ≤ pathLength Q)
    (hQint : ∀ u ∈ SPGT.interior Q, u ∈ wheelSystemX x (t - 1)) : False := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  have hpne : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hMlt : p.length - 1 < p.length := by omega
  have hpmeq : pm = p[p.length - 1]'hMlt := by
    have hh := hpmlast
    rw [List.getLast?_eq_some_getLast hp.2.1, List.getLast_eq_getElem] at hh
    exact (Option.some.inj hh).symm
  have hppath : IsPathList G p := by
    have hh := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using hh
  have hpnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpA1 : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  have hxt1p : ∀ (j : ℕ) (hj : j < p.length), G.Adj (x (t + 1)) (p[j]'hj) ↔ j = 0 := by
    intro j hj
    have hh := hp.1.2.2 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
    have h0 : (x (t + 1) :: p)[0]'(by simp) = x (t + 1) := rfl
    have hj1 : (x (t + 1) :: p)[j + 1]'(by simp only [List.length_cons]; omega) = p[j]'hj := rfl
    rw [h0, hj1] at hh
    rw [hh]; omega
  -- basic facts about `z`, `x_t`, `x_{t+1}` and the sets `A`
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro u ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hzxt : G.Adj z (x t) := hws.2.2.2.2.2.2 t (by omega)
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hxtnc : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  have hpmA : pm ∈ wheelSystemA G z A₀ x t := hpmeq ▸ hpA _ (List.getElem_mem hMlt)
  have hqmAt : qm ∈ wheelSystemA G z A₀ x t :=
    WheelSystemBasics.wheelSystemA_mono (by omega) hqmA
  have hpmxt : pm ≠ x t :=
    fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (he ▸ hpmA)
  have hqmxt : qm ≠ x t :=
    fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (he ▸ hqmAt)
  have hpmqmne : pm ≠ qm := fun he => hqmnc (he ▸ hpmc)
  have hzpm : ¬ G.Adj z pm := WheelSystemBasics.wheelSystemA_no_nbr hpmA
  have hzqm : ¬ G.Adj z qm := WheelSystemBasics.wheelSystemA_no_nbr hqmAt
  have hzp : ∀ v ∈ p, ¬ G.Adj z v := fun v hv => WheelSystemBasics.wheelSystemA_no_nbr (hpA v hv)
  have hzAt : z ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
  have hznep : ∀ v ∈ p, z ≠ v := fun v hv he => hzAt (he ▸ hpA v hv)
  have hxt1nep : ∀ v ∈ p, x (t + 1) ≠ v :=
    fun v hv he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl (he ▸ hpA v hv)
  -- `x_t` is nonadjacent to `p_{m-1}` (printed: "in particular `x_t` is nonadjacent to
  -- `p_m, p_{m−1}`"), by the same 13.6 step applied to the path `z-x_t-p_{m−1}-p_m`
  have hprev : ∀ (j : ℕ) (hj : j < p.length), j + 2 = p.length → ¬ G.Adj (x t) (p[j]'hj) := by
    intro j hj hjlen hcon
    have hjmem : (p[j]'hj) ∈ p := List.getElem_mem hj
    have hjA : (p[j]'hj) ∈ wheelSystemA G z A₀ x t := hpA _ hjmem
    have hbc : G.Adj (p[j]'hj) pm := by
      rw [hpmeq]
      exact (hppath.2.2 j (p.length - 1) hj hMlt).mpr (by omega)
    have hbX : ¬ VertexComplete G (p[j]'hj) (wheelSystemX x (t - 1)) := by
      intro hcomp
      refine WheelSystemBasics.wheelSystemA_no_complete hjA ?_
      rintro u ⟨k, hk, rfl⟩
      rcases Nat.lt_or_ge k t with hkt | hkt
      · exact hcomp (x k) ⟨k, by omega, rfl⟩
      · have : k = t := by omega
        rw [this]; exact hcon.symm
    obtain ⟨Q', hQ', hQ'odd, hQ'3, hQ'int⟩ :=
      Thm212Claim5Antipath.exists_odd_antipath (G := G) hGF.1.1
        (Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega))
        hzxt hcon hbc hxtpm (hzp _ hjmem) hzpm (hznep _ hjmem)
        (fun he => hzAt (he ▸ hpmA)) (fun he => hpmxt he.symm) hzX hpmc hxtnc hbX
        (by rintro ⟨k, hk, he⟩; exact (hws.2.2.1 k (by omega)).2 he.symm)
        (by rintro ⟨k, hk, he⟩; exact absurd (hws.2.1 k (by omega) t (by omega) he.symm) (by omega))
        (by rintro ⟨k, hk, he⟩
            exact Thm203Prelim.x_notMem_wheelSystemA hws (j := k) (by omega) (he ▸ hjA))
        (by rintro ⟨k, hk, he⟩
            exact Thm203Prelim.x_notMem_wheelSystemA hws (j := k) (by omega) (he ▸ hpmA))
    exact claim5_even_middle_in_path h hp hpmlast hpmc hxtpm hbc.symm hjmem hcon hbX
      hQ' hQ'odd hQ'3 hQ'int
  -- when `m = 1`, claim (2) forces the vertex `x_s` it produces to be `x_t`
  have hnotxt1 : p.length = 1 → ¬ G.Adj (x t) (x (t + 1)) := by
    intro hlen1 hadj
    obtain ⟨s, hst, hsx, p₁, hp₁, hsp₁⟩ := hc2
    have hhead : p.head? = some (p[0]'hpne) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpne]
    have hp₁eq : p₁ = pm := by
      rw [hhead] at hp₁
      have h0 : (p[0]'hpne) = pm := by
        rw [hpmeq]
        exact HoleArithmetic.getElem_congr_idx p hpne hMlt (by omega)
      rw [← h0]
      exact (Option.some.inj hp₁).symm
    rw [hp₁eq] at hsp₁
    have hs : s = t := by
      by_contra hsne
      exact hsp₁ (hpmc (x s) ⟨s, by omega, rfl⟩).symm
    rw [hs] at hsx
    exact hsx hadj
  -- the printed path `R'` between `x_t` and `p_m` with interior in `{z, x_{t+1}, p₁,…,p_m}`
  have hSp : ConnectedSet G {v : V | v ∈ p} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hppath
  have hS1 : ConnectedSet G ({v : V | v ∈ p} ∪ {x (t + 1)}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hSp
      ⟨p[0]'hpne, List.getElem_mem hpne, (hxt1p 0 hpne).mpr rfl⟩
  have hS2 : ConnectedSet G (({v : V | v ∈ p} ∪ {x (t + 1)}) ∪ {z}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hS1 ⟨x (t + 1), Or.inr rfl, hzxt1⟩
  have hS3 : ConnectedSet G ((({v : V | v ∈ p} ∪ {x (t + 1)}) ∪ {z}) ∪ {x t}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hS2 ⟨z, Or.inr rfl, hzxt.symm⟩
  obtain ⟨R, hR, hRS⟩ := InducedPathExtraction.exists_isPathFrom_of_connected hS3
    (Or.inr rfl) (Or.inl (Or.inl (Or.inl (show pm ∈ p from hpmeq ▸ List.getElem_mem hMlt))))
  have hRmem : ∀ w ∈ R, w = x t ∨ w = z ∨ w = x (t + 1) ∨ w ∈ p := by
    intro w hw
    have := hRS w hw
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq] at this
    tauto
  have hRpos : 0 < R.length := PathBasics.path_length_pos hR.1
  have hRlt : R.length - 1 < R.length := by omega
  have hR0 : R[0]'hRpos = x t := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hRlast : R[R.length - 1]'hRlt = pm := PathBasics.getElem_last_of_getLast? hR.2.2 hRpos
  have hRnd : R.Nodup := PathBasics.path_nodup hR.1
  -- `q` has no neighbour on `R'` except its two ends
  have hqmadj : ∀ w ∈ R, (G.Adj qm w ↔ (w = x t ∨ w = pm)) := by
    intro w hw
    constructor
    · intro hadj
      rcases hRmem w hw with he | he | he | he
      · exact Or.inl he
      · exact absurd (he ▸ hadj) (fun hc => hzqm hc.symm)
      · exact absurd (he ▸ hadj) (fun hc => hxt1A qm hqmA hc.symm)
      · obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem he
        have hjA : (j + 1 = p.length) := (hp.2.2.2 j hj).mp ⟨qm, hqmA, by rw [hjw]; exact hadj.symm⟩
        refine Or.inr ?_
        rw [← hjw, hpmeq, HoleArithmetic.getElem_congr_idx p hj hMlt (by omega)]
    · rintro (rfl | rfl)
      · exact hxtqm.symm
      · exact hpmqm.symm
  have hqmR : qm ∉ R := by
    intro hmem
    rcases hRmem qm hmem with he | he | he | he
    · exact hqmxt he
    · exact hzAt (he ▸ hqmAt)
    · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl (he ▸ hqmAt)
    · exact hpA1 qm he hqmA
  -- `R'` has length ≥ 3, so the hole below has length ≥ 5, hence ≥ 6
  have hRlen4 : 4 ≤ R.length := by
    by_contra hcon
    have hcases : R.length = 1 ∨ R.length = 2 ∨ R.length = 3 := by omega
    rcases hcases with hn | hn | hn
    · refine hpmxt ?_
      rw [← hRlast, HoleArithmetic.getElem_congr_idx R hRlt hRpos (by omega), hR0]
    · refine hxtpm ?_
      have hadj := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
      rw [hR0] at hadj
      rw [← hRlast, HoleArithmetic.getElem_congr_idx R hRlt
        (show 0 + 1 < R.length by omega) (by omega)]
      exact hadj
    · have h1lt : 1 < R.length := by omega
      have hadj1 : G.Adj (x t) (R[1]'h1lt) := by
        have hadj := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
        rw [hR0, HoleArithmetic.getElem_congr_idx R (show 0 + 1 < R.length by omega) h1lt rfl]
          at hadj
        exact hadj
      have hadj2 : G.Adj (R[1]'h1lt) pm := by
        have hadj := PathBasics.path_adj_succ hR.1 (i := 1) (by omega)
        rw [HoleArithmetic.getElem_congr_idx R (show 1 + 1 < R.length by omega) hRlt (by omega),
          hRlast] at hadj
        exact hadj
      rcases hRmem _ (List.getElem_mem h1lt) with he | he | he | he
      · have hcon2 : (R[0]'hRpos) = (R[1]'h1lt) := by rw [hR0, he]
        have := hRnd.getElem_inj_iff.mp hcon2
        omega
      · exact hzpm (he ▸ hadj2)
      · rw [he] at hadj1 hadj2
        have hidx := (hxt1p (p.length - 1) hMlt).mp (by rw [← hpmeq]; exact hadj2)
        exact hnotxt1 (by omega) hadj1
      · obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem he
        rw [← hjw] at hadj1 hadj2
        have hje : j + 2 = p.length := by
          have := (hppath.2.2 j (p.length - 1) hj hMlt).mp (by rw [← hpmeq]; exact hadj2)
          omega
        exact hprev j hj hje hadj1
  -- the hole `x_t-q-p_m-R'-x_t`
  have hsing : IsPathFrom G [qm] qm qm := ⟨PathBasics.isPathList_singleton G qm, rfl, rfl⟩
  have hhole : IsHoleList G ([qm] ++ R) := by
    refine PathGlue.glue_hole hsing hR (by
      intro w hw
      rw [List.mem_singleton] at hw
      exact hw ▸ hqmR) ?_ (by simp only [List.length_singleton]; omega)
    intro w hw y hy
    rw [List.mem_singleton] at hw
    subst hw
    rw [hqmadj y hy]
    tauto
  -- the antihole `q-Q-x_t-p_m-z-q`
  have hQmem : ∀ w ∈ Q, w = x t ∨ w = qm ∨ w ∈ wheelSystemX x (t - 1) := by
    intro w hw
    rcases eq_or_ne w (x t) with he | hwa
    · exact Or.inl he
    rcases eq_or_ne w qm with he | hwb
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr (hQint w
        ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, hwa, hwb⟩)))
  have hpmQ : pm ∉ Q := by
    intro hmem
    rcases hQmem _ hmem with he | he | he
    · exact hpmxt he
    · exact hpmqmne he
    · obtain ⟨j, hj, hje⟩ := he
      exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hje ▸ hpmA)
  have hQrev : IsAntipathFrom G Q.reverse qm (x t) := PathBasics.isAntipathFrom_reverse hQ
  have hAP : IsPathFrom Gᶜ (Q.reverse ++ [pm]) qm pm := by
    refine PathAttach.isPathFrom_concat hQrev
      (SimpleGraph.compl_adj .. |>.mpr ⟨hpmxt, fun hc => hxtpm hc.symm⟩)
      (by simpa using hpmQ) ?_
    intro w hw hwne
    have hw' : w ∈ Q := List.mem_reverse.mp hw
    rcases hQmem w hw' with he | he | he
    · exact absurd he hwne
    · exact fun hc => (SimpleGraph.compl_adj .. |>.mp hc).2 (he ▸ hpmqm)
    · obtain ⟨j, hj, hje⟩ := he
      exact fun hc => (SimpleGraph.compl_adj .. |>.mp hc).2 (hje ▸ hpmc (x j) ⟨j, hj, rfl⟩)
  have hzsing : IsPathFrom Gᶜ [z] z z := ⟨PathBasics.isPathList_singleton Gᶜ z, rfl, rfl⟩
  have hzR : z ∉ (Q.reverse ++ [pm]) := by
    intro hmem
    rcases List.mem_append.mp hmem with hw | hw
    · rcases hQmem z (List.mem_reverse.mp hw) with he | he | he
      · exact (hws.2.2.1 t (by omega)).2 he.symm
      · exact hzAt (he ▸ hqmAt)
      · obtain ⟨j, hj, hje⟩ := he
        exact (hws.2.2.1 j (by omega)).2 hje.symm
    · exact hzAt ((by simpa using hw : z = pm) ▸ hpmA)
  have hanti : IsHoleList Gᶜ ([z] ++ (Q.reverse ++ [pm])) := by
    refine PathGlue.glue_hole hzsing hAP (by
      intro w hw
      rw [List.mem_singleton] at hw
      exact hw ▸ hzR) ?_ ?_
    · intro w hw y hy
      rw [List.mem_singleton] at hw
      subst hw
      constructor
      · intro hadj
        rcases List.mem_append.mp hy with hw | hw
        · rcases hQmem y (List.mem_reverse.mp hw) with he | he | he
          · exact absurd (he ▸ (SimpleGraph.compl_adj .. |>.mp hadj).2) (fun hc => hc hzxt)
          · exact Or.inl ⟨rfl, he⟩
          · obtain ⟨j, hj, hje⟩ := he
            exact absurd (SimpleGraph.compl_adj .. |>.mp hadj).2
              (fun hc => hc (hje ▸ hws.2.2.2.2.2.2 j (by omega)))
        · exact Or.inr ⟨rfl, by simpa using hw⟩
      · rintro (⟨-, rfl⟩ | ⟨-, rfl⟩)
        · exact SimpleGraph.compl_adj .. |>.mpr ⟨fun he => hzAt (he ▸ hqmAt), hzqm⟩
        · exact SimpleGraph.compl_adj .. |>.mpr ⟨fun he => hzAt (he ▸ hpmA), hzpm⟩
    · have hQlen : 0 < Q.length := PathBasics.path_length_pos hQ.1
      have := PathBasics.pathLength_eq Q
      simp only [List.length_singleton, List.length_append, List.length_reverse]
      omega
  -- 15.7
  have h157 := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hGF.1
    ([qm] ++ R) ([z] ++ (Q.reverse ++ [pm])) hhole
    (by simp only [holeLength, List.length_append, List.length_singleton]; omega)
    hanti
    (by
      have := PathBasics.pathLength_eq Q
      simp only [holeLength, List.length_append, List.length_singleton, List.length_reverse]
      omega)
  have hxtR : x t ∈ R := by rw [← hR0]; exact List.getElem_mem hRpos
  have hpmR : pm ∈ R := by rw [← hRlast]; exact List.getElem_mem hRlt
  have hxtQ : x t ∈ Q := PathBasics.head_mem hQ.2.1
  have hqmQ : qm ∈ Q := PathBasics.getLast_mem hQ.2.2
  have hsub3 : ({x t, qm, pm} : Set V) ⊆
      ({w : V | w ∈ ([qm] ++ R)} ∩ {w : V | w ∈ ([z] ++ (Q.reverse ++ [pm]))}) := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    refine ⟨?_, ?_⟩ <;> simp only [Set.mem_setOf_eq, List.mem_append, List.mem_singleton,
      List.mem_reverse] <;> rcases hw with rfl | rfl | rfl
    · exact Or.inr hxtR
    · exact Or.inl rfl
    · exact Or.inr hpmR
    · exact Or.inr (Or.inl hxtQ)
    · exact Or.inr (Or.inl hqmQ)
    · exact Or.inr (Or.inr rfl)
  have hcard3 : ({x t, qm, pm} : Set V).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨x t, qm, pm, Ne.symm hqmxt, Ne.symm hpmxt, Ne.symm hpmqmne, rfl⟩
  have := Set.ncard_le_ncard hsub3 (Set.toFinite _)
  omega

/-- Labelled gap for the parity assertion of 21.2(5), pp. 133–134.

PAPER: *"Let `R` be a path from `x_t` to some vertex `r`, such that `r` is the unique
`X_{t−1}`-complete vertex in `R`, and `V(R \ x_t) ⊆ A_{t−1} ∪ {p₁,…,p_m}`.  Then `R` is odd
… For assume that `R` is even.  Then the path `z-x_t-R-r` is odd, and its ends are
`X_{t−1}`-complete, and its internal vertices are not, so by 13.6, it has length 3, that is,
`R` has length 2.  Let `q` be the middle vertex of `R`. … Suppose first that
`q ∈ {p₁,…,p_m}`; then it follows that `q = p_{m−1}` … contradicts 13.7 applied in the
complement.  So `q ∈ A_{t−1}` … contrary to 15.7.  So `R` is odd."* -/
theorem claim5_odd_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V}
    (hp : GoodPath G z A₀ x t p) (hc2 : Claim2 G x t p) {R : List V} {r : V}
    (hR : IsPathFrom G R (x t) r)
    (huniq : ∀ v ∈ R, VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = r)
    (hin : ∀ v ∈ R, v ≠ x t → v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p) :
    Odd (pathLength R) := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  by_contra hnodd
  have heven : Even (pathLength R) := Nat.not_odd_iff_even.mp hnodd
  have hpne : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hMlt : p.length - 1 < p.length := by omega
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hRA : ∀ v ∈ R, v ≠ x t → v ∈ wheelSystemA G z A₀ x t := by
    intro v hv hvne
    rcases hin v hv hvne with hh | hh
    · exact WheelSystemBasics.wheelSystemA_mono (by omega) hh
    · exact hpA v hh
  have hxtnc : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  have hRpath := hR.1
  have hRpos : 0 < R.length := PathBasics.path_length_pos hRpath
  have hR0 : R[0]'hRpos = x t := PathBasics.getElem_zero_of_head? hR.2.1 hRpos
  have hxtmem : x t ∈ R := PathBasics.head_mem hR.2.1
  have hrmem : r ∈ R := PathBasics.getLast_mem hR.2.2
  have hrc : VertexComplete G r (wheelSystemX x (t - 1)) := (huniq r hrmem).mpr rfl
  have hrne : r ≠ x t := fun he => hxtnc (he ▸ hrc)
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro u ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hzadj : ∀ v ∈ R, v ≠ x t → ¬ G.Adj z v :=
    fun v hv hne => WheelSystemBasics.wheelSystemA_no_nbr (hRA v hv hne)
  have hznR : z ∉ R := by
    intro hz
    rcases eq_or_ne z (x t) with he | hne
    · exact (hws.2.2.1 t (by omega)).2 he.symm
    · exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) (hRA z hz hne)
  have hzxt : G.Adj z (x t) := hws.2.2.2.2.2.2 t (by omega)
  have hL : IsPathFrom G (z :: R) z r :=
    PathAttach.isPathFrom_cons hR hzxt hznR (fun v hv hne => hzadj v hv hne)
  have hLlen : pathLength (z :: R) = pathLength R + 1 := by
    rw [PathBasics.pathLength_cons, PathBasics.pathLength_eq]; omega
  have hLodd : Odd (pathLength (z :: R)) := by
    obtain ⟨d, hd⟩ := heven; exact ⟨d, by omega⟩
  have hXP : wheelSystemX x (t - 1) ⊆ {v : V | v ∈ (z :: R)}ᶜ := by
    rintro u ⟨j, hj, rfl⟩ hmem
    simp only [Set.mem_setOf_eq] at hmem
    rcases List.mem_cons.mp hmem with he | hmem
    · exact (hws.2.2.1 j (by omega)).2 he
    · rcases eq_or_ne (x j) (x t) with he | hne
      · have := hws.2.1 j (by omega) t (by omega) he; omega
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hRA _ hmem hne)
  have h136 := Workspace.Statements.S13.SPGT.thm_13_6 G hGF.1.1 (z :: R) z r hL hLodd
    (wheelSystemX x (t - 1)) hXP
    (Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega)) hzX hrc
  rcases h136 with ⟨u, hu, v, hv, hedge⟩ | ⟨h3, c, d, hcd, Q, hQ, hQodd, hQint⟩
  · have hcomp : ∀ w ∈ (z :: R), VertexComplete G w (wheelSystemX x (t - 1)) →
        w = z ∨ w = r := by
      intro w hw hwc
      rcases List.mem_cons.mp hw with he | hw
      · exact Or.inl he
      · exact Or.inr ((huniq w hw).mp hwc)
    have hzr : ¬ G.Adj z r := hzadj r hrmem hrne
    rcases hcomp u hu hedge.2.1 with rfl | rfl <;> rcases hcomp v hv hedge.2.2 with he | he
    · exact G.irrefl (he ▸ hedge.1)
    · exact hzr (he ▸ hedge.1)
    · exact hzr (he ▸ hedge.1).symm
    · exact G.irrefl (he ▸ hedge.1)
  · -- `pathLength (z :: R) = 3`, so `R = [x t, qm, r]`
    have hRlen : R.length = 3 := by
      rw [hLlen] at h3
      have := PathBasics.pathLength_eq R
      omega
    obtain ⟨a, b, e, rfl⟩ : ∃ a b e, R = [a, b, e] := List.length_eq_three.mp hRlen
    have hax : a = x t := by simpa using hR0
    have hint : SPGT.interior (z :: [a, b, e]) = [a, b] := rfl
    rw [hint] at hcd
    have hca : c = a := by injection hcd with h1 h2; exact h1.symm
    have hdb : d = b := by
      injection hcd with h1 h2; injection h2 with h3 h4; exact h3.symm
    rw [hca, hdb] at hQ
    have hnd : ([a, b, e] : List V).Nodup := PathBasics.path_nodup hRpath
    have hab : a ≠ b := by simp at hnd; tauto
    have hbe : b ≠ e := by simp at hnd; tauto
    have hre : r = e := by
      have := PathBasics.getElem_last_of_getLast? hR.2.2
        (show 0 < ([a, b, e] : List V).length by simp)
      simpa using this.symm
    have hbmem : b ∈ ([a, b, e] : List V) := by simp
    have hqmnc : ¬ VertexComplete G b (wheelSystemX x (t - 1)) := by
      intro hc
      exact hbe (by rw [(huniq b hbmem).mp hc, hre])
    have hxtqm : G.Adj a b := by
      have := PathBasics.path_adj_succ hRpath (i := 0) (by simp)
      simpa using this
    -- `Q` has length `≥ 3`
    have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
    have hQ3 : 3 ≤ pathLength Q := by
      obtain ⟨dd, hdd⟩ := hQodd
      by_contra hcon
      have hQ2 : Q.length = 2 := by
        have := PathBasics.pathLength_eq Q
        omega
      have hd0 : Q[0]'(by omega) = a := PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
      have hd1 : Q[1]'(by omega) = b := by
        have hh := PathBasics.getElem_last_of_getLast? hQ.2.2 (show 0 < Q.length by omega)
        rw [HoleArithmetic.getElem_congr_idx Q (show 1 < Q.length by omega)
          (show Q.length - 1 < Q.length by omega) (by omega)]
        exact hh
      have hadjc := PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
      rw [hd0, HoleArithmetic.getElem_congr_idx Q (show 0 + 1 < Q.length by omega)
        (show 1 < Q.length by omega) rfl, hd1] at hadjc
      exact (SimpleGraph.compl_adj .. |>.mp hadjc).2 hxtqm
    -- `p_m` and its properties
    have hMlt' : p.length - 1 < p.length := hMlt
    have hpmA : (p[p.length - 1]'hMlt) ∈ wheelSystemA G z A₀ x t := hpA _ (List.getElem_mem hMlt)
    have hpmc : VertexComplete G (p[p.length - 1]'hMlt) (wheelSystemX x (t - 1)) :=
      Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (i := t - 1) (by omega)
        (WheelSystemBasics.wheelSystemA_no_nbr hpmA)
        (hp.2.2.1 _ (List.getElem_mem hMlt)).2
        ((hp.2.2.2 (p.length - 1) hMlt).mpr (by omega))
    have hxtpm : ¬ G.Adj a (p[p.length - 1]'hMlt) := by
      intro hadj
      refine WheelSystemBasics.wheelSystemA_no_complete hpmA ?_
      rintro u ⟨j, hj, rfl⟩
      rcases Nat.lt_or_ge j t with hjt | hjt
      · exact hpmc (x j) ⟨j, by omega, rfl⟩
      · have hjt' : j = t := by omega
        rw [hjt', ← hax]; exact hadj.symm
    have hplast : p.getLast? = some (p[p.length - 1]'hMlt) := by
      rw [List.getLast?_eq_some_getLast hp.2.1, List.getLast_eq_getElem]
    -- `p_m` is adjacent to `q`
    have hpmb : G.Adj (p[p.length - 1]'hMlt) b := by
      by_contra hnadj
      have hpmne_a : (p[p.length - 1]'hMlt) ≠ a :=
        fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
          (show x t ∈ wheelSystemA G z A₀ x t by rw [← hax, ← he]; exact hpmA)
      have hpmne_b : (p[p.length - 1]'hMlt) ≠ b := fun he => hqmnc (he ▸ hpmc)
      have hQmem : ∀ w ∈ Q, w = a ∨ w = b ∨ w ∈ wheelSystemX x (t - 1) := by
        intro w hw
        rcases eq_or_ne w a with he | hwa
        · exact Or.inl he
        rcases eq_or_ne w b with he | hwb
        · exact Or.inr (Or.inl he)
        · exact Or.inr (Or.inr (hQint w
            ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hw, hwa, hwb⟩)))
      have hpmQ : (p[p.length - 1]'hMlt) ∉ Q := by
        intro hmem
        rcases hQmem _ hmem with he | he | he
        · exact hpmne_a he
        · exact hpmne_b he
        · obtain ⟨j, hj, hje⟩ := he
          exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hje ▸ hpmA)
      have hsing : IsPathFrom Gᶜ [p[p.length - 1]'hMlt] (p[p.length - 1]'hMlt)
          (p[p.length - 1]'hMlt) := ⟨PathBasics.isPathList_singleton _ _, rfl, rfl⟩
      have hcross : ∀ w ∈ ([p[p.length - 1]'hMlt] : List V), ∀ v ∈ Q,
          (Gᶜ.Adj w v ↔ (w = (p[p.length - 1]'hMlt) ∧ v = a) ∨
            (w = (p[p.length - 1]'hMlt) ∧ v = b)) := by
        intro w hw v hv
        rw [List.mem_singleton] at hw
        subst hw
        constructor
        · intro hadj
          rcases hQmem v hv with he | he | he
          · exact Or.inl ⟨rfl, he⟩
          · exact Or.inr ⟨rfl, he⟩
          · exfalso
            obtain ⟨j, hj, hje⟩ := he
            exact (SimpleGraph.compl_adj .. |>.mp hadj).2 (hje ▸ hpmc (x j) ⟨j, hj, rfl⟩)
        · rintro (⟨-, rfl⟩ | ⟨-, rfl⟩)
          · exact SimpleGraph.compl_adj .. |>.mpr ⟨hpmne_a, fun hc => hxtpm hc.symm⟩
          · exact SimpleGraph.compl_adj .. |>.mpr ⟨hpmne_b, hnadj⟩
      have hhole : IsHoleList Gᶜ ([p[p.length - 1]'hMlt] ++ Q) :=
        PathGlue.glue_hole hsing hQ (by
          intro w hw
          rw [List.mem_singleton] at hw
          exact hw ▸ hpmQ) hcross (by
          have := PathBasics.pathLength_eq Q
          simp only [List.length_singleton]
          omega)
      obtain ⟨w2, hw2⟩ := hBerge.2 _ hhole
      simp only [holeLength, List.length_append, List.length_singleton] at hw2
      obtain ⟨dd, hdd⟩ := hQodd
      have hql := PathBasics.pathLength_eq Q
      omega
    rw [hax] at hxtqm hxtpm hQ
    rcases hin b hbmem (fun he => hab (by rw [hax, he])) with hbA | hbp
    · exact claim5_even_middle_in_A_gap h hp hc2 hplast hpmc hxtpm hpmb hbA hxtqm hqmnc hQ hQodd
        hQ3 hQint
    · exact claim5_even_middle_in_path h hp hplast hpmc hxtpm hpmb hbp hxtqm hqmnc hQ hQodd hQ3 hQint

/-- Labelled gap for 21.2(5), pp. 133–134.
PAPER: "Then `R` is odd, and has length ≥ 3." The argument uses 13.6,
13.7 in the complement, and the hole–antihole intersection bound 15.7. -/
theorem endgame_claim5_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V}
    (hp : GoodPath G z A₀ x t p) (hc2 : Claim2 G x t p) :
    OddReturnPaths G z A₀ x t p := by
  intro R r hR huniq hin
  have hodd := claim5_odd_gap h hp hc2 hR huniq hin
  refine ⟨hodd, ?_⟩
  obtain ⟨hG, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  by_contra hlt
  have hlen1 : pathLength R = 1 := by
    obtain ⟨d, hd⟩ := hodd
    omega
  have hRlen : R.length = 2 := by
    have := PathBasics.pathLength_eq R
    omega
  have hR0 : R[0]'(by omega) = x t := PathBasics.getElem_zero_of_head? hR.2.1 (by omega)
  have hR1 : R[1]'(by omega) = r := by
    have := PathBasics.getElem_last_of_getLast? hR.2.2 (show 0 < R.length by omega)
    simpa only [hRlen] using this
  have hrne : r ≠ x t := by
    rw [← hR0, ← hR1]
    exact fun he => by simpa using (PathBasics.path_nodup hR.1).getElem_inj_iff.mp he
  have hrmem : r ∈ R := PathBasics.getLast_mem hR.2.2
  have hrc : VertexComplete G r (wheelSystemX x (t - 1)) := (huniq r hrmem).mpr rfl
  have hadj : G.Adj (x t) r := by
    have := PathBasics.path_adj_succ hR.1 (i := 0) (by omega)
    simpa only [hR0, hR1] using this
  have hrct : VertexComplete G r (wheelSystemX x t) := by
    rintro w ⟨j, hj, rfl⟩
    by_cases hjt : j = t
    · exact (hjt ▸ hadj).symm
    · exact hrc (x j) ⟨j, by omega, rfl⟩
  rcases hin r hrmem hrne with hrA | hrp
  · exact WheelSystemBasics.wheelSystemA_no_complete hrA hrc
  · exact WheelSystemBasics.wheelSystemA_no_complete (hp.2.2.1 r hrp).1 hrct

/-- Labelled gap for the last part of 21.2(6), printed p. 134.

PAPER: *"Now assume that `x_{t+1}` is `X_{t−1}`-complete.  Since `x_{t+1}` is nonadjacent to
`x_s` it follows `s = t`.  Let `R` be a path between `x_t, p_m` with interior in `A_{t−1}`.
By (5), `R` is odd, and so the path `x_{t+1}-p₁-⋯-p_i-x_t-R-p_m` is odd, of length `≥ 5`, its
ends are `X_{t−1}`-complete, and its internal vertices are not, contrary to 13.6."*

`hnone` is the first half of (6), already proved: none of `p₁,…,p_{i−1}` (the entries
`q[l]` with `l + 2 ≤ i`) is `X_{t−1}`-complete. -/
theorem claim6_hub_not_complete_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ}
    (hp : GoodPath G z A₀ x t p) (hext : Extended G z A₀ x t p q i s)
    (hip : i ≤ p.length)
    (hnone : ∀ l, l + 2 ≤ i → ∀ hl : l < q.length,
      ¬ VertexComplete G q[l] (wheelSystemX x (t - 1)))
    (hc5 : OddReturnPaths G z A₀ x t p) :
    ¬ VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)) := by
  classical
  intro hxc
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  obtain ⟨hpref, hq, hqAt, hcov, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  have hiodd : Odd i := extended_index_odd h hext
  have hi3 : 3 ≤ i := by obtain ⟨d, hd⟩ := hiodd; omega
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hppath : IsPathList G p := by
    have := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using this
  have hnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpnotA : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  have hpq : p.length ≤ q.length := hpref.length_le
  have hqp : ∀ (l : ℕ) (hl : l < p.length), q[l]'(by omega) = p[l]'hl := fun l hl =>
    (hpref.getElem hl).symm
  have hxtnotp : x t ∉ p := fun hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (hpA _ hm)
  have hxt1notp : x (t + 1) ∉ p := by
    have := PathBasics.path_nodup hp.1
    exact (List.nodup_cons.mp this).1
  have hxtnotX : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  -- `s = t`
  have hi1q : i - 1 < q.length := by omega
  have hwhole : i < (x (t + 1) :: q).length := by simp; omega
  have helem : (x (t + 1) :: q)[i] = q[i - 1] := by
    cases i with
    | zero => omega
    | succ i => rfl
  have hspi : G.Adj (x s) q[i - 1] := by
    obtain ⟨w, hw, hsw⟩ := hcover s hst
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact (hsnone w hw hsw).elim
    · have he : w = (x (t + 1) :: q)[i] := by simpa using hw
      simpa only [he, helem] using hsw
  have hsplit : (x (t + 1) :: q).take i = x (t + 1) :: q.take (i - 1) := by
    obtain ⟨i', hi'⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    subst hi'; simp
  have hxt1take : x (t + 1) ∈ (x (t + 1) :: q).take i := by
    rw [hsplit]; exact List.mem_cons_self ..
  have hmemtake : ∀ l, l + 2 ≤ i → ∀ hl : l < q.length, q[l] ∈ (x (t + 1) :: q).take i := by
    intro l hli hl
    rw [hsplit]
    refine List.mem_cons_of_mem _ ?_
    have hlen : l < (q.take (i - 1)).length := by simp only [List.length_take]; omega
    have := List.getElem_mem hlen
    rwa [List.getElem_take] at this
  have hsteq : s = t := by
    by_contra hne
    exact hsnone _ hxt1take (hxc (x s) ⟨s, by omega, rfl⟩).symm
  rw [hsteq] at hsnone hspi
  -- `p_i` is not `X_{t-1}`-complete
  have hinotX : ¬ VertexComplete G q[i - 1] (wheelSystemX x (t - 1)) := by
    intro hcon
    refine WheelSystemBasics.wheelSystemA_no_complete
      (hqAt q[i - 1] (List.getElem_mem hi1q)) ?_
    rintro w ⟨j, hj, rfl⟩
    by_cases hjs : j = t
    · exact (hjs ▸ hspi).symm
    · exact hcon (x j) ⟨j, by omega, rfl⟩
  have hi1p : i - 1 < p.length := by omega
  have hinotX' : ¬ VertexComplete G (p[i - 1]'hi1p) (wheelSystemX x (t - 1)) := by
    rw [← hqp (i - 1) hi1p]; exact hinotX
  have hspi' : G.Adj (x t) (p[i - 1]'hi1p) := by rw [← hqp (i - 1) hi1p]; exact hspi
  -- `p_m` is `X_{t-1}`-complete
  have hMp : p.length - 1 < p.length := by omega
  have hpmc : VertexComplete G (p[p.length - 1]'hMp) (wheelSystemX x (t - 1)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (i := t - 1) (by omega)
      (WheelSystemBasics.wheelSystemA_no_nbr (hpA _ (List.getElem_mem hMp)))
      (hpnotA _ (List.getElem_mem hMp))
      ((hp.2.2.2 (p.length - 1) hMp).mpr (by omega))
  -- (5) forbids short returns to `p_m`
  have hnadjm : ∀ (l : ℕ) (hl : l < p.length),
      (¬ VertexComplete G (p[l]'hl) (wheelSystemX x (t - 1))) → l ≠ p.length - 1 →
      G.Adj (x t) (p[l]'hl) → G.Adj (p[l]'hl) (p[p.length - 1]'hMp) → False := by
    intro l hl hlc hlne hadj hadj2
    have hpair : IsPathFrom G [p[l]'hl, p[p.length - 1]'hMp] (p[l]'hl) (p[p.length - 1]'hMp) :=
      ⟨PathBasics.isPathList_pair hadj2, rfl, rfl⟩
    have hnotmem : x t ∉ [p[l]'hl, p[p.length - 1]'hMp] := by
      intro hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with he | he
      · exact hxtnotp (he ▸ List.getElem_mem hl)
      · exact hxtnotp (he ▸ List.getElem_mem hMp)
    have htri : IsPathFrom G [x t, p[l]'hl, p[p.length - 1]'hMp] (x t)
        (p[p.length - 1]'hMp) := by
      refine PathAttach.isPathFrom_cons hpair hadj hnotmem ?_
      intro w hw hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with he | he
      · exact (hne he).elim
      · subst he
        intro hcon
        -- `x_t` adjacent to `p_m` contradicts (5)
        have hpair2 : IsPathFrom G [x t, p[p.length - 1]'hMp] (x t) (p[p.length - 1]'hMp) :=
          ⟨PathBasics.isPathList_pair hcon, rfl, rfl⟩
        have hu2 : ∀ v ∈ [x t, p[p.length - 1]'hMp],
            VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = p[p.length - 1]'hMp := by
          intro v hv
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · refine ⟨fun hc => (hxtnotX hc).elim, fun he => ?_⟩
            exact absurd (he ▸ List.getElem_mem hMp) hxtnotp
          · exact ⟨fun _ => rfl, fun _ => hpmc⟩
        have hin2 : ∀ v ∈ [x t, p[p.length - 1]'hMp], v ≠ x t →
            v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
          intro v hv hne
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl
          · exact (hne rfl).elim
          · exact Or.inr (List.getElem_mem hMp)
        have := (hc5 _ _ hpair2 hu2 hin2).2
        norm_num [pathLength] at this
    have hu : ∀ v ∈ [x t, p[l]'hl, p[p.length - 1]'hMp],
        VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = p[p.length - 1]'hMp := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · refine ⟨fun hc => (hxtnotX hc).elim, fun he => ?_⟩
        exact absurd (he ▸ List.getElem_mem hMp) hxtnotp
      · refine ⟨fun hc => (hlc hc).elim, fun he => ?_⟩
        exact absurd (hnd.getElem_inj_iff.mp he) hlne
      · exact ⟨fun _ => rfl, fun _ => hpmc⟩
    have hin : ∀ v ∈ [x t, p[l]'hl, p[p.length - 1]'hMp], v ≠ x t →
        v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
      intro v hv hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact (hne rfl).elim
      · exact Or.inr (List.getElem_mem hl)
      · exact Or.inr (List.getElem_mem hMp)
    have hodd := (hc5 _ _ htri hu hin).1
    norm_num [pathLength] at hodd
  -- `i + 2 ≤ p.length`
  have hilt : i < p.length := by
    rcases Nat.lt_or_ge i p.length with hlt | hge
    · exact hlt
    · exfalso
      have hie : i - 1 = p.length - 1 := by omega
      exact hinotX' (by rw [HoleArithmetic.getElem_congr_idx p hi1p hMp hie]; exact hpmc)
  have hile : i + 2 ≤ p.length := by
    rcases Nat.lt_or_ge (i + 1) p.length with hlt | hge
    · omega
    · exfalso
      have hie : i = p.length - 1 := by omega
      refine hnadjm (i - 1) hi1p hinotX' (by omega) hspi' ?_
      have hadj := PathBasics.path_adj_succ hppath (i := i - 1) (by omega)
      have he2 : i - 1 + 1 = p.length - 1 := by omega
      rwa [HoleArithmetic.getElem_congr_idx p (by omega) hMp he2] at hadj
  -- the return path `R` between `x_t` and `p_m` with interior in `A_{t-1}`
  have hxtA1 : x t ∉ wheelSystemA G z A₀ x (t - 1) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
  have hpmA1 : (p[p.length - 1]'hMp) ∉ wheelSystemA G z A₀ x (t - 1) :=
    hpnotA _ (List.getElem_mem hMp)
  have hxtnbr : ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (x t) a :=
    Thm203Prelim.exists_nbr_wheelSystemA hframe hws (i := t) (k := t - 1)
      (by omega) (by omega) (by omega)
  have hpmnbr : ∃ a ∈ wheelSystemA G z A₀ x (t - 1), G.Adj (p[p.length - 1]'hMp) a :=
    (hp.2.2.2 (p.length - 1) hMp).mpr (by omega)
  obtain ⟨R, hRpath, hRint⟩ := MinimalConnectedIsPath.exists_path_interior_in
    (F := wheelSystemA G z A₀ x (t - 1))
    (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) hxtA1 hpmA1 hxtnbr hpmnbr
  have hRdec : ∀ v ∈ R, v = x t ∨ v = p[p.length - 1]'hMp ∨
      v ∈ wheelSystemA G z A₀ x (t - 1) := by
    intro v hv
    by_cases h1 : v = x t
    · exact Or.inl h1
    by_cases h2 : v = p[p.length - 1]'hMp
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (hRint v
        ((PathBasics.mem_interior_iff_of_pathFrom hRpath).mpr ⟨hv, h1, h2⟩)))
  have hRu : ∀ v ∈ R, VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = p[p.length - 1]'hMp := by
    intro v hv
    rcases hRdec v hv with he | he | hA
    · subst he
      refine ⟨fun hc => (hxtnotX hc).elim, fun he => ?_⟩
      exact absurd (by rw [he]; exact List.getElem_mem hMp) hxtnotp
    · exact ⟨fun _ => he, fun _ => by rw [he]; exact hpmc⟩
    · refine ⟨fun hc => (WheelSystemBasics.wheelSystemA_no_complete hA hc).elim, fun he => ?_⟩
      exact absurd (by rw [← he]; exact hA) hpmA1
  have hRin : ∀ v ∈ R, v ≠ x t → v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
    intro v hv hne
    rcases hRdec v hv with he | he | hA
    · exact (hne he).elim
    · exact Or.inr (by rw [he]; exact List.getElem_mem hMp)
    · exact Or.inl hA
  obtain ⟨hRodd, hRlen3⟩ := hc5 R (p[p.length - 1]'hMp) hRpath hRu hRin
  have hRlen : 4 ≤ R.length := by
    have := PathBasics.pathLength_eq R
    have hpos := PathBasics.path_length_pos hRpath.1
    omega
  have hRlenEven : Even R.length := by
    obtain ⟨d, hd⟩ := id hRodd
    have h1 := PathBasics.pathLength_eq R
    have h2 := PathBasics.path_length_pos hRpath.1
    exact ⟨d + 1, by omega⟩
  -- the prefix `x_{t+1}-p₁-⋯-p_i`
  have hMid : IsPathFrom G (x (t + 1) :: p.take i) (x (t + 1)) (p[i - 1]'hi1p) := by
    refine ⟨?_, rfl, ?_⟩
    · have := PathBasics.isPathList_take hp.1 (k := i + 1) (by omega)
      simpa using this
    · have he : i - 1 + 1 = i := by omega
      have hh := getLast?_take_succ p (i - 1) hi1p
      rw [he] at hh
      have htakepos : 0 < (p.take i).length := by simp only [List.length_take]; omega
      rw [List.getLast?_cons_of_ne_nil (List.ne_nil_of_length_pos htakepos)]
      exact hh
  have hMiddec : ∀ w ∈ (x (t + 1) :: p.take i),
      w = x (t + 1) ∨ ∃ (l : ℕ) (hl : l < p.length), l < i ∧ (p[l]'hl) = w := by
    intro w hw
    rcases List.mem_cons.mp hw with he | hw
    · exact Or.inl he
    · obtain ⟨l, hl, hlw⟩ := List.mem_iff_getElem.mp hw
      have hll : l < (p.take i).length := hl
      simp only [List.length_take] at hll
      exact Or.inr ⟨l, by omega, by omega, by rw [← hlw, List.getElem_take]⟩
  -- no vertex of the prefix has a neighbour in `A_{t-1}`
  have hpnoA : ∀ (l : ℕ) (hl : l < p.length), l < i →
      ∀ a ∈ wheelSystemA G z A₀ x (t - 1), ¬ G.Adj (p[l]'hl) a := by
    intro l hl hli a ha hadj
    have := (hp.2.2.2 l hl).mp ⟨a, ha, hadj⟩
    omega
  -- the prefix and `R` are disjoint
  have hdisj : ∀ w ∈ (x (t + 1) :: p.take i), w ∉ R := by
    intro w hw hwR
    rcases hMiddec w hw with rfl | ⟨l, hl, hli, hlw⟩
    · rcases hRdec _ hwR with he | he | hA
      · exact absurd (hws.2.1 (t + 1) le_rfl t (by omega) he) (by omega)
      · exact hxt1notp (by rw [he]; exact List.getElem_mem hMp)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl hA
    · rcases hRdec w hwR with he | he | hA
      · refine hxtnotp ?_
        rw [← he, ← hlw]
        exact List.getElem_mem hl
      · have : l = p.length - 1 := hnd.getElem_inj_iff.mp (by rw [hlw]; exact he)
        omega
      · exact hpnotA w (by rw [← hlw]; exact List.getElem_mem hl) hA
  -- the only edge between them is `p_i-x_t`
  have hcross : ∀ w ∈ (x (t + 1) :: p.take i), ∀ y ∈ R,
      (G.Adj w y ↔ (w = p[i - 1]'hi1p ∧ y = x t)) := by
    intro w hw y hy
    constructor
    · intro hadj
      rcases hMiddec w hw with rfl | ⟨l, hl, hli, hlw⟩
      · exfalso
        rcases hRdec y hy with he | he | hA
        · exact hsnone _ hxt1take (by rw [← he]; exact hadj.symm)
        · have e0 : (x (t + 1) :: p)[0]'(by simp) = x (t + 1) := rfl
          have e1 : (x (t + 1) :: p)[(p.length - 1) + 1]'(by simp; omega)
              = p[p.length - 1]'hMp := by simp
          refine PathBasics.path_not_adj_of_gap hp.1 (i := 0) (j := (p.length - 1) + 1)
            (by simp) (by simp; omega) (by omega) (by omega) ?_
          rw [e0, e1, ← he]; exact hadj
        · exact hxt1A y hA hadj
      · rcases hRdec y hy with he | he | hA
        · refine ⟨?_, he⟩
          by_contra hne
          have hlne : l ≠ i - 1 := by
            intro hcon
            exact hne (by rw [← hlw]; exact HoleArithmetic.getElem_congr_idx p hl hi1p hcon)
          refine hsnone (q[l]'(by omega)) (hmemtake l (by omega) (by omega)) ?_
          rw [hqp l hl, hlw, ← he]
          exact hadj.symm
        · exfalso
          refine PathBasics.path_not_adj_of_gap hppath hl hMp (by omega) (by omega) ?_
          rw [hlw, ← he]; exact hadj
        · exact absurd hadj (by rw [← hlw] at *; exact hpnoA l hl hli y hA)
    · rintro ⟨rfl, rfl⟩
      exact hspi'.symm
  have hglue : IsPathFrom G ((x (t + 1) :: p.take i) ++ R) (x (t + 1)) (p[p.length - 1]'hMp) :=
    PathGlue.glue_path hMid hRpath hdisj hcross
  have hgluelen : pathLength ((x (t + 1) :: p.take i) ++ R) = i + R.length := by
    simp only [pathLength, List.length_append, List.length_cons, List.length_take]
    omega
  -- 13.6, in the packaged form of `PathFor211.even`
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hXY : Complete G (wheelSystemX x (t - 1)) Y := by
    rintro w ⟨j, hj, rfl⟩ y hy
    exact hhub.2.2.2.2.2.1 j (by omega) y hy
  have hxt1R : x (t + 1) ∉ R := hdisj _ (List.mem_cons_self ..)
  have hxtY : VertexComplete G (x t) Y := hhub.2.2.2.2.2.1 t (by omega)
  have hxtnotY : x t ∉ Y := fun hm => G.irrefl (hxtY (x t) hm)
  have houtA : ∀ v ∈ wheelSystemA G z A₀ x t,
      v ∉ wheelSystemX x (t - 1) ∧ v ∉ Y := by
    intro v hvA
    refine ⟨?_, ?_⟩
    · rintro ⟨j, hj, hej⟩
      exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (hej ▸ hvA)
    · intro hvY
      exact Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1
        (j := t) (by omega) hvY hvA
  have hPF : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      ((x (t + 1) :: p.take i) ++ R) (x (t + 1)) (p[p.length - 1]'hMp) := by
    refine ⟨Set.disjoint_left.mpr (fun v hvX hvY => G.irrefl (hXY v hvX v hvY)),
      ⟨x 0, 0, by omega, rfl⟩, hhub.2.1,
      Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega),
      hhub.2.2.1, hXY, hglue, ?_, ?_, ?_⟩
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases hMiddec v hv with rfl | ⟨l, hl, hli, hlw⟩
        · refine ⟨?_, KiteTailBasics.hub_last_notMem hhub⟩
          rintro ⟨j, hj, he⟩
          exact absurd (hws.2.1 (t + 1) le_rfl j (by omega) he) (by omega)
        · exact houtA v (by rw [← hlw]; exact hpA _ (List.getElem_mem hl))
      · rcases hRdec v hv with he | he | hA
        · subst he
          refine ⟨?_, hxtnotY⟩
          rintro ⟨j, hj, hej⟩
          have := hws.2.1 t (by omega) j (by omega) hej
          omega
        · exact houtA v (by rw [he]; exact hpA _ (List.getElem_mem hMp))
        · exact houtA v (WheelSystemBasics.wheelSystemA_mono (by omega) hA)
    · rw [hgluelen]; omega
    · intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · rcases hMiddec v hv with rfl | ⟨l, hl, hli, hlw⟩
        · exact ⟨fun _ => Or.inl rfl, fun _ => hxc⟩
        · refine ⟨fun hc => ?_, ?_⟩
          · exfalso
            by_cases hle : l + 2 ≤ i
            · refine hnone l hle (by omega) ?_
              rw [hqp l hl, hlw]; exact hc
            · have : l = i - 1 := by omega
              refine hinotX' ?_
              rw [← HoleArithmetic.getElem_congr_idx p hl hi1p this, hlw]; exact hc
          · rintro (he | he)
            · exfalso
              apply hxt1notp
              rw [← he, ← hlw]
              exact List.getElem_mem hl
            · exfalso
              have hle : l = p.length - 1 := hnd.getElem_inj_iff.mp (by rw [hlw]; exact he)
              omega
      · rw [hRu v hv]
        refine ⟨Or.inr, ?_⟩
        rintro (he | he)
        · exact absurd (by rw [← he]; exact hv) hxt1R
        · exact he
  have hev := hPF.even hGF.1.1
  rw [hgluelen] at hev
  obtain ⟨d, hd⟩ := hiodd
  obtain ⟨e, he⟩ := hRlenEven
  obtain ⟨g, hg⟩ := hev
  omega

/-- Labelled gap for 21.2(6), p. 134.
PAPER: "We may assume that none of `x_{t+1},p₁,…,p_{i-1}` is
`X_{t-1}`-complete, and in particular `i ≤ m`."
The discarded case supplies 21.1's first alternative on the reversed path
`z-x_t-p_i-⋯-p_h`, which is the witness on the left. -/
theorem endgame_claim6_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ}
    (hp : GoodPath G z A₀ x t p) (hext : Extended G z A₀ x t p q i s)
    (hsupport : ∀ v ∈ q, v ∈ p ∨ v ∈ wheelSystemA G z A₀ x (t - 1))
    (hiodd : Odd i) (hic : ∃ hi : i - 1 < q.length, VertexComplete G q[i - 1] Y)
    (hc5 : OddReturnPaths G z A₀ x t p) :
    Thm211Witness G (wheelSystemX x (t - 1)) Y ∨
      (i ≤ p.length ∧ ∀ v ∈ (x (t + 1) :: q).take i,
        ¬ VertexComplete G v (wheelSystemX x (t - 1))) := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  obtain ⟨hpref, hq, hqAt, hcov, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  obtain ⟨hi1q, hicY⟩ := hic
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hXY : Complete G (wheelSystemX x (t - 1)) Y := by
    rintro w ⟨j, hj, rfl⟩ y hy
    exact hhub.2.2.2.2.2.1 j (by omega) y hy
  have hzY : z ∉ Y := fun hzy => G.irrefl (hhub.2.2.2.2.1 z hzy)
  have hxtY : VertexComplete G (x t) Y := hhub.2.2.2.2.2.1 t (by omega)
  have hxtnotY : x t ∉ Y := fun hm => G.irrefl (hxtY (x t) hm)
  have hxtnotX : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  have hqpath : IsPathList G q := by
    have := PathBasics.isPathList_drop hq (k := 1) (by simp; omega)
    simpa using this
  have hmemtake : ∀ l, l + 2 ≤ i → ∀ hl : l < q.length,
      q[l] ∈ (x (t + 1) :: q).take i := by
    intro l hli hl
    have hsplit : (x (t + 1) :: q).take i = x (t + 1) :: q.take (i - 1) := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp
    rw [hsplit]
    refine List.mem_cons_of_mem _ ?_
    have hlen : l < (q.take (i - 1)).length := by
      simp only [List.length_take]; omega
    have := List.getElem_mem hlen
    rwa [List.getElem_take] at this
  have hwhole : i < (x (t + 1) :: q).length := by simp; omega
  have helem : (x (t + 1) :: q)[i] = q[i - 1] := by
    cases i with
    | zero => omega
    | succ i => rfl
  have hspi : G.Adj (x s) q[i - 1] := by
    obtain ⟨w, hw, hsw⟩ := hcover s hst
    rw [List.take_succ_eq_append_getElem hwhole, List.mem_append] at hw
    rcases hw with hw | hw
    · exact (hsnone w hw hsw).elim
    · have he : w = (x (t + 1) :: q)[i] := by simpa using hw
      simpa only [he, helem] using hsw
  by_cases hA : ∃ l, l + 2 ≤ i ∧ ∃ hl : l < q.length,
      VertexComplete G q[l] (wheelSystemX x (t - 1))
  · left
    obtain ⟨l0, hl0⟩ := hA
    set Pr : ℕ → Prop := fun l => l + 2 ≤ i ∧ ∃ hl : l < q.length,
      VertexComplete G q[l] (wheelSystemX x (t - 1)) with hPr
    have hl0P : Pr l0 := hl0
    have hl0b : l0 ≤ i - 2 := by omega
    set L := Nat.findGreatest Pr (i - 2) with hL
    have hPL : Pr L := Nat.findGreatest_spec (m := l0) hl0b hl0P
    have hLle : L ≤ i - 2 := Nat.findGreatest_le _
    have hmax : ∀ k, L < k → k ≤ i - 2 → ¬ Pr k := fun k hk1 hk2 =>
      Nat.findGreatest_is_greatest hk1 hk2
    obtain ⟨hLi, hLq, hLc⟩ := hPL
    -- `s = t`
    have hsteq : s = t := by
      by_contra hne
      have hsX : x s ∈ wheelSystemX x (t - 1) := ⟨s, by omega, rfl⟩
      exact hsnone q[L] (hmemtake L hLi hLq) (hLc (x s) hsX).symm
    rw [hsteq] at hspi hsnone
    have hinotX : ¬ VertexComplete G q[i - 1] (wheelSystemX x (t - 1)) := by
      intro hcon
      refine WheelSystemBasics.wheelSystemA_no_complete
        (hqAt q[i - 1] (List.getElem_mem hi1q)) ?_
      rintro w ⟨j, hj, rfl⟩
      by_cases hjs : j = t
      · exact (hjs ▸ hspi).symm
      · exact hcon (x j) ⟨j, by omega, rfl⟩
    set S : List V := (q.drop L).take (i - 1 - L + 1) with hS
    have hSpath : IsPathFrom G S q[L] q[i - 1] := by
      rw [hS]; exact PathBasics.isPathFrom_slice hqpath (by omega) hi1q
    have hSlen : S.length = i - L := by
      rw [hS, PathBasics.length_slice q (i := L) (j := i - 1) (by omega) hi1q]
      omega
    have hSrev : IsPathFrom G S.reverse q[i - 1] q[L] := PathBasics.isPathFrom_reverse hSpath
    have hSrevmem : ∀ w ∈ S.reverse, ∃ (k : ℕ) (hk : k < q.length),
        L ≤ k ∧ k ≤ i - 1 ∧ q[k] = w := by
      intro w hw
      have hw' : w ∈ S := List.mem_reverse.mp hw
      rw [hS] at hw'
      exact (PathBasics.mem_slice_iff q (i := L) (j := i - 1) (by omega) hi1q).mp hw'
    have hxtnotS : x t ∉ S.reverse := by
      intro hm
      obtain ⟨k, hk, _, _, hkw⟩ := hSrevmem _ hm
      exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
        (hkw ▸ hqAt q[k] (List.getElem_mem hk))
    have hR : IsPathFrom G (x t :: S.reverse) (x t) q[L] := by
      refine PathAttach.isPathFrom_cons hSrev hspi hxtnotS ?_
      intro w hw hne
      obtain ⟨k, hk, hkL, hki, hkw⟩ := hSrevmem w hw
      have hkne : k ≠ i - 1 := by
        intro hcon
        apply hne
        rw [← hkw]
        exact HoleArithmetic.getElem_congr_idx q hk hi1q hcon
      exact hkw ▸ hsnone q[k] (hmemtake k (by omega) hk)
    have hRlen : pathLength (x t :: S.reverse) = i - L := by
      simp only [pathLength, List.length_cons, List.length_reverse, hSlen]
      omega
    have huniq : ∀ v ∈ (x t :: S.reverse),
        VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = q[L] := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · constructor
        · intro hc; exact (hxtnotX hc).elim
        · intro he
          exact (Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
            (he ▸ hqAt q[L] (List.getElem_mem hLq))).elim
      · obtain ⟨k, hk, hkL, hki, hkw⟩ := hSrevmem v hv
        subst hkw
        have hnd := PathBasics.path_nodup hqpath
        constructor
        · intro hc
          by_cases hkeq : k = L
          · exact HoleArithmetic.getElem_congr_idx q hk hLq hkeq
          · exfalso
            by_cases hki1 : k = i - 1
            · exact hinotX (hki1 ▸ hc)
            · exact hmax k (by omega) (by omega) ⟨by omega, hk, hc⟩
        · intro he
          have hkL' : k = L := hnd.getElem_inj_iff.mp he
          rw [HoleArithmetic.getElem_congr_idx q hk hLq hkL']; exact hLc
    have hin : ∀ v ∈ (x t :: S.reverse), v ≠ x t →
        v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
      intro v hv hne
      rcases List.mem_cons.mp hv with rfl | hv
      · exact (hne rfl).elim
      · obtain ⟨k, hk, _, _, hkw⟩ := hSrevmem v hv
        exact (hsupport v (hkw ▸ List.getElem_mem hk)).symm
    obtain ⟨hodd5, hlen5⟩ := hc5 (x t :: S.reverse) q[L] hR huniq hin
    rw [hRlen] at hodd5 hlen5
    have hznot : z ∉ (x t :: S.reverse) := by
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact (hws.2.2.1 t (by omega)).2 he.symm
      · obtain ⟨k, hk, _, _, hkw⟩ := hSrevmem _ hm
        refine Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) ?_
        have hmm : q[k] ∈ wheelSystemA G z A₀ x t := hqAt q[k] (List.getElem_mem hk)
        rwa [hkw] at hmm
    have hP : IsPathFrom G (z :: x t :: S.reverse) z q[L] := by
      refine PathAttach.isPathFrom_cons hR (hws.2.2.2.2.2.2 t (by omega)) hznot ?_
      intro w hw hne
      rcases List.mem_cons.mp hw with he | hw
      · exact (hne he).elim
      · obtain ⟨k, hk, _, _, hkw⟩ := hSrevmem w hw
        exact hkw ▸ WheelSystemBasics.wheelSystemA_no_nbr (hqAt q[k] (List.getElem_mem hk))
    have hPlen : pathLength (z :: x t :: S.reverse) = i - L + 1 := by
      simp only [pathLength, List.length_cons, List.length_reverse, hSlen]
      omega
    have htake3 : (z :: x t :: S.reverse).take 3 = [z, x t, q[i - 1]] := by
      have h1 : S.reverse.take 1 = [q[i - 1]] := by
        rw [List.take_one, hSrev.2.1]; rfl
      simp only [List.take_succ_cons, h1]
    refine ⟨z :: x t :: S.reverse, z, q[L],
      Set.disjoint_left.mpr (fun v hvX hvY => G.irrefl (hXY v hvX v hvY)),
      ⟨x 0, 0, by omega, rfl⟩, hhub.2.1,
      Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega),
      hhub.2.2.1, hXY, hP.1, ?_, ?_, hP.2.1, hP.2.2, ?_, Or.inl ?_⟩
    · -- outside
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · refine ⟨?_, hzY⟩
        rintro ⟨j, hj, he⟩
        exact (hws.2.2.1 j (by omega)).2 he.symm
      · rcases List.mem_cons.mp hv with rfl | hv
        · refine ⟨?_, hxtnotY⟩
          rintro ⟨j, hj, he⟩
          have := hws.2.1 t (by omega) j (by omega) he
          omega
        · obtain ⟨k, hk, _, _, hkw⟩ := hSrevmem v hv
          have hvA : v ∈ wheelSystemA G z A₀ x t := hkw ▸ hqAt q[k] (List.getElem_mem hk)
          refine ⟨?_, ?_⟩
          · rintro ⟨j, hj, he⟩
            exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (he ▸ hvA)
          · intro hvY
            exact Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1
              (j := t) (by omega) hvY hvA
    · rw [hPlen]; omega
    · -- complete ends
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨fun _ => Or.inl rfl, fun _ => hzX⟩
      · rw [huniq v hv]
        refine ⟨Or.inr, ?_⟩
        rintro (he | he)
        · rw [he] at hv; exact absurd hv hznot
        · exact he
    · -- first alternative of 21.1
      intro v hv
      rw [htake3] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hhub.2.2.2.2.1
      · exact hxtY
      · exact hicY
  · -- Case B: none of `p₁,…,p_{i-1}` is `X_{t-1}`-complete
    right
    rw [not_exists] at hA
    simp only [not_and, not_exists] at hA
    have hMlt : p.length - 1 < p.length := by
      have := hp.2.1
      have : 0 < p.length := List.length_pos_of_ne_nil this
      omega
    have hpq : p.length ≤ q.length := hpref.length_le
    have hMq : p.length - 1 < q.length := by omega
    have hpm : q[p.length - 1]'hMq = p[p.length - 1]'hMlt :=
      (hpref.getElem hMlt).symm
    have hpmA : p[p.length - 1]'hMlt ∈ wheelSystemA G z A₀ x t :=
      (hp.2.2.1 _ (List.getElem_mem hMlt)).1
    have hpmc : VertexComplete G (p[p.length - 1]'hMlt) (wheelSystemX x (t - 1)) :=
      Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (i := t - 1) (by omega)
        (WheelSystemBasics.wheelSystemA_no_nbr hpmA)
        (hp.2.2.1 _ (List.getElem_mem hMlt)).2
        ((hp.2.2.2 (p.length - 1) hMlt).mpr (by omega))
    have hip : i ≤ p.length := by
      by_contra hcon
      exact hA (p.length - 1) (by omega) hMq (by rw [hpm]; exact hpmc)
    refine ⟨hip, ?_⟩
    have hxt1 := claim6_hub_not_complete_gap h hp hext hip hA hc5
    intro v hv
    have hsplit : (x (t + 1) :: q).take i = x (t + 1) :: q.take (i - 1) := by
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      simp
    rw [hsplit] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact hxt1
    · obtain ⟨k, hk, hkv⟩ := List.mem_iff_getElem.mp hv
      have hklen : k < (q.take (i - 1)).length := hk
      simp only [List.length_take] at hklen
      have hkq : k < q.length := by omega
      have : q[k] = v := by
        rw [← hkv, List.getElem_take]
      rw [← this]
      exact hA k (by omega) hkq

/-- The counting-and-17.1 half of 21.2(8), printed p. 134.

PAPER: *"The path `z-x_t-S-p_k` is odd, and its ends are `X_{t−1}`-complete, so by 2.3 it
contains an odd number of `X_{t−1}`-complete edges.  Since `x_t` is not `X_{t−1}`-complete, all
these `X_{t−1}`-complete edges belong to `S` and hence to `C`, and there are no further
`X_{t−1}`-complete edges in `C`.  Thus an odd number of edges of `C` are `X_{t−1}`-complete,
and so by 2.3 there is exactly one, and exactly two `X_{t−1}`-complete vertices.  Since `p_k`
is `X_{t−1}`-complete, the second such vertex is the neighbour of `p_k` in `S`.  This therefore
does not belong to `A_{t−1}`, and so `k < m`, and `p_{k+1}` is the second `X_{t−1}`-complete
vertex of `C`.  By 2.10 applied to `C`, `X_{t−1}` contains a leap or hat, and in either case
some `x ∈ X_{t−1}` is nonadjacent to all of `x_t, x_{t+1}, p₁`, and adjacent to `p_k`.  Hence
`(V(C) \ {x_t, x_{t+1}}) ∪ {x}` (`= F` say) catches the triangle `{z, x_t, x_{t+1}}`; the only
neighbour of `z` in `F` is `x`; the only neighbour of `x_{t+1}` in `F` is `p₁`; and `x, p₁` are
nonadjacent, and are both nonadjacent to `x_t`, contrary to 17.1."*

The hole `C` of the paper is the list `S ++ (x_{t+1} :: p₁-⋯-p_{k−1}).reverse`, i.e. the cycle
`x_t-x_{t+1}-p₁-⋯-p_k-S-x_t` read from `x_t` along `S` first.  `hSc` is the sentence *"by (5),
some internal vertex of `S` is `X_{t−1}`-complete"*, which is proved in `claim8_hole_gap`. -/
theorem claim8_count {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V} {k : ℕ}
    (hp : GoodPath G z A₀ x t p) (hk3 : 3 ≤ k) (hkm : k ≤ p.length) (hkodd : Odd k)
    (hadj : G.Adj (x t) (x (t + 1)))
    (hnone : ∀ v ∈ p.take k, ¬ G.Adj (x t) v)
    {S : List V} (hS : IsPathFrom G S (x t) (p[k - 1]'(by omega)))
    (hSint : ∀ v ∈ SPGT.interior S,
      v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p.drop k)
    (hSeven : Even (pathLength S))
    (hSc : ∃ v ∈ SPGT.interior S, VertexComplete G v (wheelSystemX x (t - 1)))
    (hP : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1])
    (hC : IsHoleList G (S ++ (x (t + 1) :: p.take (k - 1)).reverse)) : False := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  have hk1 : k - 1 < p.length := by omega
  have hppath : IsPathList G p := by
    have hh := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using hh
  have hpnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpA1 : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  have hxt1p : ∀ (j : ℕ) (hj : j < p.length), G.Adj (x (t + 1)) (p[j]'hj) ↔ j = 0 := by
    intro j hj
    have hh := hp.1.2.2 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
    have h0 : (x (t + 1) :: p)[0]'(by simp) = x (t + 1) := rfl
    have hj1 : (x (t + 1) :: p)[j + 1]'(by simp only [List.length_cons]; omega) = p[j]'hj := rfl
    rw [h0, hj1] at hh
    rw [hh]; omega
  have hxtA : x t ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
  have hzAt : z ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
  have hdropidx : ∀ v ∈ p.drop k, ∃ (j : ℕ) (hj : j < p.length), k ≤ j ∧ (p[j]'hj) = v := by
    intro v hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    simp only [List.length_drop] at hj
    refine ⟨k + j, by omega, by omega, ?_⟩
    rw [← hjv, List.getElem_drop]
  have hRmem : ∀ v ∈ (x (t + 1) :: p.take (k - 1)).reverse,
      v = x (t + 1) ∨ ∃ (j : ℕ) (hj : j < p.length), j + 1 < k ∧ (p[j]'hj) = v := by
    intro v hv
    rcases List.mem_cons.mp (List.mem_reverse.mp hv) with he | hv'
    · exact Or.inl he
    · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv'
      simp only [List.length_take] at hj
      exact Or.inr ⟨j, by omega, by omega, by rw [← hjv, List.getElem_take]⟩
  have hSmem : ∀ v ∈ S, v = x t ∨ v = (p[k - 1]'hk1) ∨ v ∈ SPGT.interior S := by
    intro v hv
    rcases eq_or_ne v (x t) with he | h1
    · exact Or.inl he
    rcases eq_or_ne v (p[k - 1]'hk1) with he | h2
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hS).mpr ⟨hv, h1, h2⟩))
  have hznep : ∀ (j : ℕ) (hj : j < p.length), z ≠ (p[j]'hj) :=
    fun j hj he => hzAt (he ▸ hpA _ (List.getElem_mem hj))
  have hzxt1ne : z ≠ x (t + 1) := fun he => (hws.2.2.1 (t + 1) le_rfl).2 he.symm
  have hxt1notp : ∀ (j : ℕ) (hj : j < p.length), x (t + 1) ≠ (p[j]'hj) :=
    fun j hj he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
      (he ▸ hpA _ (List.getElem_mem hj))
  have hxnotA : ∀ (j : ℕ), j ≤ t - 1 → x j ∉ wheelSystemA G z A₀ x t :=
    fun j hj => Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega)
  -- vertices of `C` are outside `X_{t-1}`
  have hXout : ∀ w ∈ (S ++ (x (t + 1) :: p.take (k - 1)).reverse),
      w ∉ wheelSystemX x (t - 1) := by
    intro w hw hwX
    obtain ⟨j, hj, rfl⟩ := hwX
    rcases List.mem_append.mp hw with hw | hw
    · rcases hSmem _ hw with he | he | he
      · have := hws.2.1 j (by omega) t (by omega) he
        omega
      · exact hxnotA j hj (he ▸ hpA _ (List.getElem_mem hk1))
      · rcases hSint _ he with hh | hh
        · exact hxnotA j hj (WheelSystemBasics.wheelSystemA_mono (by omega) hh)
        · exact hxnotA j hj (hpA _ (List.mem_of_mem_drop hh))
    · rcases hRmem _ hw with he | ⟨j', hj', hj'k, he⟩
      · have := hws.2.1 j (by omega) (t + 1) le_rfl he
        omega
      · exact hxnotA j hj (he ▸ hpA _ (List.getElem_mem hj'))
  -- the vertices of the `R`-part of `C` are not `X_{t-1}`-complete
  have hxtnc : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  have hRnc : ∀ w ∈ (x (t + 1) :: p.take (k - 1)).reverse,
      ¬ VertexComplete G w (wheelSystemX x (t - 1)) := by
    intro w hw hwc
    have hmem : w ∈ (z :: x (t + 1) :: p.take k) := by
      rcases hRmem w hw with he | ⟨j, hj, hjk, he⟩
      · exact he ▸ List.mem_cons_of_mem _ List.mem_cons_self
      · refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
        have hlt : j < (p.take k).length := by simp only [List.length_take]; omega
        have hh := List.getElem_mem hlt
        rw [List.getElem_take] at hh
        exact he ▸ hh
    rcases (hP.completeEnds w hmem).mp hwc with he | he <;>
      rcases hRmem w hw with hf | ⟨j, hj, hjk, hf⟩
    · exact hzxt1ne (he.symm.trans hf)
    · exact hznep j hj (he.symm.trans hf.symm)
    · exact hxt1notp (k - 1) hk1 (hf.symm.trans he)
    · have := hpnd.getElem_inj_iff.mp (hf.trans he)
      omega
  -- the odd path `z-x_t-S-p_k`
  have hzc : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro u ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hpkmem : (p[k - 1]'hk1) ∈ (z :: x (t + 1) :: p.take k) := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    have hlt : k - 1 < (p.take k).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hpkc : VertexComplete G (p[k - 1]'hk1) (wheelSystemX x (t - 1)) :=
    (hP.completeEnds _ hpkmem).mpr (Or.inr rfl)
  have hSA : ∀ v ∈ S, v ≠ x t → v ∈ wheelSystemA G z A₀ x t := by
    intro v hv hvne
    rcases hSmem v hv with he | he | he
    · exact absurd he hvne
    · exact he ▸ hpA _ (List.getElem_mem hk1)
    · rcases hSint _ he with hh | hh
      · exact WheelSystemBasics.wheelSystemA_mono (by omega) hh
      · exact hpA _ (List.mem_of_mem_drop hh)
  have hzS : z ∉ S := by
    intro hz
    rcases eq_or_ne z (x t) with he | hne
    · exact (hws.2.2.1 t (by omega)).2 he.symm
    · exact hzAt (hSA z hz hne)
  have hzadjS : ∀ v ∈ S, v ≠ x t → ¬ G.Adj z v :=
    fun v hv hne => WheelSystemBasics.wheelSystemA_no_nbr (hSA v hv hne)
  have hzxt : G.Adj z (x t) := hws.2.2.2.2.2.2 t (by omega)
  have hL : IsPathFrom G (z :: S) z (p[k - 1]'hk1) :=
    PathAttach.isPathFrom_cons hS hzxt hzS hzadjS
  have hSpos : 0 < S.length := PathBasics.path_length_pos hS.1
  have hLodd : Odd (pathLength (z :: S)) := by
    have h1 : pathLength (z :: S) = pathLength S + 1 := by
      rw [PathBasics.pathLength_cons, PathBasics.pathLength_eq]; omega
    obtain ⟨d, hd⟩ := hSeven
    exact ⟨d, by omega⟩
  have hS0 : S[0]'hSpos = x t := PathBasics.getElem_zero_of_head? hS.2.1 hSpos
  have hznbr : ∀ v ∈ (z :: S), G.Adj z v → v = x t := by
    intro v hv hadjv
    obtain ⟨n, hn, hnv⟩ := List.getElem_of_mem hv
    have h0 : (z :: S)[0]'(by simp) = z := rfl
    rw [← hnv] at hadjv ⊢
    rw [← h0] at hadjv
    have hdd := (PathBasics.path_adj_iff hL.1 (by simp) hn).mp hadjv
    have hn1 : n = 1 := by simp only [List.length_cons] at hn; omega
    rw [HoleArithmetic.getElem_congr_idx (z :: S) hn
      (show 1 < (z :: S).length by simp only [List.length_cons]; omega) hn1]
    exact hS0
  have hLXout : ∀ w ∈ (z :: S), w ∉ wheelSystemX x (t - 1) := by
    intro w hw hwX
    obtain ⟨j, hj, rfl⟩ := hwX
    rcases List.mem_cons.mp hw with he | he
    · exact (hws.2.2.1 j (by omega)).2 he
    · rcases eq_or_ne (x j) (x t) with hf | hf
      · have := hws.2.1 j (by omega) t (by omega) hf
        omega
      · exact hxnotA j hj (hSA _ he hf)
  have hXanti : AnticonnectedSet G (wheelSystemX x (t - 1)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega)
  have h23L := (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge (wheelSystemX x (t - 1))
    hXanti (z :: S) (Or.inl hL.1) hLXout).1 (z :: S) z (p[k - 1]'hk1)
    (Or.inl ⟨hL.1, List.infix_refl _⟩) hL hzc hpkc
  obtain ⟨w0, hw0int, hw0c⟩ := hSc
  have hw0S : w0 ∈ S := PathBasics.interior_subset hw0int
  have hw0ne : w0 ≠ z := fun he => hzS (he ▸ hw0S)
  have hw0nepk : w0 ≠ (p[k - 1]'hk1) :=
    ((PathBasics.mem_interior_iff_of_pathFrom hS).mp hw0int).2.2
  have hLcount : {e : Sym2 V | ∃ u ∈ (z :: S), ∃ v ∈ (z :: S), e = s(u, v) ∧
      EdgeComplete G (wheelSystemX x (t - 1)) u v}.ncard % 2 = 1 := by
    rcases h23L with hcnt | honly
    · rw [hcnt]
      obtain ⟨d, hd⟩ := hLodd
      omega
    · exact absurd (honly w0 (List.mem_cons_of_mem _ hw0S) hw0c)
        (fun hc => hc.elim hw0ne hw0nepk)
  -- the complete edges of `C` are exactly the complete edges of `z-x_t-S-p_k`
  have hCcompS : ∀ w ∈ (S ++ (x (t + 1) :: p.take (k - 1)).reverse),
      VertexComplete G w (wheelSystemX x (t - 1)) → w ∈ S := by
    intro w hw hwc
    rcases List.mem_append.mp hw with hw | hw
    · exact hw
    · exact absurd hwc (hRnc w hw)
  have hEeq : {e : Sym2 V | ∃ u ∈ (z :: S), ∃ v ∈ (z :: S), e = s(u, v) ∧
        EdgeComplete G (wheelSystemX x (t - 1)) u v}
      = {e : Sym2 V | ∃ u ∈ (S ++ (x (t + 1) :: p.take (k - 1)).reverse),
        ∃ v ∈ (S ++ (x (t + 1) :: p.take (k - 1)).reverse), e = s(u, v) ∧
        EdgeComplete G (wheelSystemX x (t - 1)) u v} := by
    ext e
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨u, hu, v, hv, rfl, hedge⟩
      have hune : u ≠ z := by
        rintro rfl
        exact hxtnc ((hznbr v hv hedge.1) ▸ hedge.2.2)
      have hvne : v ≠ z := by
        rintro rfl
        exact hxtnc ((hznbr u hu hedge.1.symm) ▸ hedge.2.1)
      exact ⟨u, List.mem_append_left _ ((List.mem_cons.mp hu).resolve_left hune),
        v, List.mem_append_left _ ((List.mem_cons.mp hv).resolve_left hvne), rfl, hedge⟩
    · rintro ⟨u, hu, v, hv, rfl, hedge⟩
      exact ⟨u, List.mem_cons_of_mem _ (hCcompS u hu hedge.2.1),
        v, List.mem_cons_of_mem _ (hCcompS v hv hedge.2.2), rfl, hedge⟩
  -- so by 2.3 applied to the hole, `C` has exactly two `X_{t-1}`-complete vertices
  have h23C := (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge (wheelSystemX x (t - 1))
    hXanti _ (Or.inr hC) hXout).2 hC
  obtain ⟨a, b, hab, habne, habadj⟩ : ∃ a b : V,
      {w : V | w ∈ (S ++ (x (t + 1) :: p.take (k - 1)).reverse) ∧
        VertexComplete G w (wheelSystemX x (t - 1))} = {a, b} ∧ a ≠ b ∧ G.Adj a b := by
    rcases h23C with heven | hres
    · exfalso
      rw [← hEeq] at heven
      obtain ⟨d, hd⟩ := heven
      omega
    · exact hres
  set C : List V := S ++ (x (t + 1) :: p.take (k - 1)).reverse with hCdef
  have hp0 : (0 : ℕ) < p.length := by omega
  have hxtC : x t ∈ C := List.mem_append_left _ (PathBasics.head_mem hS.2.1)
  have hxt1C : x (t + 1) ∈ C :=
    List.mem_append_right _ (List.mem_reverse.mpr List.mem_cons_self)
  have hp0C : (p[0]'hp0) ∈ C := by
    refine List.mem_append_right _ (List.mem_reverse.mpr (List.mem_cons_of_mem _ ?_))
    have hlt : (0 : ℕ) < (p.take (k - 1)).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hmemab : ∀ w ∈ C, VertexComplete G w (wheelSystemX x (t - 1)) → w = a ∨ w = b := by
    intro w hw hwc
    have hh : w ∈ ({a, b} : Set V) := by rw [← hab]; exact ⟨hw, hwc⟩
    simpa using hh
  have habmem : ∀ w : V, (w = a ∨ w = b) →
      w ∈ C ∧ VertexComplete G w (wheelSystemX x (t - 1)) := by
    intro w hw
    have hh : w ∈ ({a, b} : Set V) := by rcases hw with rfl | rfl <;> simp
    rw [← hab] at hh
    exact hh
  have hxtnab : ∀ w : V, (w = a ∨ w = b) → w ≠ x t :=
    fun w hw he => hxtnc (he ▸ (habmem w hw).2)
  have hxt1nab : ∀ w : V, (w = a ∨ w = b) → w ≠ x (t + 1) := by
    intro w hw he
    exact hRnc _ (List.mem_reverse.mpr List.mem_cons_self) (he ▸ (habmem w hw).2)
  have hp0nab : ∀ w : V, (w = a ∨ w = b) → w ≠ (p[0]'hp0) := by
    intro w hw he
    refine hRnc _ (List.mem_reverse.mpr (List.mem_cons_of_mem _ ?_)) (he ▸ (habmem w hw).2)
    have hlt : (0 : ℕ) < (p.take (k - 1)).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  -- neither `x_{t+1}` nor `p₁` has a neighbour among the two complete vertices
  have hnoab : ∀ w : V, (w = a ∨ w = b) →
      ¬ G.Adj (x (t + 1)) w ∧ ¬ G.Adj (p[0]'hp0) w := by
    intro w hw
    obtain ⟨hwC, hwc⟩ := habmem w hw
    have hwS : w ∈ S := hCcompS w hwC hwc
    rcases hSmem w hwS with he | he | he
    · exact absurd he (hxtnab w hw)
    · subst he
      refine ⟨fun hadj => ?_, fun hadj => ?_⟩
      · exact absurd ((hxt1p (k - 1) hk1).mp hadj) (by omega)
      · have := (hppath.2.2 0 (k - 1) hp0 hk1).mp hadj
        omega
    · rcases hSint _ he with hh | hh
      · refine ⟨fun hadj => hxt1A w hh hadj, fun hadj => ?_⟩
        exact (hp.2.2.2 0 hp0).not.mpr (by omega) ⟨w, hh, hadj⟩
      · obtain ⟨j, hj, hkj, rfl⟩ := hdropidx _ hh
        refine ⟨fun hadj => ?_, fun hadj => ?_⟩
        · exact absurd ((hxt1p j hj).mp hadj) (by omega)
        · have := (hppath.2.2 0 j hp0 hj).mp hadj
          omega
  -- 2.10 applied to `C`
  have hSlen3 : 3 ≤ S.length := by
    refine MinimalConnectedIsPath.three_le_length_of_not_adj hS ?_ ?_
    · intro he
      exact hxtA (he ▸ hpA _ (List.getElem_mem hk1))
    · refine hnone _ ?_
      have hlt : k - 1 < (p.take k).length := by simp only [List.length_take]; omega
      have hh := List.getElem_mem hlt
      rwa [List.getElem_take] at hh
  have hClen : C.length = S.length + k := by
    simp only [hCdef, List.length_append, List.length_reverse, List.length_cons,
      List.length_take]
    omega
  have hCbig : 4 < holeLength C := by simp only [holeLength, hClen]; omega
  have h210 := Workspace.Statements.S02.SPGT.thm_2_10 G hBerge (wheelSystemX x (t - 1))
    hXanti C hC hXout hCbig a b (habmem a (Or.inl rfl)).1 (habmem b (Or.inr rfl)).1 habadj
    (habmem a (Or.inl rfl)).2 (habmem b (Or.inr rfl)).2 hmemab
  have hCnd : C.Nodup := hC.2.1
  have hXne : ∀ (c : V), c ∈ wheelSystemX x (t - 1) → ∀ w ∈ C, c ≠ w :=
    fun c hc w hw he => hXout w hw (he ▸ hc)
  have hgood : ∃ hh ∈ wheelSystemX x (t - 1), (G.Adj hh a ∨ G.Adj hh b) ∧
      ¬ G.Adj hh (x t) ∧ ¬ G.Adj hh (x (t + 1)) ∧ ¬ G.Adj hh (p[0]'hp0) := by
    rcases h210 with ⟨hh, hhX, hhat⟩ | ⟨c, hcX, d, hdX, hlp⟩
    · exact ⟨hh, hhX, Or.inl hhat.2.2.2.2.1,
        hhat.2.2.2.2.2.2 _ hxtC (fun he => hxtnab a (Or.inl rfl) he.symm)
          (fun he => hxtnab b (Or.inr rfl) he.symm),
        hhat.2.2.2.2.2.2 _ hxt1C (fun he => hxt1nab a (Or.inl rfl) he.symm)
          (fun he => hxt1nab b (Or.inr rfl) he.symm),
        hhat.2.2.2.2.2.2 _ hp0C (fun he => hp0nab a (Or.inl rfl) he.symm)
          (fun he => hp0nab b (Or.inr rfl) he.symm)⟩
    · have hbridge : ∀ (u v e w : V), e ≠ u → e ≠ v →
          ((G.deleteEdges {s(u, v)}).Adj e w ↔ G.Adj e w) := by
        intro u v e w heu hev
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨fun hq => hq.1, fun hq => ⟨hq, ?_⟩⟩
        simp only [Set.mem_singleton_iff, Sym2.eq_iff]
        rintro (⟨h1, -⟩ | ⟨h1, -⟩)
        · exact heu h1
        · exact hev h1
      have key : ∀ (u v : V), (u = a ∨ u = b) → (v = a ∨ v = b) →
          IsLeapForHole G C u v c d →
          (∀ w ∈ C, w ≠ u → w ≠ v → G.Adj c w → G.Adj w v) ∧
          (∀ w ∈ C, w ≠ u → w ≠ v → G.Adj d w → G.Adj w u) ∧
          (∀ w ∈ C, ∀ w' ∈ C, w ≠ u → w ≠ v → w' ≠ u → w' ≠ v →
            G.Adj c w → G.Adj d w' → w ≠ w') ∧ (G.Adj c u ∧ G.Adj d u) := by
        rintro u v hu hv ⟨-, idx, hhead, hlast, hlpath⟩
        obtain ⟨hDpath, hDlen2, hcdne, -, hAdjc, hAdjd⟩ := hlpath
        have hDlen : (C.rotate idx).length = C.length := List.length_rotate ..
        have hDnd : (C.rotate idx).Nodup := List.nodup_rotate.mpr hCnd
        have hCl6 : 6 ≤ C.length := by rw [hClen]; omega
        have hD0 : (C.rotate idx)[0]'(by omega) = v :=
          PathBasics.getElem_zero_of_head? hhead (by omega)
        have hDl : (C.rotate idx)[(C.rotate idx).length - 1]'(by omega) = u :=
          PathBasics.getElem_last_of_getLast? hlast (by omega)
        have hcu : c ≠ u := hXne c hcX u (habmem u hu).1
        have hcv : c ≠ v := hXne c hcX v (habmem v hv).1
        have hdu : d ≠ u := hXne d hdX u (habmem u hu).1
        have hdv : d ≠ v := hXne d hdX v (habmem v hv).1
        have hidx1 : ∀ w ∈ C, w ≠ u → w ≠ v → G.Adj c w →
            ∃ hh : 1 < (C.rotate idx).length, w = (C.rotate idx)[1]'hh := by
          intro w hw hwu hwv hadj
          obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem (List.mem_rotate.mpr hw)
          have hh := (hAdjc n hn).mp
            ((hbridge u v c _ hcu hcv).mpr (by rw [hnw]; exact hadj))
          have hn1 : n = 1 := by
            rcases hh with h0 | h1 | h2
            · exact absurd (by rw [← hnw,
                HoleArithmetic.getElem_congr_idx _ hn (by omega) h0]; exact hD0) hwv
            · exact h1
            · exact absurd (by rw [← hnw,
                HoleArithmetic.getElem_congr_idx _ hn (by omega) h2]; exact hDl) hwu
          exact ⟨by omega, by rw [← hnw,
            HoleArithmetic.getElem_congr_idx _ hn (show 1 < _ by omega) hn1]⟩
        have hidx2 : ∀ w ∈ C, w ≠ u → w ≠ v → G.Adj d w →
            ∃ hh : (C.rotate idx).length - 2 < (C.rotate idx).length,
              w = (C.rotate idx)[(C.rotate idx).length - 2]'hh := by
          intro w hw hwu hwv hadj
          obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem (List.mem_rotate.mpr hw)
          have hh := (hAdjd n hn).mp
            ((hbridge u v d _ hdu hdv).mpr (by rw [hnw]; exact hadj))
          have hn1 : n = (C.rotate idx).length - 2 := by
            rcases hh with h0 | h1 | h2
            · exact absurd (by rw [← hnw,
                HoleArithmetic.getElem_congr_idx _ hn (by omega) h0]; exact hD0) hwv
            · exact h1
            · exact absurd (by rw [← hnw,
                HoleArithmetic.getElem_congr_idx _ hn (by omega) h2]; exact hDl) hwu
          exact ⟨by omega, by rw [← hnw,
            HoleArithmetic.getElem_congr_idx _ hn (show _ - 2 < _ by omega) hn1]⟩
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · intro w hw hwu hwv hadj
          obtain ⟨hh, hwe⟩ := hidx1 w hw hwu hwv hadj
          have hadj01 := PathBasics.path_adj_succ hDpath (i := 0) (by omega)
          rw [hD0, HoleArithmetic.getElem_congr_idx _
            (show 0 + 1 < (C.rotate idx).length by omega) hh rfl] at hadj01
          rw [hwe]
          exact ((SimpleGraph.deleteEdges_adj.mp hadj01).1).symm
        · intro w hw hwu hwv hadj
          obtain ⟨hh, hwe⟩ := hidx2 w hw hwu hwv hadj
          have hadj01 := PathBasics.path_adj_succ hDpath
            (i := (C.rotate idx).length - 2) (by omega)
          rw [HoleArithmetic.getElem_congr_idx _
            (show (C.rotate idx).length - 2 + 1 < (C.rotate idx).length by omega)
            (show (C.rotate idx).length - 1 < (C.rotate idx).length by omega) (by omega),
            hDl] at hadj01
          rw [hwe]
          exact (SimpleGraph.deleteEdges_adj.mp hadj01).1
        · intro w hw w' hw' hwu hwv hw'u hw'v hadj hadj' he
          obtain ⟨hh, hwe⟩ := hidx1 w hw hwu hwv hadj
          obtain ⟨hh', hwe'⟩ := hidx2 w' hw' hw'u hw'v hadj'
          rw [hwe, hwe'] at he
          have := hDnd.getElem_inj_iff.mp he
          omega
        · have hq := (hAdjc ((C.rotate idx).length - 1) (by omega)).mpr
            (Or.inr (Or.inr rfl))
          rw [hDl] at hq
          exact (hbridge u v c _ hcu hcv).mp hq
        · have hq := (hAdjd ((C.rotate idx).length - 1) (by omega)).mpr
            (Or.inr (Or.inr rfl))
          rw [hDl] at hq
          exact (hbridge u v d _ hdu hdv).mp hq
      have hcase : ∀ (u v : V), (u = a ∨ u = b) → (v = a ∨ v = b) →
          IsLeapForHole G C u v c d → ∃ hh ∈ wheelSystemX x (t - 1),
            (G.Adj hh a ∨ G.Adj hh b) ∧
            ¬ G.Adj hh (x t) ∧ ¬ G.Adj hh (x (t + 1)) ∧ ¬ G.Adj hh (p[0]'hp0) := by
        intro u v hu hv hlk
        obtain ⟨kA, kB, kC, kD1, kD2⟩ := key u v hu hv hlk
        have hxt1u : x (t + 1) ≠ u := fun he => hxt1nab u hu he.symm
        have hxt1v : x (t + 1) ≠ v := fun he => hxt1nab v hv he.symm
        have hp0u : (p[0]'hp0) ≠ u := fun he => hp0nab u hu he.symm
        have hp0v : (p[0]'hp0) ≠ v := fun he => hp0nab v hv he.symm
        have hxtu : x t ≠ u := fun he => hxtnab u hu he.symm
        have hxtv : x t ≠ v := fun he => hxtnab v hv he.symm
        have hc1 : ¬ G.Adj c (x (t + 1)) := fun hadj =>
          (hnoab v hv).1 (kA _ hxt1C hxt1u hxt1v hadj)
        have hc2 : ¬ G.Adj c (p[0]'hp0) := fun hadj =>
          (hnoab v hv).2 (kA _ hp0C hp0u hp0v hadj)
        have hd1 : ¬ G.Adj d (x (t + 1)) := fun hadj =>
          (hnoab u hu).1 (kB _ hxt1C hxt1u hxt1v hadj)
        have hd2 : ¬ G.Adj d (p[0]'hp0) := fun hadj =>
          (hnoab u hu).2 (kB _ hp0C hp0u hp0v hadj)
        have hua : ∀ e : V, G.Adj e u → (G.Adj e a ∨ G.Adj e b) := by
          intro e he
          rcases hu with hf | hf
          · exact Or.inl (hf ▸ he)
          · exact Or.inr (hf ▸ he)
        by_cases hcxt : G.Adj c (x t)
        · exact ⟨d, hdX, hua d kD2, fun hdxt =>
            kC (x t) hxtC (x t) hxtC hxtu hxtv hxtu hxtv hcxt hdxt rfl, hd1, hd2⟩
        · exact ⟨c, hcX, hua c kD1, hcxt, hc1, hc2⟩
      rcases hlp with hl | hl
      · exact hcase a b (Or.inl rfl) (Or.inr rfl) hl
      · exact hcase b a (Or.inr rfl) (Or.inl rfl) hl
  -- 17.1: `F = (V(C) \ {x_t, x_{t+1}}) ∪ {x}` catches the triangle `{z, x_t, x_{t+1}}`
  obtain ⟨hh, hhX, hhab, hhxt, hhxt1, hhp0⟩ := hgood
  have hSnd : S.Nodup := PathBasics.path_nodup hS.1
  have hdrop1 : ∀ w : V, w ∈ S → w ≠ x t → w ∈ S.drop 1 := by
    intro w hw hne
    obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem hw
    have hn0 : n ≠ 0 := by
      intro he
      exact hne (by rw [← hnw, HoleArithmetic.getElem_congr_idx S hn hSpos he, hS0])
    have hlt : n - 1 < (S.drop 1).length := by simp only [List.length_drop]; omega
    have hq := List.getElem_mem hlt
    rw [List.getElem_drop, HoleArithmetic.getElem_congr_idx S
      (show 1 + (n - 1) < S.length by omega) hn (by omega), hnw] at hq
    exact hq
  have hdrop1' : ∀ w ∈ S.drop 1, w ∈ S ∧ w ≠ x t := by
    intro w hw
    refine ⟨List.mem_of_mem_drop hw, ?_⟩
    obtain ⟨n, hn, hnw⟩ := List.getElem_of_mem hw
    simp only [List.length_drop] at hn
    rw [List.getElem_drop] at hnw
    intro he
    have := hSnd.getElem_inj_iff.mp (hnw.trans (he.trans hS0.symm))
    omega
  have htk : ∀ w ∈ p.take (k - 1),
      ∃ (j : ℕ) (hj : j < p.length), j + 1 < k ∧ (p[j]'hj) = w := by
    intro w hw
    obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hw
    simp only [List.length_take] at hj
    exact ⟨j, by omega, by omega, by rw [← hjw, List.getElem_take]⟩
  have htkmem : ∀ (j : ℕ) (hj : j < p.length), j + 1 < k → (p[j]'hj) ∈ p.take (k - 1) := by
    intro j hj hjk
    have hlt : j < (p.take (k - 1)).length := by simp only [List.length_take]; omega
    have hq := List.getElem_mem hlt
    rwa [List.getElem_take] at hq
  have hp0take : (p[0]'hp0) ∈ p.take (k - 1) := htkmem 0 hp0 (by omega)
  have hnonetk : ∀ w ∈ p.take (k - 1), ¬ G.Adj (x t) w := by
    intro w hw
    obtain ⟨j, hj, hjk, hjw⟩ := htk w hw
    refine hjw ▸ hnone _ ?_
    have hlt : j < (p.take k).length := by simp only [List.length_take]; omega
    have hq := List.getElem_mem hlt
    rwa [List.getElem_take] at hq
  have hxt1noS : ∀ w ∈ S.drop 1, ¬ G.Adj (x (t + 1)) w := by
    intro w hw hadjw
    obtain ⟨hwS, hwne⟩ := hdrop1' w hw
    rcases hSmem w hwS with he | he | he
    · exact hwne he
    · have : G.Adj (x (t + 1)) (p[k - 1]'hk1) := by rw [← he]; exact hadjw
      exact absurd ((hxt1p (k - 1) hk1).mp this) (by omega)
    · rcases hSint _ he with hq | hq
      · exact hxt1A w hq hadjw
      · obtain ⟨j, hj, hkj, hjw⟩ := hdropidx _ hq
        have : G.Adj (x (t + 1)) (p[j]'hj) := by rw [hjw]; exact hadjw
        exact absurd ((hxt1p j hj).mp this) (by omega)
  have hzno : ∀ w : V, (w ∈ S.drop 1 ∨ w ∈ p.take (k - 1)) → ¬ G.Adj z w := by
    rintro w (hw | hw)
    · obtain ⟨hwS, hwne⟩ := hdrop1' w hw
      exact WheelSystemBasics.wheelSystemA_no_nbr (hSA w hwS hwne)
    · obtain ⟨j, hj, hjk, hjw⟩ := htk w hw
      exact WheelSystemBasics.wheelSystemA_no_nbr (hjw ▸ hpA _ (List.getElem_mem hj))
  set F : Set V := ({v : V | v ∈ S.drop 1} ∪ {v : V | v ∈ p.take (k - 1)}) ∪ {hh}
    with hFdef
  set T : Set V := ({z, x t, x (t + 1)} : Set V) with hTdef
  have hzxt1 : G.Adj z (x (t + 1)) := hws.2.2.2.2.2.2 (t + 1) le_rfl
  have hzhh : G.Adj z hh := hzc hh hhX
  have hhxtne : hh ≠ x t := by
    obtain ⟨j, hj, rfl⟩ := hhX
    intro he
    have := hws.2.1 j (by omega) t (by omega) he
    omega
  have hhxt1ne : hh ≠ x (t + 1) := by
    obtain ⟨j, hj, rfl⟩ := hhX
    intro he
    have := hws.2.1 j (by omega) (t + 1) le_rfl he
    omega
  have hhzne : hh ≠ z := by
    obtain ⟨j, hj, rfl⟩ := hhX
    exact (hws.2.2.1 j (by omega)).2
  have hpkS : (p[k - 1]'hk1) ∈ S := PathBasics.getLast_mem hS.2.2
  have hpkxt : (p[k - 1]'hk1) ≠ x t := fun he => hxtA (he ▸ hpA _ (List.getElem_mem hk1))
  have hFmem : ∀ w ∈ F, w ∈ S.drop 1 ∨ w ∈ p.take (k - 1) ∨ w = hh := by
    rintro w ((hw | hw) | hw)
    · exact Or.inl hw
    · exact Or.inr (Or.inl hw)
    · exact Or.inr (Or.inr hw)
  have hS1 : 1 < S.length := by omega
  have hSsecond : (S[1]'hS1) ∈ S.drop 1 := hdrop1 _ (List.getElem_mem hS1) (by
    intro he
    have := hSnd.getElem_inj_iff.mp (he.trans hS0.symm)
    omega)
  have hxtS1 : G.Adj (x t) (S[1]'hS1) := by
    have hq := PathBasics.path_adj_succ hS.1 (i := 0) (by omega)
    rw [hS0, HoleArithmetic.getElem_congr_idx S (show 0 + 1 < S.length by omega) hS1 rfl] at hq
    exact hq
  have hxt1p0 : G.Adj (x (t + 1)) (p[0]'hp0) := (hxt1p 0 hp0).mpr rfl
  have hFcon : ConnectedSet G F := by
    refine ConnectedSetUnionAttach.connectedSet_union_singleton ?_ ?_
    · refine ConnectedSetUnionAttach.connectedSet_union
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
          (PathBasics.isPathList_drop hS.1 (k := 1) (by omega)))
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
          (PathBasics.isPathList_take hppath (k := k - 1) (by omega)))
        (Or.inr ⟨p[k - 1]'hk1, hdrop1 _ hpkS hpkxt, p[k - 2]'(by omega),
          htkmem (k - 2) (by omega) (by omega), ?_⟩)
      have hq := PathBasics.path_adj_succ hppath (i := k - 2) (by omega)
      rw [HoleArithmetic.getElem_congr_idx p (show k - 2 + 1 < p.length by omega)
        hk1 (by omega)] at hq
      exact hq.symm
    · rcases hhab with hq | hq
      · exact ⟨a, Or.inl (hdrop1 a (hCcompS a (habmem a (Or.inl rfl)).1
          (habmem a (Or.inl rfl)).2) (hxtnab a (Or.inl rfl))), hq⟩
      · exact ⟨b, Or.inl (hdrop1 b (hCcompS b (habmem b (Or.inr rfl)).1
          (habmem b (Or.inr rfl)).2) (hxtnab b (Or.inr rfl))), hq⟩
  have hFdisj : Disjoint F T := by
    rw [Set.disjoint_left]
    intro w hwF hwT
    simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hwT
    have hkey : w = z ∨ w = x t ∨ w = x (t + 1) := hwT
    rcases hFmem w hwF with hw | hw | he
    · obtain ⟨hwS, hwne⟩ := hdrop1' w hw
      rcases hkey with hf | hf | hf
      · exact hzS (hf ▸ hwS)
      · exact hwne hf
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
          (hf ▸ hSA w hwS hwne)
    · obtain ⟨j, hj, hjk, hjw⟩ := htk w hw
      have hwA : w ∈ wheelSystemA G z A₀ x t := hjw ▸ hpA _ (List.getElem_mem hj)
      rcases hkey with hf | hf | hf
      · exact hzAt (hf ▸ hwA)
      · exact hxtA (hf ▸ hwA)
      · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl (hf ▸ hwA)
    · rcases hkey with hf | hf | hf
      · exact hhzne (he.symm.trans hf)
      · exact hhxtne (he.symm.trans hf)
      · exact hhxt1ne (he.symm.trans hf)
  have hTri : IsTriangle G T := by
    refine ⟨Set.ncard_eq_three.mpr ⟨z, x t, x (t + 1), hzxt.ne, hzxt1.ne, hadj.ne, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact absurd rfl huv
    · exact hzxt
    · exact hzxt1
    · exact hzxt.symm
    · exact absurd rfl huv
    · exact hadj
    · exact hzxt1.symm
    · exact hadj.symm
    · exact absurd rfl huv
  have hFcatch : Catches G F T := by
    refine ⟨hTri, hFcon, hFdisj, ?_⟩
    intro a' ha'
    simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
    rcases ha' with rfl | rfl | rfl
    · exact ⟨hh, Or.inr rfl, hzhh⟩
    · exact ⟨S[1]'hS1, Or.inl (Or.inl hSsecond), hxtS1⟩
    · exact ⟨p[0]'hp0, Or.inl (Or.inr hp0take), hxt1p0⟩
  have hunique : ∀ w ∈ F, G.Adj z w → w = hh := by
    intro w hwF hadjw
    rcases hFmem w hwF with hw | hw | he
    · exact absurd hadjw (hzno w (Or.inl hw))
    · exact absurd hadjw (hzno w (Or.inr hw))
    · exact he
  have hcommon : ∀ w ∈ F, G.Adj hh w → ¬ G.Adj (x (t + 1)) w := by
    intro w hwF hadjw hadj2
    rcases hFmem w hwF with hw | hw | he
    · exact hxt1noS w hw hadj2
    · obtain ⟨j, hj, hjk, hjw⟩ := htk w hw
      have hj0 : j = 0 := (hxt1p j hj).mp (by rw [hjw]; exact hadj2)
      refine hhp0 ?_
      rw [HoleArithmetic.getElem_congr_idx p hp0 hj hj0.symm, hjw]
      exact hadjw
    · exact G.irrefl (he ▸ hadjw)
  have honesub : ∀ (w c : V), (∀ a' ∈ T, G.Adj w a' → a' = c) →
      (G.neighborSet w ∩ T).ncard ≤ 1 := by
    intro w c hsub
    have hss : (G.neighborSet w ∩ T) ⊆ ({c} : Set V) := by
      rintro a' ⟨ha1, ha2⟩
      exact hsub a' ha2 ha1
    calc (G.neighborSet w ∩ T).ncard ≤ ({c} : Set V).ncard :=
          Set.ncard_le_ncard hss (Set.toFinite _)
      _ = 1 := Set.ncard_singleton _
  have hone : ∀ w ∈ F, (G.neighborSet w ∩ T).ncard ≤ 1 := by
    intro w hwF
    rcases hFmem w hwF with hw | hw | he
    · refine honesub _ (x t) ?_
      intro a' ha' hadjw
      simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
      rcases ha' with rfl | rfl | rfl
      · exact absurd hadjw.symm (hzno w (Or.inl hw))
      · rfl
      · exact absurd hadjw.symm (hxt1noS w hw)
    · obtain ⟨j, hj, hjk, hjw⟩ := htk w hw
      by_cases hj0 : j = 0
      · refine honesub _ (x (t + 1)) ?_
        intro a' ha' hadjw
        simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
        rcases ha' with rfl | rfl | rfl
        · exact absurd hadjw.symm (hzno w (Or.inr hw))
        · exact absurd hadjw.symm (hnonetk w hw)
        · rfl
      · refine honesub _ (x t) ?_
        intro a' ha' hadjw
        simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
        rcases ha' with rfl | rfl | rfl
        · exact absurd hadjw.symm (hzno w (Or.inr hw))
        · rfl
        · exact absurd ((hxt1p j hj).mp (by rw [hjw]; exact hadjw.symm)) hj0
    · refine honesub _ z ?_
      intro a' ha' hadjw
      simp only [hTdef, Set.mem_insert_iff, Set.mem_singleton_iff] at ha'
      rcases ha' with rfl | rfl | rfl
      · rfl
      · exact absurd (by rw [← he]; exact hadjw) hhxt
      · exact absurd (by rw [← he]; exact hadjw) hhxt1
  exact Thm212Claim3Tools.catch_obstruction hGF (F := F) (T := T) (u := z)
    (v := x (t + 1)) (z := hh) hFcatch (by simp [hTdef]) (by simp [hTdef]) hzxt1.ne
    hunique hcommon hone

/-- Labelled gap for the hole argument inside 21.2(8), printed p. 134.

PAPER: *"Let `S` be a path between `x_t, p_k` with interior in `A_{t−1} ∪ {p_{k+1},…,p_m}`,
and let `C` be the hole `x_t-x_{t+1}-p₁-⋯-p_k-S-x_t`.  Since `C` is even and `k` is odd, it
follows that `S` is even, and so by (5), some internal vertex of `S` is `X_{t−1}`-complete.
The path `z-x_t-S-p_k` is odd, and its ends are `X_{t−1}`-complete, so by 2.3 it contains an
odd number of `X_{t−1}`-complete edges. … By 2.10 applied to `C`, `X_{t−1}` contains a leap or
hat, and in either case some `x ∈ X_{t−1}` is nonadjacent to all of `x_t, x_{t+1}, p₁`, and
adjacent to `p_k`.  Hence `(V(C) \ {x_t, x_{t+1}}) ∪ {x}` (`= F` say) catches the triangle
`{z, x_t, x_{t+1}}`; the only neighbour of `z` in `F` is `x`; the only neighbour of `x_{t+1}`
in `F` is `p₁`; and `x, p₁` are nonadjacent, and are both nonadjacent to `x_t`, contrary to
17.1."*

`hnone` is the assumption for contradiction of (8), and `hadj` is the sentence *"From the
definition of `i` it follows that `x_t` is adjacent to `x_{t+1}`"*, which is proved below. -/
theorem claim8_hole_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s k : ℕ}
    (hp : GoodPath G z A₀ x t p) (hext : Extended G z A₀ x t p q i s)
    (hik : i ≤ k) (hk3 : 3 ≤ k) (hkm : k ≤ p.length)
    (hP : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1])
    (hkeven : Even (pathLength (z :: x (t + 1) :: p.take k)))
    (hc5 : OddReturnPaths G z A₀ x t p)
    (hnone : ∀ v ∈ p.take k, ¬ G.Adj (x t) v)
    (hadj : G.Adj (x t) (x (t + 1))) : False := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  have hk1 : k - 1 < p.length := by omega
  have hpne : 0 < p.length := by omega
  have hMlt : p.length - 1 < p.length := by omega
  have hppath : IsPathList G p := by
    have hh := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using hh
  have hpnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hpA1 : ∀ v ∈ p, v ∉ wheelSystemA G z A₀ x (t - 1) := fun v hv => (hp.2.2.1 v hv).2
  have hxt1p : ∀ (j : ℕ) (hj : j < p.length), G.Adj (x (t + 1)) (p[j]'hj) ↔ j = 0 := by
    intro j hj
    have hh := hp.1.2.2 0 (j + 1) (by simp) (by simp only [List.length_cons]; omega)
    have h0 : (x (t + 1) :: p)[0]'(by simp) = x (t + 1) := rfl
    have hj1 : (x (t + 1) :: p)[j + 1]'(by simp only [List.length_cons]; omega) = p[j]'hj := rfl
    rw [h0, hj1] at hh
    rw [hh]; omega
  -- `k` is odd
  have hkodd : Odd k := by
    have hlen : pathLength (z :: x (t + 1) :: p.take k) = k + 1 := by
      simp only [pathLength, List.length_cons, List.length_take]
      omega
    rw [hlen] at hkeven
    obtain ⟨d, hd⟩ := hkeven
    exact ⟨d - 1, by omega⟩
  -- `p_k` is `X_{t-1}`-complete
  have hpkmem : (p[k - 1]'hk1) ∈ (z :: x (t + 1) :: p.take k) := by
    refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
    have hlt : k - 1 < (p.take k).length := by simp only [List.length_take]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_take] at hh
  have hpkc : VertexComplete G (p[k - 1]'hk1) (wheelSystemX x (t - 1)) :=
    (hP.completeEnds _ hpkmem).mpr (Or.inr rfl)
  -- the connected set `A_{t-1} ∪ {p_{k+1},…,p_m}`
  have hFcon : ConnectedSet G (wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop k}) :=
    goodPath_suffix_connected h hp k
  have hxtA : x t ∉ wheelSystemA G z A₀ x t :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
  have hxtA1 : x t ∉ wheelSystemA G z A₀ x (t - 1) :=
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega)
  have hdropmem : ∀ (j : ℕ) (hj : j < p.length), k ≤ j → (p[j]'hj) ∈ p.drop k := by
    intro j hj hkj
    have hlt : j - k < (p.drop k).length := by simp only [List.length_drop]; omega
    have hh := List.getElem_mem hlt
    rwa [List.getElem_drop, HoleArithmetic.getElem_congr_idx p
      (show k + (j - k) < p.length by omega) hj (by omega)] at hh
  have hdropidx : ∀ v ∈ p.drop k, ∃ (j : ℕ) (hj : j < p.length), k ≤ j ∧ (p[j]'hj) = v := by
    intro v hv
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    simp only [List.length_drop] at hj
    refine ⟨k + j, by omega, by omega, ?_⟩
    rw [← hjv, List.getElem_drop]
  have hxtF : x t ∉ wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop k} := by
    rintro (hv | hv)
    · exact hxtA1 hv
    · exact hxtA (hpA _ (List.mem_of_mem_drop hv))
  have hpkF : (p[k - 1]'hk1) ∉ wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop k} := by
    rintro (hv | hv)
    · exact hpA1 _ (List.getElem_mem hk1) hv
    · obtain ⟨j, hj, hkj, hjv⟩ := hdropidx _ hv
      have := hpnd.getElem_inj_iff.mp hjv
      omega
  -- `x_t` and `p_k` both have neighbours in that set
  obtain ⟨B, hB0, hBcon, hBadj, hBz, hBX⟩ := hws.2.2.2.2.1 t (by omega) (by omega)
  have hxtnbr : ∃ f ∈ wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop k},
      G.Adj (x t) f := by
    obtain ⟨a, ha, hadja⟩ := WheelSystemBasics.exists_adj_wheelSystemA_of_witness
      (i := t - 1) hB0 hBcon hBz hBX hBadj
    exact ⟨a, Or.inl ha, hadja⟩
  have hpknbr : ∃ f ∈ wheelSystemA G z A₀ x (t - 1) ∪ {v : V | v ∈ p.drop k},
      G.Adj (p[k - 1]'hk1) f := by
    rcases Nat.lt_or_ge (k - 1 + 1) p.length with hlt | hge
    · refine ⟨p[k]'(by omega), Or.inr (hdropmem k (by omega) le_rfl), ?_⟩
      have hh := PathBasics.path_adj_succ hppath (i := k - 1) (by omega)
      rwa [HoleArithmetic.getElem_congr_idx p (show k - 1 + 1 < p.length by omega)
        (show k < p.length by omega) (by omega)] at hh
    · obtain ⟨a, ha, hadja⟩ := (hp.2.2.2 (k - 1) hk1).mpr (by omega)
      exact ⟨a, Or.inl ha, hadja⟩
  obtain ⟨S, hS, hSint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFcon hxtF hpkF hxtnbr hpknbr
  have hSint' : ∀ v ∈ SPGT.interior S,
      v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p.drop k := hSint
  -- the hole `x_t-x_{t+1}-p₁-⋯-p_k-S-x_t`
  have hbaseeq : (x (t + 1) :: p).take k = x (t + 1) :: p.take (k - 1) := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp
  have hLidx : (x (t + 1) :: p)[k - 1]'(by simp only [List.length_cons]; omega)
      = p[k - 2]'(show k - 2 < p.length by omega) := by
    have h2 : k - 1 = (k - 2) + 1 := by omega
    simp only [h2, List.getElem_cons_succ]
  have hbase : IsPathFrom G (x (t + 1) :: p.take (k - 1)) (x (t + 1))
      (p[k - 2]'(show k - 2 < p.length by omega)) := by
    have hh := PathBasics.isPathFrom_slice hp.1 (i := 0) (j := k - 1)
      (show 0 < k - 1 by omega) (show k - 1 < (x (t + 1) :: p).length by
        simp only [List.length_cons]; omega)
    simp only [List.drop_zero, Nat.sub_zero] at hh
    rw [show k - 1 + 1 = k from by omega, hbaseeq, hLidx] at hh
    exact hh
  have hRp : IsPathFrom G ((x (t + 1) :: p.take (k - 1)).reverse) (p[k - 2]'(by omega))
      (x (t + 1)) := PathBasics.isPathFrom_reverse hbase
  have hRmem : ∀ v ∈ (x (t + 1) :: p.take (k - 1)).reverse,
      v = x (t + 1) ∨ ∃ (j : ℕ) (hj : j < p.length), j + 1 < k ∧ (p[j]'hj) = v := by
    intro v hv
    rcases List.mem_cons.mp (List.mem_reverse.mp hv) with he | hv'
    · exact Or.inl he
    · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv'
      simp only [List.length_take] at hj
      exact Or.inr ⟨j, by omega, by omega, by rw [← hjv, List.getElem_take]⟩
  have hSmem : ∀ v ∈ S, v = x t ∨ v = (p[k - 1]'hk1) ∨ v ∈ SPGT.interior S := by
    intro v hv
    rcases eq_or_ne v (x t) with he | h1
    · exact Or.inl he
    rcases eq_or_ne v (p[k - 1]'hk1) with he | h2
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hS).mpr ⟨hv, h1, h2⟩))
  have hpkne : (p[k - 1]'hk1) ≠ x (t + 1) :=
    fun he => Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
      (he ▸ hpA _ (List.getElem_mem hk1))
  have hxtnep : ∀ (j : ℕ) (hj : j < p.length), x t ≠ (p[j]'hj) :=
    fun j hj he => hxtA (he ▸ hpA _ (List.getElem_mem hj))
  have hcross : ∀ a ∈ S, ∀ b ∈ (x (t + 1) :: p.take (k - 1)).reverse,
      (G.Adj a b ↔ (a = (p[k - 1]'hk1) ∧ b = (p[k - 2]'(by omega))) ∨
        (a = x t ∧ b = x (t + 1))) := by
    intro a ha b hb
    constructor
    · intro hab
      rcases hSmem a ha with rfl | rfl | hain
      · rcases hRmem b hb with rfl | ⟨j, hj, hjk, rfl⟩
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd hab (hnone _ (by
            have hlt : j < (p.take k).length := by simp only [List.length_take]; omega
            have hh := List.getElem_mem hlt
            rwa [List.getElem_take] at hh))
      · rcases hRmem b hb with rfl | ⟨j, hj, hjk, rfl⟩
        · exact absurd ((hxt1p (k - 1) hk1).mp hab.symm) (by omega)
        · refine Or.inl ⟨rfl, ?_⟩
          have := (hppath.2.2 (k - 1) j hk1 hj).mp hab
          exact HoleArithmetic.getElem_congr_idx p hj (by omega) (by omega)
      · exfalso
        rcases hSint' a hain with haA | haD
        · rcases hRmem b hb with rfl | ⟨j, hj, hjk, rfl⟩
          · exact hxt1A a haA hab.symm
          · exact (hp.2.2.2 j hj).not.mpr (by omega) ⟨a, haA, hab.symm⟩
        · obtain ⟨j', hj', hkj', rfl⟩ := hdropidx _ haD
          rcases hRmem b hb with rfl | ⟨j, hj, hjk, rfl⟩
          · exact absurd ((hxt1p j' hj').mp hab.symm) (by omega)
          · have := (hppath.2.2 j' j hj' hj).mp hab
            omega
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · have hh := PathBasics.path_adj_succ hppath (i := k - 2) (by omega)
        rw [HoleArithmetic.getElem_congr_idx p (show k - 2 + 1 < p.length by omega)
          hk1 (by omega)] at hh
        exact hh.symm
      · exact hadj
  have hdisjSR : ∀ a ∈ S, a ∉ (x (t + 1) :: p.take (k - 1)).reverse := by
    intro a ha hb
    rcases hRmem a hb with he | ⟨j, hj, hjk, hje⟩
    · rcases hSmem a ha with h1 | h1 | h1
      · have := hws.2.1 t (by omega) (t + 1) le_rfl (h1.symm.trans he)
        omega
      · exact hpkne (h1.symm.trans he)
      · rcases hSint' a h1 with hh | hh
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl (he ▸ hh)
        · exact Thm203Prelim.x_notMem_wheelSystemA hws (j := t + 1) le_rfl
            (he ▸ hpA _ (List.mem_of_mem_drop hh))
    · rcases hSmem a ha with h1 | h1 | h1
      · exact hxtnep j hj (h1 ▸ hje.symm)
      · have := hpnd.getElem_inj_iff.mp (hje.trans h1)
        omega
      · rcases hSint' a h1 with hh | hh
        · exact hpA1 _ (List.getElem_mem hj) (hje ▸ hh)
        · obtain ⟨j', hj', hkj', hj'e⟩ := hdropidx _ hh
          have := hpnd.getElem_inj_iff.mp (hj'e.trans hje.symm)
          omega
  have hSlen : 2 ≤ S.length := by
    have := PathBasics.path_length_pos hS.1
    have hne : x t ≠ (p[k - 1]'hk1) := hxtnep _ hk1
    by_contra hcon
    have h1 : S.length = 1 := by omega
    have h0 := PathBasics.getElem_zero_of_head? hS.2.1 (by omega)
    have hl := PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)
    rw [HoleArithmetic.getElem_congr_idx S (show S.length - 1 < S.length by omega)
      (show 0 < S.length by omega) (by omega)] at hl
    exact hne (h0 ▸ hl)
  have hC : IsHoleList G (S ++ (x (t + 1) :: p.take (k - 1)).reverse) :=
    PathGlue.glue_hole hS hRp hdisjSR hcross (by
      simp only [List.length_reverse, List.length_cons, List.length_take]
      omega)
  -- `C` is even and `k` is odd, so `S` is even
  have hCeven : Even (S ++ (x (t + 1) :: p.take (k - 1)).reverse).length := by
    have := hBerge.1 _ hC
    simpa [holeLength] using this
  have hSeven : Even (pathLength S) := by
    have hlenR : ((x (t + 1) :: p.take (k - 1)).reverse).length = k := by
      simp only [List.length_reverse, List.length_cons, List.length_take]; omega
    rw [List.length_append, hlenR] at hCeven
    obtain ⟨d, hd⟩ := hCeven
    obtain ⟨e, he⟩ := hkodd
    have hpl := PathBasics.pathLength_eq S
    exact ⟨d - e - 1, by omega⟩
  -- by (5), some internal vertex of `S` is `X_{t-1}`-complete
  have hSc : ∃ v ∈ SPGT.interior S, VertexComplete G v (wheelSystemX x (t - 1)) := by
    by_contra hcon
    push_neg at hcon
    have huniq : ∀ v ∈ S, VertexComplete G v (wheelSystemX x (t - 1)) ↔
        v = (p[k - 1]'hk1) := by
      intro v hv
      constructor
      · intro hvc
        rcases hSmem v hv with rfl | he | hin
        · exact absurd hvc (hws.2.2.2.2.2.1 t (by omega) (by omega))
        · exact he
        · exact absurd hvc (hcon v hin)
      · rintro rfl; exact hpkc
    have hin : ∀ v ∈ S, v ≠ x t → v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
      intro v hv hvne
      rcases hSmem v hv with he | he | hin
      · exact absurd he hvne
      · exact Or.inr (he ▸ List.getElem_mem hk1)
      · rcases hSint' v hin with hh | hh
        · exact Or.inl hh
        · exact Or.inr (List.mem_of_mem_drop hh)
    obtain ⟨hodd, -⟩ := hc5 S _ hS huniq hin
    exact (Nat.not_odd_iff_even.mpr hSeven) hodd
  exact claim8_count h hp hk3 hkm hkodd hadj hnone hS hSint' hSeven hSc hP hC

/-- Labelled gap for 21.2(8), p. 134.
PAPER: "`x_t` is adjacent to one of `p₁,…,p_k`."
Here `p_k` is the first complete vertex, and the prefix has even length by (7). -/
theorem endgame_claim8_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s k : ℕ}
    (hp : GoodPath G z A₀ x t p) (hext : Extended G z A₀ x t p q i s)
    (hik : i ≤ k) (hk3 : 3 ≤ k) (hkm : k ≤ p.length)
    (hP : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1])
    (hkeven : Even (pathLength (z :: x (t + 1) :: p.take k)))
    (hc5 : OddReturnPaths G z A₀ x t p) :
    ∃ v ∈ p.take k, G.Adj (x t) v := by
  classical
  by_contra hcon0
  have hcon : ∀ v ∈ p.take k, ¬ G.Adj (x t) v := by
    intro v hv hva
    exact hcon0 ⟨v, hv, hva⟩
  obtain ⟨hpref, hq, hqAt, hcov, hi2, hiq, hst, hsnone, hcover⟩ := id hext
  have hadj : G.Adj (x t) (x (t + 1)) := by
    obtain ⟨w, hw, hadjw⟩ := hcover t le_rfl
    have hsplit : (x (t + 1) :: q).take (i + 1) = x (t + 1) :: q.take i := by simp
    rw [hsplit] at hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hadjw
    · exfalso
      obtain ⟨l, hl, hlw⟩ := List.mem_iff_getElem.mp hw
      have hllen : l < (q.take i).length := hl
      simp only [List.length_take] at hllen
      have hlp : l < p.length := by omega
      have hlq : l < q.length := by omega
      have hqp : q[l]'hlq = p[l]'hlp := (hpref.getElem hlp).symm
      have hwq : q[l]'hlq = w := by rw [← hlw, List.getElem_take]
      have hmem : p[l]'hlp ∈ p.take k := by
        have hlt : l < (p.take k).length := by simp only [List.length_take]; omega
        have := List.getElem_mem hlt
        rwa [List.getElem_take] at this
      refine hcon _ hmem ?_
      rw [← hqp, hwq]
      exact hadjw
  exact claim8_hole_gap h hp hext hik hk3 hkm hP hkeven hc5 hcon hadj

/-- Labelled gap for the edge count in 21.2's final paragraph, printed p. 135.

PAPER: *"So we may assume that `p_j` is not `Y`-complete.  Now the path `x_t-p_j-⋯-p_k` has odd
length `≥ 3`, and both its ends are `Y`-complete, and the `Y`-complete vertex `z` has no
neighbour in its interior, so by 2.2 and 2.3, an odd number of its edges are `Y`-complete.
Since `p_j` is not `Y`-complete, an odd number of edges of `p_j-⋯-p_k` are `Y`-complete.  The
path `z-x_{t+1}-p₁-⋯-p_k` (`= P` say) is even, by (7), and since its ends are `Y`-complete, it
follows that an even number of its edges are `Y`-complete, by 2.3.  We deduce that an odd
number of edges of `z-x_{t+1}-p₁-⋯-p_j` are `Y`-complete.  There is therefore a `Y`-segment
`P'` of this path that has odd length.  Since `p_j` is not `Y`-complete, it follows that `P'`
is also a `Y`-segment of `P`."*

The paper's `p_j` is the entry `p[J]` with `J = j - 1`; `hJmax` is the maximality of `j`,
`hJodd` is *"`k − j` is even"* from (5), and the conclusion is the `Y`-segment `P'`, which
`Thm212EndgameTools.alternatives_of_oddRun` then feeds to 21.1. -/
theorem parity_oddRun_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V} {k J : ℕ}
    (hp : GoodPath G z A₀ x t p) (hk3 : 3 ≤ k) (hkm : k ≤ p.length)
    (hP : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1])
    (hkeven : Even (pathLength (z :: x (t + 1) :: p.take k)))
    (hkcY : VertexComplete G p[k - 1] Y)
    (hJk : J + 2 ≤ k) (hJp : J < p.length) (hJadj : G.Adj (x t) p[J])
    (hJmax : ∀ l (hl : l < p.length), J < l → l < k → ¬ G.Adj (x t) p[l])
    (hJodd : Odd (k - J)) (hJnY : ¬ VertexComplete G p[J] Y)
    (hc5 : OddReturnPaths G z A₀ x t p) :
    Thm212EndgameTools.OddRun G Y (z :: x (t + 1) :: p.take k) := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hBerge : Berge G := hGF.1.1.1.1
  have hAY : AnticonnectedSet G Y := hhub.2.2.1
  have hzY : VertexComplete G z Y := hhub.2.2.2.2.1
  have hxtY : VertexComplete G (x t) Y := hhub.2.2.2.2.2.1 t (by omega)
  have hppath : IsPathList G p := by
    have := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using this
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hk1p : k - 1 < p.length := by omega
  set P : List V := z :: x (t + 1) :: p.take k with hPdef
  have hPlen : P.length = k + 2 := by
    simp only [hPdef, List.length_cons, List.length_take]
    omega
  have hPget : ∀ (i : ℕ) (hi : i < k) (hi2 : i + 2 < P.length),
      P[i + 2]'hi2 = p[i]'(by omega) := by
    intro i hi hi2
    simp only [hPdef, List.getElem_cons_succ, List.getElem_take]
  have hP0 : P[0]'(by omega) = z := rfl
  have hP1 : P[1]'(by omega) = x (t + 1) := rfl
  set f : ℕ → Prop := Thm212RunParity.VC G Y P with hfdef
  have hfget : ∀ (i : ℕ) (hi : i < P.length), (f i ↔ VertexComplete G (P[i]'hi) Y) :=
    fun i hi => Thm212RunParity.vc_iff_getElem hi
  have hf1 : ¬ f 1 := by
    rw [hfget 1 (by omega), hP1]
    exact hhub.2.2.2.2.2.2
  have hfJ : ¬ f (J + 2) := by
    rw [hfget (J + 2) (by omega), hPget J (by omega) (by omega)]
    exact hJnY
  -- *"The path `z-x_{t+1}-p₁-⋯-p_k` (`= P` say) is even, by (7), and since its ends are
  -- `Y`-complete, it follows that an even number of its edges are `Y`-complete, by 2.3."*
  have hnotY : ∀ w ∈ P, w ∉ Y := fun w hw => (hP.outside w hw).2
  have hPlast : P[P.length - 1]'(by omega) = p[k - 1] :=
    PathBasics.getElem_last_of_getLast? hP.path.2.2 (by omega)
  have hlen4 : 4 ≤ pathLength P := hP.length
  have hzp : ¬ G.Adj z (p[k - 1]) := by
    have hh := PathBasics.path_ends_not_adj hP.path.1 (by simp only [pathLength] at hlen4; omega)
    rwa [hP0, hPlast] at hh
  have h23P := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hAY P
      (Or.inl hP.path.1) hnotY).1 P z (p[k - 1])
      (Or.inl ⟨hP.path.1, List.infix_refl P⟩) hP.path hzY hkcY
  have hyEven : Even {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := by
    rcases h23P with hpar | honly
    · rw [Nat.even_iff, hpar, ← Nat.even_iff]
      exact hkeven
    · have hempty : {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G Y u v} = ∅ := by
        ext e
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨u, hu, v, hv, rfl, hE⟩
        have hu' := honly u hu hE.2.1
        have hv' := honly v hv hE.2.2
        have hne : u ≠ v := hE.1.ne
        rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
        · exact hne rfl
        · exact hzp hE.1
        · exact hzp hE.1.symm
        · exact hne rfl
      rw [hempty]
      simp
  rw [Thm212RunParity.ncard_yEdges_eq_pEdges hP.path.1, Thm212RunParity.pEdges, hPlen,
    show k + 2 - 1 = k + 1 by omega] at hyEven
  -- *"Now the path `x_t-p_j-⋯-p_k` has odd length `≥ 3`, and both its ends are `Y`-complete,
  -- and the `Y`-complete vertex `z` has no neighbour in its interior, so by 2.2 and 2.3, an
  -- odd number of its edges are `Y`-complete."*
  set D : List V := (p.drop J).take (k - 1 - J + 1) with hDdef
  have hDlen : D.length = k - J := by
    rw [hDdef, PathBasics.length_slice p (by omega) hk1p]
    omega
  have hDpath : IsPathFrom G D (p[J]) (p[k - 1]) :=
    PathBasics.isPathFrom_slice hppath (by omega) hk1p
  have hDmem : ∀ w ∈ D, ∃ (l : ℕ) (hl : l < p.length), J ≤ l ∧ l ≤ k - 1 ∧ p[l] = w :=
    fun w hw => (PathBasics.mem_slice_iff p (by omega) hk1p).mp hw
  have hxtnotp : x t ∉ p := fun hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (hpA _ hm)
  have hxtnotD : x t ∉ D := by
    intro hm
    obtain ⟨l, hl, -, -, he⟩ := hDmem _ hm
    exact hxtnotp (he ▸ List.getElem_mem hl)
  have hDother : ∀ w ∈ D, w ≠ p[J] → ¬ G.Adj (x t) w := by
    intro w hw hne
    obtain ⟨l, hl, h1, h2, rfl⟩ := hDmem _ hw
    have hlJ : l ≠ J := fun he => hne (HoleArithmetic.getElem_congr_idx p hl hJp he)
    exact hJmax l hl (by omega) (by omega)
  set Q : List V := x t :: D with hQdef
  have hQpath : IsPathFrom G Q (x t) (p[k - 1]) :=
    PathAttach.isPathFrom_cons hDpath hJadj hxtnotD hDother
  have hQlen : Q.length = k - J + 1 := by
    simp only [hQdef, List.length_cons, hDlen]
  have hQodd : Odd (pathLength Q) := by
    simpa only [pathLength, hQlen, Nat.add_sub_cancel] using hJodd
  have hQnotY : ∀ w ∈ Q, w ∉ Y := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact fun hm => G.irrefl (hxtY _ hm)
    · obtain ⟨l, hl, -, -, rfl⟩ := hDmem _ hw
      exact fun hm => Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1 (j := t) (by omega)
        hm (hpA _ (List.getElem_mem hl))
  have hedgeQ : ∃ u ∈ Q, ∃ v ∈ Q, EdgeComplete G Y u v := by
    by_contra hno
    obtain ⟨w, hwint, hzw⟩ := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hAY Q
      (x t) (p[k - 1]) hQpath hQnotY hQodd hxtY hkcY hno z hzY
    have hd := (PathBasics.mem_interior_iff_of_pathFrom hQpath).mp hwint
    rcases List.mem_cons.mp hd.1 with he | hw
    · exact hd.2.1 he
    · obtain ⟨l, hl, -, -, rfl⟩ := hDmem _ hw
      exact WheelSystemBasics.wheelSystemA_no_nbr (hpA _ (List.getElem_mem hl)) hzw
  have hQ0 : Q[0]'(by omega) = x t := rfl
  have hQlast : Q[Q.length - 1]'(by omega) = p[k - 1] :=
    PathBasics.getElem_last_of_getLast? hQpath.2.2 (by omega)
  have hxtnadj : ¬ G.Adj (x t) (p[k - 1]) := by
    have hh := PathBasics.path_ends_not_adj hQpath.1 (by omega)
    rwa [hQ0, hQlast] at hh
  have h23Q := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hAY Q
      (Or.inl hQpath.1) hQnotY).1 Q (x t) (p[k - 1])
      (Or.inl ⟨hQpath.1, List.infix_refl Q⟩) hQpath hxtY hkcY
  have hQcount :
      Odd {e : Sym2 V | ∃ u ∈ Q, ∃ v ∈ Q, e = s(u, v) ∧ EdgeComplete G Y u v}.ncard := by
    rcases h23Q with hpar | honly
    · rw [Nat.odd_iff, hpar, ← Nat.odd_iff]
      exact hQodd
    · exfalso
      obtain ⟨u, hu, v, hv, hE⟩ := hedgeQ
      have hu' := honly u hu hE.2.1
      have hv' := honly v hv hE.2.2
      have hne : u ≠ v := hE.1.ne
      rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
      · exact hne rfl
      · exact hxtnadj hE.1
      · exact hxtnadj hE.1.symm
      · exact hne rfl
  rw [Thm212RunParity.ncard_yEdges_eq_pEdges hQpath.1, Thm212RunParity.pEdges, hQlen,
    Nat.add_sub_cancel] at hQcount
  -- *"We deduce that an odd number of edges of `z-x_{t+1}-p₁-⋯-p_j` are `Y`-complete."*
  set g : ℕ → Prop := Thm212RunParity.VC G Y Q with hgdef
  have hQget : ∀ (i : ℕ) (hi1 : i + 1 < Q.length),
      Q[i + 1]'hi1 = p[J + i]'(by simp only [hQlen] at hi1; omega) := by
    intro i hi1
    simp only [hQdef, List.getElem_cons_succ, hDdef]
    have hi1' : i + 1 < k - J + 1 := by rw [← hQlen]; exact hi1
    exact PathBasics.getElem_slice' p
      (by rw [PathBasics.length_slice p (by omega) hk1p]; omega) (by omega) rfl
  have hgiff : ∀ (i : ℕ), 1 ≤ i → i ≤ k - J → (g i ↔ f (i + (J + 1))) := by
    intro i h1 h2
    obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
    have hiQ : m + 1 < Q.length := by rw [hQlen]; omega
    have hiP : m + 1 + (J + 1) < P.length := by rw [hPlen]; omega
    rw [hgdef, Thm212RunParity.vc_iff_getElem hiQ, hfget _ hiP]
    have e1 : Q[m + 1]'hiQ = p[J + m]'(by omega) := hQget m hiQ
    have e2 : P[m + 1 + (J + 1)]'hiP = p[J + m]'(by omega) := by
      rw [HoleArithmetic.getElem_congr_idx P hiP
        (show J + m + 2 < P.length by rw [hPlen]; omega) (by omega)]
      exact hPget (J + m) (by omega) (by omega)
    rw [e1, e2]
  have hgn1 : ¬ g 1 := by
    rw [hgiff 1 le_rfl (by omega), show 1 + (J + 1) = J + 2 by omega]
    exact hfJ
  have hIco : ((Finset.Ico (J + 2) (k + 1)).filter (fun i => f i ∧ f (i + 1))).card
      = ((Finset.Ico 1 (k - J)).filter (fun i => g i ∧ g (i + 1))).card := by
    have hfg : ∀ i, 1 ≤ i → i < k - J →
        ((f (i + (J + 1)) ∧ f (i + (J + 1) + 1)) ↔ (g i ∧ g (i + 1))) := by
      intro i h1 h2
      rw [hgiff i h1 (by omega), hgiff (i + 1) (by omega) (by omega),
        show i + 1 + (J + 1) = i + (J + 1) + 1 by omega]
    have hsh := Thm212RunParity.card_Ico_filter_shift f g 1 (k - J) (J + 1) hfg
    rwa [show 1 + (J + 1) = J + 2 by omega, show k - J + (J + 1) = k + 1 by omega] at hsh
  have hsplitP := Thm212RunParity.runEdges_split f (a := J + 2) (b := k + 1) (by omega)
  have hsplitQ := Thm212RunParity.runEdges_split g (a := 1) (b := k - J) (by omega)
  have hg1 : Thm212RunParity.runEdges g 1 = 0 := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, Thm212RunParity.runEdges_succ,
      Thm212RunParity.runEdges_zero, if_neg (fun hc => hgn1 hc.2)]
  rw [hg1, hIco.symm, Nat.zero_add] at hsplitQ
  have hoddJ : Odd (Thm212RunParity.runEdges f (J + 2)) := by
    rw [Nat.odd_iff]
    rw [Nat.even_iff, hsplitP] at hyEven
    rw [Nat.odd_iff, hsplitQ] at hQcount
    omega
  -- *"There is therefore a `Y`-segment `P'` of this path that has odd length."*
  obtain ⟨l, r, hlr, hrn, hoddlr, hrun, hright, hleft⟩ :=
    Thm212RunParity.exists_odd_run (f := f) hfJ hoddJ
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with rfl | hpos
    · exact absurd (hrun 1 (by omega) (by omega)) hf1
    · omega
  refine ⟨l, r, hl1, hlr, by rw [hPlen]; omega, hoddlr, ?_, ?_, ?_⟩
  · intro j hj h1 h2
    exact (hfget j hj).mp (hrun j h1 h2)
  · intro hc
    rcases hleft with he | hne
    · omega
    · exact hne ((hfget (l - 1) (by rw [hPlen]; omega)).mpr hc)
  · intro hc
    exact hright ((hfget (r + 1) (by rw [hPlen]; omega)).mpr hc)

/-- Labelled gap for the parity count in 21.2's final paragraph, p. 135.
PAPER: "We deduce that an odd number of edges of `z-x_{t+1}-p₁-⋯-p_j`
are `Y`-complete. There is therefore a `Y`-segment `P'` of this path that
has odd length." If `p_j` is complete, the earlier sentence instead applies
21.1 to `z-x_t-p_j-⋯-p_k`; this supplies the left-hand witness. -/
theorem endgame_segment_parity_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p : List V} {k : ℕ}
    (hp : GoodPath G z A₀ x t p) (hk3 : 3 ≤ k) (hkm : k ≤ p.length)
    (hP : Thm212EndgameTools.PathFor211 G (wheelSystemX x (t - 1)) Y
      (z :: x (t + 1) :: p.take k) z p[k - 1])
    (hkeven : Even (pathLength (z :: x (t + 1) :: p.take k)))
    (hkcY : VertexComplete G p[k - 1] Y)
    (hnbr : ∃ v ∈ p.take k, G.Adj (x t) v)
    (hc5 : OddReturnPaths G z A₀ x t p) :
    Thm211Witness G (wheelSystemX x (t - 1)) Y ∨
      Thm212EndgameTools.OddRun G Y (z :: x (t + 1) :: p.take k) := by
  classical
  obtain ⟨hGF, hnops, hframe, ht, hhub, hxt1A, hsub, hyA⟩ := id h
  have hws : IsWheelSystem G z A₀ x (t + 1) := hhub.1
  have hppath : IsPathList G p := by
    have := PathBasics.isPathList_drop hp.1 (k := 1) (by simp; omega)
    simpa using this
  have hnd : p.Nodup := PathBasics.path_nodup hppath
  have hpA : ∀ v ∈ p, v ∈ wheelSystemA G z A₀ x t := fun v hv => (hp.2.2.1 v hv).1
  have hk1p : k - 1 < p.length := by omega
  have hzX : VertexComplete G z (wheelSystemX x (t - 1)) := by
    rintro w ⟨j, hj, rfl⟩
    exact hws.2.2.2.2.2.2 j (by omega)
  have hXY : Complete G (wheelSystemX x (t - 1)) Y := by
    rintro w ⟨j, hj, rfl⟩ y hy
    exact hhub.2.2.2.2.2.1 j (by omega) y hy
  have hzY : z ∉ Y := fun hzy => G.irrefl (hhub.2.2.2.2.1 z hzy)
  have hxtY : VertexComplete G (x t) Y := hhub.2.2.2.2.2.1 t (by omega)
  have hxtnotY : x t ∉ Y := fun hm => G.irrefl (hxtY (x t) hm)
  have hxtnotX : ¬ VertexComplete G (x t) (wheelSystemX x (t - 1)) :=
    hws.2.2.2.2.2.1 t (by omega) (by omega)
  have hxtnotp : x t ∉ p := fun hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws (j := t) (by omega) (hpA _ hm)
  have hmemtake : ∀ l (hl : l < p.length), l < k → p[l] ∈ p.take k := by
    intro l hl hlk
    have hlt : l < (p.take k).length := by simp only [List.length_take]; omega
    have := List.getElem_mem hlt
    rwa [List.getElem_take] at this
  -- only `p_k` is `X_{t-1}`-complete among `p₁,…,p_k`
  have hunique : ∀ l (hl : l < p.length), l < k →
      (VertexComplete G p[l] (wheelSystemX x (t - 1)) ↔ l = k - 1) := by
    intro l hl hlk
    have hmem : p[l] ∈ (z :: x (t + 1) :: p.take k) :=
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (hmemtake l hl hlk))
    rw [hP.completeEnds p[l] hmem]
    constructor
    · rintro (he | he)
      · exfalso
        have hz : p[l] ∈ wheelSystemA G z A₀ x t := hpA p[l] (List.getElem_mem hl)
        rw [he] at hz
        exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) hz
      · exact hnd.getElem_inj_iff.mp he
    · intro he
      exact Or.inr (HoleArithmetic.getElem_congr_idx p hl hk1p he)
  -- choose the largest neighbour index
  obtain ⟨v0, hv0, hv0a⟩ := hnbr
  obtain ⟨l0, hl0, hl0v⟩ := List.mem_iff_getElem.mp hv0
  have hl0len : l0 < (p.take k).length := hl0
  simp only [List.length_take] at hl0len
  have hl0p : l0 < p.length := by omega
  have hl0adj : G.Adj (x t) p[l0] := by
    rw [show p[l0]'hl0p = v0 by rw [← hl0v, List.getElem_take]]; exact hv0a
  set Pr : ℕ → Prop := fun l => l < k ∧ ∃ hl : l < p.length, G.Adj (x t) p[l] with hPr
  have hl0P : Pr l0 := ⟨by omega, hl0p, hl0adj⟩
  set J := Nat.findGreatest Pr (k - 1) with hJdef
  have hPJ : Pr J := Nat.findGreatest_spec (m := l0) (by omega) hl0P
  have hJle : J ≤ k - 1 := Nat.findGreatest_le _
  have hJmax0 : ∀ l, J < l → l ≤ k - 1 → ¬ Pr l := fun l h1 h2 =>
    Nat.findGreatest_is_greatest h1 h2
  obtain ⟨hJk0, hJp, hJadj⟩ := hPJ
  have hJmax : ∀ l (hl : l < p.length), J < l → l < k → ¬ G.Adj (x t) p[l] := by
    intro l hl h1 h2 hcon
    exact hJmax0 l h1 (by omega) ⟨h2, hl, hcon⟩
  -- `J ≠ k - 1`
  have hJne : J + 2 ≤ k := by
    by_contra hcon
    have hJk1 : J = k - 1 := by omega
    have hpair : IsPathFrom G [x t, p[k - 1]] (x t) p[k - 1] := by
      refine ⟨PathBasics.isPathList_pair ?_, rfl, rfl⟩
      rw [← HoleArithmetic.getElem_congr_idx p hJp hk1p hJk1]; exact hJadj
    have hu : ∀ v ∈ [x t, p[k - 1]],
        VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = p[k - 1] := by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · refine ⟨fun hc => (hxtnotX hc).elim, fun he => ?_⟩
        exfalso
        apply hxtnotp
        rw [he]
        exact List.getElem_mem hk1p
      · exact ⟨fun _ => rfl, fun _ => (hunique (k - 1) hk1p (by omega)).mpr rfl⟩
    have hins : ∀ v ∈ [x t, p[k - 1]], v ≠ x t →
        v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
      intro v hv hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl
      · exact (hne rfl).elim
      · exact Or.inr (List.getElem_mem hk1p)
    have hlen := (hc5 [x t, p[k - 1]] p[k - 1] hpair hu hins).2
    norm_num [pathLength] at hlen
  -- the stretch `p_{J+1}-⋯-p_k`
  set S : List V := (p.drop J).take (k - 1 - J + 1) with hS
  have hSpath : IsPathFrom G S p[J] p[k - 1] := by
    rw [hS]; exact PathBasics.isPathFrom_slice hppath (by omega) hk1p
  have hSlen : S.length = k - J := by
    rw [hS, PathBasics.length_slice p (i := J) (j := k - 1) (by omega) hk1p]; omega
  have hSmem : ∀ w ∈ S, ∃ (l : ℕ) (hl : l < p.length), J ≤ l ∧ l ≤ k - 1 ∧ p[l] = w := by
    intro w hw
    rw [hS] at hw
    exact (PathBasics.mem_slice_iff p (i := J) (j := k - 1) (by omega) hk1p).mp hw
  have hxtnotS : x t ∉ S := by
    intro hm
    obtain ⟨l, hl, _, _, hlw⟩ := hSmem _ hm
    exact hxtnotp (by rw [← hlw]; exact List.getElem_mem hl)
  have hR : IsPathFrom G (x t :: S) (x t) p[k - 1] := by
    refine PathAttach.isPathFrom_cons hSpath hJadj hxtnotS ?_
    intro w hw hne
    obtain ⟨l, hl, hlJ, hlk, hlw⟩ := hSmem w hw
    have hlne : l ≠ J := by
      intro hcon
      exact hne (by rw [← hlw]; exact HoleArithmetic.getElem_congr_idx p hl hJp hcon)
    rw [← hlw]
    exact hJmax l hl (by omega) (by omega)
  have hRlen : pathLength (x t :: S) = k - J := by
    simp only [pathLength, List.length_cons, hSlen]; omega
  have huniqR : ∀ v ∈ (x t :: S),
      VertexComplete G v (wheelSystemX x (t - 1)) ↔ v = p[k - 1] := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · refine ⟨fun hc => (hxtnotX hc).elim, fun he => ?_⟩
      exfalso; apply hxtnotp; rw [he]; exact List.getElem_mem hk1p
    · obtain ⟨l, hl, hlJ, hlk, hlw⟩ := hSmem v hv
      subst hlw
      rw [hunique l hl (by omega)]
      exact ⟨fun he => HoleArithmetic.getElem_congr_idx p hl hk1p he,
        fun he => hnd.getElem_inj_iff.mp he⟩
  have hinR : ∀ v ∈ (x t :: S), v ≠ x t →
      v ∈ wheelSystemA G z A₀ x (t - 1) ∨ v ∈ p := by
    intro v hv hne
    rcases List.mem_cons.mp hv with rfl | hv
    · exact (hne rfl).elim
    · obtain ⟨l, hl, _, _, hlw⟩ := hSmem v hv
      exact Or.inr (by rw [← hlw]; exact List.getElem_mem hl)
  obtain ⟨hoddR, hlenR⟩ := hc5 (x t :: S) p[k - 1] hR huniqR hinR
  rw [hRlen] at hoddR hlenR
  by_cases hJY : VertexComplete G p[J] Y
  · left
    have hznot : z ∉ (x t :: S) := by
      intro hm
      rcases List.mem_cons.mp hm with he | hm
      · exact (hws.2.2.1 t (by omega)).2 he.symm
      · obtain ⟨l, hl, _, _, hlw⟩ := hSmem _ hm
        have hz : p[l] ∈ wheelSystemA G z A₀ x t := hpA p[l] (List.getElem_mem hl)
        rw [hlw] at hz
        exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega) hz
    have hP2 : IsPathFrom G (z :: x t :: S) z p[k - 1] := by
      refine PathAttach.isPathFrom_cons hR (hws.2.2.2.2.2.2 t (by omega)) hznot ?_
      intro w hw hne
      rcases List.mem_cons.mp hw with he | hw
      · exact (hne he).elim
      · obtain ⟨l, hl, _, _, hlw⟩ := hSmem w hw
        rw [← hlw]
        exact WheelSystemBasics.wheelSystemA_no_nbr (hpA p[l] (List.getElem_mem hl))
    have hP2len : pathLength (z :: x t :: S) = k - J + 1 := by
      simp only [pathLength, List.length_cons, hSlen]; omega
    have htake3 : (z :: x t :: S).take 3 = [z, x t, p[J]] := by
      have h1 : S.take 1 = [p[J]] := by rw [List.take_one, hSpath.2.1]; rfl
      simp only [List.take_succ_cons, h1]
    refine ⟨z :: x t :: S, z, p[k - 1],
      Set.disjoint_left.mpr (fun v hvX hvY => G.irrefl (hXY v hvX v hvY)),
      ⟨x 0, 0, by omega, rfl⟩, hhub.2.1,
      Thm203Prelim.anticonnected_wheelSystemX hws (t - 1) (by omega),
      hhub.2.2.1, hXY, hP2.1, ?_, ?_, hP2.2.1, hP2.2.2, ?_, Or.inl ?_⟩
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · refine ⟨?_, hzY⟩
        rintro ⟨j, hj, he⟩
        exact (hws.2.2.1 j (by omega)).2 he.symm
      · rcases List.mem_cons.mp hv with rfl | hv
        · refine ⟨?_, hxtnotY⟩
          rintro ⟨j, hj, he⟩
          have := hws.2.1 t (by omega) j (by omega) he
          omega
        · obtain ⟨l, hl, _, _, hlw⟩ := hSmem v hv
          have hvA : v ∈ wheelSystemA G z A₀ x t := by
            rw [← hlw]; exact hpA _ (List.getElem_mem hl)
          refine ⟨?_, ?_⟩
          · rintro ⟨j, hj, he⟩
            exact Thm203Prelim.x_notMem_wheelSystemA hws (j := j) (by omega) (he ▸ hvA)
          · intro hvY
            exact Thm203Prelim.Y_notMem_wheelSystemA hhub.2.2.2.2.2.1
              (j := t) (by omega) hvY hvA
    · rw [hP2len]; omega
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨fun _ => Or.inl rfl, fun _ => hzX⟩
      · rw [huniqR v hv]
        refine ⟨Or.inr, ?_⟩
        rintro (he | he)
        · rw [he] at hv; exact absurd hv hznot
        · exact he
    · intro v hv
      rw [htake3] at hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl
      · exact hhub.2.2.2.2.1
      · exact hxtY
      · exact hJY
  · right
    exact parity_oddRun_gap h hp hk3 hkm hP hkeven hkcY hJne hJp hJadj hJmax hoddR hJY hc5

/-- **Labelled gap for Claims (4)–(9)** (printed pp. 133–135).

PAPER: *"(4) `i` is odd, and `p_i` is `Y`-complete. ... (5) ... (6) ... (7) ...
(8) `x_t` is adjacent to one of `p₁,…,p_k`.  (9) `p_k` is `Y`-complete. ... and again
21.1 applied to `P` implies there is a wheel with hub `Y`."*

The witness below is exactly the path called `P` in the last quoted sentence.  Its fields are
the hypotheses of 21.1 verbatim, with the paper's anticonnected set `X_{t−1}` fixed rather than
hidden behind an existential. -/
theorem endgame_thm211_witness_gap {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ}
    (hp : GoodPath G z A₀ x t p)
    (hopt : (∃ r : List V, GoodPath G z A₀ x t r ∧ SpanY G z A₀ x t Y r) →
      SpanY G z A₀ x t Y p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s) :
    Thm211Witness G (wheelSystemX x (t - 1)) Y := by
  classical
  have hc2 : Claim2 G x t p := by
    obtain ⟨hpref, _, _, _, hi2, hiq, hst, hsnone, _⟩ := id hext
    have hp0 : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
    have hq0 : 0 < q.length := by omega
    have heq : q[0] = p[0] := by
      obtain ⟨r, hr⟩ := hpref
      exact (List.getElem_of_eq hr.symm hq0).trans (List.getElem_append_left hp0)
    have ht0 : 0 < ((x (t + 1) :: q).take i).length := by
      simp only [List.length_take, List.length_cons]; omega
    have ht1 : 1 < ((x (t + 1) :: q).take i).length := by
      simp only [List.length_take, List.length_cons]; omega
    refine ⟨s, hst, hsnone _ (by simpa using List.getElem_mem ht0), p[0], ?_, ?_⟩
    · simp only [List.head?_eq_getElem?, List.getElem?_eq_getElem hp0]
    · apply hsnone
      simpa only [List.getElem_take, List.getElem_cons_succ, List.getElem_cons_zero, heq]
        using List.getElem_mem ht1
  obtain ⟨q, i, s, hext, hsupport⟩ := exists_extended_with_support h hp hc2 hc3
  obtain ⟨hiodd, hic⟩ := endgame_claim4_gap h hp hc1 hc3 hext
  have hc5 := endgame_claim5_gap h hp hc2
  rcases endgame_claim6_gap h hp hext hsupport hiodd hic hc5 with hw | ⟨him, hclean⟩
  · exact hw
  obtain ⟨hpref, _, _, _, hi2, hiq, _, _, _⟩ := id hext
  obtain ⟨_, _, hframe, ht, hhub, _, _, _⟩ := id h
  have hws := hhub.1
  have hi3 : 3 ≤ i := by
    have := Nat.odd_iff.mp hiodd
    omega
  have hplen : 0 < p.length := List.length_pos_of_ne_nil hp.2.1
  have hlastC : VertexComplete G p[p.length - 1] (wheelSystemX x (t - 1)) :=
    Thm203Prelim.vertexComplete_of_nbr_of_notMem hframe hws (by omega)
      (WheelSystemBasics.wheelSystemA_no_nbr
        ((hp.2.2.1 _ (List.getElem_mem (by omega))).1))
      ((hp.2.2.1 _ (List.getElem_mem (by omega))).2)
      ((hp.2.2.2 (p.length - 1) (by omega)).mpr (by omega))
  have hex : ∃ j : ℕ, ∃ hj : j < p.length,
      VertexComplete G p[j] (wheelSystemX x (t - 1)) :=
    ⟨p.length - 1, by omega, hlastC⟩
  obtain ⟨hl, hlC⟩ := Nat.find_spec hex
  let l := Nat.find hex
  let k := l + 1
  have hkm : k ≤ p.length := by dsimp [k, l]; omega
  have hfirst : ∀ j (hj : j < p.length), j + 1 < k →
      ¬ VertexComplete G p[j] (wheelSystemX x (t - 1)) := by
    intro j hj hjk hc
    apply Nat.find_min hex (show j < Nat.find hex by dsimp [k, l] at hjk; omega)
    exact ⟨hj, hc⟩
  have hget : ∀ j (hj : j < p.length) (hjq : j < q.length), q[j] = p[j] := by
    intro j hj hjq
    obtain ⟨r, hr⟩ := hpref
    exact (List.getElem_of_eq hr.symm hjq).trans (List.getElem_append_left hj)
  have hpclean : ∀ j (hj : j < p.length), j + 1 < i →
      ¬ VertexComplete G p[j] (wheelSystemX x (t - 1)) := by
    intro j hj hji
    apply hclean
    have hji' : j + 1 < ((x (t + 1) :: q).take i).length := by
      simp only [List.length_take, List.length_cons]
      omega
    have hm := List.getElem_mem hji'
    simpa only [List.getElem_take, List.getElem_cons_succ, hget j hj (by omega)] using hm
  have hik : i ≤ k := by
    by_contra hn
    exact hpclean l hl (by dsimp [k] at hn; omega) hlC
  have hk3 : 3 ≤ k := by omega
  have hunc : ¬ VertexComplete G (x (t + 1)) (wheelSystemX x (t - 1)) :=
    hclean _ (by
      have hp0 : 0 < ((x (t + 1) :: q).take i).length := by
        simp only [List.length_take, List.length_cons]; omega
      simpa using List.getElem_mem hp0)
  have hkc : VertexComplete G p[k - 1] (wheelSystemX x (t - 1)) := by
    simpa only [k, Nat.add_sub_cancel] using hlC
  have hP := prefix_pathFor211 h hp hk3 hkm hunc hkc hfirst
  have hkeven := hP.even h.1.1.1
  have hother : ∃ v ∈ z :: x (t + 1) :: p.take k,
      v ≠ z ∧ VertexComplete G v Y := by
    have hip : i - 1 < p.length := by omega
    refine ⟨p[i - 1], List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_), ?_, ?_⟩
    · have hiTake : i - 1 < (p.take k).length := by simp only [List.length_take]; omega
      simpa using List.getElem_mem hiTake
    · intro he
      exact Thm203Prelim.z_notMem_wheelSystemA hws (i := t) (by omega)
        (he ▸ (hp.2.2.1 _ (List.getElem_mem hip)).1)
    · obtain ⟨hi, hiY⟩ := hic
      rwa [hget (i - 1) hip hi] at hiY
  have hkcY := hP.last_complete h.2.1 rfl hhub.2.2.2.2.1 hhub.2.2.2.2.2.2 hother
  have hnbr := endgame_claim8_gap h hp hext hik hk3 hkm hP hkeven hc5
  rcases endgame_segment_parity_gap h hp hk3 hkm hP hkeven hkcY hnbr hc5 with hw | hrun
  · exact hw
  · exact ⟨_, _, _, hP.disjoint, hP.nonemptyX, hP.nonemptyY, hP.antiX, hP.antiY,
      hP.completeXY, hP.path.1, hP.outside, hP.length, hP.path.2.1, hP.path.2.2,
      hP.completeEnds, Or.inr (Thm212EndgameTools.alternatives_of_oddRun hrun)⟩

/-- **Claims (4)–(9) and the concluding paragraph** (printed pp. 133–135), which between them
produce the wheel with hub `Y`:

*"(4) `i` is odd, and `pᵢ` is `Y`-complete.  (5) Let `R` be a path from `x_t` to some vertex
`r`, such that `r` is the unique `X_{t−1}`-complete vertex in `R`, and
`V(R \ x_t) ⊆ A_{t−1} ∪ {p₁,…,p_m}`.  Then `R` is odd, and has length ≥ 3. …  (6) We may assume
that none of `x_{t+1}, p₁,…,p_{i−1}` is `X_{t−1}`-complete, and in particular `i ≤ m`. …
(7) None of `x_{t+1}, p₁,…,p_{k−1}` is `X_{t−1}`-complete, and `k` is odd.  (8) `x_t` is
adjacent to one of `p₁,…,p_k`.  (9) `p_k` is `Y`-complete. …  and again 21.1 applied to `P`
implies there is a wheel with hub `Y`.  This proves 21.2."* -/
theorem endgame {G : SimpleGraph V} {Y : Set V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (h : Setup G Y z A₀ x t) {p q : List V} {i s : ℕ} (hp : GoodPath G z A₀ x t p)
    (hopt : (∃ r : List V, GoodPath G z A₀ x t r ∧ SpanY G z A₀ x t Y r) →
      SpanY G z A₀ x t Y p)
    (hc1 : NoOddLeapPath G z A₀ x t) (hc3 : SpanY G z A₀ x t Y p)
    (hext : Extended G z A₀ x t p q i s) :
    Concl G Y := by
  have hG : InF7 G := h.1
  obtain ⟨P, p₁, pₙ, hXY, hXne, hYne, hXanti, hYanti, hcomplete,
    hP, hPXY, hlen, hhead, hlast, hXcomplete, halt⟩ :=
    endgame_thm211_witness_gap h hp hopt hc1 hc3 hext
  exact _root_.Workspace.Statements.S21.SPGT.thm_21_1 G hG
    (wheelSystemX x (t - 1)) Y hXY hXne hYne hXanti hYanti hcomplete
    P p₁ pₙ hP hPXY hlen hhead hlast hXcomplete halt

end Workspace.ProofLemmas.Thm212
