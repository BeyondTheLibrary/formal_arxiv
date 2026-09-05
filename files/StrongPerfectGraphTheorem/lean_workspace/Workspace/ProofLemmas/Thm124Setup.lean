import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm124PrefixOdd
import Workspace.ProofLemmas.StaircaseLeftRightSymmetry
import Workspace.Statements.S11.Thm_11_3

/-!
# 12.4: the standing configuration, and claim (1)

PAPER (printed p. 74):

*"Proof.  Choose a 2-breaker `(K, Q)` in `G`, with notation as above, such that for fixed `K`
the set `Q` is maximal.  Let `a₀`-`S`-`s` and `b₀`-`T`-`t` be the subpaths of `R₀` such that `s`
is the unique `Q`-complete vertex of `S`, and `t` is the unique `Q`-complete vertex of `T`.*

*(1) `S`, `T` both have odd length, and therefore `s`, `t` are different.*

*For choose `a ∈ A` and `b ∈ B`, both `Q`-complete; then `a`-`a₀`-`S`-`s` has length `> 1`, and
its ends are `Q`-complete and its internal vertices are not, and `b` is also `Q`-complete and
has no neighbours in the interior of `a`-`a₀`-`S`-`s`.  By 2.2, this path is even, and so `S` is
odd, and similarly `T` is odd.  Since `R₀` is odd it follows that `s`, `t` are different.  This
proves (1)."*

`Setup` is the standing configuration of the whole proof: the hypotheses of 12.4 together with
a 2-breaker whose `Q` is inclusion-maximal for the fixed staircase `K`.  The two subpaths
`a₀`-`S`-`s` and `b₀`-`T`-`t` are recorded through the *indices* `iS`, `iT` of `s` and `t`
along `R₀`, so that `S` is the stretch `R₀[0..iS]` (of length `iS`) and `T` the stretch
`R₀[iT..]` (of length `R₀.length - 1 - iT`).  *"`R₀` is odd"* is 11.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm124Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The standing configuration of the printed proof of 12.4: the hypotheses of 12.4, a
2-breaker `(K, Q)` with `K = (S = (A,C,B), a₀`-`R₀`-`b₀)`, and the printed choice *"such that
for fixed `K` the set `Q` is maximal"*. -/
structure Setup (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (Q : Set V) : Prop where
  berge : Berge G
  noK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4))
  noPrism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃
  noBreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q'
  twoBreaker : IsTwoBreaker G A C B a₀ R₀ b₀ Q
  /-- *"such that for fixed `K` the set `Q` is maximal"*. -/
  qmax : ∀ Q' : Set V, Q ⊆ Q' → IsTwoBreaker G A C B a₀ R₀ b₀ Q' → Q' = Q

namespace Setup

variable {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}

theorem stronglyMaximal (h : Setup G A C B a₀ R₀ b₀ Q) :
    StronglyMaximalStaircase G A C B a₀ R₀ b₀ := h.twoBreaker.1

theorem maximal (h : Setup G A C B a₀ R₀ b₀ Q) :
    MaximalStaircase G A C B a₀ R₀ b₀ := h.twoBreaker.1.1

theorem staircase (h : Setup G A C B a₀ R₀ b₀ Q) :
    IsStaircase G A C B a₀ R₀ b₀ := h.twoBreaker.1.1.1

theorem stepConnected (h : Setup G A C B a₀ R₀ b₀ Q) : StepConnected G A C B :=
  h.staircase.1

theorem banister (h : Setup G A C B a₀ R₀ b₀ Q) : IsBanister G A C B a₀ R₀ b₀ :=
  h.staircase.2.1

theorem pathFrom (h : Setup G A C B a₀ R₀ b₀ Q) : IsPathFrom G R₀ a₀ b₀ :=
  h.banister.1

theorem pathList (h : Setup G A C B a₀ R₀ b₀ Q) : IsPathList G R₀ := h.banister.1.1

theorem leftStar (h : Setup G A C B a₀ R₀ b₀ Q) : IsLeftStar G A C B a₀ :=
  h.banister.2.2.1

theorem rightStar (h : Setup G A C B a₀ R₀ b₀ Q) : IsRightStar G A C B b₀ :=
  h.banister.2.2.2.1

/-- *"there are no edges between the interior of `R` and `V(S)`"*. -/
theorem interiorAnti (h : Setup G A C B a₀ R₀ b₀ Q) :
    Anticomplete G {u : V | u ∈ SPGT.interior R₀} (A ∪ B ∪ C) :=
  h.banister.2.2.2.2

/-- *"a path `a`-`R`-`b` of `G \ (A ∪ B ∪ C)`"*. -/
theorem outsideStrip (h : Setup G A C B a₀ R₀ b₀ Q) : ∀ v ∈ R₀, v ∉ A ∪ B ∪ C :=
  h.banister.2.1

theorem lenR₀ (h : Setup G A C B a₀ R₀ b₀ Q) : 3 ≤ pathLength R₀ := h.staircase.2.2

theorem anticonnQ (h : Setup G A C B a₀ R₀ b₀ Q) : AnticonnectedSet G Q :=
  h.twoBreaker.2.1.2

theorem outsideQ (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∀ q ∈ Q, q ∉ staircaseVertices A C B R₀ := h.twoBreaker.2.1.1

theorem existsAComplete (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∃ a ∈ A, VertexComplete G a Q := h.twoBreaker.2.2.1.1

theorem existsBComplete (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∃ b ∈ B, VertexComplete G b Q := h.twoBreaker.2.2.1.2

theorem a₀NotComplete (h : Setup G A C B a₀ R₀ b₀ Q) : ¬ VertexComplete G a₀ Q :=
  h.twoBreaker.2.2.2.1.1

theorem b₀NotComplete (h : Setup G A C B a₀ R₀ b₀ Q) : ¬ VertexComplete G b₀ Q :=
  h.twoBreaker.2.2.2.1.2

theorem existsR₀Complete (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∃ r : V, r ∈ R₀ ∧ VertexComplete G r Q := h.twoBreaker.2.2.2.2

/-! ### Elementary bookkeeping about `R₀` -/

theorem lengthPos (h : Setup G A C B a₀ R₀ b₀ Q) : 0 < R₀.length :=
  PathBasics.path_length_pos h.pathList

theorem lengthGe (h : Setup G A C B a₀ R₀ b₀ Q) : 4 ≤ R₀.length := by
  have := h.lenR₀
  have := PathBasics.pathLength_eq R₀
  have := h.lengthPos
  omega

theorem getElem_zero (h : Setup G A C B a₀ R₀ b₀ Q) :
    R₀[0]'h.lengthPos = a₀ :=
  PathBasics.getElem_zero_of_head? h.pathFrom.2.1 h.lengthPos

theorem getElem_last (h : Setup G A C B a₀ R₀ b₀ Q) :
    R₀[R₀.length - 1]'(by have := h.lengthPos; omega) = b₀ :=
  PathBasics.getElem_last_of_getLast? h.pathFrom.2.2 h.lengthPos

/-- No vertex of `R₀` lies in `Q`: `Q ⊆ V(G) \ V(K)` and `V(R₀) ⊆ V(K)`. -/
theorem notMemQ_of_mem (h : Setup G A C B a₀ R₀ b₀ Q) : ∀ w ∈ R₀, w ∉ Q := by
  intro w hw hwQ
  exact h.outsideQ w hwQ (Or.inl hw)

/-- No vertex of `A ∪ B ∪ C` lies in `Q`, for the same reason. -/
theorem notMemQ_of_memStrip (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∀ w ∈ A ∪ B ∪ C, w ∉ Q := by
  intro w hw hwQ
  exact h.outsideQ w hwQ (Or.inr hw)

/-- Every vertex of `A` sits outside `V(R₀)`, since the banister avoids `V(S)`. -/
theorem notMemR₀_of_memStrip (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∀ w ∈ A ∪ B ∪ C, w ∉ R₀ := fun w hw hwR => h.outsideStrip w hwR hw

/-- *"`R₀` is odd"* — this is 11.3. -/
theorem oddR₀ (h : Setup G A C B a₀ R₀ b₀ Q) : Odd (pathLength R₀) :=
  (Workspace.Statements.S11.SPGT.thm_11_3 G h.berge h.noPrism A C B h.stepConnected a₀ b₀ R₀
    h.banister).2

/-- The only neighbour of a vertex `a ∈ A` on the banister is its left end `a₀`. -/
theorem adj_mem_A_iff (h : Setup G A C B a₀ R₀ b₀ Q) {a : V} (ha : a ∈ A)
    (k : ℕ) (hk : k < R₀.length) :
    G.Adj a (R₀[k]'hk) ↔ k = 0 := by
  have hlen := h.lengthGe
  constructor
  · intro hadj
    by_contra hk0
    rcases Nat.lt_or_ge k (R₀.length - 1) with hklt | hkge
    · exact h.interiorAnti (R₀[k]'hk)
        (PathBasics.getElem_mem_interior h.pathList hk (by omega) (by omega))
        a (Or.inl (Or.inl ha)) hadj.symm
    · have hkeq : k = R₀.length - 1 := by omega
      subst hkeq
      rw [h.getElem_last] at hadj
      exact h.rightStar.2.2 a (Or.inl ha) hadj.symm
  · rintro rfl
    have := h.leftStar.2.1 a ha
    rw [h.getElem_zero]
    exact this.symm

/-- The only neighbour of a vertex `b ∈ B` on the banister is its right end `b₀`. -/
theorem adj_mem_B_iff (h : Setup G A C B a₀ R₀ b₀ Q) {b : V} (hb : b ∈ B)
    (k : ℕ) (hk : k < R₀.length) :
    G.Adj b (R₀[k]'hk) ↔ k = R₀.length - 1 := by
  have hlen := h.lengthGe
  constructor
  · intro hadj
    by_contra hk0
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [h.getElem_zero] at hadj
      exact h.leftStar.2.2 b (Or.inl hb) hadj.symm
    · exact h.interiorAnti (R₀[k]'hk)
        (PathBasics.getElem_mem_interior h.pathList hk hkpos (by omega))
        b (Or.inl (Or.inr hb)) hadj.symm
  · rintro rfl
    have := h.rightStar.2.1 b hb
    rw [h.getElem_last]
    exact this.symm

end Setup

/-! ### The left–right exchange

The printed proof says *"suppose some vertex in `A` **say** is not `Q`-complete"* and
*"and similarly `T` is odd"*: the configuration is symmetric under exchanging `A` with `B`,
`a₀` with `b₀` and reversing `R₀`.  `Workspace.ProofLemmas.StaircaseLeftRightSymmetry` already
transports the staircase notions; the 2-breaker and hence `Setup` follow. -/

theorem staircaseVertices_swap (A C B : Set V) (R₀ : List V) :
    staircaseVertices B C A R₀.reverse = staircaseVertices A C B R₀ := by
  ext v
  simp only [staircaseVertices, Set.mem_union, Set.mem_setOf_eq, List.mem_reverse]
  tauto

theorem isTwoBreaker_swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {Q : Set V} (h : IsTwoBreaker G A C B a₀ R₀ b₀ Q) :
    IsTwoBreaker G B C A b₀ R₀.reverse a₀ Q := by
  obtain ⟨hsm, ⟨hout, hanti⟩, ⟨hA, hB⟩, ⟨ha₀, hb₀⟩, r, hrR, hrQ⟩ := h
  refine ⟨StaircaseLeftRightSymmetry.stronglyMaximalStaircase_swap.mp hsm,
    ⟨?_, hanti⟩, ⟨hB, hA⟩, ⟨hb₀, ha₀⟩, r, by rwa [List.mem_reverse], hrQ⟩
  intro q hq
  rw [staircaseVertices_swap]
  exact hout q hq

theorem Setup.swap {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Setup G A C B a₀ R₀ b₀ Q) : Setup G B C A b₀ R₀.reverse a₀ Q := by
  refine ⟨h.berge, h.noK4, h.noPrism, h.noBreaker, isTwoBreaker_swap h.twoBreaker, ?_⟩
  intro Q' hsub hQ'
  refine h.qmax Q' hsub ?_
  have := isTwoBreaker_swap hQ'
  rwa [List.reverse_reverse] at this

/-! ### Choosing the 2-breaker with `Q` maximal -/

/-- PAPER: *"Choose a 2-breaker `(K, Q)` in `G`, with notation as above, such that for fixed
`K` the set `Q` is maximal."*  A maximum-cardinality choice is inclusion-maximal. -/
theorem exists_setup (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (h2breaker : ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
      IsTwoBreaker G A C B a₀ R₀ b₀ Q) :
    ∃ (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V) (Q : Set V),
      Setup G A C B a₀ R₀ b₀ Q := by
  classical
  obtain ⟨A, C, B, a₀, R₀, b₀, Q₀, hQ₀⟩ := h2breaker
  set 𝒬 : Set (Set V) := {Q' : Set V | IsTwoBreaker G A C B a₀ R₀ b₀ Q'} with h𝒬
  obtain ⟨Q, hQmax⟩ := Set.Finite.exists_maximal (Set.toFinite 𝒬) ⟨Q₀, hQ₀⟩
  refine ⟨A, C, B, a₀, R₀, b₀, Q, hG, hK4, hprism, hbreaker, hQmax.1, ?_⟩
  intro Q' hsub hQ'
  exact Set.Subset.antisymm (hQmax.2 hQ' hsub) hsub

/-! ### Claim (1) -/

/-- **12.4(1)** *"`S`, `T` both have odd length, and therefore `s`, `t` are different."*

`iS` and `iT` are the positions of `s` and `t` along `R₀`: `s` is the first `Q`-complete vertex
of `R₀` and `t` the last, so `a₀`-`S`-`s` is the stretch `R₀[0..iS]`, of length `iS`, and
`b₀`-`T`-`t` is the stretch `R₀[iT..]`, of length `R₀.length - 1 - iT`. -/
theorem claim1 {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V} {Q : Set V}
    (h : Setup G A C B a₀ R₀ b₀ Q) :
    ∃ (iS iT : ℕ) (hiS : iS < R₀.length) (hiT : iT < R₀.length),
      0 < iS ∧ iT < R₀.length - 1 ∧ iS < iT ∧
      VertexComplete G (R₀[iS]'hiS) Q ∧ VertexComplete G (R₀[iT]'hiT) Q ∧
      (∀ (k : ℕ) (hk : k < R₀.length), k < iS → ¬ VertexComplete G (R₀[k]'hk) Q) ∧
      (∀ (k : ℕ) (hk : k < R₀.length), iT < k → ¬ VertexComplete G (R₀[k]'hk) Q) ∧
      Odd iS ∧ Odd (R₀.length - 1 - iT) := by
  classical
  have hlen := h.lengthGe
  have hpos := h.lengthPos
  -- PAPER: *"choose `a ∈ A` and `b ∈ B`, both `Q`-complete"*
  obtain ⟨a, haA, haQ⟩ := h.existsAComplete
  obtain ⟨b, hbB, hbQ⟩ := h.existsBComplete
  have haR : a ∉ R₀ := h.notMemR₀_of_memStrip a (Or.inl (Or.inl haA))
  have hbR : b ∉ R₀ := h.notMemR₀_of_memStrip b (Or.inl (Or.inr hbB))
  -- the set of positions of `Q`-complete vertices of `R₀` is nonempty
  have hP : ∃ k : ℕ, ∃ hk : k < R₀.length, VertexComplete G (R₀[k]'hk) Q := by
    obtain ⟨r, hrR, hrQ⟩ := h.existsR₀Complete
    obtain ⟨k, hk, hkr⟩ := List.getElem_of_mem hrR
    exact ⟨k, hk, by rw [hkr]; exact hrQ⟩
  -- `iS` = the first such position (the paper's `s`)
  set iS : ℕ := Nat.find hP with hiSdef
  obtain ⟨hiS, hiScomp⟩ := Nat.find_spec hP
  have hiSmin : ∀ (k : ℕ) (hk : k < R₀.length), k < iS →
      ¬ VertexComplete G (R₀[k]'hk) Q := by
    intro k hk hklt hcomp
    exact Nat.find_min hP hklt ⟨hk, hcomp⟩
  -- `iT` = the last such position (the paper's `t`)
  have hP' : ∃ k : ℕ, ∃ hk : k < R₀.length,
      VertexComplete G (R₀[R₀.length - 1 - k]'(by omega)) Q := by
    refine ⟨R₀.length - 1 - iS, by omega, ?_⟩
    have : R₀.length - 1 - (R₀.length - 1 - iS) = iS := by omega
    simpa [this] using hiScomp
  set jT : ℕ := Nat.find hP' with hjTdef
  obtain ⟨hjT, hjTcomp⟩ := Nat.find_spec hP'
  set iT : ℕ := R₀.length - 1 - jT with hiTdef
  have hiT : iT < R₀.length := by omega
  have hiTcomp : VertexComplete G (R₀[iT]'hiT) Q := hjTcomp
  have hiTmax : ∀ (k : ℕ) (hk : k < R₀.length), iT < k →
      ¬ VertexComplete G (R₀[k]'hk) Q := by
    intro k hk hklt hcomp
    refine Nat.find_min hP' (m := R₀.length - 1 - k) (by omega) ⟨by omega, ?_⟩
    have hkk : R₀.length - 1 - (R₀.length - 1 - k) = k := by omega
    simpa [hkk] using hcomp
  -- `a₀` and `b₀` are not `Q`-complete, so `0 < iS` and `iT < R₀.length - 1`
  have hget : ∀ (k l : ℕ) (hk : k < R₀.length) (hl : l < R₀.length),
      k = l → (R₀[k]'hk) = (R₀[l]'hl) := by
    rintro k l hk hl rfl; rfl
  have hiS0 : 0 < iS := by
    by_contra hcon
    refine h.a₀NotComplete ?_
    rw [← h.getElem_zero, ← hget iS 0 hiS hpos (by omega)]
    exact hiScomp
  have hiTlast : iT < R₀.length - 1 := by
    by_contra hcon
    refine h.b₀NotComplete ?_
    rw [← h.getElem_last, ← hget iT (R₀.length - 1) hiT (by omega) (by omega)]
    exact hiTcomp
  have hiSiT : iS ≤ iT := by
    by_contra hcon
    exact hiTmax iS hiS (by omega) hiScomp
  -- PAPER: *"By 2.2, this path is even, and so `S` is odd"*
  have hoddS : Odd iS :=
    Thm124PrefixOdd.prefix_odd G h.berge Q h.anticonnQ R₀ h.pathList iS hiS hiS0 hiScomp
      hiSmin h.notMemQ_of_mem a haR haQ (fun k hk => h.adj_mem_A_iff haA k hk) b hbQ
      (fun k hk hklt => by
        rw [h.adj_mem_B_iff hbB k hk]; omega)
  -- PAPER: *"and similarly `T` is odd"*
  have hoddT : Odd (R₀.length - 1 - iT) :=
    Thm124PrefixOdd.suffix_odd G h.berge Q h.anticonnQ R₀ h.pathList iT hiT hiTlast hiTcomp
      hiTmax h.notMemQ_of_mem b hbR hbQ (fun k hk => h.adj_mem_B_iff hbB k hk) a haQ
      (fun k hk hklt => by
        rw [h.adj_mem_A_iff haA k hk]; omega)
  -- PAPER: *"Since `R₀` is odd it follows that `s`, `t` are different."*
  have hiSneiT : iS ≠ iT := by
    intro hEq
    have hodd := h.oddR₀
    rw [PathBasics.pathLength_eq] at hodd
    obtain ⟨m, hm⟩ := hoddS
    obtain ⟨n, hn⟩ := hoddT
    rw [← hEq] at hn
    obtain ⟨p, hp⟩ := hodd
    omega
  exact ⟨iS, iT, hiS, hiT, hiS0, hiTlast, lt_of_le_of_ne hiSiT hiSneiT, hiScomp, hiTcomp,
    hiSmin, hiTmax, hoddS, hoddT⟩

end Workspace.ProofLemmas.Thm124Setup
