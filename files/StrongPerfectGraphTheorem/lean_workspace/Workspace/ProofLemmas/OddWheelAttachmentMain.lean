import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.OddWheelParityFacts

/-!
# 16.2, the `|F| ≥ 2` line: claims (2)–(5) and the closing paragraph

PAPER (16.2, printed pp. 98–100).  The base case `|F| = 1` is
`Workspace.ProofLemmas.OddWheelAttachmentBase.base_case`, and claim (1) is a separate module.
This module is everything after claim (1):

* the connecting prose *"From (1) we may assume there are nonadjacent vertices in `X` with
  opposite wheel-parity, say `x₁, x₂`, and therefore `F` is the interior of a path between
  `x₁, x₂`, from the minimality of `F` … Let `X₁` be the set of attachments in `C` of
  `F \ {f_k}`, and `X₂` the set of attachments of `F \ {f₁}` … Since `k ≥ 2` it follows that
  `X₁ ∪ X₂ = X`."*;
* claim (2) *"`X₁` and `X₂` do not both have members of opposite wheel-parity"*;
* claim (3) *"If `X₁` has members of opposite wheel-parity then the theorem holds"* (its proof
  derives a contradiction, so it holds vacuously);
* claim (4) *"At least one of `f₁, f_k` has only one neighbour in `C`"*;
* claim (5) *"`f_k` has no neighbour in `{p₃, …, p_{j−2}}`"*;
* the closing paragraph, which ends *"contradicting that there are nonadjacent vertices in `X`
  of opposite wheel-parity"*.

**The whole line ends in a contradiction.**  16.2's conclusion is therefore produced only in
the base case `|F| = 1` (via 16.1) and in claim (1); this module's conclusion is `False`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelAttachmentMain

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-! ### The hypotheses 16.2 places on `F`

`AttachmentHyp G C Y F` is exactly the conjunction of the five hypotheses of `thm_16_2` that
mention `F` (`hFC`, `hFY`, `hFconn`, `hFnc`, `hopp`, `hnonadj`), with `X` unfolded to
`attachments G F {u | u ∈ C}`.  It exists so that the paper's opening *"We may assume that `F`
is minimal"* can be stated: minimality is minimality among the sets satisfying it.

Note that `hopp` and `hnonadj` are kept **separate**, as printed — the opposite-wheel-parity
pair and the non-adjacent pair need not be the same pair.  This matters: the prose after claim
(1) uses minimality in the form *"either all members of `X_i` have the same wheel-parity, or
there are at most two members of `X_i`, adjacent if there are two"*, which is precisely the
negation of the conjunction of the two separate clauses. -/
def AttachmentHyp (G : SimpleGraph V) (C : List V) (Y : Set V) (F : Set V) : Prop :=
  (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧ ConnectedSet G F ∧
    (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
    (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
      OppositeWheelParity G C Y a b) ∧
    (∃ a ∈ attachments G F {u : V | u ∈ C}, ∃ b ∈ attachments G F {u : V | u ∈ C},
      a ≠ b ∧ ¬ G.Adj a b)

/-- Unfolding `attachments`: `u` is an attachment of `F` in `V(C)` exactly when it is a vertex
of `C` with a neighbour in `F`. -/
theorem mem_attachments_iff {G : SimpleGraph V} {C : List V} {F : Set V} {u : V} :
    u ∈ attachments G F {w : V | w ∈ C} ↔ u ∈ C ∧ ∃ f ∈ F, G.Adj u f := Iff.rfl

/-! ### *"`F` is the interior of a path between `x₁` and `x₂`, from the minimality of `F`"* -/

/-- **The first sentence of the connecting prose.**

PAPER: *"From (1) we may assume there are nonadjacent vertices in `X` with opposite
wheel-parity, say `x₁, x₂`, and therefore `F` is the interior of a path between `x₁, x₂`, from
the minimality of `F`."*

`MinimalConnectedIsPath.exists_path_interior_attached` supplies the graph-theoretic half (a
connected `F` attached at two non-adjacent vertices carries an induced path between them whose
interior is a connected subset of `F` still attached to both); minimality then forces that
interior to be all of `F`. -/
theorem exists_min_path {G : SimpleGraph V} {C : List V} {Y : Set V}
    {F : Set V} (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFconn : ConnectedSet G F) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ¬ AttachmentHyp G C Y F')
    {x₁ x₂ : V}
    (hx₁ : x₁ ∈ attachments G F {u : V | u ∈ C})
    (hx₂ : x₂ ∈ attachments G F {u : V | u ∈ C})
    (hopp : OppositeWheelParity G C Y x₁ x₂) (hnadj : ¬ G.Adj x₁ x₂) :
    ∃ P : List V, IsPathFrom G P x₁ x₂ ∧ 3 ≤ P.length ∧
      F = {z : V | z ∈ SPGT.interior P} := by
  classical
  obtain ⟨hx₁C, hx₁nb⟩ := hx₁
  obtain ⟨hx₂C, hx₂nb⟩ := hx₂
  have hx₁F : x₁ ∉ F := fun hmem => hFC x₁ hmem hx₁C
  have hx₂F : x₂ ∉ F := fun hmem => hFC x₂ hmem hx₂C
  obtain ⟨P, hP, h3, hint, hconn, ⟨d₁, hd₁, hadj₁⟩, ⟨d₂, hd₂, hadj₂⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn hopp.1 hnadj hx₁F hx₂F
      hx₁nb hx₂nb
  refine ⟨P, hP, h3, ?_⟩
  by_contra hne
  refine hmin {z : V | z ∈ SPGT.interior P} hint (fun he => hne he.symm) ?_
  have hx₁att : x₁ ∈ attachments G {z : V | z ∈ SPGT.interior P} {u : V | u ∈ C} :=
    ⟨hx₁C, ⟨d₁, hd₁, hadj₁⟩⟩
  have hx₂att : x₂ ∈ attachments G {z : V | z ∈ SPGT.interior P} {u : V | u ∈ C} :=
    ⟨hx₂C, ⟨d₂, hd₂, hadj₂⟩⟩
  exact ⟨fun f hf => hFC f (hint f hf), fun f hf => hFY f (hint f hf), hconn,
    fun f hf => hFnc f (hint f hf),
    ⟨x₁, hx₁att, x₂, hx₂att, hopp⟩, ⟨x₁, hx₁att, x₂, hx₂att, hopp.1, hnadj⟩⟩

/-! ### The index picture: `P = p₁-f₁-⋯-f_k-p_m`, and the two sub-paths

Writing `P` for the path of `exists_min_path`, the paper's `f_i` is `P[i]` (`1 ≤ i ≤ k`) and
`k = |P| - 2 = |F|`.  The two sets whose attachments the proof calls `X₁` and `X₂` are

* `F \ {f_k}`, the interior of the sub-path `p₁-f₁-⋯-f_k` = `slice P 0 (|P|-2)`;
* `F \ {f₁}`, the interior of the sub-path `f₁-⋯-f_k-p_m` = `slice P 1 (|P|-1)`.
-/

theorem interior_nodup {P : List V} (hnd : P.Nodup) : (SPGT.interior P).Nodup :=
  List.Nodup.sublist ((List.dropLast_sublist P.tail).trans (List.tail_sublist P)) hnd

/-- `|F| = |P| - 2`, i.e. `F = {f₁, …, f_k}` with `k = |P| - 2`. -/
theorem ncard_interior [Fintype V] {P : List V} (hnd : P.Nodup) :
    {z : V | z ∈ SPGT.interior P}.ncard = P.length - 2 := by
  classical
  rw [← List.coe_toFinset, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (interior_nodup hnd), PathBasics.interior_length]

/-- **`F \ {f_k}` is the interior of `p₁-f₁-⋯-f_k`.** -/
theorem sdiff_last_eq {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    {z : V | z ∈ SPGT.interior P} \ {P[P.length - 2]'(by omega)}
      = {z : V | z ∈ SPGT.interior ((P.drop 0).take (P.length - 2 - 0 + 1))} := by
  ext z
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    PathBasics.mem_interior_slice_iff hP (show (0 : ℕ) < P.length - 2 by omega)
      (show P.length - 2 < P.length by omega)]
  constructor
  · rintro ⟨hzin, hzne⟩
    obtain ⟨k, hk, h1, h2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP hzin
    refine ⟨k, hk, by omega, ?_, rfl⟩
    by_contra hcon
    have hke : k = P.length - 2 := by omega
    exact hzne ((List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mpr hke)
  · rintro ⟨k, hk, h1, h2, rfl⟩
    refine ⟨PathBasics.getElem_mem_interior hP hk (by omega) (by omega), ?_⟩
    intro hcon
    have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp hcon
    omega

/-- **`F \ {f₁}` is the interior of `f₁-⋯-f_k-p_m`.** -/
theorem sdiff_first_eq {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    {z : V | z ∈ SPGT.interior P} \ {P[1]'(by omega)}
      = {z : V | z ∈ SPGT.interior ((P.drop 1).take (P.length - 1 - 1 + 1))} := by
  ext z
  simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff,
    PathBasics.mem_interior_slice_iff hP (show (1 : ℕ) < P.length - 1 by omega)
      (show P.length - 1 < P.length by omega)]
  constructor
  · rintro ⟨hzin, hzne⟩
    obtain ⟨k, hk, h1, h2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP hzin
    refine ⟨k, hk, ?_, by omega, rfl⟩
    by_contra hcon
    have hke : k = 1 := by omega
    exact hzne ((List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mpr hke)
  · rintro ⟨k, hk, h1, h2, rfl⟩
    refine ⟨PathBasics.getElem_mem_interior hP hk (by omega) (by omega), ?_⟩
    intro hcon
    have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp hcon
    omega

/-- `F \ {f_k}` is connected: it is the interior of the path `p₁-f₁-⋯-f_k`. -/
theorem connectedSet_sdiff_last {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    ConnectedSet G ({z : V | z ∈ SPGT.interior P} \ {P[P.length - 2]'(by omega)}) := by
  rw [sdiff_last_eq hP h4]
  exact MinimalConnectedIsPath.connectedSet_interior
    (PathBasics.isPathFrom_slice hP (show (0 : ℕ) < P.length - 2 by omega)
      (show P.length - 2 < P.length by omega))

/-- `F \ {f₁}` is connected: it is the interior of the path `f₁-⋯-f_k-p_m`. -/
theorem connectedSet_sdiff_first {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    ConnectedSet G ({z : V | z ∈ SPGT.interior P} \ {P[1]'(by omega)}) := by
  rw [sdiff_first_eq hP h4]
  exact MinimalConnectedIsPath.connectedSet_interior
    (PathBasics.isPathFrom_slice hP (show (1 : ℕ) < P.length - 1 by omega)
      (show P.length - 1 < P.length by omega))

/-! ### `X₁`, `X₂`, and what the minimality of `F` says about them -/

/-- **PAPER**: *"From the minimality of `F`, for `i = 1, 2` either all members of `X_i` have the
same wheel-parity, or there are at most two members of `X_i`, adjacent if there are two."*

The printed dichotomy is exactly the negation of the conjunction of 16.2's two hypotheses on
the attachment set of the smaller connected set `F'`: the first disjunct is *"no two members of
`X_i` have opposite wheel-parity"*, the second *"no two members of `X_i` are non-adjacent"* —
and a set of pairwise adjacent vertices of a hole has at most two members. -/
theorem dichotomy_of_min {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V}
    (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ¬ AttachmentHyp G C Y F')
    {F' : Set V} (hsub : F' ⊆ F) (hne : F' ≠ F) (hconn : ConnectedSet G F') :
    ¬ ((∃ a ∈ attachments G F' {u : V | u ∈ C}, ∃ b ∈ attachments G F' {u : V | u ∈ C},
          OppositeWheelParity G C Y a b) ∧
       (∃ a ∈ attachments G F' {u : V | u ∈ C}, ∃ b ∈ attachments G F' {u : V | u ∈ C},
          a ≠ b ∧ ¬ G.Adj a b)) := by
  rintro ⟨h1, h2⟩
  exact hmin F' hsub hne ⟨fun f hf => hFC f (hsub hf), fun f hf => hFY f (hsub hf), hconn,
    fun f hf => hFnc f (hsub hf), h1, h2⟩

/-- **PAPER**: *"Since `k ≥ 2` it follows that `X₁ ∪ X₂ = X`."*  Every `f_i` lies in
`F \ {f_k}` or in `F \ {f₁}` as soon as `k ≥ 2`. -/
theorem attachments_union {G : SimpleGraph V} {C : List V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    attachments G {z : V | z ∈ SPGT.interior P} {u : V | u ∈ C}
      = attachments G ({z : V | z ∈ SPGT.interior P} \ {P[P.length - 2]'(by omega)})
            {u : V | u ∈ C}
        ∪ attachments G ({z : V | z ∈ SPGT.interior P} \ {P[1]'(by omega)})
            {u : V | u ∈ C} := by
  have hnd := PathBasics.path_nodup hP
  ext u
  constructor
  · rintro ⟨huC, f, hf, hadj⟩
    obtain ⟨k, hk, h1, h2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP hf
    by_cases hkl : k = P.length - 2
    · refine Or.inr ⟨huC, _, ⟨PathBasics.getElem_mem_interior hP hk h1 h2, ?_⟩, hadj⟩
      intro hcon
      have := (List.Nodup.getElem_inj_iff hnd).mp hcon
      omega
    · refine Or.inl ⟨huC, _, ⟨PathBasics.getElem_mem_interior hP hk h1 h2, ?_⟩, hadj⟩
      intro hcon
      exact hkl ((List.Nodup.getElem_inj_iff hnd).mp hcon)
  · rintro (⟨huC, f, hf, hadj⟩ | ⟨huC, f, hf, hadj⟩)
    · exact ⟨huC, f, hf.1, hadj⟩
    · exact ⟨huC, f, hf.1, hadj⟩

/-- `f_k ∈ F`, so `F \ {f_k}` is a proper subset of `F`. -/
theorem sdiff_last_ne {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    ({z : V | z ∈ SPGT.interior P} \ {P[P.length - 2]'(by omega)})
      ≠ {z : V | z ∈ SPGT.interior P} := by
  intro he
  have hmem : (P[P.length - 2]'(by omega)) ∈ {z : V | z ∈ SPGT.interior P} :=
    PathBasics.getElem_mem_interior hP (by omega) (by omega) (by omega)
  rw [← he] at hmem
  exact hmem.2 rfl

/-- `f₁ ∈ F`, so `F \ {f₁}` is a proper subset of `F`. -/
theorem sdiff_first_ne {G : SimpleGraph V} {P : List V} (hP : IsPathList G P)
    (h4 : 4 ≤ P.length) :
    ({z : V | z ∈ SPGT.interior P} \ {P[1]'(by omega)})
      ≠ {z : V | z ∈ SPGT.interior P} := by
  intro he
  have hmem : (P[1]'(by omega)) ∈ {z : V | z ∈ SPGT.interior P} :=
    PathBasics.getElem_mem_interior hP (by omega) (by omega) (by omega)
  rw [← he] at hmem
  exact hmem.2 rfl

/-! ### Vocabulary for the printed claims

`Att G C Z` is the paper's *"set of attachments of `Z` in `C`"*; `HasOpp` and `HasNonadj` are
the two clauses that 16.2's hypotheses put on `X`, and that the minimality dichotomy negates.
-/

/-- The paper's *"the set of attachments of `Z` in `C`"*. -/
abbrev Att (G : SimpleGraph V) (C : List V) (Z : Set V) : Set V :=
  attachments G Z {u : V | u ∈ C}

/-- *"some two members of `Z` have opposite wheel-parity"*.  Its negation is the paper's
*"all members of `Z` have the same wheel-parity"*. -/
def HasOpp (G : SimpleGraph V) (C : List V) (Y : Set V) (Z : Set V) : Prop :=
  ∃ a ∈ Z, ∃ b ∈ Z, OppositeWheelParity G C Y a b

/-- *"some two members of `Z` are non-adjacent"*.  Its negation is the paper's *"there are at
most two members of `Z`, adjacent if there are two"* (a set of pairwise adjacent vertices of a
hole has at most two members). -/
def HasNonadj (G : SimpleGraph V) (Z : Set V) : Prop :=
  ∃ a ∈ Z, ∃ b ∈ Z, a ≠ b ∧ ¬ G.Adj a b

/-- **The configuration the printed proof works in from the paragraph after claim (1)
onwards.**

PAPER: *"From (1) we may assume there are nonadjacent vertices in `X` with opposite
wheel-parity, say `x₁, x₂`, and therefore `F` is the interior of a path between `x₁, x₂`, from
the minimality of `F`. … there is a path `p₁-f₁-⋯-f_k-p_m` where `F = {f₁, …, f_k}`. Let `X₁` be
the set of attachments in `C` of `F \ {f_k}`, and `X₂` the set of attachments of `F \ {f₁}`.
From the minimality of `F`, for `i = 1, 2` either all members of `X_i` have the same
wheel-parity, or there are at most two members of `X_i`, adjacent if there are two. Since
`k ≥ 2` it follows that `X₁ ∪ X₂ = X`."*

`P` is the path `p₁-f₁-⋯-f_k-p_m`, so `x₁ = p₁`, `x₂ = p_m`, `f₁ = P[1]`, `f_k = P[|P|-2]`,
`k = |P| - 2 = |F| ≥ 2` and `4 ≤ |P|`.  `X₁ = Att G C (F \ {f_k})`, `X₂ = Att G C (F \ {f₁})`.

Minimality itself is not a field: it enters only through `dich₁`, `dich₂`, which is all the
printed proof uses it for after claim (1). -/
structure Config (G : SimpleGraph V) (C : List V) (Y : Set V) (F : Set V) (P : List V)
    (x₁ x₂ f₁ fk : V) : Prop where
  inF6 : InF6 G
  wheel : IsWheel G C Y
  notC : ∀ f ∈ F, f ∉ C
  notY : ∀ f ∈ F, f ∉ Y
  notComplete : ∀ f ∈ F, ¬ VertexComplete G f Y
  path : IsPathFrom G P x₁ x₂
  len : 4 ≤ P.length
  interiorEq : F = {z : V | z ∈ SPGT.interior P}
  fstEq : P[1]? = some f₁
  lstEq : P[P.length - 2]? = some fk
  dich₁ : ¬ (HasOpp G C Y (Att G C (F \ {fk})) ∧ HasNonadj G (Att G C (F \ {fk})))
  dich₂ : ¬ (HasOpp G C Y (Att G C (F \ {f₁})) ∧ HasNonadj G (Att G C (F \ {f₁})))
  union : Att G C F = Att G C (F \ {fk}) ∪ Att G C (F \ {f₁})
  att₁ : x₁ ∈ Att G C F
  att₂ : x₂ ∈ Att G C F
  opp : OppositeWheelParity G C Y x₁ x₂
  nadj : ¬ G.Adj x₁ x₂

/-- **Claim (2)**: *"`X₁` and `X₂` do not both have members of opposite wheel-parity."* -/
def Claim2 (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V) (F : Set V) (P : List V) (x₁ x₂ f₁ fk : V),
    Config G C Y F P x₁ x₂ f₁ fk →
    ¬ (HasOpp G C Y (Att G C (F \ {fk})) ∧ HasOpp G C Y (Att G C (F \ {f₁})))

/-- **Claim (3)**: *"If `X₁` has members of opposite wheel-parity then the theorem holds."*

The printed proof of (3) derives a **contradiction** (it ends *"…a contradiction. This proves
(3)"*), so the Lean form is the negation.  Its proof cites claim (2), which is therefore passed
in. -/
def Claim3 (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V) (F : Set V) (P : List V) (x₁ x₂ f₁ fk : V),
    Config G C Y F P x₁ x₂ f₁ fk → Claim2 G →
    ¬ HasOpp G C Y (Att G C (F \ {fk}))

/-- **Claim (4)**: *"At least one of `f₁, f_k` has only one neighbour in `C`."*

The extra hypotheses are the paragraph between (3) and (4): *"From (3) we may assume that all
members of `X₁` have the same wheel-parity, and all members of `X₂` have the opposite
wheel-parity.  It follows that `X₁ ∩ X₂ = ∅`, and so there are no edges between the interior of
`F` and `C`.  So `X₁` is the set of neighbours of `f₁` in `C`, and `X₂` is the set of
neighbours of `f_k` in `C`."* -/
def Claim4 (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V) (F : Set V) (P : List V) (x₁ x₂ f₁ fk : V),
    Config G C Y F P x₁ x₂ f₁ fk →
    Att G C (F \ {fk}) = {u : V | u ∈ C ∧ G.Adj f₁ u} →
    Att G C (F \ {f₁}) = {u : V | u ∈ C ∧ G.Adj fk u} →
    (∀ a ∈ Att G C (F \ {fk}), ∀ b ∈ Att G C (F \ {f₁}), OppositeWheelParity G C Y a b) →
    {u : V | u ∈ C ∧ G.Adj f₁ u}.ncard = 1 ∨ {u : V | u ∈ C ∧ G.Adj fk u}.ncard = 1

/-- **The configuration exists.**  This is the whole paragraph between claim (1) and claim (2),
assembled from `exists_min_path`, `ncard_interior`, `connectedSet_sdiff_*`, `dichotomy_of_min`
and `attachments_union`. -/
theorem exists_config [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    {F : Set V} (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFconn : ConnectedSet G F) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (hFcard : 2 ≤ F.ncard)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ¬ AttachmentHyp G C Y F')
    {x₁ x₂ : V} (hx₁ : x₁ ∈ Att G C F) (hx₂ : x₂ ∈ Att G C F)
    (hopp : OppositeWheelParity G C Y x₁ x₂) (hnadj : ¬ G.Adj x₁ x₂) :
    ∃ (P : List V) (f₁ fk : V), Config G C Y F P x₁ x₂ f₁ fk := by
  classical
  obtain ⟨P, hP, h3, hFP⟩ :=
    exists_min_path hFC hFY hFconn hFnc hmin hx₁ hx₂ hopp hnadj
  have hnd : P.Nodup := PathBasics.path_nodup hP.1
  have hcard : F.ncard = P.length - 2 := by rw [hFP]; exact ncard_interior hnd
  have h4 : 4 ≤ P.length := by omega
  refine ⟨P, P[1]'(by omega), P[P.length - 2]'(by omega), ?_⟩
  refine ⟨hG, hw, hFC, hFY, hFnc, hP, h4, hFP,
    List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
    ?_, ?_, ?_, hx₁, hx₂, hopp, hnadj⟩
  · refine dichotomy_of_min hFC hFY hFnc hmin Set.diff_subset ?_ ?_
    · rw [hFP]; exact sdiff_last_ne hP.1 h4
    · rw [hFP]; exact connectedSet_sdiff_last hP.1 h4
  · refine dichotomy_of_min hFC hFY hFnc hmin Set.diff_subset ?_ ?_
    · rw [hFP]; exact sdiff_first_ne hP.1 h4
    · rw [hFP]; exact connectedSet_sdiff_first hP.1 h4
  · rw [hFP]; exact attachments_union hP.1 h4

/-- **The configuration is symmetric under reversing `P`.**  Reversing `p₁-f₁-⋯-f_k-p_m`
exchanges `p₁ ↔ p_m` and `f₁ ↔ f_k`, hence `X₁ ↔ X₂`.  This is what licenses the paper's
repeated *"and similarly"* / *"from the symmetry we may assume"* in this part of the proof —
in particular *"all members of `X₂` have the opposite wheel-parity"* from claim (3), and
*"we may assume that `X₁` has only one member"* from claim (4). -/
theorem config_reverse {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) :
    Config G C Y F P.reverse x₂ x₁ fk f₁ := by
  have hL : 4 ≤ P.length := h.len
  have hlen : P.reverse.length = P.length := List.length_reverse
  have hint : {z : V | z ∈ SPGT.interior P.reverse} = {z : V | z ∈ SPGT.interior P} := by
    ext z; exact PathBasics.mem_interior_reverse
  refine ⟨h.inF6, h.wheel, h.notC, h.notY, h.notComplete,
    PathBasics.isPathFrom_reverse h.path, by omega, by rw [hint]; exact h.interiorEq,
    ?_, ?_, h.dich₂, h.dich₁, by rw [h.union, Set.union_comm], h.att₂, h.att₁, ?_,
    fun hadj => h.nadj hadj.symm⟩
  · have h1 : P.reverse[1]? = P[P.length - 2]? := by
      rw [List.getElem?_eq_getElem (show 1 < P.reverse.length by omega),
        List.getElem?_eq_getElem (show P.length - 2 < P.length by have := h.len; omega)]
      have := h.len
      exact congrArg some (by
        simp only [List.getElem_reverse]
        exact HoleArithmetic.getElem_congr_idx P _ _ (by omega))
    rw [h1]; exact h.lstEq
  · have h1 : P.reverse[P.reverse.length - 2]? = P[1]? := by
      rw [List.getElem?_eq_getElem (show P.reverse.length - 2 < P.reverse.length by
          have := h.len; omega),
        List.getElem?_eq_getElem (show 1 < P.length by have := h.len; omega)]
      have := h.len
      exact congrArg some (by
        simp only [List.getElem_reverse]
        exact HoleArithmetic.getElem_congr_idx P _ _ (by omega))
    rw [h1]; exact h.fstEq
  · exact ⟨h.opp.1.symm, h.opp.2.2.1, h.opp.2.1,
      fun hs => h.opp.2.2.2 (WheelParity.sameWheelParity_symm hs)⟩

/-! ### `f₁` and `f_k` as members of `F` -/

/-- `f₁ = P[1]`. -/
theorem fst_getElem {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) :
    (P[1]'(by have := h.len; omega)) = f₁ :=
  Option.some_injective _
    ((List.getElem?_eq_getElem (show 1 < P.length by have := h.len; omega)).symm.trans h.fstEq)

/-- `f_k = P[|P| - 2]`. -/
theorem lst_getElem {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) :
    (P[P.length - 2]'(by have := h.len; omega)) = fk :=
  Option.some_injective _
    ((List.getElem?_eq_getElem
      (show P.length - 2 < P.length by have := h.len; omega)).symm.trans h.lstEq)

theorem fst_mem {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) : f₁ ∈ F := by
  have hl := h.len
  rw [h.interiorEq, ← fst_getElem h]
  exact PathBasics.getElem_mem_interior h.path.1 (by omega) (by omega) (by omega)

theorem lst_mem {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) : fk ∈ F := by
  have hl := h.len
  rw [h.interiorEq, ← lst_getElem h]
  exact PathBasics.getElem_mem_interior h.path.1 (by omega) (by omega) (by omega)

/-- `f₁ ≠ f_k`, i.e. `k ≥ 2` — the paper's standing assumption `|F| ≥ 2`. -/
theorem fst_ne_lst {G : SimpleGraph V} {C : List V} {Y : Set V} {F : Set V} {P : List V}
    {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk) : f₁ ≠ fk := by
  have hl := h.len
  intro he
  have e1 := fst_getElem h
  have e2 := lst_getElem h
  have hidx : (P[1]'(by omega)) = (P[P.length - 2]'(by omega)) := by rw [e1, e2]; exact he
  have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup h.path.1)).mp hidx
  omega

/-! ### The paragraph between claims (3) and (4) -/

/-- **PAPER**: *"From (3) we may assume that all members of `X₁` have the same wheel-parity, and
all members of `X₂` have the opposite wheel-parity.  It follows that `X₁ ∩ X₂ = ∅`, and so there
are no edges between the interior of `F` and `C`.  So `X₁` is the set of neighbours of `f₁` in
`C`, and `X₂` is the set of neighbours of `f_k` in `C`."*

The two hypotheses are the conclusion of claim (3) and its mirror image under `config_reverse`.
Wheel-parity is two-valued (`OddWheelParityFacts.exists_parity'`), and `X = X₁ ∪ X₂` contains a
pair of opposite wheel-parity; so the two mono-parity classes `X₁`, `X₂` must be the two
*different* classes, whence they are disjoint and cross-opposite.  Disjointness then forces
every attachment of `F \ {f_k}` to be attached at `f₁` itself. -/
theorem cross_parity [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}
    {F : Set V} {P : List V} {x₁ x₂ f₁ fk : V} (h : Config G C Y F P x₁ x₂ f₁ fk)
    (h1 : ¬ HasOpp G C Y (Att G C (F \ {fk}))) (h2 : ¬ HasOpp G C Y (Att G C (F \ {f₁}))) :
    (∀ a ∈ Att G C (F \ {fk}), ∀ b ∈ Att G C (F \ {f₁}), OppositeWheelParity G C Y a b) ∧
      Att G C (F \ {fk}) = {u : V | u ∈ C ∧ G.Adj f₁ u} ∧
      Att G C (F \ {f₁}) = {u : V | u ∈ C ∧ G.Adj fk u} := by
  classical
  have hl := h.len
  have hC : IsHoleList G C := h.wheel.1.1
  have hBerge : Berge G := h.inF6.1.1.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge h.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  -- a mono-parity class has a single `π`-value
  have hmono : ∀ Z : Set V, ¬ HasOpp G C Y Z → (∀ z ∈ Z, z ∈ C) →
      ∀ a ∈ Z, ∀ b ∈ Z, π a = π b := by
    intro Z hZ hZC a ha b hb
    by_cases hab : a = b
    · rw [hab]
    · have hnopp : ¬ OppositeWheelParity G C Y a b := fun hcon => hZ ⟨a, ha, b, hb, hcon⟩
      have hsame : SameWheelParity G C Y a b := by
        by_contra hcon
        exact hnopp ⟨hab, hZC a ha, hZC b hb, hcon⟩
      exact (hπ a b (hZC a ha) (hZC b hb) hab).mp hsame
  have hC₁ : ∀ z ∈ Att G C (F \ {fk}), z ∈ C := fun z hz => hz.1
  have hC₂ : ∀ z ∈ Att G C (F \ {f₁}), z ∈ C := fun z hz => hz.1
  have hm₁ := hmono _ h1 hC₁
  have hm₂ := hmono _ h2 hC₂
  -- `x₁` and `x₂` cannot lie in the same class
  have hx₁' : x₁ ∈ Att G C (F \ {fk}) ∪ Att G C (F \ {f₁}) := h.union ▸ h.att₁
  have hx₂' : x₂ ∈ Att G C (F \ {fk}) ∪ Att G C (F \ {f₁}) := h.union ▸ h.att₂
  have hπx : π x₁ ≠ π x₂ := fun he =>
    h.opp.2.2.2 ((hπ x₁ x₂ h.opp.2.1 h.opp.2.2.1 h.opp.1).mpr he)
  -- so there are `u ∈ X₁` and `v ∈ X₂` of different `π`-value
  obtain ⟨u, hu, v, hv, huv⟩ :
      ∃ u ∈ Att G C (F \ {fk}), ∃ v ∈ Att G C (F \ {f₁}), π u ≠ π v := by
    rcases hx₁' with hA | hA <;> rcases hx₂' with hB | hB
    · exact absurd (hm₁ _ hA _ hB) hπx
    · exact ⟨x₁, hA, x₂, hB, hπx⟩
    · exact ⟨x₂, hB, x₁, hA, fun he => hπx he.symm⟩
    · exact absurd (hm₂ _ hA _ hB) hπx
  -- every cross pair is therefore of opposite wheel-parity
  have hcross : ∀ a ∈ Att G C (F \ {fk}), ∀ b ∈ Att G C (F \ {f₁}),
      OppositeWheelParity G C Y a b := by
    intro a ha b hb
    have hne : π a ≠ π b := by
      have e1 := hm₁ _ ha _ hu
      have e2 := hm₂ _ hv _ hb
      rw [e1, ← e2]; exact huv
    refine ⟨fun he => hne (by rw [he]), hC₁ a ha, hC₂ b hb, ?_⟩
    intro hs
    exact hne ((hπ a b (hC₁ a ha) (hC₂ b hb) (fun he => hne (by rw [he]))).mp hs)
  -- hence `X₁ ∩ X₂ = ∅`
  have hdisj : ∀ z, z ∈ Att G C (F \ {fk}) → z ∈ Att G C (F \ {f₁}) → False := by
    intro z hz₁ hz₂
    exact (hcross z hz₁ z hz₂).1 rfl
  have hf₁mem : f₁ ∈ F \ {fk} := ⟨fst_mem h, fun hc => fst_ne_lst h hc⟩
  have hfkmem : fk ∈ F \ {f₁} := ⟨lst_mem h, fun hc => fst_ne_lst h hc.symm⟩
  refine ⟨hcross, ?_, ?_⟩
  · ext w
    constructor
    · rintro hw
      obtain ⟨hwC, g, hg, hadj⟩ := hw
      refine ⟨hwC, ?_⟩
      by_cases hgf : g = f₁
      · rw [← hgf]; exact hadj.symm
      · exact absurd (hdisj w ⟨hwC, g, hg, hadj⟩ ⟨hwC, g, ⟨hg.1, hgf⟩, hadj⟩) not_false
    · rintro ⟨hwC, hadj⟩
      exact ⟨hwC, f₁, hf₁mem, hadj.symm⟩
  · ext w
    constructor
    · rintro hw
      obtain ⟨hwC, g, hg, hadj⟩ := hw
      refine ⟨hwC, ?_⟩
      by_cases hgf : g = fk
      · rw [← hgf]; exact hadj.symm
      · exact absurd (hdisj w ⟨hwC, g, ⟨hg.1, hgf⟩, hadj⟩ ⟨hwC, g, hg, hadj⟩) not_false
    · rintro ⟨hwC, hadj⟩
      exact ⟨hwC, fk, hfkmem, hadj.symm⟩

theorem oppositeWheelParity_symm {G : SimpleGraph V} {C : List V} {Y : Set V} {a b : V}
    (h : OppositeWheelParity G C Y a b) : OppositeWheelParity G C Y b a :=
  ⟨h.1.symm, h.2.2.1, h.2.1, fun hs => h.2.2.2 (WheelParity.sameWheelParity_symm hs)⟩

/-! ### The endgame -/

/-- **The endgame of 16.2**: everything from *"From (4) we may assume that `X₁` has only one
member, say `p₁`"* to the last sentence of the printed proof — the paragraph fixing `i`, `j`
and the holes `H₁`, `H₂`, then claim (5), then the closing paragraph.

PAPER (printed pp. 99–100): *"From (4) we may assume that `X₁` has only one member, say `p₁`.
Choose `i, j` with `2 ≤ i, j ≤ n`, such that `p_i, p_j` are adjacent to `f_k`, with `i` minimum
and `j` maximum. … So `p₁` is `Y`-complete. Since `H₁` contains only two `Y`-complete vertices
and they are adjacent, the other is `p₂`, and similarly `p_n` is `Y`-complete."*, then

*"(5) `f_k` has no neighbour in `{p₃, …, p_{j−2}}`."*, then

*"Since `f_k` is adjacent to `p_i`, and `i < j` and `j − i` is even, it follows from (5) that
`i = 2`, and similarly `f_k` has no neighbours in `{p_{i+2}, …, p_{n−1}}` and `j = n`. So `f_k`
has no neighbours in `{p₃, …, p_{n−1}}`, and therefore `p₂, p_n` are its only neighbours,
contradicting that there are nonadjacent vertices in `X` of opposite wheel-parity."*

The `X₁ = {p₁}` normalisation is the hypothesis `{u | u ∈ C ∧ G.Adj f₁ u}.ncard = 1`; claim (4)
supplies it for `f₁` or for `f_k`, and `config_reverse` turns the second case into the first. -/
def Endgame (G : SimpleGraph V) : Prop :=
  ∀ (C : List V) (Y : Set V) (F : Set V) (P : List V) (x₁ x₂ f₁ fk : V),
    Config G C Y F P x₁ x₂ f₁ fk →
    Att G C (F \ {fk}) = {u : V | u ∈ C ∧ G.Adj f₁ u} →
    Att G C (F \ {f₁}) = {u : V | u ∈ C ∧ G.Adj fk u} →
    (∀ a ∈ Att G C (F \ {fk}), ∀ b ∈ Att G C (F \ {f₁}), OppositeWheelParity G C Y a b) →
    {u : V | u ∈ C ∧ G.Adj f₁ u}.ncard = 1 →
    False

/-- **Piece D of 16.2, assembled from claims (2), (3), (4) and the endgame.**

Every use of the printed proof's *"and similarly"* / *"from the symmetry we may assume"* in
this part of 16.2 is `config_reverse`: claim (3) is applied to `P` and to `P.reverse` (giving
that `X₁` and `X₂` are each mono-parity), and the endgame is applied to whichever of `f₁`, `f_k`
claim (4) hands back with a single neighbour on the rim. -/
theorem contradiction_of_claims [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    (hc2 : Claim2 G) (hc3 : Claim3 G) (hc4 : Claim4 G) (hend : Endgame G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    {F : Set V} (hFC : ∀ f ∈ F, f ∉ C) (hFY : ∀ f ∈ F, f ∉ Y)
    (hFconn : ConnectedSet G F) (hFnc : ∀ f ∈ F, ¬ VertexComplete G f Y)
    (hFcard : 2 ≤ F.ncard)
    (hmin : ∀ F' : Set V, F' ⊆ F → F' ≠ F → ¬ AttachmentHyp G C Y F')
    {x₁ x₂ : V}
    (hx₁ : x₁ ∈ attachments G F {u : V | u ∈ C})
    (hx₂ : x₂ ∈ attachments G F {u : V | u ∈ C})
    (hopp : OppositeWheelParity G C Y x₁ x₂) (hnadj : ¬ G.Adj x₁ x₂) :
    False := by
  obtain ⟨P, f₁, fk, hcfg⟩ :=
    exists_config hG hw hFC hFY hFconn hFnc hFcard hmin hx₁ hx₂ hopp hnadj
  -- claim (3), applied to `P` and to `P.reverse`
  have h3 : ¬ HasOpp G C Y (Att G C (F \ {fk})) := hc3 C Y F P x₁ x₂ f₁ fk hcfg hc2
  have h3' : ¬ HasOpp G C Y (Att G C (F \ {f₁})) :=
    hc3 C Y F P.reverse x₂ x₁ fk f₁ (config_reverse hcfg) hc2
  obtain ⟨hcross, hX₁, hX₂⟩ := cross_parity hcfg h3 h3'
  have hcross' : ∀ a ∈ Att G C (F \ {f₁}), ∀ b ∈ Att G C (F \ {fk}),
      OppositeWheelParity G C Y a b :=
    fun a ha b hb => oppositeWheelParity_symm (hcross b hb a ha)
  rcases hc4 C Y F P x₁ x₂ f₁ fk hcfg hX₁ hX₂ hcross with hone | hone
  · exact hend C Y F P x₁ x₂ f₁ fk hcfg hX₁ hX₂ hcross hone
  · exact hend C Y F P.reverse x₂ x₁ fk f₁ (config_reverse hcfg) hX₂ hX₁ hcross' hone

end Workspace.ProofLemmas.OddWheelAttachmentMain
