import Workspace.Types.Pseudowheels
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics

/-! The path, parity, and segment bookkeeping in the last part of 21.2. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm212EndgameTools

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Pseudowheels.SPGT Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common path hypotheses of 21.1, before its three alternatives are checked. -/
structure PathFor211 (G : SimpleGraph V) (X Y : Set V) (P : List V) (a b : V) : Prop where
  disjoint : Disjoint X Y
  nonemptyX : X.Nonempty
  nonemptyY : Y.Nonempty
  antiX : AnticonnectedSet G X
  antiY : AnticonnectedSet G Y
  completeXY : Complete G X Y
  path : IsPathFrom G P a b
  outside : ∀ v ∈ P, v ∉ X ∧ v ∉ Y
  length : 4 ≤ pathLength P
  completeEnds : ∀ v ∈ P, VertexComplete G v X ↔ (v = a ∨ v = b)

/-- PAPER (21.2(7), p. 134): "its ends are `X_{t-1}`-complete, and its
internal vertices are not; so by 13.6, it has even length." -/
theorem PathFor211.even {G : SimpleGraph V} {X Y : Set V} {P : List V} {a b : V}
    (h : PathFor211 G X Y P a b) (hG : InF5 G) : Even (pathLength P) := by
  apply Nat.not_odd_iff_even.mp
  intro hodd
  have hlen : 5 ≤ P.length := by have := h.length; simp only [pathLength] at this; omega
  have hna : ¬ G.Adj a b := by
    have hh := PathBasics.path_ends_not_adj h.path.1 (by omega)
    have hfirst := PathBasics.getElem_zero_of_head? h.path.2.1 (by omega)
    have hlast := PathBasics.getElem_last_of_getLast? h.path.2.2 (by omega)
    simpa only [hfirst, hlast] using hh
  rcases Workspace.Statements.S13.SPGT.thm_13_6 G hG P a b h.path hodd X
      (fun v hv hvP => (h.outside v hvP).1 hv) h.antiX
      ((h.completeEnds a (PathBasics.head_mem h.path.2.1)).mpr (Or.inl rfl))
      ((h.completeEnds b (PathBasics.getLast_mem h.path.2.2)).mpr (Or.inr rfl)) with
    ⟨u, hu, v, hv, huv, huX, hvX⟩ | hshort
  · rcases (h.completeEnds u hu).mp huX with rfl | rfl <;>
      rcases (h.completeEnds v hv).mp hvX with he | he
    · exact G.irrefl (he ▸ huv)
    · exact hna (he ▸ huv)
    · exact hna (he ▸ huv.symm)
    · exact G.irrefl (he ▸ huv)
  · have := h.length
    omega

/-- PAPER (21.2(9), p. 135): if `p_k` were not `Y`-complete, the prefix
would be a pseudowheel, since it already contains the `Y`-complete vertex `p_i`. -/
theorem PathFor211.last_complete {G : SimpleGraph V} {X Y : Set V} {P : List V}
    {a u b : V} (h : PathFor211 G X Y P a b)
    (hno : ¬ ∃ (X : Set V) (P : List V), IsPseudowheel G X Y P)
    (hsecond : P.tail.head? = some u) (ha : VertexComplete G a Y)
    (hu : ¬ VertexComplete G u Y)
    (hother : ∃ v ∈ P, v ≠ a ∧ VertexComplete G v Y) : VertexComplete G b Y := by
  by_contra hb
  apply hno
  refine ⟨X, P, ⟨h.disjoint, h.nonemptyX, h.nonemptyY, h.antiX, h.antiY, h.completeXY⟩,
    a, u, b, ⟨h.path, hsecond, h.outside, ?_⟩, h.completeEnds, ha, hother, hu, hb⟩
  have := h.length
  simp only [pathLength] at this
  omega

/-- An internal maximal run of `Y`-complete vertices with odd path length.
This is the `Y`-segment `P'` in the final paragraph of 21.2. -/
def OddRun (G : SimpleGraph V) (Y : Set V) (P : List V) : Prop :=
  ∃ l r : ℕ, ∃ (_hl : 1 ≤ l) (_hlr : l < r) (_hr : r + 1 < P.length),
    Odd (r - l) ∧
    (∀ j (hj : j < P.length), l ≤ j → j ≤ r → VertexComplete G P[j] Y) ∧
    ¬ VertexComplete G P[l - 1] Y ∧ ¬ VertexComplete G P[r + 1] Y

/-- PAPER (21.2, final paragraph, p. 135): "If `P'` has length > 1 then
21.1 applied to `P` ... So we may assume that `P'` has length 1 ... and again
21.1 applied to `P`". The two cases give alternatives 2 and 3 of 21.1. -/
theorem alternatives_of_oddRun {G : SimpleGraph V} {Y : Set V} {P : List V}
    (h : OddRun G Y P) :
    (∃ (j : ℕ) (_h1 : 1 ≤ j) (_h2 : j ≤ P.length - 3),
      VertexComplete G P[j - 1] Y ∧ VertexComplete G P[j] Y ∧
        VertexComplete G P[j + 1] Y ∧ VertexComplete G P[j + 2] Y) ∨
    (∃ (j : ℕ) (_h1 : 1 ≤ j) (_h2 : j ≤ P.length - 3),
      VertexComplete G P[j] Y ∧ VertexComplete G P[j + 1] Y ∧
        ¬ VertexComplete G P[j - 1] Y ∧ ¬ VertexComplete G P[j + 2] Y) := by
  obtain ⟨l, r, hl, hlr, hr, hodd, hc, hleft, hright⟩ := h
  by_cases he : r = l + 1
  · subst r
    exact Or.inr ⟨l, hl, by omega, hc l (by omega) le_rfl (by omega),
      hc (l + 1) (by omega) (by omega) le_rfl, hleft, hright⟩
  · have hthree : l + 3 ≤ r := by
      obtain ⟨d, hd⟩ := hodd
      omega
    refine Or.inl ⟨l + 1, by omega, by omega, ?_, ?_, ?_, ?_⟩
    · exact hc _ (by omega) (by omega) (by omega)
    · exact hc _ (by omega) (by omega) (by omega)
    · exact hc _ (by omega) (by omega) (by omega)
    · exact hc _ (by omega) (by omega) (by omega)

end Workspace.ProofLemmas.Thm212EndgameTools
