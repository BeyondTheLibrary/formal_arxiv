import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OddWheelSpan
import Workspace.ProofLemmas.OddWheelArc
import Workspace.ProofLemmas.OddWheelClaimOneYes
import Workspace.ProofLemmas.OddWheelClaimOneNoEnd
import Workspace.ProofLemmas.RimReverse

/-!
# Claim (1) of the printed proof of 16.1

PAPER (16.1, printed p. 96), claim (1):

> *"Let `P` be a path in `C` of length `≥ 1`, such that its ends are adjacent to `v` and have
> opposite wheel-parity.  Then either some internal vertex of `P` is a neighbour of `v`, or `P`
> has length `1`."*

`OddWheelSpan.Claim1 G C Y v` is exactly that statement, phrased on cyclic positions of the rim
(the form the printed argument uses: *"let `C` have vertices `p₁, …, pₙ` in order, and let `P`
be the path `p₁-⋯-p_j`"*).  With it, `OddWheelTrichotomy.thm_16_1_of_claim1` delivers 16.1.

## The printed proof, step by step

> *"For let `C` have vertices `p₁, …, pₙ` in order, and let `P` be the path `p₁-⋯-p_j` say, where
> `j < n`.  We assume no internal vertex of `P` is a neighbour of `v`, and that `j ≥ 3`.  From
> the hole `v-p₁-⋯-p_j-v` it follows that `j` is odd."*  — `OddWheelArc.even_L`.

> *"Since `p₁, p_j` have opposite wheel-parity with respect to `(C,Y)`, there are an odd number
> of `Y`-complete edges in `P`."*  — `OddWheelArc.odd_arcCount`.

> *"Choose `Y' ⊆ Y` minimal such that `Y'` is anticonnected and there are an odd number of
> `Y'`-complete edges in `P`."*  — `OddWheelArc.exists_minimal`.  (The printed sentence omits
> *"and `v` is not `Y'`-complete"*, which the rest of the argument uses and which is preserved
> by the choice: `v` is not `Y`-complete, so it fails to be `Z`-complete for every `Z ⊆ Y` that
> witnesses a non-neighbour of `v`; the minimisation is therefore carried out inside the family
> of anticonnected `Z ⊆ Y` with odd arc-count to which `v` is *not* complete.)

> *"From 2.3 applied to the hole `v-p₁-⋯-p_j-v`, it contains just one `Y'`-complete edge and only
> two `Y'`-complete vertices.  Hence there exists `i` with `1 ≤ i < j` such that `p_i, p_{i+1}`
> are the only `Y'`-complete vertices in `P`."*  — `OddWheelArc.two_complete`.

> *"Since `j` is odd, it follows that exactly one of `i − 1`, `j − i` is even; so (by replacing
> `P` by its reverse if necessary) we may assume that `i` is odd."*  — the parity split below.
> (The printed *"`j − i`"* is a slip for *"`j − i − 1`"*, the length of the second flank
> `p_{i+1}-⋯-p_j`: the two flanks have lengths `i−1` and `j−i−1`, whose sum `j−2` is odd, so
> exactly one of them is even.  With `j − i` the assertion is false, both `i−1` and `j−i` having
> the same parity when `j` is odd.  The conclusion drawn — *"we may assume `i` is odd"* — is the
> one the flank reading gives.)  Reversing `P` is `RimReverse.exists_reverse_rim`.

> *"So `p_j` is different from `p_{i+1}`, and hence `p_j` is not `Y'`-complete.  There are two
> disjoint `Y'`-complete edges in `C`, … Therefore there is a `Y'`-complete vertex in
> `{p_{j+2}, …, p_{n−1}}`."*  — `OddWheelArc.far_complete`.

> *"Suppose that `v` has a neighbour in `{p_{j+2}, …, p_{n−1}}`. …"*  —
> `OddWheelClaimOneYes.branch_yes`.

> *"This proves that `v` has no neighbour in `{p_{j+2}, …, p_{n−1}}`. …"*  —
> `OddWheelClaimOneNoEnd.branch_no` (whose configuration analysis is
> `OddWheelClaimOneNoCore.no_config`).

Index dictionary: `n = C.length`; `D t` is the rim vertex at cyclic position `k + t`, so the
paper's `p_a` is `D (a-1)`, its `j` is `L + 1` and its `i` is `s + 1`.  *"`j` is odd"* is
`Even L`; *"`i` is odd"* is `Even s`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelClaimOne

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*}

/-! ### Two facts about reversing the rim -/

/-- A wheel stays a wheel when the rim is read the other way round. -/
private theorem isWheel_reverse {G : SimpleGraph V} {C : List V} {Y : Set V}
    (hw : IsWheel G C Y) : IsWheel G C.reverse Y := by
  obtain ⟨⟨hC, hlen⟩, ⟨hne, hanti, hdisj⟩, a, b, c, d, ha, hb, hc, hd, hab, hcd, e1, e2, e3, e4⟩ :=
    hw
  refine ⟨⟨HoleBasics.isHoleList_reverse hC, ?_⟩, ⟨hne, hanti, ?_⟩,
    a, b, c, d, List.mem_reverse.mpr ha, List.mem_reverse.mpr hb, List.mem_reverse.mpr hc,
    List.mem_reverse.mpr hd, hab, hcd, e1, e2, e3, e4⟩
  · rwa [HoleBasics.holeLength_reverse]
  · intro w hw'
    exact hdisj w (List.mem_reverse.mp hw')

/-- The number of `Z`-complete edges on an arc does not depend on the direction in which the arc
is traversed. -/
private theorem arcCount_rev {G : SimpleGraph V} {Z : Set V} {C C₂ : List V} :
    ∀ (L k k₂ : ℕ),
      (∀ t, t < L → (WheelParity.CycEdge G Z C₂ (k₂ + t) ↔
        WheelParity.CycEdge G Z C (k + (L - 1 - t)))) →
      OddWheelArc.arcCount G Z C₂ k₂ L = OddWheelArc.arcCount G Z C k L := by
  intro L
  induction L with
  | zero => intro k k₂ _; rw [OddWheelArc.arcCount_zero, OddWheelArc.arcCount_zero]
  | succ L ih =>
      intro k k₂ h
      have e1 : OddWheelArc.arcCount G Z C₂ k₂ (L + 1)
          = OddWheelArc.arcCount G Z C₂ k₂ L + OddWheelArc.arcCount G Z C₂ (k₂ + L) 1 :=
        OddWheelArc.arcCount_split Z k₂ L 1
      have e2 : OddWheelArc.arcCount G Z C k (L + 1)
          = OddWheelArc.arcCount G Z C k 1 + OddWheelArc.arcCount G Z C (k + 1) L := by
        have h2 := OddWheelArc.arcCount_split (G := G) (C := C) Z k 1 L
        rwa [show 1 + L = L + 1 from by omega] at h2
      have hhead : OddWheelArc.arcCount G Z C₂ (k₂ + L) 1
          = OddWheelArc.arcCount G Z C k 1 := by
        have hL := h L (by omega)
        simp only [show L + 1 - 1 - L = 0 from by omega, Nat.add_zero] at hL
        by_cases hc : WheelParity.CycEdge G Z C₂ (k₂ + L)
        · rw [OddWheelArc.arcCount_one_pos hc, OddWheelArc.arcCount_one_pos (hL.mp hc)]
        · rw [OddWheelArc.arcCount_one_neg hc,
            OddWheelArc.arcCount_one_neg (fun hh => hc (hL.mpr hh))]
      have htail : OddWheelArc.arcCount G Z C₂ k₂ L
          = OddWheelArc.arcCount G Z C (k + 1) L := by
        refine ih (k + 1) k₂ (fun t ht => ?_)
        have h3 := h t (by omega)
        rwa [show k + (L + 1 - 1 - t) = k + 1 + (L - 1 - t) from by omega] at h3
      omega

/-! ### The body of the printed proof, once `i` has been arranged to be odd -/

/-- Everything from *"So `p_j` is different from `p_{i+1}`"* to the end of the printed proof of
claim (1), i.e. the two branches *"Suppose that `v` has a neighbour in `{p_{j+2},…,p_{n−1}}`"*
and *"This proves that `v` has no neighbour in `{p_{j+2},…,p_{n−1}}`"*. -/
private theorem core [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y Y' : Set V} {v : V} {D : ℕ → V} {k n L s : ℕ}
    (hw : IsWheel G C Y)
    (hC : IsHoleList G C) (hn : 0 < C.length) (hnn : C.length = n) (hn6 : 6 ≤ n)
    (hneven : Even n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t))
    (hvC : v ∉ C) (hvY : v ∉ Y)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hLeven : Even L)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hY'Y : Y' ⊆ Y) (hY'anti : AnticonnectedSet G Y') (hvY' : v ∉ Y')
    (hvZ : ¬ VertexComplete G v Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hmin : ∀ Z : Set V, Z ⊆ Y' → AnticonnectedSet G Z →
      Odd (OddWheelArc.arcCount G Z C k L) → ¬ VertexComplete G v Z → Z = Y')
    (hseven : Even s) (hsL : s + 1 ≤ L)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1)) :
    False := by
  -- *"So `p_j` is different from `p_{i+1}`"*: `s + 1` is odd and `L` is even.
  have hsL' : s + 1 < L := by
    rw [Nat.even_iff] at hLeven hseven
    omega
  -- *"There are two disjoint `Y'`-complete edges in `C` … Therefore there is a `Y'`-complete
  -- vertex in `{p_{j+2},…,p_{n−1}}`."*
  obtain ⟨hn4, hfar⟩ :=
    OddWheelArc.far_complete hG.1.1.1 hw hY'Y hC hn hD hnn hL1 hL2 hLeven hseven hsL honly
  by_cases hyes : ∃ t, L + 2 ≤ t ∧ t ≤ n - 2 ∧ G.Adj v (D t)
  · exact OddWheelClaimOneYes.branch_yes hG hw hC hn hn6 hneven hD hnn hvC hvY hL1 hL2 hLeven
      hn4 hvD hY'Y hY'anti hvY' hvZ hCY' hseven hsL' hcs hcs1 honly hfar hyes
  · push_neg at hyes
    exact OddWheelClaimOneNoEnd.branch_no hG hw hC hn hn6 hneven hD hnn hvC hvY hL1 hL2 hLeven
      hn4 hvD hY'Y hY'anti hvY' hvZ hCY' hmin hseven hsL' hcs hcs1 honly hfar hyes

/-! ### Claim (1) -/

/-- **Claim (1) of the printed proof of 16.1.**

PAPER: *"Let `P` be a path in `C` of length `≥ 1`, such that its ends are adjacent to `v` and
have opposite wheel-parity.  Then either some internal vertex of `P` is a neighbour of `v`, or
`P` has length `1`."* -/
theorem claim_one [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V}
    (hvC : v ∉ C) (hvY : v ∉ Y) (hvnc : ¬ VertexComplete G v Y) :
    OddWheelSpan.Claim1 G C Y v := by
  intro k L x y hL1 hLn hx hy hvx hvy hint hopp
  by_contra hLne
  -- *"and that `j ≥ 3`"*
  have hL2 : 2 ≤ L := by omega
  have hBerge : Berge G := hG.1.1.1
  have hC : IsHoleList G C := hw.1.1
  have h6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hneven : Even C.length := by
    have h := hBerge.1 C hC
    rwa [holeLength] at h
  -- *"let `C` have vertices `p₁, …, pₙ` in order"*
  obtain ⟨D, hD⟩ := OddWheelArc.rim_exists (C := C) hn k
  have hx0 : D 0 = x := by
    have h := hD 0
    rw [Nat.add_zero] at h
    exact (Option.some_injective _ (hx.symm.trans h)).symm
  have hyL : D L = y := (Option.some_injective _ (hy.symm.trans (hD L))).symm
  -- *"We assume no internal vertex of `P` is a neighbour of `v`"*
  have hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)) := by
    intro t ht
    constructor
    · intro hadj
      by_contra hcon
      push_neg at hcon
      refine hint t (by omega) (by omega) ⟨D t, hD t, ?_⟩
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hadj.symm
    · rintro (rfl | rfl)
      · rw [hx0]; exact hvx
      · rw [hyL]; exact hvy
  -- *"From the hole `v-p₁-⋯-p_j-v` it follows that `j` is odd."*
  have hLeven : Even L := OddWheelArc.even_L hBerge hC hn hD rfl hL2 hLn hvC hvD
  -- *"there are an odd number of `Y`-complete edges in `P`"*
  have hodd : Odd (OddWheelArc.arcCount G Y C k L) :=
    OddWheelArc.odd_arcCount hBerge hw hn hx hy hopp
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  -- *"Choose `Y' ⊆ Y` minimal …"*
  obtain ⟨Y', hY'Y, hY'anti, hY'odd, hvZ, hmin⟩ :=
    OddWheelArc.exists_minimal hYanti hvnc hodd
  have hvY' : v ∉ Y' := fun h => hvY (hY'Y h)
  have hCY' : ∀ w ∈ C, w ∉ Y' := fun w hwC h => hw.2.1.2.2 w hwC (hY'Y h)
  -- *"Hence there exists `i` with `1 ≤ i < j` such that `p_i, p_{i+1}` are the only
  -- `Y'`-complete vertices in `P`."*
  obtain ⟨s, hs1, hcs, hcs1, honly⟩ :=
    OddWheelArc.two_complete hBerge hC hn hD rfl hL2 hLn hvC hvY' hY'anti hCY' hvD hvZ hY'odd
  -- *"(by replacing `P` by its reverse if necessary) we may assume that `i` is odd"*
  by_cases hse : Even s
  · exact core hG hw hC hn rfl h6 hneven hD hvC hvY hL2 hLn hLeven hvD hY'Y hY'anti hvY' hvZ
      hCY' hmin hse hs1 hcs hcs1 honly
  · -- the reversed rim
    obtain ⟨k₂, D₂, hD₂, hrel⟩ :=
      RimReverse.exists_reverse_rim (C := C) (D := D) (k := k) hn rfl hD L
    have hlen₂ : C.reverse.length = C.length := List.length_reverse
    have hn₂ : 0 < C.reverse.length := by rw [hlen₂]; exact hn
    have hD₂rel : ∀ t, t ≤ L → D₂ t = D (L - t) := by
      intro t ht
      exact hrel t (L - t) (by rw [show t + (L - t) = L from by omega])
    have hsodd : s % 2 = 1 := Nat.not_even_iff.mp hse
    have hLe : L % 2 = 0 := Nat.even_iff.mp hLeven
    have hvD₂ : ∀ t, t ≤ L → (G.Adj v (D₂ t) ↔ (t = 0 ∨ t = L)) := by
      intro t ht
      rw [hD₂rel t ht, hvD (L - t) (by omega)]
      constructor
      · rintro (h | h)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      · rintro (h | h)
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
    have hcs₂ : VertexComplete G (D₂ (L - s - 1)) Y' := by
      rw [hD₂rel (L - s - 1) (by omega), show L - (L - s - 1) = s + 1 from by omega]
      exact hcs1
    have hcs1₂ : VertexComplete G (D₂ (L - s - 1 + 1)) Y' := by
      rw [hD₂rel (L - s - 1 + 1) (by omega), show L - (L - s - 1 + 1) = s from by omega]
      exact hcs
    have honly₂ : ∀ t, t ≤ L → VertexComplete G (D₂ t) Y' →
        (t = L - s - 1 ∨ t = L - s - 1 + 1) := by
      intro t ht hcomp
      rw [hD₂rel t ht] at hcomp
      rcases honly (L - t) (by omega) hcomp with h | h <;> omega
    have hmin₂ : ∀ Z : Set V, Z ⊆ Y' → AnticonnectedSet G Z →
        Odd (OddWheelArc.arcCount G Z C.reverse k₂ L) → ¬ VertexComplete G v Z → Z = Y' := by
      intro Z hZ hZa hZodd hZv
      refine hmin Z hZ hZa ?_ hZv
      have heq : OddWheelArc.arcCount G Z C.reverse k₂ L = OddWheelArc.arcCount G Z C k L := by
        refine arcCount_rev L k k₂ (fun t ht => ?_)
        have ha₂ : C.reverse[(k₂ + t) % C.reverse.length]? = some (D₂ t) := hD₂ t
        have hb₂ : C.reverse[(k₂ + t + 1) % C.reverse.length]? = some (D₂ (t + 1)) := by
          have h4 := hD₂ (t + 1)
          rwa [show k₂ + (t + 1) = k₂ + t + 1 from by omega] at h4
        have ha : C[(k + (L - 1 - t)) % C.length]? = some (D (L - 1 - t)) := hD (L - 1 - t)
        have hb : C[(k + (L - 1 - t) + 1) % C.length]? = some (D (L - t)) := by
          have h4 := hD (L - t)
          rwa [show k + (L - t) = k + (L - 1 - t) + 1 from by omega] at h4
        rw [OddWheelArc.cycEdge_iff' ha₂ hb₂, OddWheelArc.cycEdge_iff' ha hb,
          hD₂rel t (by omega), hD₂rel (t + 1) (by omega),
          show L - (t + 1) = L - 1 - t from by omega]
        exact ⟨fun h => WheelParity.edgeComplete_symm h, fun h => WheelParity.edgeComplete_symm h⟩
      rwa [heq] at hZodd
    refine core hG (isWheel_reverse hw) (HoleBasics.isHoleList_reverse hC) hn₂ hlen₂ h6 hneven
      hD₂ (fun h => hvC (List.mem_reverse.mp h)) hvY hL2 hLn hLeven hvD₂ hY'Y hY'anti hvY' hvZ
      (fun w hwC h => hCY' w (List.mem_reverse.mp hwC) h) hmin₂ ?_ (by omega) hcs₂ hcs1₂ honly₂
    · rw [Nat.even_iff]
      omega

end Workspace.ProofLemmas.OddWheelClaimOne
