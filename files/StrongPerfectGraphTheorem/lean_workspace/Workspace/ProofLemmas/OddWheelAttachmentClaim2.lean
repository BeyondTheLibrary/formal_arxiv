import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentMain

/-!
# 16.2, claim (2)

PAPER (16.2, printed p. 98):

> **(2) `X₁` and `X₂` do not both have members of opposite wheel-parity.**
> For suppose they do; then `X₁, X₂` both consist of exactly two adjacent vertices of opposite
> wheel-parity, say `X₁ = {p₁, p₂}` and `X₂ = {p_{m'}, p_{m'+1}}`.  So `p₁, p₂, p_{m'},
> p_{m'+1}` are all `Y`-complete, and all distinct since two of them are nonadjacent and of
> opposite wheel-parity.  So the only edges between `F` and `{p₁, p₂}` are incident with `f₁`,
> and similarly for `f_k`.  But then `G` contains a long prism since `n ≥ 6`, a contradiction.
> This proves (2).

The four printed steps are, in order, `two_adjacent` (the dichotomy of the minimality of `F`
forces each `X_i` to be a single edge of the rim), `not_share` (the four ends are distinct),
the `honly`/`hadj` block inside `claim_two` (the only edges between `F` and `C` are the four
listed ones) and `long_prism`.

The long prism is the one the paper leaves to the reader: its two triangles are
`{f₁, p₁, p₂}` and `{f_k, p_{m'}, p_{m'+1}}`, and the three paths joining them are
`f₁-⋯-f_k` together with the two arcs into which the four rim vertices cut `C`.  Those two
arcs have lengths summing to `n - 2 ≥ 4`, so one of them has length `> 1` — which is exactly
the printed *"since `n ≥ 6`"*.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.OddWheelAttachmentClaim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs
open Workspace.ProofLemmas.OddWheelAttachmentMain

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### A hole has no triangle -/

/-- Three pairwise-adjacent vertices of a hole are impossible. -/
theorem hole_no_triangle_mem {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) {u v w : V}
    (hu : u ∈ C) (hv : v ∈ C) (hw : w ∈ C)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : G.Adj v w) : False := by
  have hn4 : 4 ≤ C.length := hC.1
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  obtain ⟨l, hl, rfl⟩ := List.getElem_of_mem hw
  have d1 : i ≠ j := by rintro rfl; exact G.irrefl huv
  have d2 : i ≠ l := by rintro rfl; exact G.irrefl huw
  have d3 : j ≠ l := by rintro rfl; exact G.irrefl hvw
  have e1 := WheelParity.hole_adj_index hC hi hj huv
  have e2 := WheelParity.hole_adj_index hC hi hl huw
  have e3 := WheelParity.hole_adj_index hC hj hl hvw
  omega

/-! ### *"`X₁`, `X₂` both consist of exactly two adjacent vertices of opposite wheel-parity"* -/

/-- **The first printed sentence of (2).**  A set of rim vertices that has two members of
opposite wheel-parity but no two non-adjacent members is a single edge of the rim: its members
are pairwise adjacent, and three pairwise adjacent vertices would be a triangle of the hole. -/
theorem two_adjacent {G : SimpleGraph V} {C : List V} {Y : Set V} (hC : IsHoleList G C)
    {Z : Set V} (hZC : ∀ z ∈ Z, z ∈ C)
    (hdich : ¬ (HasOpp G C Y Z ∧ HasNonadj G Z)) (hopp : HasOpp G C Y Z) :
    ∃ u v : V, u ∈ Z ∧ v ∈ Z ∧ G.Adj u v ∧ OppositeWheelParity G C Y u v ∧
      ∀ z ∈ Z, z = u ∨ z = v := by
  have hnn : ¬ HasNonadj G Z := fun hn => hdich ⟨hopp, hn⟩
  have hadjall : ∀ p ∈ Z, ∀ q ∈ Z, p ≠ q → G.Adj p q := by
    intro p hp q hq hne
    by_contra hc
    exact hnn ⟨p, hp, q, hq, hne, hc⟩
  obtain ⟨u, hu, v, hv, hopuv⟩ := hopp
  refine ⟨u, v, hu, hv, hadjall u hu v hv hopuv.1, hopuv, ?_⟩
  intro z hz
  by_contra hcon
  push Not at hcon
  exact hole_no_triangle_mem hC (hZC z hz) (hZC u hu) (hZC v hv)
    (hadjall z hz u hu hcon.1) (hadjall z hz v hv hcon.2)
    (hadjall u hu v hv hopuv.1)

/-! ### *"and all distinct since two of them are nonadjacent and of opposite wheel-parity"* -/

/-- **The distinctness step.**  If the two rim edges `uv` and `wz` shared an end, then every
pair of members of `X` of opposite wheel-parity would be adjacent — because wheel-parity is
two-valued, so the shared end forces the two far ends into the same class.  That contradicts
the standing hypothesis that `X` has a *non-adjacent* pair of opposite wheel-parity. -/
theorem not_share {G : SimpleGraph V} {π : V → ℕ} {X : Set V} {u v w z x₁ x₂ : V}
    (hπ2 : ∀ t : V, π t < 2)
    (hX : ∀ t ∈ X, t = u ∨ t = v ∨ t = w ∨ t = z)
    (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hnadj : ¬ G.Adj x₁ x₂) (hπx : π x₁ ≠ π x₂)
    (huv : G.Adj u v) (hwz : G.Adj w z)
    (hπuv : π u ≠ π v) (hπwz : π w ≠ π z) : u ≠ w := by
  intro huw
  rw [← huw] at hwz hπwz hX
  have hvz : π v = π z := by
    have t1 := hπ2 u; have t2 := hπ2 v; have t3 := hπ2 z; omega
  have hall : ∀ p ∈ X, ∀ q ∈ X, π p ≠ π q → G.Adj p q := by
    intro p hp q hq hpq
    rcases hX p hp with hp' | hp' | hp' | hp' <;> rcases hX q hq with hq' | hq' | hq' | hq' <;>
      rw [hp', hq'] at hpq ⊢ <;>
      first
        | exact huv
        | exact huv.symm
        | exact hwz
        | exact hwz.symm
        | (exfalso; omega)
  exact hnadj (hall x₁ hx₁ x₂ hx₂ hπx)

/-! ### The long prism -/

/-- A cyclic position reached by walking forward from `base` at most as far as one full turn
is never equal to a position strictly before `base` (and non-zero). -/
theorem mod_ne_of_range {n s base t : ℕ} (hn : 0 < n) (hb : base + t ≤ n)
    (hlow : s < base) (hs0 : 0 < s) : (base + t) % n ≠ s := by
  rcases Nat.lt_or_ge (base + t) n with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt]; omega
  · have he : base + t = n := by omega
    rw [he, Nat.mod_self]; omega

/-- **The long prism of claim (2).**

Two triangles `{g₁, D₀, D₁}` and `{g₂, D_γ, D_{γ+1}}`, the first sitting on the rim at cyclic
positions `0, 1` and the second at `γ, γ+1`, joined by a path `S` from `g₁` to `g₂` that is
disjoint from the rim and whose only edges to the rim are the four triangle edges.  The three
paths of the prism are `S` and the two arcs `D₁-⋯-D_γ` and `D_{γ+1}-⋯-D₀`, whose lengths sum to
`n - 2 ≥ 4`; so one of them exceeds `1` and the prism is long. -/
theorem long_prism {G : SimpleGraph V} {D : List V} (hD : IsHoleList G D)
    (hpos : 0 < D.length) (hn6 : 6 ≤ D.length) {γ : ℕ} (hγ1 : 2 ≤ γ) (hγ2 : γ + 2 ≤ D.length)
    {g₁ g₂ : V} {S : List V} (hS : IsPathFrom G S g₁ g₂) (hg : g₁ ≠ g₂)
    (hSD : ∀ p ∈ S, p ∉ D)
    (hcross : ∀ p ∈ S, ∀ q ∈ D, (G.Adj p q ↔
      ((p = g₁ ∧ (q = cyc D hpos 0 ∨ q = cyc D hpos 1)) ∨
        (p = g₂ ∧ (q = cyc D hpos γ ∨ q = cyc D hpos (γ + 1)))))) :
    ∃ (α β : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsLongPrism G α β Q₁ Q₂ Q₃ := by
  classical
  have hn : D.length = D.length := rfl
  -- the four rim vertices
  set A : V := cyc D hpos 0 with hA
  set B : V := cyc D hpos 1 with hB
  set Cc : V := cyc D hpos γ with hCc
  set Dd : V := cyc D hpos (γ + 1) with hDd
  have hAD : A ∈ D := cyc_mem hpos 0
  have hBD : B ∈ D := cyc_mem hpos 1
  have hCD : Cc ∈ D := cyc_mem hpos γ
  have hDD : Dd ∈ D := cyc_mem hpos (γ + 1)
  have hg₁S : g₁ ∈ S := (PathBasics.isPathFrom_ends_mem hS).1
  have hg₂S : g₂ ∈ S := (PathBasics.isPathFrom_ends_mem hS).2
  -- the four triangle edges
  have hg₁A : G.Adj g₁ A := (hcross g₁ hg₁S A hAD).mpr (Or.inl ⟨rfl, Or.inl rfl⟩)
  have hg₁B : G.Adj g₁ B := (hcross g₁ hg₁S B hBD).mpr (Or.inl ⟨rfl, Or.inr rfl⟩)
  have hg₂C : G.Adj g₂ Cc := (hcross g₂ hg₂S Cc hCD).mpr (Or.inr ⟨rfl, Or.inl rfl⟩)
  have hg₂D : G.Adj g₂ Dd := (hcross g₂ hg₂S Dd hDD).mpr (Or.inr ⟨rfl, Or.inr rfl⟩)
  have hBA : G.Adj B A := by
    rw [hA, hB, cyc_adj hD hpos]
    exact Or.inr rfl
  have hCDadj : G.Adj Cc Dd := by
    rw [hCc, hDd, cyc_adj hD hpos]
    exact Or.inl rfl
  -- distinctness
  have hne : ∀ s t : ℕ, s < D.length → t < D.length → s ≠ t →
      cyc D hpos s ≠ cyc D hpos t := fun s t hs ht hst => cyc_ne hD hpos hs ht hst
  have hBC : B ≠ Cc := hne 1 γ (by omega) (by omega) (by omega)
  have hBD' : B ≠ Dd := hne 1 (γ + 1) (by omega) (by omega) (by omega)
  have hAC : A ≠ Cc := hne 0 γ (by omega) (by omega) (by omega)
  have hAD' : A ≠ Dd := hne 0 (γ + 1) (by omega) (by omega) (by omega)
  have hg₁C : g₁ ≠ Cc := fun he => hSD g₁ hg₁S (he ▸ hCD)
  have hg₁D : g₁ ≠ Dd := fun he => hSD g₁ hg₁S (he ▸ hDD)
  have hBg : B ≠ g₂ := fun he => hSD g₂ hg₂S (he ▸ hBD)
  have hAg : A ≠ g₂ := fun he => hSD g₂ hg₂S (he ▸ hAD)
  -- the two arcs
  have harc1 : IsPathFrom G (arc D hpos 1 γ) B Cc := by
    have h := arc_isPathFrom hD hpos (a := 1) (L := γ) (by omega) (by omega)
    rw [show (1 : ℕ) + γ - 1 = γ by omega] at h
    exact h
  have harc2 : IsPathFrom G (arc D hpos (γ + 1) (D.length - γ)) Dd A := by
    have h := arc_isPathFrom hD hpos (a := γ + 1) (L := D.length - γ) (by omega) (by omega)
    rw [show γ + 1 + (D.length - γ) - 1 = D.length by omega] at h
    rw [show cyc D hpos D.length = A from
      (cyc_congr hpos (by rw [Nat.mod_self, Nat.zero_mod]))] at h
    exact h
  have harc2' : IsPathFrom G (arc D hpos (γ + 1) (D.length - γ)).reverse A Dd :=
    PathBasics.isPathFrom_reverse harc2
  -- membership decoders for the two arcs
  have hmem1 : ∀ x, x ∈ arc D hpos 1 γ → ∃ t, t < γ ∧ cyc D hpos (1 + t) = x := by
    intro x hx; exact (mem_arc hpos).mp hx
  have hmem2 : ∀ x, x ∈ (arc D hpos (γ + 1) (D.length - γ)).reverse →
      ∃ t, t < D.length - γ ∧ cyc D hpos (γ + 1 + t) = x := by
    intro x hx
    exact (mem_arc hpos).mp (List.mem_reverse.mp hx)
  have harc1D : ∀ x ∈ arc D hpos 1 γ, x ∈ D := by
    intro x hx; obtain ⟨t, ht, rfl⟩ := hmem1 x hx; exact cyc_mem hpos _
  have harc2D : ∀ x ∈ (arc D hpos (γ + 1) (D.length - γ)).reverse, x ∈ D := by
    intro x hx; obtain ⟨t, ht, rfl⟩ := hmem2 x hx; exact cyc_mem hpos _
  -- positions on the first arc are in `[1, γ]`, so they are neither `A` nor `Dd`
  have h1ne : ∀ t, t < γ → cyc D hpos (1 + t) ≠ A ∧ cyc D hpos (1 + t) ≠ Dd := by
    intro t ht
    constructor
    · exact hne (1 + t) 0 (by omega) (by omega) (by omega)
    · exact hne (1 + t) (γ + 1) (by omega) (by omega) (by omega)
  -- positions on the second arc are in `[γ+1, n]`, so they are neither `B` nor `Cc`
  have h2ne : ∀ t, t < D.length - γ → cyc D hpos (γ + 1 + t) ≠ B ∧ cyc D hpos (γ + 1 + t) ≠ Cc := by
    intro t ht
    constructor
    · intro he
      have hmod := cyc_inj hD hpos (he.trans hB)
      rw [Nat.mod_eq_of_lt (show 1 < D.length by omega)] at hmod
      exact mod_ne_of_range hpos (by omega) (by omega) (by omega) hmod
    · intro he
      have hmod := cyc_inj hD hpos (he.trans hCc)
      rw [Nat.mod_eq_of_lt (show γ < D.length by omega)] at hmod
      exact mod_ne_of_range hpos (by omega) (by omega) (by omega) hmod
  refine PrismBasics.formPrism_mk (a0 := g₁) (a1 := B) (a2 := A) (b0 := g₂) (b1 := Cc) (b2 := Dd)
    hg₁B hg₁A hBA hg₂C hg₂D hCDadj hg hg₁C hg₁D hBg hBC hBD' hAg hAC hAD'
    hS harc1 harc2' ?_ ?_ ?_ ?_
  · -- `S` against the first arc
    intro p hp q hq
    obtain ⟨t, ht, rfl⟩ := hmem1 q hq
    obtain ⟨hnA, hnD⟩ := h1ne t ht
    rw [hcross p hp _ (cyc_mem hpos _)]
    constructor
    · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
      · rcases hq with hq | hq
        · exact absurd hq hnA
        · exact Or.inl ⟨rfl, hq⟩
      · rcases hq with hq | hq
        · exact Or.inr ⟨rfl, hq⟩
        · exact absurd hq hnD
    · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
      · exact Or.inl ⟨rfl, Or.inr hq⟩
      · exact Or.inr ⟨rfl, Or.inl hq⟩
  · -- `S` against the second arc
    intro p hp q hq
    obtain ⟨t, ht, rfl⟩ := hmem2 q hq
    obtain ⟨hnB, hnC⟩ := h2ne t ht
    rw [hcross p hp _ (cyc_mem hpos _)]
    constructor
    · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
      · rcases hq with hq | hq
        · exact Or.inl ⟨rfl, hq⟩
        · exact absurd hq hnB
      · rcases hq with hq | hq
        · exact absurd hq hnC
        · exact Or.inr ⟨rfl, hq⟩
    · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
      · exact Or.inl ⟨rfl, Or.inl hq⟩
      · exact Or.inr ⟨rfl, Or.inr hq⟩
  · -- the two arcs against each other: `C` is induced, so only the two rim edges survive
    intro p hp q hq
    obtain ⟨s, hs, rfl⟩ := hmem1 p hp
    obtain ⟨t, ht, rfl⟩ := hmem2 q hq
    have hslt : 1 + s < D.length := by omega
    -- reduce the second position modulo `n`
    rcases Nat.lt_or_ge (γ + 1 + t) D.length with hlt | hge
    · have hkey := fun (h : G.Adj (cyc D hpos (1 + s)) (cyc D hpos (γ + 1 + t))) =>
        cyc_adj_index hD hpos hslt hlt h
      constructor
      · intro hadj
        have e := hkey hadj
        have hst : 1 + s = γ ∧ γ + 1 + t = γ + 1 := by omega
        exact Or.inr ⟨by rw [hCc, hst.1], by rw [hDd, hst.2]⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exfalso
          have e1 := cyc_inj hD hpos (h1.trans hB)
          have e2 := cyc_inj hD hpos (h2.trans hA)
          rw [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt (show 1 < D.length by omega)] at e1
          rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at e2
          omega
        · have e1 := cyc_inj hD hpos (h1.trans hCc)
          have e2 := cyc_inj hD hpos (h2.trans hDd)
          rw [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt (show γ < D.length by omega)] at e1
          rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt (show γ + 1 < D.length by omega)] at e2
          rw [show (1 : ℕ) + s = γ from e1, show γ + 1 + t = γ + 1 from e2]
          exact hCDadj
    · -- the second arc has wrapped: the position is `0`, i.e. the vertex is `A`
      have he : γ + 1 + t = D.length := by omega
      have hzero : cyc D hpos (γ + 1 + t) = A := by
        rw [hA]; exact cyc_congr hpos (by rw [he, Nat.mod_self, Nat.zero_mod])
      rw [hzero]
      constructor
      · intro hadj
        have e := cyc_adj_index hD hpos hslt (show 0 < D.length by omega) hadj
        have hs1 : 1 + s = 1 := by omega
        exact Or.inl ⟨by rw [hB, hs1], rfl⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · have e1 := cyc_inj hD hpos (h1.trans hB)
          rw [Nat.mod_eq_of_lt hslt, Nat.mod_eq_of_lt (show 1 < D.length by omega)] at e1
          rw [show (1 : ℕ) + s = 1 from e1, ← hB]
          exact hBA
        · exfalso
          exact hAD' h2
  · -- the prism is long: the two arcs have lengths summing to `n - 2 ≥ 4`
    have hl1 : pathLength (arc D hpos 1 γ) = γ - 1 := by
      rw [PathBasics.pathLength_eq, arc_length]
    have hl2 : pathLength (arc D hpos (γ + 1) (D.length - γ)).reverse
        = D.length - γ - 1 := by
      rw [PathBasics.pathLength_reverse, PathBasics.pathLength_eq, arc_length]
    rcases Nat.lt_or_ge γ 3 with h | h
    · exact Or.inr (Or.inr (by rw [hl2]; omega))
    · exact Or.inr (Or.inl (by rw [hl1]; omega))

/-! ### Claim (2) -/

/-- **Claim (2) of 16.2.** -/
theorem claim_two [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    OddWheelAttachmentMain.Claim2 G := by
  classical
  rintro C Y F P x₁ x₂ f₁ fk h ⟨ho₁, ho₂⟩
  have hl := h.len
  have hC : IsHoleList G C := h.wheel.1.1
  have hn6 : 6 ≤ C.length := h.wheel.1.2
  have hBerge : Berge G := h.inF6.1.1.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge h.wheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  -- `X₁` and `X₂` are each a single edge of the rim
  obtain ⟨a, b, haZ, hbZ, hab, hopab, hZ₁⟩ :=
    two_adjacent hC (fun z hz => hz.1) h.dich₁ ho₁
  obtain ⟨c, d, hcZ, hdZ, hcd, hopcd, hZ₂⟩ :=
    two_adjacent hC (fun z hz => hz.1) h.dich₂ ho₂
  have hπab : π a ≠ π b := fun he =>
    hopab.2.2.2 ((hπ a b hopab.2.1 hopab.2.2.1 hopab.1).mpr he)
  have hπcd : π c ≠ π d := fun he =>
    hopcd.2.2.2 ((hπ c d hopcd.2.1 hopcd.2.2.1 hopcd.1).mpr he)
  -- `X = X₁ ∪ X₂ ⊆ {a, b, c, d}`
  have hX : ∀ t ∈ Att G C F, t = a ∨ t = b ∨ t = c ∨ t = d := by
    intro t ht
    rcases (h.union ▸ ht : t ∈ Att G C (F \ {fk}) ∪ Att G C (F \ {f₁})) with ht' | ht'
    · rcases hZ₁ t ht' with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · rcases hZ₂ t ht' with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
  have hπx : π x₁ ≠ π x₂ := fun he =>
    h.opp.2.2.2 ((hπ x₁ x₂ h.opp.2.1 h.opp.2.2.1 h.opp.1).mpr he)
  -- the four ends are distinct
  have hXbadc : ∀ t ∈ Att G C F, t = a ∨ t = b ∨ t = d ∨ t = c := by
    intro t ht; rcases hX t ht with h'|h'|h'|h' <;> tauto
  have hXba : ∀ t ∈ Att G C F, t = b ∨ t = a ∨ t = c ∨ t = d := by
    intro t ht; rcases hX t ht with h'|h'|h'|h' <;> tauto
  have hXbadc' : ∀ t ∈ Att G C F, t = b ∨ t = a ∨ t = d ∨ t = c := by
    intro t ht; rcases hX t ht with h'|h'|h'|h' <;> tauto
  have hac : a ≠ c :=
    not_share hπ2 hX h.att₁ h.att₂ h.nadj hπx hab hcd hπab hπcd
  have had : a ≠ d :=
    not_share hπ2 hXbadc h.att₁ h.att₂ h.nadj hπx hab hcd.symm hπab (Ne.symm hπcd)
  have hbc : b ≠ c :=
    not_share hπ2 hXba h.att₁ h.att₂ h.nadj hπx hab.symm hcd (Ne.symm hπab) hπcd
  have hbd : b ≠ d :=
    not_share hπ2 hXbadc' h.att₁ h.att₂ h.nadj hπx hab.symm hcd.symm
      (Ne.symm hπab) (Ne.symm hπcd)
  -- *"the only edges between `F` and `{p₁, p₂}` are incident with `f₁`, and similarly for `f_k`"*
  have honly₁ : ∀ u : V, (u = a ∨ u = b) → ∀ g ∈ F, G.Adj u g → g = f₁ := by
    intro u hu g hg hadj
    by_contra hgf
    have huC : u ∈ C := by rcases hu with rfl | rfl; exacts [haZ.1, hbZ.1]
    have hu₂ : u ∈ Att G C (F \ {f₁}) := ⟨huC, g, ⟨hg, hgf⟩, hadj⟩
    rcases hu with rfl | rfl <;> rcases hZ₂ u hu₂ with h' | h'
    exacts [hac h', had h', hbc h', hbd h']
  have honly₂ : ∀ u : V, (u = c ∨ u = d) → ∀ g ∈ F, G.Adj u g → g = fk := by
    intro u hu g hg hadj
    by_contra hgf
    have huC : u ∈ C := by rcases hu with rfl | rfl; exacts [hcZ.1, hdZ.1]
    have hu₁ : u ∈ Att G C (F \ {fk}) := ⟨huC, g, ⟨hg, hgf⟩, hadj⟩
    rcases hu with rfl | rfl <;> rcases hZ₁ u hu₁ with h' | h'
    exacts [hac h'.symm, hbc h'.symm, had h'.symm, hbd h'.symm]
  -- so each of the four is adjacent to its own `f`
  have hadjf₁ : ∀ u : V, (u = a ∨ u = b) → G.Adj u f₁ := by
    intro u hu
    have hu₁ : u ∈ Att G C (F \ {fk}) := by rcases hu with rfl | rfl; exacts [haZ, hbZ]
    obtain ⟨-, g, hg, hadj⟩ := hu₁
    rw [← honly₁ u hu g hg.1 hadj]
    exact hadj
  have hadjfk : ∀ u : V, (u = c ∨ u = d) → G.Adj u fk := by
    intro u hu
    have hu₂ : u ∈ Att G C (F \ {f₁}) := by rcases hu with rfl | rfl; exacts [hcZ, hdZ]
    obtain ⟨-, g, hg, hadj⟩ := hu₂
    rw [← honly₂ u hu g hg.1 hadj]
    exact hadj
  -- the whole `F`–`C` edge set
  have hFC : ∀ w ∈ C, ∀ g ∈ F, G.Adj w g →
      ((g = f₁ ∧ (w = a ∨ w = b)) ∨ (g = fk ∧ (w = c ∨ w = d))) := by
    intro w hwC g hg hadj
    have hwX : w ∈ Att G C F := ⟨hwC, g, hg, hadj⟩
    rcases hX w hwX with h' | h' | h' | h'
    · exact Or.inl ⟨honly₁ w (Or.inl h') g hg hadj, Or.inl h'⟩
    · exact Or.inl ⟨honly₁ w (Or.inr h') g hg hadj, Or.inr h'⟩
    · exact Or.inr ⟨honly₂ w (Or.inl h') g hg hadj, Or.inl h'⟩
    · exact Or.inr ⟨honly₂ w (Or.inr h') g hg hadj, Or.inr h'⟩
  -- the path `f₁-⋯-f_k`
  have hSpath : IsPathFrom G ((P.drop 1).take (P.length - 2 - 1 + 1)) f₁ fk := by
    have hsl := PathBasics.isPathFrom_slice h.path.1
      (show (1 : ℕ) < P.length - 2 by omega) (show P.length - 2 < P.length by omega)
    rw [fst_getElem h, lst_getElem h] at hsl
    exact hsl
  have hSF : ∀ p ∈ (P.drop 1).take (P.length - 2 - 1 + 1), p ∈ F := by
    intro p hp
    obtain ⟨k, hk, h1, h2, rfl⟩ :=
      (PathBasics.mem_slice_iff P (show (1 : ℕ) ≤ P.length - 2 by omega)
        (show P.length - 2 < P.length by omega)).mp hp
    rw [h.interiorEq]
    exact PathBasics.getElem_mem_interior h.path.1 hk (by omega) (by omega)
  -- re-orient the rim so that `a`, `b` sit at positions `0`, `1`
  obtain ⟨D, hD, hDlen, hDmem, hpos, hone, hD0, hD1⟩ :=
    exists_reorient hC haZ.1 hbZ.1 hab
  have hposD : 0 < D.length := hpos
  have hcyc0 : cyc D hposD 0 = a := by rw [cyc_eq hposD hpos]; exact hD0
  have hcyc1 : cyc D hposD 1 = b := by rw [cyc_eq hposD hone]; exact hD1
  have hn6D : 6 ≤ D.length := by omega
  -- locate `c` and `d`
  obtain ⟨sc, hsc, hscc⟩ := cyc_surj hposD ((hDmem c).mpr hcZ.1)
  obtain ⟨sd, hsd, hsdd⟩ := cyc_surj hposD ((hDmem d).mpr hdZ.1)
  have hsc0 : sc ≠ 0 := fun he => hac (by rw [← hscc, he, hcyc0])
  have hsc1 : sc ≠ 1 := fun he => hbc (by rw [← hscc, he, hcyc1])
  have hsd0 : sd ≠ 0 := fun he => had (by rw [← hsdd, he, hcyc0])
  have hsd1 : sd ≠ 1 := fun he => hbd (by rw [← hsdd, he, hcyc1])
  have hidx := cyc_adj_index hD hposD hsc hsd (by rw [hscc, hsdd]; exact hcd)
  -- the prism, in whichever of the two orientations `c`, `d` sit
  have hkey : ∀ (u w : V) (su sw : ℕ), su < D.length → sw < D.length →
      cyc D hposD su = u → cyc D hposD sw = w → sw = su + 1 → 2 ≤ su → su + 2 ≤ D.length →
      (u = c ∨ u = d) → (w = c ∨ w = d) → u ≠ w → False := by
    intro u w su sw hsu hsw hcu hcw hsucc hsu2 hsu2' huc hwc hne
    have hprism : ∃ (α β : Fin 3 → V) (Q₁ Q₂ Q₃ : List V), IsLongPrism G α β Q₁ Q₂ Q₃ := by
      refine long_prism hD hposD hn6D hsu2 hsu2' hSpath (fst_ne_lst h) ?_ ?_
      · intro p hp hpD
        exact h.notC p (hSF p hp) ((hDmem p).mp hpD)
      · intro p hp q hqD
        have hpF : p ∈ F := hSF p hp
        have hqC : q ∈ C := (hDmem q).mp hqD
        rw [hcyc0, hcyc1, show cyc D hposD su = u from hcu,
          show cyc D hposD (su + 1) = w from (hsucc ▸ hcw)]
        constructor
        · intro hadj
          rcases hFC q hqC p hpF hadj.symm with ⟨hg, hw⟩ | ⟨hg, hw⟩
          · exact Or.inl ⟨hg, hw⟩
          · refine Or.inr ⟨hg, ?_⟩
            rcases hw with hw' | hw' <;> rcases huc with hu' | hu' <;> rcases hwc with hw2 | hw2
            exacts [absurd (hu'.trans hw2.symm) hne, Or.inl (hw'.trans hu'.symm),
              Or.inr (hw'.trans hw2.symm), absurd (hu'.trans hw2.symm) hne,
              absurd (hu'.trans hw2.symm) hne, Or.inr (hw'.trans hw2.symm),
              Or.inl (hw'.trans hu'.symm), absurd (hu'.trans hw2.symm) hne]
        · rintro (⟨rfl, hq⟩ | ⟨rfl, hq⟩)
          · rcases hq with rfl | rfl
            exacts [(hadjf₁ q (Or.inl rfl)).symm, (hadjf₁ q (Or.inr rfl)).symm]
          · rcases hq with rfl | rfl
            · rcases huc with rfl | rfl
              exacts [(hadjfk q (Or.inl rfl)).symm, (hadjfk q (Or.inr rfl)).symm]
            · rcases hwc with rfl | rfl
              exacts [(hadjfk q (Or.inl rfl)).symm, (hadjfk q (Or.inr rfl)).symm]
    obtain ⟨α, β, Q₁, Q₂, Q₃, hprism'⟩ := hprism
    exact h.inF6.1.2.1 ⟨α, β, Q₁, Q₂, Q₃, hprism'⟩
  have hcdne : c ≠ d := hcd.ne
  rcases hidx with e | e | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact hkey c d sc sd hsc hsd hscc hsdd e (by omega) (by omega) (Or.inl rfl) (Or.inr rfl)
      hcdne
  · exact hkey d c sd sc hsd hsc hsdd hscc e (by omega) (by omega) (Or.inr rfl) (Or.inl rfl)
      (Ne.symm hcdne)
  · exact hsc0 e1
  · exact hsd0 e1

end Workspace.ProofLemmas.OddWheelAttachmentClaim2
