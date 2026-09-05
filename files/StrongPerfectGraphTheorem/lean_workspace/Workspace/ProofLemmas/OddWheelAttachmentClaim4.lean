import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Appearances
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.OddWheelTrichotomy
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentMain

/-!
# 16.2, claim (4): the two disjoint minimal arcs

PAPER (16.2, printed p. 99):

> **(4) At least one of `f₁, f_k` has only one neighbour in `C`.**
> For assume they both have at least two.  Then there are disjoint paths `Q, R` of `C`, both
> containing neighbours of both `f₁, f_k`.  Choose `Q, R` minimal, and let `Q` have ends
> `q₁, q₂`; then from the minimality of `Q`, `q₁` is the unique neighbour of one of `f₁, f_k`
> in `Q`, and `q₂` is the unique neighbour of the other. …

This module contains the **first two printed sentences**, as `exists_two_trans_arcs`: from two
disjoint sets `Z₁ = N(f₁) ∩ C` and `Z₂ = N(f_k) ∩ C` of rim vertices, each with at least two
members, it produces two *disjoint clean transition arcs* — blocks of cyclic positions whose
two ends are marked, one in each of `Z₁`, `Z₂`, and none of whose interior positions is marked.
"Clean" is exactly the printed *"from the minimality of `Q`, `q₁` is the unique neighbour of one
of `f₁, f_k` in `Q`, and `q₂` is the unique neighbour of the other"*.

Both arcs come from **minimising the arc length**, not from walking to the next marked position:
if an interior position of a minimal arc were marked, then either its initial or its terminal
segment would be a shorter arc of the same kind — and the case analysis needs both orientations
`(Z₁, Z₂)` and `(Z₂, Z₁)` to be admitted, which is why `IsTransArc` is stated with a
disjunction.

`2 ≤ Z₁.ncard` is used exactly twice: once to rule out the degenerate first arc of length
`n - 1` (whose complement is a single vertex, which would force `Z₁` to be a singleton), and
once to place a second `Z₁`-member outside the first arc.  Likewise for `Z₂`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.OddWheelAttachmentClaim4

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-! ### Clean transition arcs of the rim -/

/-- **A clean transition arc.**  The block of cyclic positions `[b, b + s]` of the rim whose two
ends are marked — one in `Z₁`, the other in `Z₂` — and none of whose interior positions is
marked.  The side condition `s + 2 ≤ C.length` says the block is a proper arc (at most `n - 1`
vertices), so it really is a path of the rim. -/
def IsTransArc {V : Type*} (C : List V) (hpos : 0 < C.length) (Z₁ Z₂ : Set V) (b s : ℕ) :
    Prop :=
  1 ≤ s ∧ s + 2 ≤ C.length ∧
    ((cyc C hpos b ∈ Z₁ ∧ cyc C hpos (b + s) ∈ Z₂) ∨
      (cyc C hpos b ∈ Z₂ ∧ cyc C hpos (b + s) ∈ Z₁)) ∧
    ∀ t : ℕ, 0 < t → t < s → cyc C hpos (b + t) ∉ Z₁ ∧ cyc C hpos (b + t) ∉ Z₂

/-- Every rim vertex occupies a cyclic offset `< n` from any given base. -/
theorem exists_offset_cyc {C : List V} (hpos : 0 < C.length) (base : ℕ) {x : V} (hx : x ∈ C) :
    ∃ t : ℕ, t < C.length ∧ cyc C hpos (base + t) = x := by
  obtain ⟨j, hj, hjx⟩ := cyc_surj hpos hx
  refine ⟨(j + C.length - base % C.length) % C.length, Nat.mod_lt _ hpos, ?_⟩
  rw [← hjx]
  exact cyc_congr hpos (by rw [OddWheelTrichotomy.offset_spec hpos base j])

/-- Offsets `< n` from a common base determine the rim vertex. -/
theorem offset_inj {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) (hpos : 0 < C.length)
    (base : ℕ) {t u : ℕ} (ht : t < C.length) (hu : u < C.length)
    (h : cyc C hpos (base + t) = cyc C hpos (base + u)) : t = u := by
  have hmod : t % C.length = u % C.length :=
    Nat.ModEq.add_left_cancel' base (cyc_inj hC hpos h)
  rw [Nat.mod_eq_of_lt ht, Nat.mod_eq_of_lt hu] at hmod
  exact hmod

/-! ### Closing a path and an arc of the rim into a hole -/

/-- **The hole `f₁-⋯-f_k-q₂-Q-q₁-f₁`.**

An induced path `S` from `g₁` to `g₂`, disjoint from the rim, together with the arc
`[b, b+s]` of the rim, closes into a hole as soon as the only edges between `S` and the arc are
`g₁`–`cyc b` and `g₂`–`cyc (b+s)`.  That hypothesis is exactly what a *clean* transition arc
provides in claim (4) (where `S = f₁-⋯-f_k`), and what the minimality of `i` and maximality of
`j` provide for the endgame's holes `H₁` and `H₂`.

The resulting hole is `S ++ (arc).reverse`, of length `|S| + s + 1`. -/
theorem hole_of_path_and_arc {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    (hpos : 0 < C.length) {b s : ℕ} (hs1 : 1 ≤ s) (hs2 : s + 2 ≤ C.length)
    {g₁ g₂ : V} {S : List V} (hS : IsPathFrom G S g₁ g₂) (hSlen : 2 ≤ S.length)
    (hSC : ∀ z ∈ S, z ∉ C)
    (hcross : ∀ z ∈ S, ∀ t : ℕ, t ≤ s →
      (G.Adj z (cyc C hpos (b + t)) ↔ ((z = g₁ ∧ t = 0) ∨ (z = g₂ ∧ t = s)))) :
    IsHoleList G (S ++ (arc C hpos b (s + 1)).reverse) := by
  have harc : IsPathFrom G (arc C hpos b (s + 1)) (cyc C hpos b) (cyc C hpos (b + s)) := by
    have h := arc_isPathFrom hC hpos (a := b) (L := s + 1) (by omega) (by omega)
    rw [show b + (s + 1) - 1 = b + s by omega] at h
    exact h
  have hrev : IsPathFrom G (arc C hpos b (s + 1)).reverse (cyc C hpos (b + s))
      (cyc C hpos b) := PathBasics.isPathFrom_reverse harc
  refine PathGlue.glue_hole hS hrev ?_ ?_ ?_
  · intro x hx hxr
    rw [List.mem_reverse] at hxr
    obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hxr
    exact hSC x hx (by rw [← hte]; exact cyc_mem hpos _)
  · intro x hx y hy
    rw [List.mem_reverse] at hy
    obtain ⟨t, ht, hte⟩ := (mem_arc hpos).mp hy
    rw [← hte, hcross x hx t (by omega)]
    constructor
    · rintro (⟨hx1, ht0⟩ | ⟨hx2, hts⟩)
      · exact Or.inr ⟨hx1, by rw [ht0, Nat.add_zero]⟩
      · exact Or.inl ⟨hx2, by rw [hts]⟩
    · rintro (⟨hx2, hy2⟩ | ⟨hx1, hy1⟩)
      · exact Or.inr ⟨hx2, offset_inj hC hpos b (by omega) (by omega) hy2⟩
      · refine Or.inl ⟨hx1, ?_⟩
        have hy1' : cyc C hpos (b + t) = cyc C hpos (b + 0) := by rw [Nat.add_zero]; exact hy1
        exact offset_inj hC hpos b (by omega) (by omega) hy1'
  · have hlr : (arc C hpos b (s + 1)).reverse.length = s + 1 := by
      rw [List.length_reverse, arc_length]
    omega

/-! ### The two disjoint arcs -/

/-- **The first two printed sentences of claim (4).**

Two disjoint sets of rim vertices, each with at least two members, are separated by two
*disjoint* clean transition arcs `[b, b+s]` and `[b', b'+s']`; `b + s < b'` and
`b' + s' < b + n` record that they are disjoint blocks of one turn of the rim. -/
theorem exists_two_trans_arcs [Fintype V] {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hpos : 0 < C.length) {Z₁ Z₂ : Set V}
    (hZ₁C : ∀ z ∈ Z₁, z ∈ C) (hZ₂C : ∀ z ∈ Z₂, z ∈ C)
    (hdisj : ∀ z : V, z ∈ Z₁ → z ∈ Z₂ → False)
    (h₁ : 2 ≤ Z₁.ncard) (h₂ : 2 ≤ Z₂.ncard) :
    ∃ b s b' s' : ℕ, IsTransArc C hpos Z₁ Z₂ b s ∧ IsTransArc C hpos Z₁ Z₂ b' s' ∧
      b + s < b' ∧ b' + s' < b + C.length := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  obtain ⟨x, hx, x', hx', hxx'⟩ := (Set.one_lt_ncard (Set.toFinite Z₁)).mp (by omega)
  obtain ⟨y, hy, -, -, -⟩ := (Set.one_lt_ncard (Set.toFinite Z₂)).mp (by omega)
  -- the predicate whose minimisers are the clean transition arcs
  have hex : ∃ p : ℕ × ℕ, 1 ≤ p.2 ∧ p.2 + 2 ≤ C.length ∧
      ((cyc C hpos p.1 ∈ Z₁ ∧ cyc C hpos (p.1 + p.2) ∈ Z₂) ∨
        (cyc C hpos p.1 ∈ Z₂ ∧ cyc C hpos (p.1 + p.2) ∈ Z₁)) := by
    obtain ⟨px, hpx, hpxx⟩ := exists_offset_cyc hpos 0 (hZ₁C x hx)
    obtain ⟨px', hpx', hpxx'⟩ := exists_offset_cyc hpos 0 (hZ₁C x' hx')
    rw [Nat.zero_add] at hpxx hpxx'
    obtain ⟨t, ht, hty⟩ := exists_offset_cyc hpos px (hZ₂C y hy)
    obtain ⟨t', ht', hty'⟩ := exists_offset_cyc hpos px' (hZ₂C y hy)
    have hne : px ≠ px' := fun he => hxx' (by rw [← hpxx, ← hpxx', he])
    have ht0 : t ≠ 0 := by
      intro he
      rw [he, Nat.add_zero, hpxx] at hty
      exact hdisj x hx (by rw [hty]; exact hy)
    have ht'0 : t' ≠ 0 := by
      intro he
      rw [he, Nat.add_zero, hpxx'] at hty'
      exact hdisj x' hx' (by rw [hty']; exact hy)
    by_cases hcase : t + 2 ≤ C.length
    · exact ⟨(px, t), by omega, by omega, Or.inl ⟨by rw [hpxx]; exact hx, by rw [hty]; exact hy⟩⟩
    · by_cases hcase' : t' + 2 ≤ C.length
      · exact ⟨(px', t'), by omega, by omega,
          Or.inl ⟨by rw [hpxx']; exact hx', by rw [hty']; exact hy⟩⟩
      · exfalso
        have htt' : t = t' := by omega
        have heq : cyc C hpos (px + t) = cyc C hpos (px' + t) := by
          rw [hty, htt', hty']
        have hmod : px % C.length = px' % C.length :=
          Nat.ModEq.add_right_cancel' t (cyc_inj hC hpos heq)
        rw [Nat.mod_eq_of_lt hpx, Nat.mod_eq_of_lt hpx'] at hmod
        exact hne hmod
  obtain ⟨⟨b, s⟩, hbs, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : ℕ × ℕ => 1 ≤ p.2 ∧ p.2 + 2 ≤ C.length ∧
        ((cyc C hpos p.1 ∈ Z₁ ∧ cyc C hpos (p.1 + p.2) ∈ Z₂) ∨
          (cyc C hpos p.1 ∈ Z₂ ∧ cyc C hpos (p.1 + p.2) ∈ Z₁)))
      (fun p => p.2) hex
  simp only at hbs hmin
  obtain ⟨hs1, hs2, hends⟩ := hbs
  -- minimality of `s` makes the interior of the arc unmarked
  have hclean : ∀ t : ℕ, 0 < t → t < s →
      cyc C hpos (b + t) ∉ Z₁ ∧ cyc C hpos (b + t) ∉ Z₂ := by
    intro t ht0 hts
    have hidx : b + t + (s - t) = b + s := by omega
    constructor
    · intro hmem
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- ends `(Z₁, Z₂)`: the terminal segment `[b+t, b+s]` is a shorter arc
        have h2' : cyc C hpos (b + t + (s - t)) ∈ Z₂ := by rw [hidx]; exact h2
        have hsm : s ≤ s - t := hmin (b + t, s - t) ⟨by omega, by omega, Or.inl ⟨hmem, h2'⟩⟩
        omega
      · -- ends `(Z₂, Z₁)`: the initial segment `[b, b+t]` is a shorter arc
        have hsm : s ≤ t := hmin (b, t) ⟨by omega, by omega, Or.inr ⟨h1, hmem⟩⟩
        omega
    · intro hmem
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hsm : s ≤ t := hmin (b, t) ⟨by omega, by omega, Or.inl ⟨h1, hmem⟩⟩
        omega
      · have h2' : cyc C hpos (b + t + (s - t)) ∈ Z₁ := by rw [hidx]; exact h2
        have hsm : s ≤ s - t := hmin (b + t, s - t) ⟨by omega, by omega, Or.inr ⟨hmem, h2'⟩⟩
        omega
  have harc1 : IsTransArc C hpos Z₁ Z₂ b s := ⟨hs1, hs2, hends, hclean⟩
  -- name the two ends of the first arc
  obtain ⟨e₁, e₂, he₁, he₂, hoff⟩ :
      ∃ e₁ e₂ : V, e₁ ∈ Z₁ ∧ e₂ ∈ Z₂ ∧
        ((cyc C hpos b = e₁ ∧ cyc C hpos (b + s) = e₂) ∨
          (cyc C hpos b = e₂ ∧ cyc C hpos (b + s) = e₁)) := by
    rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, h1, h2, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨_, _, h2, h1, Or.inr ⟨rfl, rfl⟩⟩
  -- any marked vertex off the first arc sits at an offset in `(s, n)`
  have hmarked_off : ∀ z : V, (z ∈ Z₁ ∨ z ∈ Z₂) → z ≠ cyc C hpos b →
      z ≠ cyc C hpos (b + s) → ∃ t : ℕ, s < t ∧ t < C.length ∧ cyc C hpos (b + t) = z := by
    intro z hz hz1 hz2
    obtain ⟨t, ht, htz⟩ :=
      exists_offset_cyc hpos b (by rcases hz with h | h; exacts [hZ₁C z h, hZ₂C z h])
    refine ⟨t, ?_, ht, htz⟩
    by_contra hcon
    push Not at hcon
    rcases Nat.eq_zero_or_pos t with rfl | ht0
    · exact hz1 (by rw [← htz, Nat.add_zero])
    · rcases Nat.lt_or_ge t s with hlt | hge
      · rcases hz with h | h
        · exact (hclean t ht0 hlt).1 (by rw [htz]; exact h)
        · exact (hclean t ht0 hlt).2 (by rw [htz]; exact h)
      · exact hz2 (by rw [← htz, show t = s by omega])
  -- a second member of each class, necessarily off the first arc
  obtain ⟨z₁, hz₁, hz₁ne⟩ := Set.exists_ne_of_one_lt_ncard (s := Z₁) (by omega) e₁
  obtain ⟨z₂, hz₂, hz₂ne⟩ := Set.exists_ne_of_one_lt_ncard (s := Z₂) (by omega) e₂
  have hz₁notZ₂ : z₁ ≠ e₂ := by
    intro he
    exact hdisj z₁ hz₁ (by rw [he]; exact he₂)
  have hz₂notZ₁ : z₂ ≠ e₁ := by
    intro he
    exact hdisj z₂ (by rw [he]; exact he₁) hz₂
  have hz₁b : z₁ ≠ cyc C hpos b ∧ z₁ ≠ cyc C hpos (b + s) := by
    rcases hoff with ⟨q1, q2⟩ | ⟨q1, q2⟩
    · exact ⟨by rw [q1]; exact hz₁ne, by rw [q2]; exact hz₁notZ₂⟩
    · exact ⟨by rw [q1]; exact hz₁notZ₂, by rw [q2]; exact hz₁ne⟩
  have hz₂b : z₂ ≠ cyc C hpos b ∧ z₂ ≠ cyc C hpos (b + s) := by
    rcases hoff with ⟨q1, q2⟩ | ⟨q1, q2⟩
    · exact ⟨by rw [q1]; exact hz₂notZ₁, by rw [q2]; exact hz₂ne⟩
    · exact ⟨by rw [q1]; exact hz₂ne, by rw [q2]; exact hz₂notZ₁⟩
  obtain ⟨t₁, ht₁s, ht₁n, ht₁z⟩ := hmarked_off z₁ (Or.inl hz₁) hz₁b.1 hz₁b.2
  obtain ⟨t₂, ht₂s, ht₂n, ht₂z⟩ := hmarked_off z₂ (Or.inr hz₂) hz₂b.1 hz₂b.2
  have ht₁₂ : t₁ ≠ t₂ := by
    intro he
    rw [he, ht₂z] at ht₁z
    exact hdisj z₂ (by rw [ht₁z]; exact hz₁) hz₂
  -- the second arc, minimal inside the complementary window `(s, n)`
  have hex2 : ∃ p : ℕ × ℕ, s < p.1 ∧ 1 ≤ p.2 ∧ p.1 + p.2 < C.length ∧
      ((cyc C hpos (b + p.1) ∈ Z₁ ∧ cyc C hpos (b + (p.1 + p.2)) ∈ Z₂) ∨
        (cyc C hpos (b + p.1) ∈ Z₂ ∧ cyc C hpos (b + (p.1 + p.2)) ∈ Z₁)) := by
    rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
    · have e1 : cyc C hpos (b + t₁) ∈ Z₁ := by rw [ht₁z]; exact hz₁
      have hix : t₁ + (t₂ - t₁) = t₂ := by omega
      have e2 : cyc C hpos (b + (t₁ + (t₂ - t₁))) ∈ Z₂ := by rw [hix, ht₂z]; exact hz₂
      exact ⟨(t₁, t₂ - t₁), by omega, by omega, by omega, Or.inl ⟨e1, e2⟩⟩
    · have hlt' : t₂ < t₁ := by omega
      have e1 : cyc C hpos (b + t₂) ∈ Z₂ := by rw [ht₂z]; exact hz₂
      have hix : t₂ + (t₁ - t₂) = t₁ := by omega
      have e2 : cyc C hpos (b + (t₂ + (t₁ - t₂))) ∈ Z₁ := by rw [hix, ht₁z]; exact hz₁
      exact ⟨(t₂, t₁ - t₂), by omega, by omega, by omega, Or.inr ⟨e1, e2⟩⟩
  obtain ⟨⟨u, σ⟩, huσ, hmin2⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : ℕ × ℕ => s < p.1 ∧ 1 ≤ p.2 ∧ p.1 + p.2 < C.length ∧
        ((cyc C hpos (b + p.1) ∈ Z₁ ∧ cyc C hpos (b + (p.1 + p.2)) ∈ Z₂) ∨
          (cyc C hpos (b + p.1) ∈ Z₂ ∧ cyc C hpos (b + (p.1 + p.2)) ∈ Z₁)))
      (fun p => p.2) hex2
  simp only at huσ hmin2
  obtain ⟨hus, hσ1, huσn, hends2⟩ := huσ
  have hclean2 : ∀ t : ℕ, 0 < t → t < σ →
      cyc C hpos (b + u + t) ∉ Z₁ ∧ cyc C hpos (b + u + t) ∉ Z₂ := by
    intro t ht0 htσ
    have hrw : b + u + t = b + (u + t) := by omega
    have hix : u + t + (σ - t) = u + σ := by omega
    constructor
    · intro hmem
      rw [hrw] at hmem
      rcases hends2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h2' : cyc C hpos (b + (u + t + (σ - t))) ∈ Z₂ := by rw [hix]; exact h2
        have hsm : σ ≤ σ - t :=
          hmin2 (u + t, σ - t) ⟨by omega, by omega, by omega, Or.inl ⟨hmem, h2'⟩⟩
        omega
      · have hsm : σ ≤ t := hmin2 (u, t) ⟨by omega, by omega, by omega, Or.inr ⟨h1, hmem⟩⟩
        omega
    · intro hmem
      rw [hrw] at hmem
      rcases hends2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have hsm : σ ≤ t := hmin2 (u, t) ⟨by omega, by omega, by omega, Or.inl ⟨h1, hmem⟩⟩
        omega
      · have h2' : cyc C hpos (b + (u + t + (σ - t))) ∈ Z₁ := by rw [hix]; exact h2
        have hsm : σ ≤ σ - t :=
          hmin2 (u + t, σ - t) ⟨by omega, by omega, by omega, Or.inr ⟨hmem, h2'⟩⟩
        omega
  refine ⟨b, s, b + u, σ, harc1, ⟨hσ1, by omega, ?_, hclean2⟩, by omega, by omega⟩
  rw [show b + u + σ = b + (u + σ) by omega]
  exact hends2

end Workspace.ProofLemmas.OddWheelAttachmentClaim4
