import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.OddWheelAttachmentArcs
import Workspace.ProofLemmas.OddWheelAttachmentClaim4
import Workspace.ProofLemmas.OddWheelAttachmentYCount

/-!
# Cyclic-rim bookkeeping for 16.2, claim (4)

These lemmas spell out the elementary fact used in the paper when two proper arcs occur in
the order `[b,b+s]`, `[b',b'+s']` around an induced cycle.  The arcs are disjoint, and their
only possible cross-edges join the two pairs of consecutive boundary vertices.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm162ClaimFourRim

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.ProofLemmas.OddWheelAttachmentArcs

attribute [local instance] Classical.propDecidable

variable {V : Type*}

/-- Two separated cyclic arcs in one turn of a hole have disjoint vertex sets. -/
theorem separated_arcs_disjoint {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hp : 0 < C.length) {b s b' s' : ℕ}
    (hs2 : s + 2 ≤ C.length) (hsep₁ : b + s < b') (hsep₂ : b' + s' < b + C.length) :
    ∀ x ∈ arc C hp b (s + 1), x ∉ arc C hp b' (s' + 1) := by
  intro x hxQ hxR
  obtain ⟨t, ht, htx⟩ := (mem_arc hp).mp hxQ
  obtain ⟨u, hu, hux⟩ := (mem_arc hp).mp hxR
  have hbb : b ≤ b' := by omega
  have hrewrite : b' + u = b + ((b' - b) + u) := by omega
  have hoff : (b' - b) + u < C.length := by omega
  have htC : t < C.length := by omega
  have heq : cyc C hp (b + t) = cyc C hp (b + ((b' - b) + u)) := by
    calc
      cyc C hp (b + t) = x := htx
      _ = cyc C hp (b' + u) := hux.symm
      _ = cyc C hp (b + ((b' - b) + u)) := congrArg (cyc C hp) hrewrite
  have := Workspace.ProofLemmas.OddWheelAttachmentClaim4.offset_inj hC hp b htC hoff heq
  omega

/-- The only possible edges between separated cyclic arcs are the two boundary edges. -/
theorem separated_arcs_adj_iff {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hp : 0 < C.length) {b s b' s' : ℕ}
    (hs2 : s + 2 ≤ C.length) (hs'2 : s' + 2 ≤ C.length)
    (hsep₁ : b + s < b') (hsep₂ : b' + s' < b + C.length) :
    ∀ x ∈ arc C hp b (s + 1), ∀ y ∈ arc C hp b' (s' + 1),
      (G.Adj x y ↔
        (x = cyc C hp (b + s) ∧ y = cyc C hp b' ∧
          G.Adj (cyc C hp (b + s)) (cyc C hp b')) ∨
        (x = cyc C hp b ∧ y = cyc C hp (b' + s') ∧
          G.Adj (cyc C hp b) (cyc C hp (b' + s')))) := by
  intro x hxQ y hyR
  obtain ⟨t, ht, htx⟩ := (mem_arc hp).mp hxQ
  obtain ⟨u, hu, huy⟩ := (mem_arc hp).mp hyR
  have hbb : b ≤ b' := by omega
  have hrewrite : b' + u = b + ((b' - b) + u) := by omega
  have htC : t < C.length := by omega
  have ht1C : t + 1 < C.length := by omega
  have huC : (b' - b) + u < C.length := by omega
  have hu1C : (b' - b) + u + 1 ≤ C.length := by omega
  constructor
  · intro hxy
    have hcyc : G.Adj (cyc C hp (b + t)) (cyc C hp (b + ((b' - b) + u))) := by
      simpa only [htx, ← hrewrite, huy] using hxy
    rcases (cyc_adj hC hp _ _).mp hcyc with hfwd | hwrap
    · have hm : ((b' - b) + u) % C.length = (t + 1) % C.length := by
        exact Nat.ModEq.add_left_cancel' b (show
          (b + ((b' - b) + u)) % C.length = (b + (t + 1)) % C.length by
            simpa only [Nat.add_assoc] using hfwd)
      rw [Nat.mod_eq_of_lt huC, Nat.mod_eq_of_lt ht1C] at hm
      left
      have htS : t = s := by omega
      have hu0 : u = 0 := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [← htx, htS]
      · rw [← huy, hu0, Nat.add_zero]
      · rw [← htx, ← huy] at hxy
        simpa [htS, hu0] using hxy
    · have hm : t % C.length = (((b' - b) + u) + 1) % C.length := by
        exact Nat.ModEq.add_left_cancel' b (show
          (b + t) % C.length = (b + (((b' - b) + u) + 1)) % C.length by
            simpa only [Nat.add_assoc] using hwrap)
      have heq : (b' - b) + u + 1 = C.length := by
        by_contra hn
        have hlt : (b' - b) + u + 1 < C.length := by omega
        rw [Nat.mod_eq_of_lt htC, Nat.mod_eq_of_lt hlt] at hm
        omega
      right
      have ht0 : t = 0 := by
        rw [heq, Nat.mod_self, Nat.mod_eq_of_lt htC] at hm
        exact hm
      have huS : u = s' := by omega
      refine ⟨?_, ?_, ?_⟩
      · rw [← htx, ht0, Nat.add_zero]
      · rw [← huy, huS]
      · rw [← htx, ← huy] at hxy
        simpa [ht0, huS] using hxy
  · rintro (⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩) <;> exact h

/-- If both boundary edges are present and both arcs are single edges, the hole would have
length four, contrary to the wheel lower bound. -/
theorem separated_short_not_both {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hp : 0 < C.length) (hn6 : 6 ≤ C.length)
    {b s b' s' : ℕ} (hsep₁ : b + s < b') (hsep₂ : b' + s' < b + C.length)
    (hs : s = 1) (hs' : s' = 1)
    (hinner : G.Adj (cyc C hp (b + s)) (cyc C hp b'))
    (houter : G.Adj (cyc C hp b) (cyc C hp (b' + s'))) : False := by
  have hbb : b ≤ b' := by omega
  have hdelta : b' - b < C.length := by omega
  have hinnerEq : b' - b = s + 1 := by
    rcases (cyc_adj hC hp (b + s) b').mp hinner with hi | hi
    · have hm : (b' - b) % C.length = (s + 1) % C.length :=
        Nat.ModEq.add_left_cancel' b (show
          (b + (b' - b)) % C.length = (b + (s + 1)) % C.length by
            simpa only [show b + (b' - b) = b' by omega, Nat.add_assoc] using hi)
      rw [Nat.mod_eq_of_lt hdelta, Nat.mod_eq_of_lt (by omega : s + 1 < C.length)] at hm
      exact hm
    · have hm : s % C.length = ((b' - b) + 1) % C.length :=
        Nat.ModEq.add_left_cancel' b (show
          (b + s) % C.length = (b + ((b' - b) + 1)) % C.length by
            have he : b + ((b' - b) + 1) = b' + 1 := by omega
            rw [he]
            exact hi)
      rw [Nat.mod_eq_of_lt (by omega : s < C.length),
        Nat.mod_eq_of_lt (by omega : (b' - b) + 1 < C.length)] at hm
      omega
  have houterEq : (b' - b) + s' + 1 = C.length := by
    rcases (cyc_adj hC hp b (b' + s')).mp houter with ho | ho
    · have hm : ((b' - b) + s') % C.length = 1 % C.length :=
        Nat.ModEq.add_left_cancel' b (show
          (b + ((b' - b) + s')) % C.length = (b + 1) % C.length by
            have he : b + ((b' - b) + s') = b' + s' := by omega
            rw [he]
            exact ho)
      rw [Nat.mod_eq_of_lt (by omega : (b' - b) + s' < C.length),
        Nat.mod_eq_of_lt (by omega : 1 < C.length)] at hm
      omega
    · have hm : 0 % C.length = (((b' - b) + s') + 1) % C.length :=
        Nat.ModEq.add_left_cancel' b (show
          b % C.length = (b + (((b' - b) + s') + 1)) % C.length by
            have he : b + (((b' - b) + s') + 1) = b' + s' + 1 := by omega
            rw [he]
            exact ho)
      have hle : ((b' - b) + s') + 1 ≤ C.length := by omega
      by_contra hn
      rw [Nat.zero_mod, Nat.mod_eq_of_lt (by omega)] at hm
      omega
  omega

/-! ## Turning a clean transition arc into an oriented track -/

/-- All data attached to a transition arc after orienting it from `Z₁` to `Z₂`.
It is Prop-valued so the choice of orientation may be eliminated without introducing
noncomputable data into `Type`. -/
inductive TransitionData (G : SimpleGraph V) (C : List V) (hp : 0 < C.length)
    (Y Z₁ Z₂ : Set V) (S : List V) (f₁ fk : V) (b s : ℕ) : Prop where
  | mk (Q : List V) (q₁ q₂ c d : V)
      (length_eq : Q.length = s + 1)
      (path : IsPathFrom G Q q₁ q₂)
      (q₁Z₁ : q₁ ∈ Z₁) (q₂Z₂ : q₂ ∈ Z₂)
      (memC : ∀ x ∈ Q, x ∈ C) (disjointS : ∀ x ∈ S, x ∉ Q)
      (attachS : ∀ x ∈ S, ∀ y ∈ Q,
        (G.Adj x y ↔ (x = f₁ ∧ y = q₁) ∨ (x = fk ∧ y = q₂)))
      (notY : ∀ x ∈ Q, x ∉ Y)
      (complete_pair : {x : V | x ∈ Q ∧ VertexComplete G x Y} = {c, d})
      (pair_ne : c ≠ d) (pair_adj : G.Adj c d)
      (parity : Even (S.length + Q.length))
      (orientation :
        (Q = arc C hp b (s + 1) ∧ q₁ = cyc C hp b ∧ q₂ = cyc C hp (b + s)) ∨
        (Q = (arc C hp b (s + 1)).reverse ∧ q₁ = cyc C hp (b + s) ∧
          q₂ = cyc C hp b)) : TransitionData G C hp Y Z₁ Z₂ S f₁ fk b s

/-- A clean transition arc, in either of its two natural orientations, supplies one of the
paper's tracks `Q` together with its hole-parity and exact pair of `Y`-complete vertices. -/
theorem transition_data [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) (hp : 0 < C.length)
    {Y Z₁ Z₂ : Set V} {S : List V} {f₁ fk : V} {b s : ℕ}
    (hBerge : Berge G) (hYanti : AnticonnectedSet G Y) (hCY : ∀ x ∈ C, x ∉ Y)
    {π : V → ℕ} (hπ2 : ∀ x : V, π x < 2)
    (hπ : ∀ x y : V, x ∈ C → y ∈ C → x ≠ y →
      (SameWheelParity G C Y x y ↔ π x = π y))
    (hstep : ∀ x y : V, x ∈ C → y ∈ C → G.Adj x y →
      (π x ≠ π y ↔ EdgeComplete G Y x y))
    (hS : IsPathFrom G S f₁ fk) (hS2 : 2 ≤ S.length)
    (hSnotC : ∀ x ∈ S, x ∉ C) (hSnotY : ∀ x ∈ S, x ∉ Y)
    (hSnc : ∀ x ∈ S, ¬ VertexComplete G x Y)
    (hSC : ∀ x ∈ S, ∀ y ∈ C,
      (G.Adj x y ↔ (x = f₁ ∧ y ∈ Z₁) ∨ (x = fk ∧ y ∈ Z₂)))
    (hZ₁C : ∀ z ∈ Z₁, z ∈ C) (hZ₂C : ∀ z ∈ Z₂, z ∈ C)
    (hZdisj : ∀ z : V, z ∈ Z₁ → z ∈ Z₂ → False)
    (hopp : ∀ x ∈ Z₁, ∀ y ∈ Z₂, OppositeWheelParity G C Y x y)
    (ht : OddWheelAttachmentClaim4.IsTransArc C hp Z₁ Z₂ b s) :
    TransitionData G C hp Y Z₁ Z₂ S f₁ fk b s := by
  classical
  rcases ht with ⟨hs1, hs2, hends, hclean⟩
  have hmemC : ∀ x ∈ arc C hp b (s + 1), x ∈ C := by
    intro x hx
    obtain ⟨t, -, rfl⟩ := (mem_arc hp).mp hx
    exact cyc_mem hp _
  have hdisjS : ∀ x ∈ S, x ∉ arc C hp b (s + 1) := by
    intro x hxS hxQ
    exact hSnotC x hxS (hmemC x hxQ)
  have hnotY : ∀ x ∈ arc C hp b (s + 1), x ∉ Y := by
    intro x hx
    exact hCY x (hmemC x hx)
  rcases hends with hforward | hreverse
  · have hZ₁iff : ∀ t : ℕ, t ≤ s → (cyc C hp (b + t) ∈ Z₁ ↔ t = 0) := by
      intro t hts
      constructor
      · intro hz
        rcases Nat.eq_zero_or_pos t with rfl | ht0
        · rfl
        · by_cases he : t = s
          · subst t
            exact absurd hforward.2 (hZdisj _ hz)
          · exact absurd hz (hclean t ht0 (by omega)).1
      · rintro rfl
        simpa only [Nat.add_zero] using hforward.1
    have hZ₂iff : ∀ t : ℕ, t ≤ s → (cyc C hp (b + t) ∈ Z₂ ↔ t = s) := by
      intro t hts
      constructor
      · intro hz
        by_cases he : t = s
        · exact he
        · rcases Nat.eq_zero_or_pos t with rfl | ht0
          · exact absurd hforward.1 (fun hz₁ => hZdisj _ hz₁ (by simpa using hz))
          · exact absurd hz (hclean t ht0 (by omega)).2
      · rintro rfl
        exact hforward.2
    have hcrossT : ∀ x ∈ S, ∀ t : ℕ, t ≤ s →
        (G.Adj x (cyc C hp (b + t)) ↔ (x = f₁ ∧ t = 0) ∨ (x = fk ∧ t = s)) := by
      intro x hx t hts
      rw [hSC x hx _ (cyc_mem hp _), hZ₁iff t hts, hZ₂iff t hts]
    have hQpath : IsPathFrom G (arc C hp b (s + 1))
        (cyc C hp b) (cyc C hp (b + s)) := by
      have hh := arc_isPathFrom hC hp (a := b) (L := s + 1) (by omega) (by omega)
      rw [show b + (s + 1) - 1 = b + s by omega] at hh
      exact hh
    have hH := OddWheelAttachmentClaim4.hole_of_path_and_arc hC hp hs1 hs2 hS hS2
      hSnotC hcrossT
    have hπne : π (cyc C hp b) ≠ π (cyc C hp (b + s)) := by
      have ho := hopp _ hforward.1 _ hforward.2
      intro he
      exact ho.2.2.2 ((hπ _ _ ho.2.1 ho.2.2.1 ho.1).mpr he)
    obtain ⟨heven, -, c, d, hpairH, hcd, hcdadj⟩ :=
      OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep hs1 hs2
        hSnotY hSnc hπne hH
    have hpairQ : {x : V | x ∈ arc C hp b (s + 1) ∧ VertexComplete G x Y} = {c, d} := by
      ext x
      constructor
      · intro hx
        have hm : x ∈ {w : V | w ∈ S ++ (arc C hp b (s + 1)).reverse ∧
            VertexComplete G w Y} :=
          ⟨List.mem_append_right _ (List.mem_reverse.mpr hx.1), hx.2⟩
        rw [hpairH] at hm
        exact hm
      · intro hx
        have hm : x ∈ {w : V | w ∈ S ++ (arc C hp b (s + 1)).reverse ∧
            VertexComplete G w Y} := by
          rw [hpairH]
          exact hx
        rcases List.mem_append.mp hm.1 with hxS | hxQ
        · exact absurd hm.2 (hSnc x hxS)
        · exact ⟨List.mem_reverse.mp hxQ, hm.2⟩
    refine ⟨arc C hp b (s + 1), cyc C hp b, cyc C hp (b + s), c, d,
      arc_length hp b (s + 1), hQpath, hforward.1, hforward.2, hmemC, hdisjS, ?_,
      hnotY, hpairQ, hcd, hcdadj, ?_, Or.inl ⟨rfl, rfl, rfl⟩⟩
    · intro x hx y hy
      obtain ⟨t, ht, hty⟩ := (mem_arc hp).mp hy
      rw [← hty, hcrossT x hx t (by omega)]
      constructor
      · rintro (⟨hxf, ht0⟩ | ⟨hxk, hts⟩)
        · exact Or.inl ⟨hxf, by rw [ht0, Nat.add_zero]⟩
        · exact Or.inr ⟨hxk, by rw [hts]⟩
      · rintro (⟨hxf, hy1⟩ | ⟨hxk, hy2⟩)
        · exact Or.inl ⟨hxf, OddWheelAttachmentClaim4.offset_inj hC hp b
            (by omega) (by omega) (by simpa [Nat.add_zero] using hy1)⟩
        · exact Or.inr ⟨hxk, OddWheelAttachmentClaim4.offset_inj hC hp b
            (by omega) (by omega) hy2⟩
    · rw [arc_length]
      exact heven
  · have hZ₂iff : ∀ t : ℕ, t ≤ s → (cyc C hp (b + t) ∈ Z₂ ↔ t = 0) := by
      intro t hts
      constructor
      · intro hz
        rcases Nat.eq_zero_or_pos t with rfl | ht0
        · rfl
        · by_cases he : t = s
          · subst t
            exact absurd hreverse.2 (fun hz₁ => hZdisj _ hz₁ hz)
          · exact absurd hz (hclean t ht0 (by omega)).2
      · rintro rfl
        simpa only [Nat.add_zero] using hreverse.1
    have hZ₁iff : ∀ t : ℕ, t ≤ s → (cyc C hp (b + t) ∈ Z₁ ↔ t = s) := by
      intro t hts
      constructor
      · intro hz
        by_cases he : t = s
        · exact he
        · rcases Nat.eq_zero_or_pos t with rfl | ht0
          · exact absurd hreverse.1 (hZdisj _ (by simpa using hz))
          · exact absurd hz (hclean t ht0 (by omega)).1
      · rintro rfl
        exact hreverse.2
    have hcrossT : ∀ x ∈ S.reverse, ∀ t : ℕ, t ≤ s →
        (G.Adj x (cyc C hp (b + t)) ↔ (x = fk ∧ t = 0) ∨ (x = f₁ ∧ t = s)) := by
      intro x hx t hts
      have hxS := List.mem_reverse.mp hx
      rw [hSC x hxS _ (cyc_mem hp _), hZ₁iff t hts, hZ₂iff t hts]
      tauto
    have hQnat : IsPathFrom G (arc C hp b (s + 1))
        (cyc C hp b) (cyc C hp (b + s)) := by
      have hh := arc_isPathFrom hC hp (a := b) (L := s + 1) (by omega) (by omega)
      rw [show b + (s + 1) - 1 = b + s by omega] at hh
      exact hh
    have hQpath := PathBasics.isPathFrom_reverse hQnat
    have hH := OddWheelAttachmentClaim4.hole_of_path_and_arc hC hp hs1 hs2
      (PathBasics.isPathFrom_reverse hS) (by simpa using hS2)
      (fun x hx => hSnotC x (List.mem_reverse.mp hx)) hcrossT
    have hπne : π (cyc C hp b) ≠ π (cyc C hp (b + s)) := by
      have ho := hopp _ hreverse.2 _ hreverse.1
      intro he
      exact ho.2.2.2 ((hπ _ _ ho.2.1 ho.2.2.1 ho.1).mpr he.symm)
    obtain ⟨heven, -, c, d, hpairH, hcd, hcdadj⟩ :=
      OddWheelAttachmentYCount.hole_yData hC hp hBerge hYanti hCY hπ2 hstep hs1 hs2
        (fun x hx => hSnotY x (List.mem_reverse.mp hx))
        (fun x hx => hSnc x (List.mem_reverse.mp hx)) hπne hH
    have hpairQ : {x : V | x ∈ (arc C hp b (s + 1)).reverse ∧
        VertexComplete G x Y} = {c, d} := by
      ext x
      constructor
      · intro hx
        have hm : x ∈ {w : V | w ∈ S.reverse ++ (arc C hp b (s + 1)).reverse ∧
            VertexComplete G w Y} := ⟨List.mem_append_right _ hx.1, hx.2⟩
        rw [hpairH] at hm
        exact hm
      · intro hx
        have hm : x ∈ {w : V | w ∈ S.reverse ++ (arc C hp b (s + 1)).reverse ∧
            VertexComplete G w Y} := by
          rw [hpairH]
          exact hx
        rcases List.mem_append.mp hm.1 with hxS | hxQ
        · exact absurd hm.2 (hSnc x (List.mem_reverse.mp hxS))
        · exact ⟨hxQ, hm.2⟩
    refine ⟨(arc C hp b (s + 1)).reverse, cyc C hp (b + s), cyc C hp b, c, d,
      by rw [List.length_reverse, arc_length], hQpath, hreverse.2, hreverse.1,
      (fun x hx => hmemC x (List.mem_reverse.mp hx)),
      (fun x hx hxQ => hdisjS x hx (List.mem_reverse.mp hxQ)), ?_,
      (fun x hx => hnotY x (List.mem_reverse.mp hx)), hpairQ, hcd, hcdadj, ?_,
      Or.inr ⟨rfl, rfl, rfl⟩⟩
    · intro x hx y hy
      have hyNat := List.mem_reverse.mp hy
      obtain ⟨t, ht, hty⟩ := (mem_arc hp).mp hyNat
      rw [← hty, hSC x hx _ (cyc_mem hp _), hZ₁iff t (by omega), hZ₂iff t (by omega)]
      constructor
      · rintro (⟨hxf, hts⟩ | ⟨hxk, ht0⟩)
        · exact Or.inl ⟨hxf, by rw [hts]⟩
        · exact Or.inr ⟨hxk, by rw [ht0, Nat.add_zero]⟩
      · rintro (⟨hxf, hy1⟩ | ⟨hxk, hy2⟩)
        · exact Or.inl ⟨hxf, OddWheelAttachmentClaim4.offset_inj hC hp b
            (by omega) (by omega) (by simpa [hty] using hy1)⟩
        · exact Or.inr ⟨hxk, OddWheelAttachmentClaim4.offset_inj hC hp b
            (by omega) (by omega) (by simpa [Nat.add_zero, hty] using hy2)⟩
    · simpa only [List.length_reverse, arc_length] using heven

/-! ## Four complete rim edges contain two separated ones -/

private def CloseEdgePos (n i j : ℕ) : Prop :=
  j = (i + 1) % n ∨ i = (j + 1) % n ∨ j = (i + 2) % n ∨ i = (j + 2) % n

/-- Four distinct positions on a cycle of length at least six cannot all be within cyclic
distance two of one another. -/
private theorem no_four_close {n a b c d : ℕ} (hn : 6 ≤ n)
    (ha : a < n) (hb : b < n) (hc : c < n) (hd : d < n)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : CloseEdgePos n a b) (h2 : CloseEdgePos n a c)
    (h3 : CloseEdgePos n a d) (h4 : CloseEdgePos n b c)
    (h5 : CloseEdgePos n b d) (h6 : CloseEdgePos n c d) : False := by
  have next : ∀ x : ℕ, x < n →
      (((x + 1) % n = x + 1 ∧ x + 1 < n) ∨
        ((x + 1) % n = 0 ∧ x + 1 = n)) := by
    intro x hx
    rcases Nat.lt_or_ge (x + 1) n with hlt | hge
    · exact Or.inl ⟨Nat.mod_eq_of_lt hlt, hlt⟩
    · have he : x + 1 = n := by omega
      exact Or.inr ⟨by rw [he]; exact Nat.mod_self n, he⟩
  have next2 : ∀ x : ℕ, x < n →
      (((x + 2) % n = x + 2 ∧ x + 2 < n) ∨
        ((x + 2) % n = 0 ∧ x + 2 = n) ∨
        ((x + 2) % n = 1 ∧ x + 1 = n)) := by
    intro x hx
    rcases Nat.lt_or_ge (x + 2) n with hlt | hge
    · exact Or.inl ⟨Nat.mod_eq_of_lt hlt, hlt⟩
    · rcases Nat.eq_or_lt_of_le hge with he | hgt
      · have he' : x + 2 = n := he.symm
        exact Or.inr (Or.inl ⟨by rw [he']; exact Nat.mod_self n, he'⟩)
      · have he : x + 1 = n := by omega
        refine Or.inr (Or.inr ⟨?_, he⟩)
        rw [show x + 2 = n + 1 by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  rcases next a ha with ⟨ha1, ha1lt⟩ | ⟨ha1, ha1eq⟩ <;>
    rcases next b hb with ⟨hb1, hb1lt⟩ | ⟨hb1, hb1eq⟩ <;>
    rcases next c hc with ⟨hc1, hc1lt⟩ | ⟨hc1, hc1eq⟩ <;>
    rcases next d hd with ⟨hd1, hd1lt⟩ | ⟨hd1, hd1eq⟩ <;>
    rcases next2 a ha with ⟨ha2, ha2lt⟩ | ⟨ha2, ha2eq⟩ | ⟨ha2, ha2eq⟩ <;>
    rcases next2 b hb with ⟨hb2, hb2lt⟩ | ⟨hb2, hb2eq⟩ | ⟨hb2, hb2eq⟩ <;>
    rcases next2 c hc with ⟨hc2, hc2lt⟩ | ⟨hc2, hc2eq⟩ | ⟨hc2, hc2eq⟩ <;>
    rcases next2 d hd with ⟨hd2, hd2lt⟩ | ⟨hd2, hd2eq⟩ | ⟨hd2, hd2eq⟩ <;>
    simp only [CloseEdgePos, ha1, hb1, hc1, hd1, ha2, hb2, hc2, hd2] at h1 h2 h3 h4 h5 h6 <;>
    omega

/-- Positions farther than two apart index anticomplete rim edges. -/
private theorem far_edges_anticomplete {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hp : 0 < C.length) {i j : ℕ}
    (hi : i < C.length) (hj : j < C.length) (hij : i ≠ j)
    (hfar : ¬ CloseEdgePos C.length i j) :
    ∀ x ∈ ([cyc C hp i, cyc C hp (i + 1)] : List V),
      ∀ y ∈ ([cyc C hp j, cyc C hp (j + 1)] : List V), ¬ G.Adj x y := by
  intro x hx y hy hxy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hfar (by
      rcases (cyc_adj hC hp i j).mp hxy with hh | hh
      · exact Or.inl (by simpa [Nat.mod_eq_of_lt hj] using hh)
      · exact Or.inr (Or.inl (by simpa [Nat.mod_eq_of_lt hi] using hh)))
  · rcases (cyc_adj hC hp i (j + 1)).mp hxy with hh | hh
    · have heq : i = j := by
        have hm : j % C.length = i % C.length :=
          Nat.ModEq.add_right_cancel' 1 (show
            (j + 1) % C.length = (i + 1) % C.length by simpa [Nat.add_assoc] using hh)
        have hm' : j = i := by simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hm
        exact hm'.symm
      exact hij heq
    · exact hfar (Or.inr (Or.inr (Or.inr (by simpa [Nat.mod_eq_of_lt hi,
        Nat.add_assoc] using hh))))
  · rcases (cyc_adj hC hp (i + 1) j).mp hxy with hh | hh
    · exact hfar (Or.inr (Or.inr (Or.inl (by simpa [Nat.mod_eq_of_lt hj,
        Nat.add_assoc] using hh))))
    · have heq : i = j := by
        have hm : i % C.length = j % C.length :=
          Nat.ModEq.add_right_cancel' 1 (show
            (i + 1) % C.length = (j + 1) % C.length by simpa [Nat.add_assoc] using hh)
        simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using hm
      exact hij heq
  · rcases (cyc_adj hC hp (i + 1) (j + 1)).mp hxy with hh | hh
    · have hm : j % C.length = (i + 1) % C.length :=
        Nat.ModEq.add_right_cancel' 1 (show
          (j + 1) % C.length = ((i + 1) + 1) % C.length by
            simpa only [Nat.add_assoc] using hh)
      exact hfar (Or.inl (by simpa [Nat.mod_eq_of_lt hj] using hm))
    · have hm : i % C.length = (j + 1) % C.length :=
        Nat.ModEq.add_right_cancel' 1 (show
          (i + 1) % C.length = ((j + 1) + 1) % C.length by
            simpa only [Nat.add_assoc] using hh)
      exact hfar (Or.inr (Or.inl (by simpa [Nat.mod_eq_of_lt hi] using hm)))

/-- If a hole has at least four `Y`-complete edges, two of them have no edge between their
endpoint pairs.  This is the elementary selection made in the last paragraph of claim (4). -/
theorem four_yEdges_give_anticomplete_pair [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C) (hp : 0 < C.length)
    (hn6 : 6 ≤ C.length) {Y : Set V}
    (h4 : 4 ≤ (HoleYEdgeParity.yEdges G Y C).ncard) :
    ∃ a b c d : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      EdgeComplete G Y a b ∧ EdgeComplete G Y c d ∧
      (∀ x ∈ ([a, b] : List V), ∀ y ∈ ([c, d] : List V), ¬ G.Adj x y) := by
  classical
  have hcount : 4 ≤ ((Finset.range C.length).filter
      (fun m => WheelParity.CycEdge G Y C m)).card := by
    rw [← WheelParity.cycCount]
    rw [← WheelParity.ncard_yEdges_eq_cycCount (Y := Y) hC]
    exact h4
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hcount
  obtain ⟨i, j, k, l, hij, hik, hil, hjk, hjl, hkl, rfl⟩ := Finset.card_eq_four.mp hTcard
  have hmem : ∀ t ∈ ({i, j, k, l} : Finset ℕ),
      t < C.length ∧ WheelParity.CycEdge G Y C t := by
    intro t ht
    have hh := Finset.mem_filter.mp (hTsub ht)
    exact ⟨Finset.mem_range.mp hh.1, hh.2⟩
  obtain ⟨hi, hiE⟩ := hmem i (by simp)
  obtain ⟨hj, hjE⟩ := hmem j (by simp)
  obtain ⟨hk, hkE⟩ := hmem k (by simp)
  obtain ⟨hl, hlE⟩ := hmem l (by simp)
  have hfar : ∃ p q : ℕ, p < C.length ∧ q < C.length ∧ p ≠ q ∧
      WheelParity.CycEdge G Y C p ∧ WheelParity.CycEdge G Y C q ∧
      ¬ CloseEdgePos C.length p q := by
    by_cases h1 : CloseEdgePos C.length i j
    · by_cases h2 : CloseEdgePos C.length i k
      · by_cases h3 : CloseEdgePos C.length i l
        · by_cases h4' : CloseEdgePos C.length j k
          · by_cases h5 : CloseEdgePos C.length j l
            · by_cases h6 : CloseEdgePos C.length k l
              · exact absurd (no_four_close hn6 hi hj hk hl hij hik hil hjk hjl hkl
                    h1 h2 h3 h4' h5 h6) False.elim
              · exact ⟨k, l, hk, hl, hkl, hkE, hlE, h6⟩
            · exact ⟨j, l, hj, hl, hjl, hjE, hlE, h5⟩
          · exact ⟨j, k, hj, hk, hjk, hjE, hkE, h4'⟩
        · exact ⟨i, l, hi, hl, hil, hiE, hlE, h3⟩
      · exact ⟨i, k, hi, hk, hik, hiE, hkE, h2⟩
    · exact ⟨i, j, hi, hj, hij, hiE, hjE, h1⟩
  obtain ⟨p, q, hp', hq', hpq, hpE, hqE, hpqfar⟩ := hfar
  have hpEc : EdgeComplete G Y (cyc C hp p) (cyc C hp (p + 1)) := by
    have hh := (WheelParity.cycEdge_iff_getElem (G := G) (Y := Y) hp p).mp hpE
    simpa only [cyc] using hh
  have hqEc : EdgeComplete G Y (cyc C hp q) (cyc C hp (q + 1)) := by
    have hh := (WheelParity.cycEdge_iff_getElem (G := G) (Y := Y) hp q).mp hqE
    simpa only [cyc] using hh
  exact ⟨cyc C hp p, cyc C hp (p + 1), cyc C hp q, cyc C hp (q + 1),
    cyc_mem hp _, cyc_mem hp _, cyc_mem hp _, cyc_mem hp _, hpEc, hqEc,
    far_edges_anticomplete hC hp hp' hq' hpq hpqfar⟩

/-- Four pairwise distinct rim vertices cannot carry the four edges of a square when the
ambient hole has length at least six. -/
theorem no_square_on_long_hole {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) (hn6 : 6 ≤ C.length) {a b c d : V}
    (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) (hd : d ∈ C)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (habE : G.Adj a b) (hcdE : G.Adj c d)
    (hacE : G.Adj a c) (hbdE : G.Adj b d) : False := by
  obtain ⟨ia, hia, hiaa⟩ := List.getElem_of_mem ha
  obtain ⟨ib, hib, hibb⟩ := List.getElem_of_mem hb
  obtain ⟨ic, hic, hicc⟩ := List.getElem_of_mem hc
  obtain ⟨id, hid, hidd⟩ := List.getElem_of_mem hd
  have hiad : ia ≠ id := by
    intro he
    exact had (hiaa.symm.trans
      ((HoleArithmetic.getElem_congr_idx C hia hid he).trans hidd))
  have hibc : ib ≠ ic := by
    intro he
    exact hbc (hibb.symm.trans
      ((HoleArithmetic.getElem_congr_idx C hib hic he).trans hicc))
  exact HoleArithmetic.two_common_nbrs (by omega : 5 ≤ C.length)
    hia hid hib hic hiad hibc
    ((HoleBasics.hole_adj_iff hC hia hib).mp (by simpa [hiaa, hibb] using habE))
    ((HoleBasics.hole_adj_iff hC hid hib).mp (by simpa [hidd, hibb] using hbdE.symm))
    ((HoleBasics.hole_adj_iff hC hia hic).mp (by simpa [hiaa, hicc] using hacE))
    ((HoleBasics.hole_adj_iff hC hid hic).mp (by simpa [hidd, hicc] using hcdE.symm))

end Workspace.ProofLemmas.Thm162ClaimFourRim
