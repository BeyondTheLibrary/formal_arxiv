import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm232Claim3C2
import Workspace.ProofLemmas.Thm232OppositeNeighbours
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.YEdgeFourConfig

/-!
# 23.2 — claim (3)

The first half of claim (3) is reduced to the general consequence of 16.1 in
`Thm232OppositeNeighbours`.  Two exact pieces of the printed argument are kept separate below:
the parity reading of the four-edge layout, and the special case at `c₂`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232Claim3

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem succ_mod_eq {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

private theorem succ_succ_ne_self {n i : ℕ} (hn : 4 ≤ n) (hi : i < n) :
    ((i + 1) % n + 1) % n ≠ i := by
  rw [succ_mod_eq hi]
  by_cases h : i + 1 = n
  · rw [if_pos h, Nat.mod_eq_of_lt (show 1 < n by omega)]
    omega
  · rw [if_neg h, succ_mod_eq (show i + 1 < n by omega)]
    split_ifs <;> omega

/-- A cyclic edge of a nodup list has a unique cyclic position, even though its ends are
recorded as an unordered pair. -/
private theorem edge_position_eq {C : List V} (hnd : C.Nodup) (hn4 : 4 ≤ C.length)
    {m a : ℕ}
    (hpair :
      ({C[m % C.length]'(Nat.mod_lt _ (by omega)),
          C[(m + 1) % C.length]'(Nat.mod_lt _ (by omega))} : Set V) =
        {C[a % C.length]'(Nat.mod_lt _ (by omega)),
          C[(a + 1) % C.length]'(Nat.mod_lt _ (by omega))}) :
    m % C.length = a % C.length := by
  rcases Set.pair_eq_pair_iff.mp hpair with h | h
  · exact hnd.getElem_inj_iff.mp h.1
  · exfalso
    have h0 : m % C.length = (a + 1) % C.length := hnd.getElem_inj_iff.mp h.1
    have h1 : (m + 1) % C.length = a % C.length := hnd.getElem_inj_iff.mp h.2
    have ha : (a % C.length + 1) % C.length = (a + 1) % C.length :=
      Nat.mod_add_mod a C.length 1
    have hm : (m % C.length + 1) % C.length = (m + 1) % C.length :=
      Nat.mod_add_mod m C.length 1
    apply succ_succ_ne_self hn4 (Nat.mod_lt _ (by omega))
    calc
      ((a % C.length + 1) % C.length + 1) % C.length =
          ((a + 1) % C.length + 1) % C.length := by rw [ha]
      _ = (m % C.length + 1) % C.length := by rw [h0]
      _ = (m + 1) % C.length := hm
      _ = a % C.length := h1

/-- **PAPER (23.2, claim (3), printed p. 139):**
*"Then `c,z` are nonadjacent and have opposite wheel-parity in the wheel `(C,Y)`"*.

Here `c` lies in `A₀ \ {c₂}`.  The four exhaustive `Y`-complete edges make `z` and `c₂`
the two vertices in one parity class, while every other rim vertex lies in the other class. -/
theorem layout_opposite (G : SimpleGraph V) (C : List V) (Y : Set V)
    (hC : IsHoleList G C)
    (heven : Even (Workspace.ProofLemmas.WheelParity.cycCount G Y C C.length))
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (c : V) (hcC : c ∈ C) (hcz : c ≠ z) (hc0 : c ≠ x₀) (hc1 : c ≠ x₁)
    (hcc2 : c ≠ c₂) :
    OppositeWheelParity G C Y c z := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  have hrotlen : ∀ q : ℕ, (C.rotate q).length = C.length := by intro q; simp
  have hget : ∀ (q i : ℕ) (hi : i < (C.rotate q).length),
      (C.rotate q)[i]'hi = C[(q + i) % C.length]'(Nat.mod_lt _ hn) := by
    intro q i hi
    rw [Workspace.ProofLemmas.WheelParity.getElem_rotate_eq hn hi]
    exact hC.2.1.getElem_inj_iff.mpr (congrArg (fun a => a % C.length) (by omega))
  obtain ⟨hx0C, hzC, hx1C, hnb⟩ :=
    Workspace.ProofLemmas.KiteTailBasics.hole_triple hC ⟨k, hpre1⟩
  obtain ⟨hc1C, hc2C, hc3C, hnbc⟩ :=
    Workspace.ProofLemmas.KiteTailBasics.hole_triple hC ⟨k + d, hpre2⟩
  obtain ⟨r₀, hr₀⟩ := hpre1
  obtain ⟨r₁, hr₁⟩ := hpre2
  have hk0 : 0 < (C.rotate k).length := by simpa using (show 0 < C.length by omega)
  have hk1 : 1 < (C.rotate k).length := by simpa using (show 1 < C.length by omega)
  have hk2 : 2 < (C.rotate k).length := by simpa using (show 2 < C.length by omega)
  have hkd0 : 0 < (C.rotate (k + d)).length := by simpa using (show 0 < C.length by omega)
  have hkd1 : 1 < (C.rotate (k + d)).length := by simpa using (show 1 < C.length by omega)
  have hkd2 : 2 < (C.rotate (k + d)).length := by simpa using (show 2 < C.length by omega)
  have hx0p : C[k % C.length]'(Nat.mod_lt _ hn) = x₀ := by
    have e : (C.rotate k)[0]? = some x₀ := by rw [← hr₀]; rfl
    rw [List.getElem?_eq_getElem hk0] at e
    have er : (C.rotate k)[0]'hk0 = x₀ := Option.some_inj.mp e
    simpa only [Nat.add_zero] using (hget k 0 hk0).symm.trans er
  have hzp : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z := by
    have e : (C.rotate k)[1]? = some z := by rw [← hr₀]; rfl
    rw [List.getElem?_eq_getElem hk1] at e
    exact (hget k 1 hk1).symm.trans (Option.some_inj.mp e)
  have hx1p : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ := by
    have e : (C.rotate k)[2]? = some x₁ := by rw [← hr₀]; rfl
    rw [List.getElem?_eq_getElem hk2] at e
    exact (hget k 2 hk2).symm.trans (Option.some_inj.mp e)
  have hc1p : C[(k + d) % C.length]'(Nat.mod_lt _ hn) = c₁ := by
    have e : (C.rotate (k + d))[0]? = some c₁ := by rw [← hr₁]; rfl
    rw [List.getElem?_eq_getElem hkd0] at e
    simpa only [Nat.add_zero] using
      (hget (k + d) 0 hkd0).symm.trans (Option.some_inj.mp e)
  have hc2p : C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) = c₂ := by
    have e : (C.rotate (k + d))[1]? = some c₂ := by rw [← hr₁]; rfl
    rw [List.getElem?_eq_getElem hkd1] at e
    have h := (hget (k + d) 1 hkd1).symm.trans (Option.some_inj.mp e)
    exact (hC.2.1.getElem_inj_iff.mpr
      (congrArg (fun a => a % C.length) (show k + (d + 1) = k + d + 1 by omega))).trans h
  have hc3p : C[(k + (d + 2)) % C.length]'(Nat.mod_lt _ hn) = c₃ := by
    have e : (C.rotate (k + d))[2]? = some c₃ := by rw [← hr₁]; rfl
    rw [List.getElem?_eq_getElem hkd2] at e
    have h := (hget (k + d) 2 hkd2).symm.trans (Option.some_inj.mp e)
    exact (hC.2.1.getElem_inj_iff.mpr
      (congrArg (fun a => a % C.length) (show k + (d + 2) = k + d + 2 by omega))).trans h
  have hE0 : EdgeComplete G Y x₀ z := ⟨hnb.2.2.2.1.symm, h0Y, hzY⟩
  have hE1 : EdgeComplete G Y z x₁ := ⟨hnb.2.2.2.2.1, hzY, h1Y⟩
  have hE2 : EdgeComplete G Y c₁ c₂ := ⟨hnbc.2.2.2.1.symm, hc1Y, hc2Y⟩
  have hE3 : EdgeComplete G Y c₂ c₃ := ⟨hnbc.2.2.2.2.1, hc2Y, hc3Y⟩
  have hlayout : ∀ i : ℕ, i < C.length →
      (Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + i) ↔
        i = 0 ∨ i = 1 ∨ i = d ∨ i = d + 1) := by
    intro i hi
    constructor
    · intro hce
      have hE := (Workspace.ProofLemmas.WheelParity.cycEdge_iff_getElem hn (k + i)).mp hce
      have hpairs := hexh _ _ (List.getElem_mem _) (List.getElem_mem _) hE
      rcases hpairs with hp | hp | hp | hp
      · have hpos : (k + i) % C.length = k % C.length :=
          edge_position_eq hC.2.1 hn4 (hp.trans (by rw [hx0p, hzp]))
        have hmod : k + i ≡ k + 0 [MOD C.length] := by simpa only [Nat.add_zero] using hpos
        have hoff := Nat.ModEq.add_left_cancel' k hmod
        change i % C.length = 0 % C.length at hoff
        rw [Nat.mod_eq_of_lt hi, Nat.zero_mod] at hoff
        exact Or.inl hoff
      · have hpos : (k + i) % C.length = (k + 1) % C.length :=
          edge_position_eq hC.2.1 hn4 (hp.trans (by rw [hzp, hx1p]))
        have hmod : k + i ≡ k + 1 [MOD C.length] := hpos
        have hoff := Nat.ModEq.add_left_cancel' k hmod
        change i % C.length = 1 % C.length at hoff
        rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (show 1 < C.length by omega)] at hoff
        exact Or.inr (Or.inl hoff)
      · have hpos : (k + i) % C.length = (k + d) % C.length :=
          edge_position_eq hC.2.1 hn4 (hp.trans (by
            rw [hc1p]
            rw [show k + d + 1 = k + (d + 1) by omega, hc2p]))
        have hmod : k + i ≡ k + d [MOD C.length] := hpos
        have hoff := Nat.ModEq.add_left_cancel' k hmod
        change i % C.length = d % C.length at hoff
        rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (show d < C.length by omega)] at hoff
        exact Or.inr (Or.inr (Or.inl hoff))
      · have hpos : (k + i) % C.length = (k + (d + 1)) % C.length :=
          edge_position_eq hC.2.1 hn4 (hp.trans (by
            rw [hc2p]
            rw [show k + (d + 1) + 1 = k + (d + 2) by omega, hc3p]))
        have hmod : k + i ≡ k + (d + 1) [MOD C.length] := hpos
        have hoff := Nat.ModEq.add_left_cancel' k hmod
        change i % C.length = (d + 1) % C.length at hoff
        rw [Nat.mod_eq_of_lt hi,
          Nat.mod_eq_of_lt (show d + 1 < C.length by omega)] at hoff
        exact Or.inr (Or.inr (Or.inr hoff))
    · intro hi4
      rcases hi4 with hi0 | hi1 | hid | hid1
      · rw [hi0]
        apply (Workspace.ProofLemmas.WheelParity.cycEdge_iff_getElem hn (k + 0)).mpr
        simpa only [Nat.add_zero, hx0p, hzp] using hE0
      · rw [hi1]
        apply (Workspace.ProofLemmas.WheelParity.cycEdge_iff_getElem hn (k + 1)).mpr
        simpa only [Nat.add_assoc, hzp, hx1p] using hE1
      · rw [hid]
        apply (Workspace.ProofLemmas.WheelParity.cycEdge_iff_getElem hn (k + d)).mpr
        simpa only [Nat.add_assoc, hc1p, hc2p] using hE2
      · rw [hid1]
        apply (Workspace.ProofLemmas.WheelParity.cycEdge_iff_getElem hn (k + (d + 1))).mpr
        simpa only [Nat.add_assoc, hc2p, hc3p] using hE3
  obtain ⟨m, hm, hmc⟩ := List.getElem_of_mem hcC
  obtain ⟨t, ht, hkt⟩ :=
    Workspace.ProofLemmas.OddWheelParityFacts.exists_offset hn k m
  have hcpos : C[(k + t) % C.length]'(Nat.mod_lt _ hn) = c := by
    have hidx : (k + t) % C.length = m := hkt.trans (Nat.mod_eq_of_lt hm)
    exact (hC.2.1.getElem_inj_iff.mpr hidx).trans hmc
  have ht0 : t ≠ 0 := by
    intro h
    subst t
    exact hc0 (hcpos.symm.trans hx0p)
  have ht1 : t ≠ 1 := by
    intro h
    subst t
    exact hcz (hcpos.symm.trans hzp)
  have ht2 : t ≠ 2 := by
    intro h
    subst t
    exact hc1 (hcpos.symm.trans hx1p)
  have htd1 : t ≠ d + 1 := by
    intro h
    rw [h] at hcpos
    exact hcc2 (hcpos.symm.trans hc2p)
  let g : ℕ → ℕ := fun j =>
    Workspace.ProofLemmas.WheelParity.cycCount G Y C (k + j)
  have hgsucc : ∀ j : ℕ, g (j + 1) = g j +
      (if Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + j) then 1 else 0) := by
    intro j
    dsimp only [g]
    rw [show k + (j + 1) = (k + j) + 1 by omega,
      Workspace.ProofLemmas.WheelParity.cycCount_succ]
  have he0 : Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + 0) :=
    (hlayout 0 (by omega)).mpr (Or.inl rfl)
  have he1 : Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + 1) :=
    (hlayout 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hg1 : g 1 = g 0 + 1 := by
    have h := hgsucc 0
    rw [if_pos he0] at h
    simpa using h
  have hg2 : g 2 = g 0 + 2 := by
    have h := hgsucc 1
    rw [if_pos he1] at h
    have h' : g 2 = g 1 + 1 := by
      convert h using 1 <;> omega
    rw [hg1] at h'
    omega
  have hflatBefore : ∀ q : ℕ, 2 + q ≤ d → g (2 + q) = g 2 := by
    intro q
    induction q with
    | zero => intro _; rfl
    | succ q ih =>
        intro hqd
        have hjlt : 2 + q < C.length := by omega
        have hno : ¬ Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + (2 + q)) := by
          intro hce
          have hh := (hlayout (2 + q) hjlt).mp hce
          rcases hh with hh | hh | hh | hh <;> omega
        have hs := hgsucc (2 + q)
        rw [if_neg hno] at hs
        calc
          g (2 + (q + 1)) = g (2 + q + 1) := congrArg g (by omega)
          _ = g (2 + q) + 0 := hs
          _ = g 2 + 0 := by rw [ih (by omega)]
          _ = g 2 := Nat.add_zero _
  have hgd : g d = g 0 + 2 := by
    have h := hflatBefore (d - 2) (by omega)
    rw [show 2 + (d - 2) = d by omega, hg2] at h
    exact h
  have hed : Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + d) :=
    (hlayout d (by omega)).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hed1 : Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + (d + 1)) :=
    (hlayout (d + 1) (by omega)).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hgd1 : g (d + 1) = g 0 + 3 := by
    have h := hgsucc d
    rw [if_pos hed] at h
    omega
  have hgd2 : g (d + 2) = g 0 + 4 := by
    have h := hgsucc (d + 1)
    rw [if_pos hed1] at h
    have h' : g (d + 2) = g (d + 1) + 1 := by
      convert h using 1 <;> omega
    rw [hgd1] at h'
    omega
  have hflatAfter : ∀ q : ℕ, d + 2 + q ≤ C.length →
      g (d + 2 + q) = g (d + 2) := by
    intro q
    induction q with
    | zero => intro _; rfl
    | succ q ih =>
        intro hqn
        have hjlt : d + 2 + q < C.length := by omega
        have hno : ¬ Workspace.ProofLemmas.WheelParity.CycEdge G Y C (k + (d + 2 + q)) := by
          intro hce
          have hh := (hlayout (d + 2 + q) hjlt).mp hce
          rcases hh with hh | hh | hh | hh <;> omega
        have hs := hgsucc (d + 2 + q)
        rw [if_neg hno] at hs
        calc
          g (d + 2 + (q + 1)) = g (d + 2 + q + 1) := congrArg g (by omega)
          _ = g (d + 2 + q) + 0 := hs
          _ = g (d + 2) + 0 := by rw [ih (by omega)]
          _ = g (d + 2) := Nat.add_zero _
  have hgt : g t = g 0 + 2 ∨ g t = g 0 + 4 := by
    rcases Nat.lt_or_ge t (d + 1) with htd | htd
    · left
      have h := hflatBefore (t - 2) (by omega)
      rw [show 2 + (t - 2) = t by omega, hg2] at h
      exact h
    · have htd2 : d + 2 ≤ t := by omega
      right
      have h := hflatAfter (t - (d + 2)) (by omega)
      rw [show d + 2 + (t - (d + 2)) = t by omega, hgd2] at h
      exact h
  refine ⟨hcz, hcC, hzC, ?_⟩
  intro hsame
  have hitz : (k + t) % C.length ≠ (k + 1) % C.length := by
    intro he
    apply hcz
    rw [← hcpos, ← hzp]
    exact hC.2.1.getElem_inj_iff.mpr he
  have hsame' : SameWheelParity G C Y
      (C[(k + t) % C.length]'(Nat.mod_lt _ hn))
      (C[(k + 1) % C.length]'(Nat.mod_lt _ hn)) := by
    rwa [hcpos, hzp]
  have hpar := (Workspace.ProofLemmas.WheelParity.sameWheelParity_iff hC heven
    (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) hitz).mp hsame'
  have hraw : g t % 2 = g 1 % 2 := by
    dsimp only [g]
    calc
      Workspace.ProofLemmas.WheelParity.cycCount G Y C (k + t) % 2 =
          Workspace.ProofLemmas.WheelParity.cycCount G Y C ((k + t) % C.length) % 2 :=
            Workspace.ProofLemmas.WheelParity.cycCount_mod_two heven (k + t)
      _ = Workspace.ProofLemmas.WheelParity.cycCount G Y C ((k + 1) % C.length) % 2 := hpar
      _ = Workspace.ProofLemmas.WheelParity.cycCount G Y C (k + 1) % 2 :=
        (Workspace.ProofLemmas.WheelParity.cycCount_mod_two heven (k + 1)).symm
  rcases hgt with hgt | hgt <;> rw [hgt, hg1] at hraw <;> omega

/-- The first paragraph of claim (3): `y` has no neighbour in `A₀ \ {c₂}`. -/
theorem no_neighbour_except_c2 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k) (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w) (hwC : w ∈ C) (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y) :
    ∀ c : V, c ∈ C → c ≠ z → c ≠ x₀ → c ≠ x₁ → c ≠ c₂ → ¬ G.Adj y c := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hBerge : Berge G := hG.1.1.1.1.1
  have heven := Workspace.ProofLemmas.WheelBasics.even_cycCount_of_wheel hBerge hw
  have hzy : G.Adj z y := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hpath.1 (i := 0) (by rw [hTeq]; simp)
    simpa [hTeq] using h
  have hyT : y ∈ T := by rw [hTeq]; simp
  have hyw : y ≠ w := by
    intro hyw
    rw [hyw] at hzy
    rcases hnb.2.2.2.2.2 w hwC hzy with he | he
    · exact hw0 he
    · exact hw1 he
  have hyz : y ≠ z := hzy.ne'
  have hyint : y ∈ SPGT.interior T :=
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hpath).mpr
      ⟨hyT, hyz, hyw⟩
  obtain ⟨hyY, hyNC⟩ := hint y hyint
  have hyC : y ∉ C := by
    intro hyC
    rcases hnb.2.2.2.2.2 y hyC hzy with he | he
    · exact (havoid y hyT).1 he
    · exact (havoid y hyT).2 he
  intro c hcC hcz hc0 hc1 hcc2 hyc
  have hzc : ¬ G.Adj z c := by
    intro h
    rcases hnb.2.2.2.2.2 c hcC h with he | he
    · exact hc0 he
    · exact hc1 he
  have hopp := layout_opposite G C Y hC heven x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn
    hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hexh c hcC hcz hc0 hc1 hcc2
  exact Workspace.ProofLemmas.Thm232OppositeNeighbours.impossible G hG hbsp C Y hopt
    y c z hyC hyY hyNC hcC hopp.2.2.1 hyc hzy.symm (fun h => hzc h.symm) hopp

/-- **PAPER (23.2, claim (3), printed pp. 139–140):**
*"Next suppose that `y` is adjacent to `c₂`. … But then the hole
`x₀-Q-c₃-c₂-y-z-x₀` is the rim of an odd wheel with hub `Y`, contrary to `G ∈ F₈`.
So `y` is not adjacent to `c₂`."* -/
theorem not_adj_c2_gap (G : SimpleGraph V) (hG : InF8 G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ y : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k) (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (hyz : G.Adj y z) (hyC : y ∉ C) (hyY : y ∉ Y)
    (hyNC : ¬ VertexComplete G y Y)
    (hnone : ∀ c : V, c ∈ C → c ≠ z → c ≠ x₀ → c ≠ x₁ → c ≠ c₂ →
      ¬ G.Adj y c) (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁)) :
    ¬ G.Adj y c₂ :=
  Workspace.ProofLemmas.Thm232Claim3C2.not_adj_c2 hG C Y hopt x₀ z x₁ c₁ c₂ c₃ y k d
    hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh hyz hyC hyY hyNC hnone

/-- **PAPER (23.2), claim (3):** `y` is anticomplete to
`A₀ = V(C) \ {z,x₀,x₁}`. -/
theorem claim3 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k) (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : KiteTailBasics.IsRimNeighbours G C z x₀ x₁)
    (hnbc : KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w) (hwC : w ∈ C) (hw0 : w ≠ x₀) (hw1 : w ≠ x₁)
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁)) :
    VertexAnticomplete G y ({v : V | v ∈ C} \ ({z, x₀, x₁} : Set V)) := by
  classical
  have hnone := no_neighbour_except_c2 G hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ k d
    hd2 hdn hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hexh T R y w hTeq hpath
    hwC hw0 hw1 havoid hint
  have hzy : G.Adj z y := by
    have h := Workspace.ProofLemmas.PathBasics.path_adj_succ hpath.1 (i := 0) (by rw [hTeq]; simp)
    simpa [hTeq] using h
  have hyT : y ∈ T := by rw [hTeq]; simp
  have hyw : y ≠ w := by
    intro hyw
    rw [hyw] at hzy
    rcases hnb.2.2.2.2.2 w hwC hzy with he | he
    · exact hw0 he
    · exact hw1 he
  have hyint : y ∈ SPGT.interior T :=
    (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hpath).mpr
      ⟨hyT, hzy.ne', hyw⟩
  have hyC : y ∉ C := by
    intro hyC
    rcases hnb.2.2.2.2.2 y hyC hzy with he | he
    · exact (havoid y hyT).1 he
    · exact (havoid y hyT).2 he
  have hc2 := not_adj_c2_gap G hG C Y hopt x₀ z x₁ c₁ c₂ c₃ y k d hd2 hdn
    hpre1 hpre2 h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh hzy.symm hyC (hint y hyint).1
    (hint y hyint).2 hnone h2
  intro c hcA
  rw [KiteTailBasics.mem_rim_minus] at hcA
  by_cases he : c = c₂
  · subst c
    exact hc2
  · exact hnone c hcA.1 hcA.2.1 hcA.2.2.1 hcA.2.2.2 he

end Workspace.ProofLemmas.Thm232Claim3
