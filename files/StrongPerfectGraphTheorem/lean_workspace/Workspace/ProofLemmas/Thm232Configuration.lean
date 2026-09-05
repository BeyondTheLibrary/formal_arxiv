import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.YEdgeFourConfig
import Workspace.ProofLemmas.Thm232FourYEdges
import Workspace.ProofLemmas.Thm232YEdgeLayout

/-!
# 23.2 — the six vertices `x₀, z, x₁, c₁, c₂, c₃`

PAPER (23.2, printed p. 139), the sentence after step (1):

> *"Since `(C,Y)` is not an odd wheel, there are vertices `x₀, z, x₁, c₁, c₂, c₃` of `C`, in
> order, and all distinct except possibly `x₁ = c₁` or `c₃ = x₀`, such that the `Y`-complete
> edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`."*

This is the vertex-level reading of `Thm232YEdgeLayout.exists_yEdge_layout`, which does the
work on cyclic positions.  *"In order"* is recorded by the two prefixes
`[x₀,z,x₁] <+: C.rotate k` and `[c₁,c₂,c₃] <+: C.rotate (k+d)` sharing the one base rotation
`k`, with `2 ≤ d` and `d + 2 ≤ |C|`; the two permitted coincidences are exactly `d = 2`
(`x₁ = c₁`) and `d + 2 = |C|` (`c₃ = x₀`), and `|C| ≥ 6` forbids both at once.

The last two conjuncts are what the rest of the printed proof actually consumes: the
parenthetical of step (2) — *"at least one of the `Y`-complete edges `c₁c₂`, `c₂c₃` belongs to
`C \ {x₀,z,x₁}`"* — and the exhaustiveness clause *"the `Y`-complete edges in `C` are `x₀z`,
`zx₁`, `c₁c₂`, `c₂c₃`"*, which step (3) uses in the form *"it is not the case that `c` and
both its neighbours in `C` are `Y`-complete"*.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm232Configuration

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.OptimalWheelChoice
open Workspace.ProofLemmas.WheelParity

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (23.2, printed p. 139):** *"Since `(C,Y)` is not an odd wheel, there are vertices
`x₀, z, x₁, c₁, c₂, c₃` of `C`, in order, and all distinct except possibly `x₁ = c₁` or
`c₃ = x₀`, such that the `Y`-complete edges in `C` are `x₀z, zx₁, c₁c₂, c₂c₃`."* -/
theorem exists_configuration (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (hmin : ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C') :
    ∃ (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ),
      2 ≤ d ∧ d + 2 ≤ C.length ∧
      [x₀, z, x₁] <+: C.rotate k ∧
      [c₁, c₂, c₃] <+: C.rotate (k + d) ∧
      (x₀ ∈ C ∧ z ∈ C ∧ x₁ ∈ C ∧ c₁ ∈ C ∧ c₂ ∈ C ∧ c₃ ∈ C) ∧
      (VertexComplete G x₀ Y ∧ VertexComplete G z Y ∧ VertexComplete G x₁ Y ∧
        VertexComplete G c₁ Y ∧ VertexComplete G c₂ Y ∧ VertexComplete G c₃ Y) ∧
      KiteTailBasics.IsRimNeighbours G C z x₀ x₁ ∧
      KiteTailBasics.IsRimNeighbours G C c₂ c₁ c₃ ∧
      (x₁ = c₁ ↔ d = 2) ∧ (c₃ = x₀ ↔ d + 2 = C.length) ∧
      (x₀ ≠ z ∧ x₀ ≠ x₁ ∧ x₀ ≠ c₁ ∧ x₀ ≠ c₂ ∧ z ≠ x₁ ∧ z ≠ c₁ ∧ z ≠ c₂ ∧ z ≠ c₃ ∧
        x₁ ≠ c₂ ∧ x₁ ≠ c₃ ∧ c₁ ≠ c₂ ∧ c₁ ≠ c₃ ∧ c₂ ≠ c₃) ∧
      (∃ u v : V, u ∈ C ∧ v ∈ C ∧ (u ≠ x₀ ∧ u ≠ z ∧ u ≠ x₁) ∧
        (v ≠ x₀ ∧ v ≠ z ∧ v ≠ x₁) ∧ EdgeComplete G Y u v) ∧
      (∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
        ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
        ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃}) := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hno : ¬ IsOddWheel G C Y := fun h => hG.1.2.1 ⟨C, Y, h⟩
  have h4 : yEdgeCount G Y C = 4 :=
    Thm232FourYEdges.exactly_four_yEdges G hG hbsp C Y hopt hmin
  obtain ⟨k, d, hd2, hdn, hlay⟩ := Thm232YEdgeLayout.exists_yEdge_layout hC hn6 hw hno h4
  ------------------------------------------------------------------
  -- index toolkit
  ------------------------------------------------------------------
  have gidx : ∀ (a b : ℕ) (ha : a < C.length) (hb : b < C.length), a = b →
      (C[a]'ha) = (C[b]'hb) := by intro a b ha hb h; subst h; rfl
  have hlenrot : ∀ q : ℕ, (C.rotate q).length = C.length := by intro q; simp
  have hget : ∀ (q i : ℕ) (hi : i < (C.rotate q).length),
      (C.rotate q)[i]'hi = C[(q + i) % C.length]'(Nat.mod_lt _ hn) := by
    intro q i hi
    rw [WheelParity.getElem_rotate_eq hn hi]
    exact gidx _ _ _ _ (by rw [show i + q = q + i from by omega])
  have hcons : ∀ L : List V, 3 ≤ L.length →
      ∃ (a b c : V) (r : List V), L = a :: b :: c :: r := by
    intro L hL
    match L with
    | [] => simp at hL
    | [a] => simp at hL
    | [a, b] => simp at hL
    | a :: b :: c :: r => exact ⟨a, b, c, r, rfl⟩
  have hread : ∀ (q : ℕ) (a b c : V) (r : List V), C.rotate q = a :: b :: c :: r →
      a = C[(q + 0) % C.length]'(Nat.mod_lt _ hn) ∧
      b = C[(q + 1) % C.length]'(Nat.mod_lt _ hn) ∧
      c = C[(q + 2) % C.length]'(Nat.mod_lt _ hn) := by
    intro q a b c r hrq
    have h0 : (0 : ℕ) < (C.rotate q).length := by rw [hlenrot]; omega
    have h1 : (1 : ℕ) < (C.rotate q).length := by rw [hlenrot]; omega
    have h2 : (2 : ℕ) < (C.rotate q).length := by rw [hlenrot]; omega
    have e0 : (C.rotate q)[0]? = some a := by rw [hrq]; rfl
    have e1 : (C.rotate q)[1]? = some b := by rw [hrq]; rfl
    have e2 : (C.rotate q)[2]? = some c := by rw [hrq]; rfl
    rw [List.getElem?_eq_getElem h0] at e0
    rw [List.getElem?_eq_getElem h1] at e1
    rw [List.getElem?_eq_getElem h2] at e2
    exact ⟨by rw [← Option.some_inj.mp e0, hget q 0 h0],
      by rw [← Option.some_inj.mp e1, hget q 1 h1],
      by rw [← Option.some_inj.mp e2, hget q 2 h2]⟩
  obtain ⟨x₀, z, x₁, r₁, hr₁⟩ := hcons (C.rotate k) (by rw [hlenrot]; omega)
  obtain ⟨c₁, c₂, c₃, r₂, hr₂⟩ := hcons (C.rotate (k + d)) (by rw [hlenrot]; omega)
  obtain ⟨hx₀, hz, hx₁⟩ := hread k x₀ z x₁ r₁ hr₁
  obtain ⟨hc₁, hc₂, hc₃⟩ := hread (k + d) c₁ c₂ c₃ r₂ hr₂
  -- the six vertices as positions on the rim, in the uniform shape `Q s`
  have hQ : ∀ s : ℕ, ∃ hs : (k + s) % C.length < C.length, True := by
    intro s; exact ⟨Nat.mod_lt _ hn, trivial⟩
  have hx₀' : x₀ = C[(k + 0) % C.length]'(Nat.mod_lt _ hn) := hx₀
  have hz' : z = C[(k + 1) % C.length]'(Nat.mod_lt _ hn) := hz
  have hx₁' : x₁ = C[(k + 2) % C.length]'(Nat.mod_lt _ hn) := hx₁
  have hc₁' : c₁ = C[(k + d) % C.length]'(Nat.mod_lt _ hn) := by
    rw [hc₁]; exact gidx _ _ _ _ (by rw [show k + d + 0 = k + d from by omega])
  have hc₂' : c₂ = C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) := by
    rw [hc₂]; exact gidx _ _ _ _ (by rw [show k + d + 1 = k + (d + 1) from by omega])
  have hc₃' : c₃ = C[(k + (d + 2)) % C.length]'(Nat.mod_lt _ hn) := by
    rw [hc₃]; exact gidx _ _ _ _ (by rw [show k + d + 2 = k + (d + 2) from by omega])
  ------------------------------------------------------------------
  -- distinctness from distinct residues
  ------------------------------------------------------------------
  have hne : ∀ s t : ℕ, s % C.length ≠ t % C.length →
      (C[(k + s) % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(k + t) % C.length]'(Nat.mod_lt _ hn)) := by
    intro s t hst
    refine HoleBasics.hole_ne_of_ne_index hC _ _ ?_
    intro h
    exact hst (Nat.ModEq.add_left_cancel' k h)
  have hlt : ∀ s : ℕ, s < C.length → s % C.length = s := fun s hs => Nat.mod_eq_of_lt hs
  have hd3mod : (d + 2) % C.length = 0 ∨ ((d + 2) % C.length = d + 2 ∧ d + 2 < C.length) := by
    rcases Nat.lt_or_ge (d + 2) C.length with h | h
    · exact Or.inr ⟨Nat.mod_eq_of_lt h, h⟩
    · have he : d + 2 = C.length := by omega
      exact Or.inl (by rw [he]; exact Nat.mod_self _)
  ------------------------------------------------------------------
  -- the four `Y`-complete edges
  ------------------------------------------------------------------
  have hE : ∀ s : ℕ, s < C.length → CycEdge G Y C (k + s) →
      EdgeComplete G Y (C[(k + s) % C.length]'(Nat.mod_lt _ hn))
        (C[(k + (s + 1)) % C.length]'(Nat.mod_lt _ hn)) := by
    intro s hs hce
    have h := (cycEdge_iff_getElem hn (k + s)).mp hce
    rw [gidx ((k + s + 1) % C.length) ((k + (s + 1)) % C.length) (Nat.mod_lt _ hn)
      (Nat.mod_lt _ hn) (by rw [show k + s + 1 = k + (s + 1) from by omega])] at h
    exact h
  have hce0 : CycEdge G Y C (k + 0) := (hlay 0 (by omega)).mpr (Or.inl rfl)
  have hce1 : CycEdge G Y C (k + 1) := (hlay 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hced : CycEdge G Y C (k + d) := (hlay d (by omega)).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have hced1 : CycEdge G Y C (k + (d + 1)) :=
    (hlay (d + 1) (by omega)).mpr (Or.inr (Or.inr (Or.inr rfl)))
  have hE0 : EdgeComplete G Y x₀ z := by rw [hx₀', hz']; exact hE 0 (by omega) hce0
  have hE1 : EdgeComplete G Y z x₁ := by rw [hz', hx₁']; exact hE 1 (by omega) hce1
  have hE2 : EdgeComplete G Y c₁ c₂ := by rw [hc₁', hc₂']; exact hE d (by omega) hced
  have hE3 : EdgeComplete G Y c₂ c₃ := by
    rw [hc₂', hc₃']
    have h := hE (d + 1) (by omega) hced1
    rw [gidx ((k + (d + 1 + 1)) % C.length) ((k + (d + 2)) % C.length) (Nat.mod_lt _ hn)
      (Nat.mod_lt _ hn) (by rw [show k + (d + 1 + 1) = k + (d + 2) from by omega])] at h
    exact h
  ------------------------------------------------------------------
  -- membership and the two rim-neighbour triples
  ------------------------------------------------------------------
  have hpre1 : [x₀, z, x₁] <+: C.rotate k := ⟨r₁, by rw [hr₁]; rfl⟩
  have hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d) := ⟨r₂, by rw [hr₂]; rfl⟩
  obtain ⟨hx₀C, hzC, hx₁C, hnb⟩ := KiteTailBasics.hole_triple hC ⟨k, hpre1⟩
  obtain ⟨hc₁C, hc₂C, hc₃C, hnbc⟩ := KiteTailBasics.hole_triple hC ⟨k + d, hpre2⟩
  refine ⟨x₀, z, x₁, c₁, c₂, c₃, k, d, hd2, hdn, hpre1, hpre2,
    ⟨hx₀C, hzC, hx₁C, hc₁C, hc₂C, hc₃C⟩,
    ⟨hE0.2.1, hE0.2.2, hE1.2.2, hE2.2.1, hE2.2.2, hE3.2.2⟩, hnb, hnbc, ?_, ?_, ?_, ?_, ?_⟩
  ------------------------------------------------------------------
  -- `x₁ = c₁ ↔ d = 2`
  ------------------------------------------------------------------
  · constructor
    · intro h
      by_contra hcon
      exact hne 2 d (by rw [hlt 2 (by omega), hlt d (by omega)]; omega) (by rw [← hx₁', ← hc₁']; exact h)
    · intro h; rw [hx₁', hc₁', h]
  ------------------------------------------------------------------
  -- `c₃ = x₀ ↔ d + 2 = C.length`
  ------------------------------------------------------------------
  · constructor
    · intro h
      rcases hd3mod with hm | ⟨hm, hmlt⟩
      · rcases Nat.lt_or_ge (d + 2) C.length with hlt2 | hge2
        · rw [Nat.mod_eq_of_lt hlt2] at hm; omega
        · omega
      · exact absurd (by rw [← hc₃', ← hx₀']; exact h)
          (hne (d + 2) 0 (by rw [hm, hlt 0 (by omega)]; omega))
    · intro h
      rw [hc₃', hx₀']
      exact gidx _ _ _ _ (by rw [show (k + (d + 2)) % C.length = (k + 0) % C.length from by
        rw [show k + (d + 2) = (k + 0) + C.length from by omega, Nat.add_mod_right]])
  ------------------------------------------------------------------
  -- pairwise distinctness
  ------------------------------------------------------------------
  · have key : ∀ s t : ℕ, s < C.length → t < C.length → s ≠ t →
        (C[(k + s) % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(k + t) % C.length]'(Nat.mod_lt _ hn)) :=
      fun s t hs ht hst => hne s t (by rw [hlt s hs, hlt t ht]; exact hst)
    have hc₃'' : c₃ = C[(k + ((d + 2) % C.length)) % C.length]'(Nat.mod_lt _ hn) := by
      rw [hc₃']
      exact gidx _ _ _ _ (by rw [Nat.add_mod_mod])
    have hd3lt : (d + 2) % C.length < C.length := Nat.mod_lt _ hn
    have hd3ne : (d + 2) % C.length ≠ 1 ∧ (d + 2) % C.length ≠ 2 ∧
        (d + 2) % C.length ≠ d ∧ (d + 2) % C.length ≠ d + 1 := by
      rcases hd3mod with hm | ⟨hm, hmlt⟩ <;> rw [hm] <;> omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hx₀', hz']; exact key 0 1 (by omega) (by omega) (by omega)
    · rw [hx₀', hx₁']; exact key 0 2 (by omega) (by omega) (by omega)
    · rw [hx₀', hc₁']; exact key 0 d (by omega) (by omega) (by omega)
    · rw [hx₀', hc₂']; exact key 0 (d + 1) (by omega) (by omega) (by omega)
    · rw [hz', hx₁']; exact key 1 2 (by omega) (by omega) (by omega)
    · rw [hz', hc₁']; exact key 1 d (by omega) (by omega) (by omega)
    · rw [hz', hc₂']; exact key 1 (d + 1) (by omega) (by omega) (by omega)
    · rw [hz', hc₃'']; exact key 1 ((d + 2) % C.length) (by omega) hd3lt (by omega)
    · rw [hx₁', hc₂']; exact key 2 (d + 1) (by omega) (by omega) (by omega)
    · rw [hx₁', hc₃'']; exact key 2 ((d + 2) % C.length) (by omega) hd3lt (by omega)
    · rw [hc₁', hc₂']; exact key d (d + 1) (by omega) (by omega) (by omega)
    · rw [hc₁', hc₃'']; exact key d ((d + 2) % C.length) (by omega) hd3lt (by omega)
    · rw [hc₂', hc₃'']; exact key (d + 1) ((d + 2) % C.length) (by omega) hd3lt (by omega)
  ------------------------------------------------------------------
  -- a `Y`-complete edge inside `C \ {x₀, z, x₁}`
  ------------------------------------------------------------------
  · have key : ∀ s t : ℕ, s < C.length → t < C.length → s ≠ t →
        (C[(k + s) % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(k + t) % C.length]'(Nat.mod_lt _ hn)) :=
      fun s t hs ht hst => hne s t (by rw [hlt s hs, hlt t ht]; exact hst)
    rcases Nat.lt_or_ge 2 d with hd | hd
    · refine ⟨c₁, c₂, hc₁C, hc₂C, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hE2⟩
      · rw [hc₁', hx₀']; exact key d 0 (by omega) (by omega) (by omega)
      · rw [hc₁', hz']; exact key d 1 (by omega) (by omega) (by omega)
      · rw [hc₁', hx₁']; exact key d 2 (by omega) (by omega) (by omega)
      · rw [hc₂', hx₀']; exact key (d + 1) 0 (by omega) (by omega) (by omega)
      · rw [hc₂', hz']; exact key (d + 1) 1 (by omega) (by omega) (by omega)
      · rw [hc₂', hx₁']; exact key (d + 1) 2 (by omega) (by omega) (by omega)
    · have hde : d = 2 := by omega
      refine ⟨c₂, c₃, hc₂C, hc₃C, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, hE3⟩
      · rw [hc₂', hx₀']; exact key (d + 1) 0 (by omega) (by omega) (by omega)
      · rw [hc₂', hz']; exact key (d + 1) 1 (by omega) (by omega) (by omega)
      · rw [hc₂', hx₁']; exact key (d + 1) 2 (by omega) (by omega) (by omega)
      · rw [hc₃', hx₀']; exact key (d + 2) 0 (by omega) (by omega) (by omega)
      · rw [hc₃', hz']; exact key (d + 2) 1 (by omega) (by omega) (by omega)
      · rw [hc₃', hx₁']; exact key (d + 2) 2 (by omega) (by omega) (by omega)
  ------------------------------------------------------------------
  -- the `Y`-complete edges of `C` are exactly the four listed
  ------------------------------------------------------------------
  · intro u v huC hvC hEuv
    obtain ⟨m, hmlt, hme, hmv⟩ := Thm232FourYEdges.exists_pos_of_yEdge hC huC hvC hEuv
    obtain ⟨t, htlt, hteq⟩ := OddWheelParityFacts.exists_offset hn k m
    have hmmod : m % C.length = m := hlt m hmlt
    have hcet : CycEdge G Y C (k + t) := (YEdgeFourConfig.cycEdge_congr hn hteq).mpr hme
    have hpu : C[m % C.length]'(Nat.mod_lt _ hn)
        = C[(k + t) % C.length]'(Nat.mod_lt _ hn) := gidx _ _ _ _ hteq.symm
    have hpv : C[(m + 1) % C.length]'(Nat.mod_lt _ hn)
        = C[(k + (t + 1)) % C.length]'(Nat.mod_lt _ hn) := by
      refine gidx _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) ?_
      have e : (k + (t + 1)) % C.length = (m + 1) % C.length := by
        conv_lhs => rw [show k + (t + 1) = (k + t) + 1 from by omega]
        rw [← Nat.mod_add_mod (k + t) C.length 1, hteq, Nat.mod_add_mod]
      exact e.symm
    have hu' : u = C[(k + t) % C.length]'(Nat.mod_lt _ hn) ∧
        v = C[(k + (t + 1)) % C.length]'(Nat.mod_lt _ hn) ∨
        v = C[(k + t) % C.length]'(Nat.mod_lt _ hn) ∧
        u = C[(k + (t + 1)) % C.length]'(Nat.mod_lt _ hn) := by
      rcases hmv with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at e1 e2
        exact Or.inl ⟨by rw [← Option.some_inj.mp e1, hpu],
          by rw [← Option.some_inj.mp e2, hpv]⟩
      · rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at e1 e2
        exact Or.inr ⟨by rw [← Option.some_inj.mp e1, hpu],
          by rw [← Option.some_inj.mp e2, hpv]⟩
    have ht4 : t = 0 ∨ t = 1 ∨ t = d ∨ t = d + 1 := (hlay t htlt).mp hcet
    have hpair : ({u, v} : Set V) = {C[(k + t) % C.length]'(Nat.mod_lt _ hn),
        C[(k + (t + 1)) % C.length]'(Nat.mod_lt _ hn)} := by
      rcases hu' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Set.pair_comm _ _
    rcases ht4 with rfl | rfl | rfl | rfl
    · left; rw [hpair, hx₀', hz']
    · right; left; rw [hpair, hz', hx₁']
    · right; right; left; rw [hpair, hc₁', hc₂']
    · right; right; right; rw [hpair, hc₂', hc₃']


end Workspace.ProofLemmas.Thm232Configuration
