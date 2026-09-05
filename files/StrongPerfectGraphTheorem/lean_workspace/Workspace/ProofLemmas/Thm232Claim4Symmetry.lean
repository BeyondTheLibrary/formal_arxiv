import Workspace.ProofLemmas.Thm232Claim4Core

/-!
# 23.2, claim (4)

PAPER (23.2, printed p. 140):

> ***(4) If `n = 1` then no neighbour of `v₁` in `A₀` is `Y`-complete.***

Here `n = 1` means that the path `T` is `z-y-v₁-v₂` with `v₂ ∈ A₀`, so `v₁` is its last interior
vertex.  `claim4` discharges the printed *"from the symmetry we may assume that `x₀ ≠ c₃`"* by
applying `Thm232Claim4Core.orientation_absurd` either to the arc of `C \ z` from `c₃` to `x₀`,
or — when `x₀ = c₃` — to the reversed arc from `c₁` to `x₁`.  Both cannot degenerate: `x₀ = c₃`
and `x₁ = c₁` together would make `C` a four-cycle, while the rim of a wheel has length at
least six.  The cyclic-position bookkeeping is the one written for claim (3) in
`Thm232Claim3C2`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232Claim4Symmetry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.ProofLemmas.Thm232Claim3C2

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **PAPER (23.2), claim (4), printed p. 140:** *"If `n = 1` then no neighbour of `v₁` in `A₀`
is `Y`-complete."*  See `Thm232Claim4Core.orientation_absurd` for the printed argument. -/
theorem claim4 (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁) (hnbc : IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T : List V) (y v₁ w : V) (hTeq : T = [z, y, v₁, w])
    (hpath : IsPathFrom G T z w)
    (hwA : w ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h3 : VertexAnticomplete G y ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (u : V) (hu : u ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (huadj : G.Adj v₁ u) :
    ¬ VertexComplete G u Y := by
  intro huY
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hCY : ∀ v ∈ C, v ∉ Y := hw.2.1.2.2
  have hBerge : Berge G := hG.1.1.1.1.1
  obtain ⟨hx0C, hzC, hx1C, -⟩ := hole_triple hC ⟨k, hpre1⟩
  obtain ⟨hc1C, hc2C, hc3C, -⟩ := hole_triple hC ⟨k + d, hpre2⟩
  -- the shape of `T`
  subst hTeq
  have hnd : ([z, y, v₁, w] : List V).Nodup := hpath.1.2.1
  have hyint : y ∈ SPGT.interior ([z, y, v₁, w] : List V) := by simp [SPGT.interior]
  have hvint : v₁ ∈ SPGT.interior ([z, y, v₁, w] : List V) := by simp [SPGT.interior]
  have hyY : y ∉ Y := (hint y hyint).1
  have hyNC : ¬ VertexComplete G y Y := (hint y hyint).2
  have hvY : v₁ ∉ Y := (hint v₁ hvint).1
  have hvNC : ¬ VertexComplete G v₁ Y := (hint v₁ hvint).2
  have hzy : G.Adj z y := by simpa using path_adj_succ hpath.1 (i := 0) (by simp)
  have hyv : G.Adj y v₁ := by simpa using path_adj_succ hpath.1 (i := 1) (by simp)
  have hzv : ¬ G.Adj z v₁ := by
    have h := path_adj_iff hpath.1 (i := 0) (j := 2) (by simp) (by simp)
    simpa using h
  have hyv0 : y ≠ x₀ ∧ y ≠ x₁ := havoid y (by simp)
  have hv10 : v₁ ≠ x₀ ∧ v₁ ≠ x₁ := havoid v₁ (by simp)
  have hyC : y ∉ C := by
    intro h
    rcases hnb.2.2.2.2.2 y h hzy with h' | h'
    · exact hyv0.1 h'
    · exact hyv0.2 h'
  have hvz : v₁ ≠ z := by
    intro h
    subst h
    simp at hnd
  have hvC : v₁ ∉ C := by
    intro h
    exact h3 v₁ ⟨h, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hvz, hv10.1, hv10.2⟩⟩ hyv
  -- `u` lies on the rim, away from `z, x₀, x₁`
  have huC : u ∈ C := hu.1
  have huz : u ≠ z := fun h => hu.2 (by simp [h])
  have hu0 : u ≠ x₀ := fun h => hu.2 (by simp [h])
  have hu1 : u ≠ x₁ := fun h => hu.2 (by simp [h])
  -- claim (3), in the form the core lemma wants
  have hyanti : ∀ c ∈ C, c ≠ z → c ≠ x₀ → c ≠ x₁ → ¬ G.Adj y c := by
    intro c hcC hcz hc0 hc1
    exact h3 c ⟨hcC, by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hcz, hc0, hc1⟩⟩
  -- cyclic positions
  have p0 : C[(k + 0) % C.length]'(Nat.mod_lt _ hn) = x₀ :=
    (prefix_getElem hn hpre1 (i := 0) (j := k + 0) (by simp) rfl).symm
  have p1 : C[(k + 1) % C.length]'(Nat.mod_lt _ hn) = z :=
    (prefix_getElem hn hpre1 (i := 1) (j := k + 1) (by simp) rfl).symm
  have p2 : C[(k + 2) % C.length]'(Nat.mod_lt _ hn) = x₁ :=
    (prefix_getElem hn hpre1 (i := 2) (j := k + 2) (by simp) rfl).symm
  have pd : C[(k + d) % C.length]'(Nat.mod_lt _ hn) = c₁ :=
    (prefix_getElem hn hpre2 (i := 0) (j := k + d) (by simp) (by omega)).symm
  have pd1 : C[(k + (d + 1)) % C.length]'(Nat.mod_lt _ hn) = c₂ :=
    (prefix_getElem hn hpre2 (i := 1) (j := k + (d + 1)) (by simp) (by omega)).symm
  have pd2 : C[(k + (d + 2)) % C.length]'(Nat.mod_lt _ hn) = c₃ :=
    (prefix_getElem hn hpre2 (i := 2) (j := k + (d + 2)) (by simp) (by omega)).symm
  have hne : ∀ i j : ℕ, i ≤ C.length → j ≤ C.length →
      (if i = C.length then 0 else i) ≠ (if j = C.length then 0 else j) →
      C[(k + i) % C.length]'(Nat.mod_lt _ hn) ≠ C[(k + j) % C.length]'(Nat.mod_lt _ hn) := by
    intro i j hi hj hij
    refine pos_ne hC.2.1 hn k i j ?_
    rw [mod_le_self hn hi, mod_le_self hn hj]
    exact hij
  have hzc2 : z ≠ c₂ := by
    rw [← p1, ← pd1]; exact hne 1 (d + 1) (by omega) (by omega) (by split_ifs <;> omega)
  have hzc1 : z ≠ c₁ := by
    rw [← p1, ← pd]; exact hne 1 d (by omega) (by omega) (by split_ifs <;> omega)
  have hzc3 : z ≠ c₃ := by
    rw [← p1, ← pd2]; exact hne 1 (d + 2) (by omega) (by omega) (by split_ifs <;> omega)
  have h1c2 : x₁ ≠ c₂ := by
    rw [← p2, ← pd1]; exact hne 2 (d + 1) (by omega) (by omega) (by split_ifs <;> omega)
  have h0c2 : x₀ ≠ c₂ := by
    rw [← p0, ← pd1]; exact hne 0 (d + 1) (by omega) (by omega) (by split_ifs <;> omega)
  have h0c1 : x₀ ≠ c₁ := by
    rw [← p0, ← pd]; exact hne 0 d (by omega) (by omega) (by split_ifs <;> omega)
  have h1c3 : x₁ ≠ c₃ := by
    rw [← p2, ← pd2]; exact hne 2 (d + 2) (by omega) (by omega) (by split_ifs <;> omega)
  by_cases hx0c3 : x₀ = c₃
  · -- `x₀ = c₃`: run the argument on the reversed arc from `c₁` to `x₁`.
    have hmod : (k + 0) % C.length = (k + (d + 2)) % C.length :=
      hC.2.1.getElem_inj_iff.mp (p0.trans (hx0c3.trans pd2.symm))
    have h0 : 0 % C.length = (d + 2) % C.length := Nat.ModEq.add_left_cancel' k hmod
    have hde : d + 2 = C.length := by
      rw [Nat.zero_mod, mod_le_self hn (by omega)] at h0
      split_ifs at h0 <;> omega
    have hd3 : 3 ≤ d := by omega
    set A0 : List V := (C.rotate (k + 2)).take (d - 2 + 1) with hA0def
    have hA0len : A0.length = d - 2 + 1 := by
      simp only [hA0def, List.length_take, List.length_rotate]; omega
    have hA0sub : ∀ v ∈ A0, v ∈ C := fun v hv =>
      List.mem_rotate.mp (List.mem_of_mem_take hv)
    have hA0from : IsPathFrom G A0 x₁ c₁ := by
      have h := WheelParity.arc_isPathFrom (G := G) (C := C) hC
        (k := k + 2) (L := d - 2 + 1) (p := (k + 2) % C.length)
        (q := (k + d) % C.length) (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)
        (by omega) (by omega) rfl
        (by
          have he : k + 2 + (d - 2 + 1) - 1 = k + d := by omega
          rw [he])
      rw [p2, pd] at h
      exact h
    have hnotmem : ∀ m : ℕ, (∀ j, 2 ≤ j → j ≤ d → m % C.length ≠ j % C.length) →
        C[(k + m) % C.length]'(Nat.mod_lt _ hn) ∉ A0 := by
      intro m hm
      exact not_mem_arc (C := C) hC.2.1 hn k 2 d m (by omega) (by omega) hm
    have hzA : z ∉ A0 := by
      rw [← p1]
      exact hnotmem 1 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hx0A : x₀ ∉ A0 := by
      rw [← p0]
      exact hnotmem 0 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc3A : c₃ ∉ A0 := by
      rw [← pd2]
      exact hnotmem (d + 2) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc2A : c₂ ∉ A0 := by
      rw [← pd1]
      exact hnotmem (d + 1) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hempty : ∀ p ∈ A0, ∀ q ∈ A0, ¬ EdgeComplete G Y p q := by
      intro p hp q hq hE
      rcases hexh p q (hA0sub p hp) (hA0sub q hq) hE with h | h | h | h <;>
        rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hzA (h2 ▸ hq)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h2 ▸ hq)
      · exact hc2A (h2 ▸ hq)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h2 ▸ hq)
    have hA0even : Even (pathLength A0) :=
      arc_even hBerge hC hCY hw.2.1.2.1 A0 (k + 2) (List.take_prefix _ _) x₁ c₁ hA0from
        h1Y hc1Y z hzC hzY (fun he => hzA (he ▸ head_mem hA0from.2.1))
        (fun he => hzA (he ▸ getLast_mem hA0from.2.2)) hempty
    have hQ : IsPathFrom G A0.reverse c₁ x₁ := isPathFrom_reverse hA0from
    have hx1c1 : x₁ ≠ c₁ := by
      rw [← p2, ← pd]; exact hne 2 d (by omega) (by omega) (by split_ifs <;> omega)
    refine Thm232Claim4Core.orientation_absurd hG hbsp C Y hopt x₁ z x₀ c₃ c₂ c₁ y v₁ u
      A0.reverse hQ (fun v hv => hA0sub v (List.mem_reverse.mp hv)) ?_ ?_
      (fun h => hzA (List.mem_reverse.mp h)) (fun h => hx0A (List.mem_reverse.mp h))
      (fun h => hc3A (List.mem_reverse.mp h)) (fun h => hc2A (List.mem_reverse.mp h))
      hzC hc2C (isRimNeighbours_symm hnb) hnbc
      (fun h => hnb.1 (hx0c3.trans h.symm)) hx1c1 h1c2 hzc3 hzc1 hzc2
      (fun h => h0c1 h) h0c2 h1Y hzY hc2Y hc1Y ?_ hyC hvC hyY hvY hyNC hvNC hzy hyv hzv
      huC huz hu1 hu0 huY huadj ?_
    · rwa [pathLength_reverse]
    · rw [pathLength_reverse, PathBasics.pathLength_eq, hA0len]; omega
    · intro p q hpC hqC hE
      rcases hexh p q hpC hqC hE with h | h | h | h
      · exact Or.inr (Or.inl (h.trans (Set.pair_comm x₀ z)))
      · exact Or.inl (h.trans (Set.pair_comm z x₁))
      · exact Or.inr (Or.inr (Or.inr (h.trans (Set.pair_comm c₁ c₂))))
      · exact Or.inr (Or.inr (Or.inl (h.trans (Set.pair_comm c₂ c₃))))
    · intro c hcC hcz hc1' hc0'
      exact hyanti c hcC hcz hc0' hc1'
  · -- `x₀ ≠ c₃`: the printed orientation.
    have hlt : d + 2 < C.length := by
      rcases Nat.lt_or_ge (d + 2) C.length with h | h
      · exact h
      · exfalso
        have hde : d + 2 = C.length := by omega
        refine hx0c3 ?_
        rw [← p0, ← pd2]
        exact hC.2.1.getElem_inj_iff.mpr (by rw [hde]; simp)
    set A0 : List V := (C.rotate (k + (d + 2))).take (C.length - (d + 2) + 1) with hA0def
    have hA0len : A0.length = C.length - (d + 2) + 1 := by
      simp only [hA0def, List.length_take, List.length_rotate]; omega
    have hA0sub : ∀ v ∈ A0, v ∈ C := fun v hv =>
      List.mem_rotate.mp (List.mem_of_mem_take hv)
    have hA0from : IsPathFrom G A0 c₃ x₀ := by
      have h := WheelParity.arc_isPathFrom (G := G) (C := C) hC
        (k := k + (d + 2)) (L := C.length - (d + 2) + 1)
        (p := (k + (d + 2)) % C.length) (q := (k + 0) % C.length)
        (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) (by omega) (by omega) rfl
        (by
          have he : k + (d + 2) + (C.length - (d + 2) + 1) - 1 = k + C.length := by omega
          rw [he]
          simp)
      rw [pd2, p0] at h
      exact h
    have hnotmem : ∀ m : ℕ,
        (∀ j, d + 2 ≤ j → j ≤ C.length → m % C.length ≠ j % C.length) →
        C[(k + m) % C.length]'(Nat.mod_lt _ hn) ∉ A0 :=
      fun m hm => not_mem_arc (C := C) hC.2.1 hn k (d + 2) C.length m (by omega) (by omega) hm
    have hzA : z ∉ A0 := by
      rw [← p1]
      exact hnotmem 1 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hx1A : x₁ ∉ A0 := by
      rw [← p2]
      exact hnotmem 2 (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc1A : c₁ ∉ A0 := by
      rw [← pd]
      exact hnotmem d (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hc2A : c₂ ∉ A0 := by
      rw [← pd1]
      exact hnotmem (d + 1) (by
        intro j hj1 hj2
        rw [mod_le_self hn (by omega), mod_le_self hn (by omega)]
        split_ifs <;> omega)
    have hempty : ∀ p ∈ A0, ∀ q ∈ A0, ¬ EdgeComplete G Y p q := by
      intro p hp q hq hE
      rcases hexh p q (hA0sub p hp) (hA0sub q hq) hE with h | h | h | h <;>
        rcases Set.pair_eq_pair_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact hzA (h2 ▸ hq)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h1 ▸ hp)
      · exact hzA (h2 ▸ hq)
      · exact hc2A (h2 ▸ hq)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h1 ▸ hp)
      · exact hc2A (h2 ▸ hq)
    have hA0even : Even (pathLength A0) :=
      arc_even hBerge hC hCY hw.2.1.2.1 A0 (k + (d + 2)) (List.take_prefix _ _) c₃ x₀ hA0from
        hc3Y h0Y z hzC hzY (fun he => hzA (he ▸ head_mem hA0from.2.1))
        (fun he => hzA (he ▸ getLast_mem hA0from.2.2)) hempty
    exact Thm232Claim4Core.orientation_absurd hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ y v₁ u
      A0 hA0from hA0sub hA0even (by rw [PathBasics.pathLength_eq, hA0len]; omega)
      hzA hx1A hc1A hc2A hzC hc2C hnb (isRimNeighbours_symm hnbc) h0c1 hx0c3 h0c2 hzc1 hzc3 hzc2 h1c3 h1c2
      h0Y hzY hc2Y hc3Y hexh hyC hvC hyY hvY hyNC hvNC hzy hyv hzv
      huC huz hu0 hu1 huY huadj hyanti

end Workspace.ProofLemmas.Thm232Claim4Symmetry
