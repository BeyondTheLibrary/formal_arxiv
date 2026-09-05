import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OddWheelParityFacts

/-!
# Claim (1) of 16.3 kills the first two bullets of 16.2

PAPER (16.3, printed p. 101): *"By 16.2 and (1), there is a 3-vertex path `p₁-p₂-p₃` in `C`, all
`Y`-complete, and a path `p₁-f₁-⋯-f_k-p₃` with interior in `F`, …"* — i.e. the **third** bullet of
16.2 holds.  The paper does not say how (1) excludes the other two; this module does it.

Throughout, `hclaim1` is claim (1) of the printed proof: *"there is no vertex
`v ∈ V(G) \ (V(C) ∪ Y)` such that `v` is not `Y`-complete and has nonadjacent neighbours in `C`
of opposite wheel-parity."*

* `not_isWheel_union` kills bullet 1 (*"there is a vertex `v ∈ F` such that `(C, Y ∪ {v})` is a
  wheel"*).  Such a wheel supplies two disjoint `Y ∪ {v}`-complete edges `ab`, `cd` of `C`; all
  four ends are neighbours of `v` and `Y`-complete, so `a,b` have opposite wheel-parity and so do
  `c,d`.  Exactly two of the four cross pairs are therefore of opposite parity, and they are
  either `{ac, bd}` or `{ad, bc}`; in each case the two cannot both be adjacent, since that would
  make `a,b,c,d` a four-cycle inside a hole of length `≥ 6`.

* `not_bullet_two` kills bullet 2.  There `v` has a fourth neighbour `u` on `C` besides
  `p₁, p₂, p₃`, and `u` has the same wheel-parity as `p₁` while `p₁p₂` is a `Y`-complete edge, so
  `u` and `p₂` have opposite parity; and `u` is not adjacent to `p₂`, whose only neighbours on the
  rim are `p₁` and `p₃`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.OddWheelBullets12

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Index bookkeeping on the rim -/

private theorem pos_ne (hC : IsHoleList G C) {x y : V} {ix iy : ℕ}
    (hix : ix < C.length) (hiy : iy < C.length)
    (hxv : (C[ix]'hix) = x) (hyv : (C[iy]'hiy) = y) (hxy : x ≠ y) : ix ≠ iy := by
  intro hcon
  subst hcon
  exact hxy (hxv.symm.trans hyv)

private theorem adj_idx (hC : IsHoleList G C) {x y : V} {ix iy : ℕ}
    (hix : ix < C.length) (hiy : iy < C.length)
    (hxv : (C[ix]'hix) = x) (hyv : (C[iy]'hiy) = y) (hadj : G.Adj x y) :
    iy = ix + 1 ∨ ix = iy + 1 ∨ (ix = 0 ∧ iy = C.length - 1) ∨ (iy = 0 ∧ ix = C.length - 1) :=
  WheelParity.hole_adj_index hC hix hiy (by rw [hxv, hyv]; exact hadj)

/-- A vertex of a hole has at most two neighbours on it. -/
theorem hole_no_three_nbrs (hC : IsHoleList G C) {x u₁ u₂ u₃ : V}
    (hx : x ∈ C) (h1 : u₁ ∈ C) (h2 : u₂ ∈ C) (h3 : u₃ ∈ C)
    (d12 : u₁ ≠ u₂) (d13 : u₁ ≠ u₃) (d23 : u₂ ≠ u₃)
    (a1 : G.Adj x u₁) (a2 : G.Adj x u₂) (a3 : G.Adj x u₃) : False := by
  have hn4 : 4 ≤ C.length := hC.1
  obtain ⟨ix, hix, hixv⟩ := List.getElem_of_mem hx
  obtain ⟨i1, hi1, hi1v⟩ := List.getElem_of_mem h1
  obtain ⟨i2, hi2, hi2v⟩ := List.getElem_of_mem h2
  obtain ⟨i3, hi3, hi3v⟩ := List.getElem_of_mem h3
  have n12 := pos_ne hC hi1 hi2 hi1v hi2v d12
  have n13 := pos_ne hC hi1 hi3 hi1v hi3v d13
  have n23 := pos_ne hC hi2 hi3 hi2v hi3v d23
  have e1 := adj_idx hC hix hi1 hixv hi1v a1
  have e2 := adj_idx hC hix hi2 hixv hi2v a2
  have e3 := adj_idx hC hix hi3 hixv hi3v a3
  omega

/-! ### Bullet 1 -/

/-- PAPER (16.3): claim (1) rules out the first alternative of 16.2. -/
theorem not_isWheel_union [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hBerge : Berge G) {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    (hclaim1 : ∀ z : V, z ∉ C → z ∉ Y → ¬ VertexComplete G z Y →
      ∀ x y : V, G.Adj z x → G.Adj z y → ¬ G.Adj x y → ¬ OppositeWheelParity G C Y x y)
    {v : V} (hvC : v ∉ C) (hvY : v ∉ Y) (hvnc : ¬ VertexComplete G v Y) :
    ¬ IsWheel G C (Y ∪ {v}) := by
  intro hW
  have hhole : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hhole heven
  obtain ⟨-, -, a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hac, had, hbc, hbd⟩ := hW
  have hYc : ∀ x : V, VertexComplete G x (Y ∪ {v}) → VertexComplete G x Y :=
    fun x hx y hy => hx y (Set.mem_union_left _ hy)
  have hadjv : ∀ x : V, VertexComplete G x (Y ∪ {v}) → G.Adj v x :=
    fun x hx => (hx v (Set.mem_union_right _ rfl)).symm
  have haE : EdgeComplete G Y a b := ⟨hab.1, hYc a hab.2.1, hYc b hab.2.2⟩
  have hcE : EdgeComplete G Y c d := ⟨hcd.1, hYc c hcd.2.1, hYc d hcd.2.2⟩
  have hva : G.Adj v a := hadjv a hab.2.1
  have hvb : G.Adj v b := hadjv b hab.2.2
  have hvc : G.Adj v c := hadjv c hcd.2.1
  have hvd : G.Adj v d := hadjv d hcd.2.2
  have habne : a ≠ b := hab.1.ne
  have hcdne : c ≠ d := hcd.1.ne
  have hpab : π a ≠ π b := fun h =>
    OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hhole heven haC hbC haE
      ((hπ a b haC hbC habne).mpr h)
  have hpcd : π c ≠ π d := fun h =>
    OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hhole heven hcC hdC hcE
      ((hπ c d hcC hdC hcdne).mpr h)
  have p2a := hπ2 a
  have p2b := hπ2 b
  have p2c := hπ2 c
  have p2d := hπ2 d
  -- positions
  obtain ⟨ia, hia, hiav⟩ := List.getElem_of_mem haC
  obtain ⟨ib, hib, hibv⟩ := List.getElem_of_mem hbC
  obtain ⟨ic, hic, hicv⟩ := List.getElem_of_mem hcC
  obtain ⟨idd, hidd, hiddv⟩ := List.getElem_of_mem hdC
  have nab := pos_ne hhole hia hib hiav hibv habne
  have ncd := pos_ne hhole hic hidd hicv hiddv hcdne
  have nac := pos_ne hhole hia hic hiav hicv hac
  have nad := pos_ne hhole hia hidd hiav hiddv had
  have nbc := pos_ne hhole hib hic hibv hicv hbc
  have nbd := pos_ne hhole hib hidd hibv hiddv hbd
  have eab := adj_idx hhole hia hib hiav hibv hab.1
  have ecd := adj_idx hhole hic hidd hicv hiddv hcd.1
  -- a four-cycle inside a hole of length `≥ 6` is impossible
  have hACBD : ¬ (G.Adj a c ∧ G.Adj b d) := by
    rintro ⟨h1, h2⟩
    have e1 := adj_idx hhole hia hic hiav hicv h1
    have e2 := adj_idx hhole hib hidd hibv hiddv h2
    omega
  have hADBC : ¬ (G.Adj a d ∧ G.Adj b c) := by
    rintro ⟨h1, h2⟩
    have e1 := adj_idx hhole hia hidd hiav hiddv h1
    have e2 := adj_idx hhole hib hic hibv hicv h2
    omega
  by_cases hp : π a = π c
  · by_cases h1 : G.Adj a d
    · exact hclaim1 v hvC hvY hvnc b c hvb hvc (fun hx => hADBC ⟨h1, hx⟩)
        ⟨hbc, hbC, hcC, fun hs => by
          have := (hπ b c hbC hcC hbc).mp hs
          omega⟩
    · exact hclaim1 v hvC hvY hvnc a d hva hvd h1
        ⟨had, haC, hdC, fun hs => by
          have := (hπ a d haC hdC had).mp hs
          omega⟩
  · by_cases h1 : G.Adj a c
    · exact hclaim1 v hvC hvY hvnc b d hvb hvd (fun hx => hACBD ⟨h1, hx⟩)
        ⟨hbd, hbC, hdC, fun hs => by
          have := (hπ b d hbC hdC hbd).mp hs
          omega⟩
    · exact hclaim1 v hvC hvY hvnc a c hva hvc h1
        ⟨hac, haC, hcC, fun hs => by
          have := (hπ a c haC hcC hac).mp hs
          omega⟩

/-! ### Bullet 2 -/

/-- PAPER (16.3): claim (1) rules out the second alternative of 16.2. -/
theorem not_bullet_two [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hBerge : Berge G) {C : List V} {Y : Set V} (hw : IsWheel G C Y)
    (hclaim1 : ∀ z : V, z ∉ C → z ∉ Y → ¬ VertexComplete G z Y →
      ∀ x y : V, G.Adj z x → G.Adj z y → ¬ G.Adj x y → ¬ OppositeWheelParity G C Y x y)
    {v : V} (hvC : v ∉ C) (hvY : v ∉ Y) (hvnc : ¬ VertexComplete G v Y)
    (hdeg : 4 ≤ (G.neighborSet v ∩ {u : V | u ∈ C}).ncard)
    {p₁ p₂ p₃ : V} (hpath : IsPathList G [p₁, p₂, p₃])
    (hblock : ∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k)
    (hw1 : VertexComplete G p₁ (Y ∪ {v})) (hw2 : VertexComplete G p₂ (Y ∪ {v}))
    (hw3 : VertexComplete G p₃ (Y ∪ {v}))
    (hother : ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) :
    False := by
  classical
  have hhole : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hhole heven
  -- the three vertices lie on `C`
  have hmemC : ∀ z : V, z ∈ ([p₁, p₂, p₃] : List V) → z ∈ C := by
    obtain ⟨k, hk⟩ := hblock
    rcases hk with h | h
    · intro z hz
      exact List.mem_rotate.mp (h.subset hz)
    · intro z hz
      refine List.mem_rotate.mp (h.subset ?_)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
      tauto
  have hp1C : p₁ ∈ C := hmemC p₁ (by simp)
  have hp2C : p₂ ∈ C := hmemC p₂ (by simp)
  have hp3C : p₃ ∈ C := hmemC p₃ (by simp)
  have hnd : ([p₁, p₂, p₃] : List V).Nodup := hpath.2.1
  have d12 : p₁ ≠ p₂ := by rintro rfl; simp at hnd
  have d13 : p₁ ≠ p₃ := by rintro rfl; simp at hnd
  have d23 : p₂ ≠ p₃ := by rintro rfl; simp at hnd
  have a12 : G.Adj p₁ p₂ := by
    have h := PathBasics.path_adj_succ hpath (i := 0) (by simp)
    simpa using h
  have a23 : G.Adj p₂ p₃ := by
    have h := PathBasics.path_adj_succ hpath (i := 1) (by simp)
    simpa using h
  have hYc : ∀ x : V, VertexComplete G x (Y ∪ {v}) → VertexComplete G x Y :=
    fun x hx y hy => hx y (Set.mem_union_left _ hy)
  have hadjv : ∀ x : V, VertexComplete G x (Y ∪ {v}) → G.Adj v x :=
    fun x hx => (hx v (Set.mem_union_right _ rfl)).symm
  have hE12 : EdgeComplete G Y p₁ p₂ := ⟨a12, hYc p₁ hw1, hYc p₂ hw2⟩
  have hp12 : π p₁ ≠ π p₂ := fun h =>
    OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hhole heven hp1C hp2C hE12
      ((hπ p₁ p₂ hp1C hp2C d12).mpr h)
  -- a fourth neighbour of `v` on `C`
  obtain ⟨u, huN, hu1, hu2, hu3⟩ : ∃ u : V, u ∈ (G.neighborSet v ∩ {u : V | u ∈ C}) ∧
      u ≠ p₁ ∧ u ≠ p₂ ∧ u ≠ p₃ := by
    by_contra hcon
    push Not at hcon
    have hsub : (G.neighborSet v ∩ {u : V | u ∈ C}) ⊆ ({p₁, p₂, p₃} : Set V) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases h1 : z = p₁
      · exact Or.inl h1
      · by_cases h2 : z = p₂
        · exact Or.inr (Or.inl h2)
        · exact Or.inr (Or.inr (hcon z hz h1 h2))
    have h3 : ({p₁, p₂, p₃} : Set V).ncard ≤ 3 := by
      refine le_trans (Set.ncard_insert_le _ _) ?_
      have h := Set.ncard_insert_le p₂ ({p₃} : Set V)
      rw [Set.ncard_singleton] at h
      omega
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hvu : G.Adj v u := huN.1
  have huC : u ∈ C := huN.2
  -- `u` has the wheel-parity of `p₁`, hence the opposite of `p₂`
  have hsame := hother u huC hvu hu1 hu2 hu3
  have hpu : π u = π p₁ := (hπ u p₁ huC hp1C hu1).mp hsame
  -- and `u` is not adjacent to `p₂`, whose rim neighbours are `p₁` and `p₃`
  have hnadj : ¬ G.Adj u p₂ := by
    intro hcon
    exact hole_no_three_nbrs hhole hp2C hp1C hp3C huC d13 (Ne.symm hu1) (Ne.symm hu3)
      a12.symm a23 hcon.symm
  exact hclaim1 v hvC hvY hvnc u p₂ hvu (hadjv p₂ hw2) hnadj
    ⟨hu2, huC, hp2C, fun hs => by
      have := (hπ u p₂ huC hp2C hu2).mp hs
      omega⟩

end Workspace.ProofLemmas.OddWheelBullets12
