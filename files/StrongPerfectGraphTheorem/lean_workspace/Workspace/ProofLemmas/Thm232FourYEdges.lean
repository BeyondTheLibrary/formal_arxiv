import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions
import Workspace.Statements.S23.Thm_23_1
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.YEdgeFourConfig
import Workspace.ProofLemmas.RimSurgery

/-!
# 23.2 step (1) — *"Exactly 4 edges of `C` are `Y`-complete"*

PAPER (23.2, printed p. 139):

> *"**(1) Exactly 4 edges of `C` are `Y`-complete.**
>
> For by 23.1 there is a subpath `c₁-c₂-c₃` of `C` such that `c₁, c₂, c₃` are all
> `Y`-complete, and a path `c₁-p₁-⋯-p_k-c₃` such that none of `p₁, …, p_k` are in `V(C) ∪ Y`,
> none of them is `Y`-complete, and none of them has a neighbour in `V(C) \ {c₁,c₂,c₃}`.  Let
> `C'` be the hole formed by the union of the paths `C \ c₂`, `c₁-p₁-⋯-p_k-c₃`.  Then it has
> length `≥ 6`, and it contains fewer `Y`-complete edges than `C`.  From the choice of `(C,Y)`
> it follows that `(C',Y)` is not a wheel, and since `C` has at least 4 `Y`-complete edges,
> and `C'` has only two fewer, it follows that exactly 4 edges of `C` are `Y`-complete.  This
> proves (1)."*

The surgery producing `C'` is `Workspace.ProofLemmas.RimSurgery.exists_rim_surgery_of_wheel`;
this module supplies the counting argument that the printed proof leaves implicit, namely the
two bounds.

* **Upper bound.**  `(C',Y)` is not a wheel: were it one, the minimality clause in the choice
  of `(C,Y)` would give `e(C) ≤ e(C') = e(C) − 2`.  `C'` is a hole of length `≥ 6` disjoint
  from the (nonempty, anticonnected) `Y`, so the only clause of `IsWheel` that can fail is
  *"there are two disjoint `Y`-complete edges of `C'`"*.  Three `Y`-complete edges of a hole
  always contain two disjoint ones — three cyclic positions of a cycle of length `≥ 4` cannot
  be pairwise cyclically consecutive (`no_three_cyc_adj`) — so `e(C') ≤ 2`, whence
  `e(C) = e(C') + 2 ≤ 4`.
* **Lower bound.**  This is the printed *"`C` has at least 4 `Y`-complete edges"*.  The two
  rim edges `c₁c₂`, `c₂c₃` supplied by 23.1 meet in `c₂`, whereas the two `Y`-complete edges
  furnished by `IsWheel G C Y` are disjoint; so the two pairs of edges cannot coincide and
  `C` carries at least three `Y`-complete edges.  By 2.3 (through
  `WheelBasics.even_ncard_yEdges_of_wheel`) that number is even, hence `≥ 4`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232FourYEdges

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.WheelParity
open Workspace.ProofLemmas.OptimalWheelChoice

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Three positions of a cycle cannot be pairwise consecutive -/

/-- In the cyclic order on `{0, …, n−1}` with `n ≥ 4`, three distinct positions cannot be
pairwise cyclically consecutive. -/
private theorem no_three_cyc_adj {n a b c : ℕ} (hn : 4 ≤ n)
    (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (h1 : b = (a + 1) % n ∨ a = (b + 1) % n)
    (h2 : c = (a + 1) % n ∨ a = (c + 1) % n)
    (h3 : c = (b + 1) % n ∨ b = (c + 1) % n) : False := by
  have key : ∀ x : ℕ, x < n →
      ((x + 1) % n = x + 1 ∧ x + 1 < n) ∨ ((x + 1) % n = 0 ∧ x + 1 = n) := by
    intro x hx
    rcases Nat.lt_or_ge (x + 1) n with h | h
    · exact Or.inl ⟨Nat.mod_eq_of_lt h, h⟩
    · have he : x + 1 = n := by omega
      exact Or.inr ⟨by rw [he]; exact Nat.mod_self n, he⟩
  rcases key a ha with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;>
    rcases key b hb with ⟨e2, f2⟩ | ⟨e2, f2⟩ <;>
      rcases key c hc with ⟨e3, f3⟩ | ⟨e3, f3⟩ <;>
        simp only [e1, e2, e3] at h1 h2 h3 <;> omega

/-! ### Locating a `Y`-complete edge of the rim at a cyclic position -/

/-- Every `Y`-complete edge of a hole occurs at one of its cyclic positions. -/
theorem exists_pos_of_yEdge (hC : IsHoleList G C) {a b : V} (ha : a ∈ C) (hb : b ∈ C)
    (hE : EdgeComplete G Y a b) :
    ∃ m : ℕ, m < C.length ∧ CycEdge G Y C m ∧
      ((C[m % C.length]? = some a ∧ C[(m + 1) % C.length]? = some b) ∨
        (C[m % C.length]? = some b ∧ C[(m + 1) % C.length]? = some a)) := by
  have hn : 0 < C.length := by have := hC.1; omega
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  have hadj : G.Adj (C[i]'hi) (C[j]'hj) := by rw [hia, hjb]; exact hE.1
  rcases (HoleBasics.hole_adj_iff hC hi hj).mp hadj with h | h
  · refine ⟨i, hi, ?_, Or.inl ⟨?_, ?_⟩⟩
    · exact ⟨a, b, by rw [Nat.mod_eq_of_lt hi, List.getElem?_eq_getElem hi, hia],
        by rw [← h, List.getElem?_eq_getElem hj, hjb], hE⟩
    · rw [Nat.mod_eq_of_lt hi, List.getElem?_eq_getElem hi, hia]
    · rw [← h, List.getElem?_eq_getElem hj, hjb]
  · refine ⟨j, hj, ?_, Or.inr ⟨?_, ?_⟩⟩
    · exact ⟨b, a, by rw [Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj, hjb],
        by rw [← h, List.getElem?_eq_getElem hi, hia], edgeComplete_symm hE⟩
    · rw [Nat.mod_eq_of_lt hj, List.getElem?_eq_getElem hj, hjb]
    · rw [← h, List.getElem?_eq_getElem hi, hia]

/-- Reading a cyclic position off a `getElem?` equation. -/
private theorem pos_eq_of_getElem? {m : ℕ} {u : V} (hn : 0 < C.length)
    (h : C[m % C.length]? = some u) : (C[m % C.length]'(Nat.mod_lt _ hn)) = u := by
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at h
  exact Option.some_inj.mp h

/-! ### Three `Y`-complete edges give two disjoint ones -/

/-- A hole with at least three `Y`-complete edges carries two **disjoint** `Y`-complete
edges — the last clause of `IsWheel`. -/
theorem exists_disjoint_yEdges (hC : IsHoleList G C)
    (h3 : 3 ≤ yEdgeCount G Y C) :
    ∃ a b c d : V, a ∈ C ∧ b ∈ C ∧ c ∈ C ∧ d ∈ C ∧
      EdgeComplete G Y a b ∧ EdgeComplete G Y c d ∧
      a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  -- three distinct cyclic positions carrying a `Y`-complete edge
  rw [YEdgeFourConfig.yEdgeCount_eq_card hC, cycCount] at h3
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq h3
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hTcard
  have hmem : ∀ x ∈ ({p, q, r} : Finset ℕ), x < C.length ∧ CycEdge G Y C x := by
    intro x hx
    have := Finset.mem_filter.mp (hTsub hx)
    exact ⟨Finset.mem_range.mp this.1, this.2⟩
  obtain ⟨hp, hpe⟩ := hmem p (by simp)
  obtain ⟨hq, hqe⟩ := hmem q (by simp)
  obtain ⟨hr, hre⟩ := hmem r (by simp)
  -- two of them are not cyclically consecutive
  have hpair : ∃ i j : ℕ, i < C.length ∧ j < C.length ∧ i ≠ j ∧
      CycEdge G Y C i ∧ CycEdge G Y C j ∧
      ¬ (j = (i + 1) % C.length) ∧ ¬ (i = (j + 1) % C.length) := by
    by_cases h1 : (q = (p + 1) % C.length ∨ p = (q + 1) % C.length)
    · by_cases h2 : (r = (p + 1) % C.length ∨ p = (r + 1) % C.length)
      · by_cases h3' : (r = (q + 1) % C.length ∨ q = (r + 1) % C.length)
        · exact absurd (no_three_cyc_adj hn4 hp hq hr hpq hpr hqr h1 h2 h3') id
        · exact ⟨q, r, hq, hr, hqr, hqe, hre, fun h => h3' (Or.inl h),
            fun h => h3' (Or.inr h)⟩
      · exact ⟨p, r, hp, hr, hpr, hpe, hre, fun h => h2 (Or.inl h), fun h => h2 (Or.inr h)⟩
    · exact ⟨p, q, hp, hq, hpq, hpe, hqe, fun h => h1 (Or.inl h), fun h => h1 (Or.inr h)⟩
  obtain ⟨i, j, hi, hj, hij, hie, hje, hnadj1, hnadj2⟩ := hpair
  refine ⟨C[i % C.length]'(Nat.mod_lt _ hn), C[(i + 1) % C.length]'(Nat.mod_lt _ hn),
    C[j % C.length]'(Nat.mod_lt _ hn), C[(j + 1) % C.length]'(Nat.mod_lt _ hn),
    List.getElem_mem _, List.getElem_mem _, List.getElem_mem _, List.getElem_mem _,
    (cycEdge_iff_getElem hn i).mp hie, (cycEdge_iff_getElem hn j).mp hje, ?_, ?_, ?_, ?_⟩
  · exact HoleBasics.hole_ne_of_ne_index hC _ _ (by
      rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj]; exact hij)
  · exact HoleBasics.hole_ne_of_ne_index hC _ _ (by
      rw [Nat.mod_eq_of_lt hi]; exact hnadj2)
  · exact HoleBasics.hole_ne_of_ne_index hC _ _ (by
      rw [Nat.mod_eq_of_lt hj]; intro h; exact hnadj1 h.symm)
  · refine HoleBasics.hole_ne_of_ne_index hC _ _ ?_
    intro h
    have h2 : i % C.length = j % C.length := Nat.ModEq.add_right_cancel' 1 h
    rw [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2
    exact hij h2

/-- A hole of length `≥ 6`, disjoint from a nonempty anticonnected `Y` and carrying at least
three `Y`-complete edges, **is** the rim of a wheel with hub `Y`. -/
theorem isWheel_of_three_yEdges (hC : IsHoleList G C) (hlen : 6 ≤ holeLength C)
    (hYne : Y.Nonempty) (hYa : AnticonnectedSet G Y) (hCY : ∀ v ∈ C, v ∉ Y)
    (h3 : 3 ≤ yEdgeCount G Y C) : IsWheel G C Y :=
  ⟨⟨hC, hlen⟩, ⟨hYne, hYa, hCY⟩, exists_disjoint_yEdges hC h3⟩

/-! ### The lower bound: at least four -/

/-- The rim of a wheel that carries two `Y`-complete edges meeting in a common vertex carries
at least **three** `Y`-complete edges: the wheel's own two `Y`-complete edges are disjoint, so
the two pairs of edges cannot coincide. -/
theorem three_le_yEdgeCount (hC : IsHoleList G C) (hw : IsWheel G C Y)
    {c₁ c₂ c₃ : V} (h1C : c₁ ∈ C) (h2C : c₂ ∈ C) (h3C : c₃ ∈ C) (h13 : c₁ ≠ c₃)
    (hE1 : EdgeComplete G Y c₁ c₂) (hE2 : EdgeComplete G Y c₂ c₃) :
    3 ≤ yEdgeCount G Y C := by
  classical
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  obtain ⟨-, -, a, b, c, d, haC, hbC, hcC, hdC, hab, hcd, hac, had, hbc, hbd⟩ := hw
  obtain ⟨p₁, hp₁lt, hp₁e, hp₁v⟩ := exists_pos_of_yEdge hC h1C h2C hE1
  obtain ⟨p₂, hp₂lt, hp₂e, hp₂v⟩ := exists_pos_of_yEdge hC h2C h3C hE2
  obtain ⟨m₁, hm₁lt, hm₁e, hm₁v⟩ := exists_pos_of_yEdge hC haC hbC hab
  obtain ⟨m₂, hm₂lt, hm₂e, hm₂v⟩ := exists_pos_of_yEdge hC hcC hdC hcd
  -- the positions of the two rim edges through `c₂` are distinct
  have hp : p₁ ≠ p₂ := by
    rintro rfl
    rcases hp₁v with ⟨u1, v1⟩ | ⟨u1, v1⟩ <;> rcases hp₂v with ⟨u2, v2⟩ | ⟨u2, v2⟩
    · rw [u1] at u2; exact hE1.1.ne (Option.some_inj.mp u2)
    · rw [u1] at u2; exact h13 (Option.some_inj.mp u2)
    · rw [v1] at v2; exact h13 (Option.some_inj.mp v2)
    · rw [u1] at u2; exact hE2.1.ne (Option.some_inj.mp u2)
  -- the two disjoint edges of the wheel sit at distinct positions
  have hm : m₁ ≠ m₂ := by
    rintro rfl
    rcases hm₁v with ⟨u1, v1⟩ | ⟨u1, v1⟩ <;> rcases hm₂v with ⟨u2, v2⟩ | ⟨u2, v2⟩
    · rw [u1] at u2; exact hac (Option.some_inj.mp u2)
    · rw [u1] at u2; exact had (Option.some_inj.mp u2)
    · rw [u1] at u2; exact hbc (Option.some_inj.mp u2)
    · rw [u1] at u2; exact hbd (Option.some_inj.mp u2)
  -- one of `m₁, m₂` differs from both `p₁, p₂`
  have hkey : m₁ ∉ ({p₁, p₂} : Finset ℕ) ∨ m₂ ∉ ({p₁, p₂} : Finset ℕ) := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2⟩ := hcon
    simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2
    -- then `{m₁, m₂} = {p₁, p₂}`, so `c₂` lies on both of the two disjoint edges
    have hc₂ : ∀ m : ℕ, (m = p₁ ∨ m = p₂) →
        (C[m % C.length]? = some c₂ ∨ C[(m + 1) % C.length]? = some c₂) := by
      rintro m (rfl | rfl)
      · rcases hp₁v with ⟨-, h⟩ | ⟨h, -⟩
        · exact Or.inr h
        · exact Or.inl h
      · rcases hp₂v with ⟨h, -⟩ | ⟨-, h⟩
        · exact Or.inl h
        · exact Or.inr h
    have e₁ := hc₂ m₁ h1
    have e₂ := hc₂ m₂ h2
    -- `c₂ ∈ {a, b}` and `c₂ ∈ {c, d}`, contradicting disjointness
    have hmem₁ : c₂ = a ∨ c₂ = b := by
      rcases hm₁v with ⟨u1, v1⟩ | ⟨u1, v1⟩ <;> rcases e₁ with h | h
      · rw [u1] at h; exact Or.inl (Option.some_inj.mp h).symm
      · rw [v1] at h; exact Or.inr (Option.some_inj.mp h).symm
      · rw [u1] at h; exact Or.inr (Option.some_inj.mp h).symm
      · rw [v1] at h; exact Or.inl (Option.some_inj.mp h).symm
    have hmem₂ : c₂ = c ∨ c₂ = d := by
      rcases hm₂v with ⟨u1, v1⟩ | ⟨u1, v1⟩ <;> rcases e₂ with h | h
      · rw [u1] at h; exact Or.inl (Option.some_inj.mp h).symm
      · rw [v1] at h; exact Or.inr (Option.some_inj.mp h).symm
      · rw [u1] at h; exact Or.inr (Option.some_inj.mp h).symm
      · rw [v1] at h; exact Or.inl (Option.some_inj.mp h).symm
    rcases hmem₁ with rfl | rfl <;> rcases hmem₂ with h | h
    · exact hac h
    · exact had h
    · exact hbc h
    · exact hbd h
  -- three distinct positions carrying a `Y`-complete edge
  have hsub : ∃ S : Finset ℕ, S.card = 3 ∧
      S ⊆ (Finset.range C.length).filter (fun m => CycEdge G Y C m) := by
    rcases hkey with h | h
    · refine ⟨{p₁, p₂, m₁}, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        push_neg at h
        rw [Finset.card_insert_of_notMem (by simp [hp, Ne.symm h.1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm h.2]), Finset.card_singleton]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by assumption), by assumption⟩
    · refine ⟨{p₁, p₂, m₂}, ?_, ?_⟩
      · simp only [Finset.mem_insert, Finset.mem_singleton] at h
        push_neg at h
        rw [Finset.card_insert_of_notMem (by simp [hp, Ne.symm h.1]),
          Finset.card_insert_of_notMem (by simp [Ne.symm h.2]), Finset.card_singleton]
      · intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl | rfl <;>
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by assumption), by assumption⟩
  obtain ⟨S, hScard, hSsub⟩ := hsub
  rw [YEdgeFourConfig.yEdgeCount_eq_card hC, cycCount]
  calc (3 : ℕ) = S.card := hScard.symm
    _ ≤ _ := Finset.card_le_card hSsub

/-! ### Step (1) -/

/-- **PAPER (23.2, printed p. 139), step (1):** *"Exactly 4 edges of `C` are `Y`-complete."*

`hmin` is the second half of the opening sentence of the proof — *"choose an optimal wheel
`(C,Y)` such that `C` contains as few `Y`-complete edges as possible"* — in the form delivered
by `OptimalWheelChoice.exists_optimal_wheel`. -/
theorem exactly_four_yEdges (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (hmin : ∀ C' : List V, IsWheel G C' Y → yEdgeCount G Y C ≤ yEdgeCount G Y C') :
    yEdgeCount G Y C = 4 := by
  classical
  have hw : IsWheel G C Y := hopt.1
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hBerge : Berge G := hG.1.1.1.1.1
  -- "For by 23.1 there is a subpath `c₁-c₂-c₃` of `C` …"
  obtain ⟨c₁, c₂, c₃, P, hblock, h1Y, h2Y, h3Y, hP, hPne, hPCY, hPnc, hPno⟩ :=
    _root_.Workspace.Statements.S23.SPGT.thm_23_1 G hG hbsp C Y hopt
  obtain ⟨h1C, h2C, h3C, hnb⟩ := KiteTailBasics.hole_triple hC hblock
  -- "Let `C'` be the hole formed by the union of the paths `C \ c₂`, `c₁-p₁-⋯-p_k-c₃`."
  obtain ⟨C', hC'hole, hC'len, hC'Y, hC'mem, hcount, -⟩ :=
    RimSurgery.exists_rim_surgery_of_wheel hw c₁ c₂ c₃ P hblock h1Y h2Y h3Y hP hPCY hPnc hPno
  -- "From the choice of `(C,Y)` it follows that `(C',Y)` is not a wheel"
  have hub : yEdgeCount G Y C' ≤ 2 := by
    by_contra hcon
    have h3 : 3 ≤ yEdgeCount G Y C' := by omega
    have hwheel' : IsWheel G C' Y :=
      isWheel_of_three_yEdges hC'hole hC'len hw.2.1.1 hw.2.1.2.1 hC'Y h3
    have := hmin C' hwheel'
    omega
  -- "since `C` has at least 4 `Y`-complete edges"
  have hlow : 3 ≤ yEdgeCount G Y C := by
    refine three_le_yEdgeCount hC hw h1C h2C h3C hnb.1 ⟨hnb.2.2.2.1.symm, h1Y, h2Y⟩
      ⟨hnb.2.2.2.2.1, h2Y, h3Y⟩
  have heven : Even (yEdgeCount G Y C) := by
    rw [yEdgeCount]
    exact WheelBasics.even_ncard_yEdges_of_wheel hBerge hw
  rw [Nat.even_iff] at heven
  omega

end Workspace.ProofLemmas.Thm232FourYEdges
