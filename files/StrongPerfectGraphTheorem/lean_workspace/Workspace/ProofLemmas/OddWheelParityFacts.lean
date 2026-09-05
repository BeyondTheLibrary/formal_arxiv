import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration

/-!
# Wheel-parity facts used by the main argument of 16.3

Three things the printed proof of 16.3 (p. 101) uses without comment once claim (1) is available.

* `exists_parity` — wheel-parity really is a **two-valued function** on the rim.  §16 composes
  "same"/"opposite" freely (*"every other neighbour of `v` has the same wheel-parity as `p₁`"*
  next to *"`p₁, p₂` have opposite wheel-parity"*), which is only legitimate once one knows this.
  With `π` in hand every such composition is an `omega`.

* `sameWheelParity_of_adj_of_not_complete` — *"Since `p, q` have opposite wheel-parity and are not
  `Y`-complete, they are not adjacent."*  Contrapositive: two adjacent rim vertices, at least one
  of them not `Y`-complete, have the **same** wheel-parity (the edge between them is not
  `Y`-complete, so the running count does not change across it).

* `exists_two_nonComplete_opposite` — *"Since `(C,Y)` is an odd wheel, `C` has at least two
  segments, and therefore there are vertices `u, v` in `C` with different wheel-parity and
  neither of them `Y`-complete."*  The two vertices produced here are the ones flanking the odd
  segment: an odd segment has an even number `L` of vertices, so the running count changes by
  `L - 1`, an odd number, between its two flanking positions.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelParityFacts

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

attribute [local instance] Classical.propDecidable

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V}

/-! ### Reading positions off the list -/

theorem cycVert_iff' (hn : 0 < C.length) {i : ℕ} (hi : i < C.length) :
    SegmentBasics.CycVert G Y C i ↔ VertexComplete G (C[i]'hi) Y := by
  constructor
  · rintro ⟨u, hu, huY⟩
    rw [Nat.mod_eq_of_lt hi, List.getElem?_eq_getElem hi] at hu
    rw [Option.some_injective _ hu]
    exact huY
  · intro h
    refine ⟨C[i]'hi, ?_, h⟩
    rw [Nat.mod_eq_of_lt hi]
    exact List.getElem?_eq_getElem hi

/-- Every residue is hit by the window `k, …, k + n - 1`. -/
theorem exists_offset (hn : 0 < C.length) (k m : ℕ) :
    ∃ t < C.length, (k + t) % C.length = m % C.length := by
  refine ⟨(m + C.length - k % C.length) % C.length, Nat.mod_lt _ hn, ?_⟩
  have hkm : k % C.length < C.length := Nat.mod_lt _ hn
  have s1 : (k + (m + C.length - k % C.length) % C.length) % C.length
      = (k % C.length + (m + C.length - k % C.length) % C.length) % C.length :=
    (Nat.mod_add_mod k C.length _).symm
  have s2 : (k % C.length + (m + C.length - k % C.length) % C.length) % C.length
      = (k % C.length + (m + C.length - k % C.length)) % C.length := Nat.add_mod_mod _ _ _
  have s3 : k % C.length + (m + C.length - k % C.length) = m + C.length := by omega
  rw [s1, s2, s3, Nat.add_mod_right]

/-! ### Counting `Y`-complete edges along a run -/

/-- A run of `L` consecutive `Y`-complete positions, ending because position `k+L` is not
`Y`-complete, carries exactly `L - 1` of the `Y`-complete cyclic edges. -/
theorem cycCount_run (hC : IsHoleList G C) {k L : ℕ}
    (hall : ∀ t < L, SegmentBasics.CycVert G Y C (k + t))
    (hnext : ¬ SegmentBasics.CycVert G Y C (k + L)) :
    WheelParity.cycCount G Y C (k + L) = WheelParity.cycCount G Y C k + (L - 1) := by
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  obtain ⟨M, rfl⟩ : ∃ M, L = M + 1 := ⟨L - 1, by omega⟩
  have hsum : ∑ t ∈ Finset.range (M + 1),
      (if WheelParity.CycEdge G Y C (k + t) then 1 else 0) = M := by
    rw [Finset.sum_range_succ]
    have h1 : ∀ t ∈ Finset.range M,
        (if WheelParity.CycEdge G Y C (k + t) then 1 else 0) = 1 := by
      intro t ht
      rw [Finset.mem_range] at ht
      exact if_pos (YEdgeConfiguration.cycEdge_of_run (L := M + 1) hC hall (by omega))
    have h2 : ¬ WheelParity.CycEdge G Y C (k + M) := by
      intro hce
      refine hnext ?_
      have hv := YEdgeConfiguration.cycVert_succ_of_cycEdge hC hce
      rwa [show k + M + 1 = k + (M + 1) by omega] at hv
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      if_neg h2]
    omega
  rw [WheelParity.cycCount_add, hsum]
  omega

/-- If every cyclic edge is `Y`-complete then the total count is the length of the cycle. -/
theorem cycCount_full (hall : ∀ m : ℕ, WheelParity.CycEdge G Y C m) :
    WheelParity.cycCount G Y C C.length = C.length := by
  rw [WheelParity.cycCount_eq_sum, Finset.sum_congr rfl (fun t _ => if_pos (hall t))]
  simp

/-! ### The parity function -/

/-- **Wheel-parity is a two-valued function of the rim vertex.** -/
theorem exists_parity (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length)) :
    ∃ π : V → ℕ, ∀ x y : V, x ∈ C → y ∈ C → x ≠ y →
      (SameWheelParity G C Y x y ↔ π x = π y) := by
  classical
  obtain ⟨idx, hkey⟩ : ∃ idx : V → ℕ, ∀ x ∈ C, ∃ hi : idx x < C.length, (C[idx x]'hi) = x := by
    refine ⟨fun x => if h : ∃ i : ℕ, ∃ hi : i < C.length, (C[i]'hi) = x then h.choose else 0, ?_⟩
    intro x hx
    have h : ∃ i : ℕ, ∃ hi : i < C.length, (C[i]'hi) = x := by
      obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
      exact ⟨i, hi, hix⟩
    simp only [dif_pos h]
    exact h.choose_spec
  refine ⟨fun x => WheelParity.cycCount G Y C (idx x) % 2, ?_⟩
  intro x y hx hy hxy
  obtain ⟨hix, hixv⟩ := hkey x hx
  obtain ⟨hiy, hiyv⟩ := hkey y hy
  have hne : idx x ≠ idx y := by
    intro h
    refine hxy ?_
    rw [← hixv, ← hiyv]
    simp only [h]
  have hiff := WheelParity.sameWheelParity_iff hC heven hix hiy hne
  rw [hixv, hiyv] at hiff
  exact hiff

/-- `exists_parity` with the extra information that `π` is genuinely two-valued, which is what
lets every §16 parity composition be discharged by `omega`. -/
theorem exists_parity' (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length)) :
    ∃ π : V → ℕ, (∀ x : V, π x < 2) ∧ ∀ x y : V, x ∈ C → y ∈ C → x ≠ y →
      (SameWheelParity G C Y x y ↔ π x = π y) := by
  classical
  obtain ⟨idx, hkey⟩ : ∃ idx : V → ℕ, ∀ x ∈ C, ∃ hi : idx x < C.length, (C[idx x]'hi) = x := by
    refine ⟨fun x => if h : ∃ i : ℕ, ∃ hi : i < C.length, (C[i]'hi) = x then h.choose else 0, ?_⟩
    intro x hx
    have h : ∃ i : ℕ, ∃ hi : i < C.length, (C[i]'hi) = x := by
      obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
      exact ⟨i, hi, hix⟩
    simp only [dif_pos h]
    exact h.choose_spec
  refine ⟨fun x => WheelParity.cycCount G Y C (idx x) % 2, fun x => Nat.mod_lt _ (by norm_num), ?_⟩
  intro x y hx hy hxy
  obtain ⟨hix, hixv⟩ := hkey x hx
  obtain ⟨hiy, hiyv⟩ := hkey y hy
  have hne : idx x ≠ idx y := by
    intro h
    refine hxy ?_
    rw [← hixv, ← hiyv]
    simp only [h]
  have hiff := WheelParity.sameWheelParity_iff hC heven hix hiy hne
  rw [hixv, hiyv] at hiff
  exact hiff

/-! ### Adjacent rim vertices, one of them not `Y`-complete -/

/-- PAPER (16.3): the contrapositive of *"since `p, q` have opposite wheel-parity and are not
`Y`-complete, they are not adjacent"*. -/
theorem sameWheelParity_of_adj_of_not_complete (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length)) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) (hadj : G.Adj x y) (hnc : ¬ VertexComplete G x Y) :
    SameWheelParity G C Y x y := by
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  have hadjidx : G.Adj (C[i]'hi) (C[j]'hj) := by rw [hix, hjy]; exact hadj
  have hncI : ¬ SegmentBasics.CycVert G Y C i := by
    rw [cycVert_iff' hn hi, hix]; exact hnc
  have hij : i ≠ j := by rintro rfl; exact G.irrefl hadjidx
  have hstep : ∀ m : ℕ, ¬ WheelParity.CycEdge G Y C m →
      WheelParity.cycCount G Y C (m + 1) % 2 = WheelParity.cycCount G Y C m % 2 := by
    intro m hce
    rw [WheelParity.cycCount_succ, if_neg hce]
    simp
  have hwrap : ¬ WheelParity.CycEdge G Y C (C.length - 1) →
      WheelParity.cycCount G Y C (C.length - 1) % 2 = WheelParity.cycCount G Y C 0 % 2 := by
    intro hce
    have h1 : WheelParity.cycCount G Y C ((C.length - 1) + 1)
        = WheelParity.cycCount G Y C (C.length - 1) + 0 := by
      rw [WheelParity.cycCount_succ, if_neg hce]
    rw [show (C.length - 1) + 1 = C.length by omega] at h1
    obtain ⟨f, hf⟩ := heven
    rw [WheelParity.cycCount_zero]
    omega
  have hpar : WheelParity.cycCount G Y C i % 2 = WheelParity.cycCount G Y C j % 2 := by
    rcases WheelParity.hole_adj_index hC hi hj hadjidx with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h
      exact (hstep i (fun hce => hncI (YEdgeConfiguration.cycVert_of_cycEdge hC hce))).symm
    · subst h
      exact hstep j (fun hce => hncI (YEdgeConfiguration.cycVert_succ_of_cycEdge hC hce))
    · subst h1; subst h2
      refine (hwrap (fun hce => hncI ?_)).symm
      refine (SegmentBasics.cycVert_congr ?_).mp
        (YEdgeConfiguration.cycVert_succ_of_cycEdge hC hce)
      rw [show C.length - 1 + 1 = C.length by omega, Nat.mod_self, Nat.zero_mod]
    · subst h1; subst h2
      exact hwrap (fun hce => hncI (YEdgeConfiguration.cycVert_of_cycEdge hC hce))
  have hsame : SameWheelParity G C Y (C[i]'hi) (C[j]'hj) :=
    (WheelParity.sameWheelParity_iff hC heven hi hj hij).mpr hpar
  rw [hix, hjy] at hsame
  exact hsame

/-- Dually: the two ends of a `Y`-complete edge of the rim have **opposite** wheel-parity. -/
theorem not_sameWheelParity_of_edgeComplete (hC : IsHoleList G C)
    (heven : Even (WheelParity.cycCount G Y C C.length)) {x y : V}
    (hx : x ∈ C) (hy : y ∈ C) (hE : EdgeComplete G Y x y) :
    ¬ SameWheelParity G C Y x y := by
  have hn4 : 4 ≤ C.length := hC.1
  have hn : 0 < C.length := by omega
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  have hadjidx : G.Adj (C[i]'hi) (C[j]'hj) := by rw [hix, hjy]; exact hE.1
  have hij : i ≠ j := by rintro rfl; exact G.irrefl hadjidx
  have hcvi : SegmentBasics.CycVert G Y C i := by rw [cycVert_iff' hn hi, hix]; exact hE.2.1
  have hcvj : SegmentBasics.CycVert G Y C j := by rw [cycVert_iff' hn hj, hjy]; exact hE.2.2
  have hstep : ∀ m : ℕ, WheelParity.CycEdge G Y C m →
      WheelParity.cycCount G Y C (m + 1) % 2 ≠ WheelParity.cycCount G Y C m % 2 := by
    intro m hce
    rw [WheelParity.cycCount_succ, if_pos hce]
    omega
  have hwrap : WheelParity.CycEdge G Y C (C.length - 1) →
      WheelParity.cycCount G Y C (C.length - 1) % 2 ≠ WheelParity.cycCount G Y C 0 % 2 := by
    intro hce
    have h1 : WheelParity.cycCount G Y C ((C.length - 1) + 1)
        = WheelParity.cycCount G Y C (C.length - 1) + 1 := by
      rw [WheelParity.cycCount_succ, if_pos hce]
    rw [show (C.length - 1) + 1 = C.length by omega] at h1
    obtain ⟨f, hf⟩ := heven
    rw [WheelParity.cycCount_zero]
    omega
  have hzero : SegmentBasics.CycVert G Y C 0 → SegmentBasics.CycVert G Y C C.length := by
    intro h
    exact (SegmentBasics.cycVert_congr (by rw [Nat.mod_self, Nat.zero_mod])).mp h
  have hpar : WheelParity.cycCount G Y C i % 2 ≠ WheelParity.cycCount G Y C j % 2 := by
    rcases WheelParity.hole_adj_index hC hi hj hadjidx with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h
      exact fun hq => hstep i ((YEdgeConfiguration.cycEdge_iff hC).mpr ⟨hcvi, hcvj⟩) hq.symm
    · subst h
      exact hstep j ((YEdgeConfiguration.cycEdge_iff hC).mpr ⟨hcvj, hcvi⟩)
    · subst h1; subst h2
      refine fun hq => hwrap ((YEdgeConfiguration.cycEdge_iff hC).mpr ⟨hcvj, ?_⟩) hq.symm
      rw [show C.length - 1 + 1 = C.length by omega]
      exact hzero hcvi
    · subst h1; subst h2
      refine hwrap ((YEdgeConfiguration.cycEdge_iff hC).mpr ⟨hcvi, ?_⟩)
      rw [show C.length - 1 + 1 = C.length by omega]
      exact hzero hcvj
  intro hsame
  rw [← hix, ← hjy] at hsame
  exact hpar ((WheelParity.sameWheelParity_iff hC heven hi hj hij).mp hsame)

/-! ### The two flanking vertices of an odd segment -/

/-- The first half of the decoder of `SegmentBasics.isSegment_run`, needing no length
hypothesis: a segment occupies consecutive `Y`-complete positions. -/
theorem isSegment_arc (hC : IsHoleList G C) {S : List V} (hS : IsSegment G C Y S) :
    ∃ k : ℕ, 1 ≤ S.length ∧ S.length + 1 ≤ C.length ∧
      (∀ t < S.length, SegmentBasics.CycVert G Y C (k + t)) := by
  have hn : 0 < C.length := by have := hC.1; omega
  obtain ⟨⟨hpath, ⟨k, hk⟩, hSY⟩, -⟩ := hS
  have hpos : 1 ≤ S.length := PathBasics.path_length_pos hpath
  obtain ⟨S', hS'pre, hS'mem, hS'len, hS'path⟩ : ∃ S' : List V, S' <+: C.rotate k ∧
      (∀ x, x ∈ S' ↔ x ∈ S) ∧ S'.length = S.length ∧ IsPathList G S' := by
    rcases hk with h | h
    · exact ⟨S, h, fun _ => Iff.rfl, rfl, hpath⟩
    · exact ⟨S.reverse, h, fun x => List.mem_reverse, by simp,
        PathBasics.isPathList_reverse hpath⟩
  refine ⟨k, hpos, ?_, ?_⟩
  · have := SegmentBasics.length_le_of_path_prefix hC hS'path hS'pre
    omega
  · intro t ht
    have ht' : t < S'.length := by omega
    exact ⟨S'[t]'ht', SegmentBasics.prefix_pos hn hS'pre ht',
      (hSY _ ((hS'mem _).mp (List.getElem_mem ht'))).2⟩

/-- PAPER (16.3, printed p. 101): *"Since `(C,Y)` is an odd wheel, `C` has at least two segments,
and therefore there are vertices `u, v` in `C` with different wheel-parity and neither of them
`Y`-complete."* -/
theorem exists_two_nonComplete_opposite [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hBerge : Berge G) {C : List V} {Y : Set V} (hw : IsWheel G C Y) (hodd : IsOddWheel G C Y) :
    ∃ u w : V, u ∈ C ∧ w ∈ C ∧ ¬ VertexComplete G u Y ∧ ¬ VertexComplete G w Y ∧
      OppositeWheelParity G C Y u w := by
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  have hhole : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  obtain ⟨-, S, hS, hSodd⟩ := hodd
  obtain ⟨k, hL1, hLn, hall⟩ := isSegment_arc hhole hS
  have hLeven : Even S.length :=
    (SegmentBasics.odd_pathLength_iff_even_length hL1).mp hSodd
  have hLn2 : S.length + 2 ≤ C.length := by
    by_contra hcon
    have hLeq : C.length = S.length + 1 := by omega
    by_cases hfull : SegmentBasics.CycVert G Y C (k + S.length)
    · have hallpos : ∀ m : ℕ, SegmentBasics.CycVert G Y C m := by
        intro m
        obtain ⟨t, ht, hteq⟩ := exists_offset hn k m
        refine (SegmentBasics.cycVert_congr hteq).mp ?_
        rcases Nat.lt_or_ge t S.length with h | h
        · exact hall t h
        · have htt : t = S.length := by omega
          rw [htt]; exact hfull
      have hcc : WheelParity.cycCount G Y C C.length = C.length :=
        cycCount_full (fun m =>
          (YEdgeConfiguration.cycEdge_iff hhole).mpr ⟨hallpos m, hallpos (m + 1)⟩)
      rw [hcc] at heven
      obtain ⟨e, he⟩ := hLeven
      obtain ⟨f, hf⟩ := heven
      omega
    · have hcc := cycCount_run hhole hall hfull
      have hcc2 : WheelParity.cycCount G Y C (k + C.length)
          = WheelParity.cycCount G Y C (k + S.length) + 0 := by
        rw [show k + C.length = (k + S.length) + 1 by omega, WheelParity.cycCount_succ,
          if_neg (YEdgeConfiguration.not_cycEdge_at_run_end hhole hfull)]
      rw [WheelParity.cycCount_add_length] at hcc2
      obtain ⟨e, he⟩ := hLeven
      obtain ⟨f, hf⟩ := heven
      omega
  obtain ⟨k', -, hall', hnext', hprev', -⟩ := SegmentBasics.isSegment_run hhole hS hLn2
  have hccL := cycCount_run hhole hall' hnext'
  have hccP : WheelParity.cycCount G Y C (k' + (C.length - 1))
      = WheelParity.cycCount G Y C k' + WheelParity.cycCount G Y C C.length := by
    have h1 : WheelParity.cycCount G Y C ((k' + (C.length - 1)) + 1)
        = WheelParity.cycCount G Y C (k' + (C.length - 1)) + 0 := by
      rw [WheelParity.cycCount_succ,
        if_neg (YEdgeConfiguration.not_cycEdge_at_run_end hhole hprev')]
    rw [show (k' + (C.length - 1)) + 1 = k' + C.length by omega,
      WheelParity.cycCount_add_length] at h1
    omega
  have hiL : (k' + S.length) % C.length < C.length := Nat.mod_lt _ hn
  have hjP : (k' + (C.length - 1)) % C.length < C.length := Nat.mod_lt _ hn
  have hpari : WheelParity.cycCount G Y C ((k' + S.length) % C.length) % 2
      = WheelParity.cycCount G Y C (k' + S.length) % 2 :=
    (WheelParity.cycCount_mod_two heven _).symm
  have hparj : WheelParity.cycCount G Y C ((k' + (C.length - 1)) % C.length) % 2
      = WheelParity.cycCount G Y C (k' + (C.length - 1)) % 2 :=
    (WheelParity.cycCount_mod_two heven _).symm
  have hdiff : WheelParity.cycCount G Y C ((k' + S.length) % C.length) % 2
      ≠ WheelParity.cycCount G Y C ((k' + (C.length - 1)) % C.length) % 2 := by
    obtain ⟨e, he⟩ := hLeven
    obtain ⟨f, hf⟩ := heven
    omega
  have hijne : (k' + S.length) % C.length ≠ (k' + (C.length - 1)) % C.length := by
    intro h; rw [h] at hdiff; exact hdiff rfl
  refine ⟨C[(k' + S.length) % C.length]'hiL, C[(k' + (C.length - 1)) % C.length]'hjP,
    List.getElem_mem _, List.getElem_mem _, ?_, ?_,
    HoleBasics.hole_ne_of_ne_index hhole _ _ hijne, List.getElem_mem _, List.getElem_mem _, ?_⟩
  · rw [← cycVert_iff' hn hiL]
    intro hcv
    exact hnext' ((SegmentBasics.cycVert_congr (by simp)).mp hcv)
  · rw [← cycVert_iff' hn hjP]
    intro hcv
    exact hprev' ((SegmentBasics.cycVert_congr (by simp)).mp hcv)
  · rw [WheelParity.sameWheelParity_iff hhole heven hiL hjP hijne]
    exact hdiff

end Workspace.ProofLemmas.OddWheelParityFacts
