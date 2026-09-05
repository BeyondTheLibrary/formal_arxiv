import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelSpan

/-!
# The second assertion of 16.1, from claim (1) of its proof

PAPER (16.1, printed p. 96): *"Moreover, either:*

*   `v` *has only two neighbours in* `C`*, and they are adjacent and both* `Y`*-complete, or*
*   *there is a 3-vertex path* `p₁-p₂-p₃` *in* `C`*, such that* `p₁, p₂, p₃` *are all*
    `Y ∪ {v}`*-complete, and every other neighbour of* `v` *in* `C` *has the same wheel-parity as*
    `p₁`*, or*
*   `(C, Y ∪ {v})` *is a wheel."*

PAPER (proof, printed p. 97): *"Now we prove the second assertion.  Suppose that `v` has at least
four neighbours in `C`, two with the same wheel-parity, and two others with the opposite
wheel-parity.  Then there are two disjoint paths as in (1), and therefore from (1) there are two
disjoint `Y ∪ {v}`-complete edges in `C`, and so `(C, Y ∪ {v})` is a wheel and the theorem holds.
So we may assume that `C` has vertices `p₁, …, pₙ` in order, and `v` is adjacent to `p₁`, and `v`
has no other neighbour in `C` with the same wheel-parity as `p₁`.  … Choose `i > 1` minimum such
that `v` is adjacent to `p_i`; then `i < n`, so by (1), `i = 2`.  So `p₂` is `Y ∪ {v}`-complete.
If `v` has a third neighbour in `C` then similarly `pₙ` is `Y ∪ {v}`-complete and the theorem
holds; and if not then again the theorem holds."*

This module builds the second assertion on top of `OddWheelSpan.Claim1`, exactly along those
lines.  Everything is done on cyclic positions of the rim, and wheel-parity is used through the
two-valued invariant `π` of `OddWheelParityFacts.exists_parity'`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelTrichotomy

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} {G : SimpleGraph V} {C : List V} {Y : Set V} {v : V}

/-! ### Neighbours of `v` among the cyclic positions of the rim -/

/-- *"The vertex at cyclic position `m` of `C` is adjacent to `v`."*  As in `OddWheelLines`,
this is `CycVert` for the singleton hub `{v}`, since `VertexComplete G u {v}` unfolds to
`G.Adj u v`. -/
theorem nbr_getElem_iff (hn : 0 < C.length) (m : ℕ) :
    SegmentBasics.CycVert G ({v} : Set V) C m ↔ G.Adj (C[m % C.length]'(Nat.mod_lt _ hn)) v := by
  constructor
  · rintro ⟨u, hu, hcu⟩
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hu
    rw [Option.some_injective _ hu]
    exact hcu v rfl
  · intro h
    refine ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hn), ?_⟩
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h

theorem nbr_congr {m m' : ℕ} (h : m % C.length = m' % C.length) :
    SegmentBasics.CycVert G ({v} : Set V) C m ↔ SegmentBasics.CycVert G ({v} : Set V) C m' :=
  SegmentBasics.cycVert_congr (G := G) (Y := ({v} : Set V)) (C := C) h

/-- The cyclic offset of a position `i` from a position `k`, as an element of `[0, n)`. -/
theorem offset_spec (hn : 0 < C.length) (k i : ℕ) :
    (k + (i + C.length - k % C.length) % C.length) % C.length = i % C.length := by
  have hcm : k % C.length < C.length := Nat.mod_lt _ hn
  have s1 : (k + (i + C.length - k % C.length) % C.length) % C.length
      = (k % C.length + (i + C.length - k % C.length) % C.length) % C.length :=
    (Nat.mod_add_mod k C.length _).symm
  have s2 : (k % C.length + (i + C.length - k % C.length) % C.length) % C.length
      = (k % C.length + (i + C.length - k % C.length)) % C.length :=
    Nat.add_mod_mod _ _ _
  have s3 : k % C.length + (i + C.length - k % C.length) = i + C.length := by omega
  rw [s1, s2, s3, Nat.add_mod_right]

/-! ### The case `v` has only the two given neighbours on the rim -/

/-- **Bullet 1.**  PAPER: *"`v` has only two neighbours in `C`, and they are adjacent and both
`Y`-complete."*

If `a` and `b` are the only neighbours of `v` on the rim, then — since they have opposite
wheel-parity — both arcs of `C` between them satisfy the hypotheses of claim (1), so both would
have length `1` unless one of them is the whole cycle; that forces `a` and `b` to be adjacent,
and then the edge `ab` is `Y ∪ {v}`-complete. -/
theorem bullet_one [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V}
    (hcl : OddWheelSpan.Claim1 G C Y v) {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b)
    (honly : ∀ u ∈ C, G.Adj v u → u = a ∨ u = b) :
    G.Adj a b ∧ VertexComplete G a Y ∧ VertexComplete G b Y := by
  classical
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  have hnd : C.Nodup := hC.2.1
  obtain ⟨ia, hia_lt, hia_eq⟩ := List.getElem_of_mem hab.2.1
  obtain ⟨ib, hib_lt, hib_eq⟩ := List.getElem_of_mem hab.2.2.1
  have hia_mod : ia % C.length = ia := Nat.mod_eq_of_lt hia_lt
  have hib_mod : ib % C.length = ib := Nat.mod_eq_of_lt hib_lt
  have hiab : ia ≠ ib := by
    rintro rfl
    exact hab.1 (hia_eq.symm.trans hib_eq)
  have hxa : C[ia % C.length]? = some a := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
    congr 1
    exact ((List.Nodup.getElem_inj_iff hnd).mpr hia_mod).trans hia_eq
  have hxb : C[ib % C.length]? = some b := by
    rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)]
    congr 1
    exact ((List.Nodup.getElem_inj_iff hnd).mpr hib_mod).trans hib_eq
  -- the cyclic distance from `a` to `b`
  set d : ℕ := (ib + C.length - ia % C.length) % C.length with hddef
  have hdspec : (ia + d) % C.length = ib % C.length := offset_spec hn ia ib
  have hdlt : d < C.length := Nat.mod_lt _ hn
  have hd0 : d ≠ 0 := by
    intro hcon
    rw [hcon, Nat.add_zero, hia_mod, hib_mod] at hdspec
    exact hiab hdspec
  -- no interior position of either arc is a neighbour of `v`
  have hinterior : ∀ (k t : ℕ), (k + t) % C.length ≠ ia % C.length →
      (k + t) % C.length ≠ ib % C.length →
      ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t) := by
    intro k t h1 h2 hcv
    obtain ⟨u, hu, hcu⟩ := hcv
    have huC : u ∈ C := SegmentBasics.mem_of_pos hn hu
    rcases honly u huC (hcu v rfl).symm with rfl | rfl
    · exact h1 (SegmentBasics.pos_unique hC hu hxa)
    · exact h2 (SegmentBasics.pos_unique hC hu hxb)
  -- both arcs would have length one, which is impossible unless one of them is the whole cycle
  have hadj : d = 1 ∨ d = C.length - 1 := by
    by_contra hcon
    push Not at hcon
    have hd2 : 2 ≤ d := by omega
    have hdn2 : d + 2 ≤ C.length := by omega
    have hint : ∀ t, 0 < t → t < d → ¬ SegmentBasics.CycVert G ({v} : Set V) C (ia + t) := by
      intro t ht0 htd
      refine hinterior ia t ?_ ?_
      · intro hcon2
        have h1 : (ia + t) % C.length = (ia + 0) % C.length := by
          rw [Nat.add_zero]; exact hcon2
        have h3 : t % C.length = 0 % C.length := Nat.ModEq.add_left_cancel' ia h1
        rw [Nat.mod_eq_of_lt (show t < C.length by omega), Nat.zero_mod] at h3
        omega
      · intro hcon2
        have h1 : (ia + t) % C.length = (ia + d) % C.length := hcon2.trans hdspec.symm
        have h3 : t % C.length = d % C.length := Nat.ModEq.add_left_cancel' ia h1
        rw [Nat.mod_eq_of_lt (show t < C.length by omega),
          Nat.mod_eq_of_lt (show d < C.length by omega)] at h3
        omega
    have hone := hcl ia d a b (by omega) hdn2 hxa (by rw [hdspec]; exact hxb) hva hvb hint hab
    omega
  -- so the edge between them is `Y ∪ {v}`-complete
  have hkey : ∃ k : ℕ, C[k % C.length]? = some a ∧ C[(k + 1) % C.length]? = some b ∨
      C[k % C.length]? = some b ∧ C[(k + 1) % C.length]? = some a := by
    rcases hadj with hd | hd
    · exact ⟨ia, Or.inl ⟨hxa, by rw [← hd, hdspec]; exact hxb⟩⟩
    · refine ⟨ib, Or.inr ⟨hxb, ?_⟩⟩
      have h1 : (ib + 1) % C.length = ia % C.length := by
        have e1 : (ib + 1) % C.length = (ib % C.length + 1) % C.length :=
          (Nat.mod_add_mod ib C.length 1).symm
        rw [e1, ← hdspec, Nat.mod_add_mod,
          show ia + d + 1 = ia + C.length from by omega, Nat.add_mod_right]
      rw [h1]; exact hxa
  obtain ⟨k, hk⟩ := hkey
  have hce : ∀ (x y : V), C[k % C.length]? = some x → C[(k + 1) % C.length]? = some y →
      G.Adj v x → G.Adj v y → OppositeWheelParity G C Y x y →
      G.Adj x y ∧ VertexComplete G x Y ∧ VertexComplete G y Y := by
    intro x y hx hy hvx hvy hopp
    obtain ⟨t, ht, hcyc⟩ :=
      OddWheelSpan.exists_ext_edge hC heven hcl (L := 1) (k := k) le_rfl (by omega) hx hy
        hvx hvy hopp
    have ht0 : t = 0 := by omega
    subst ht0
    obtain ⟨x', y', hx', hy', hE⟩ := hcyc
    have hx'' : C[k % C.length]? = some x' := hx'
    have hy'' : C[(k + 1) % C.length]? = some y' := hy'
    have ex : x' = x := Option.some_injective _ (hx''.symm.trans hx)
    have ey : y' = y := Option.some_injective _ (hy''.symm.trans hy)
    subst ex; subst ey
    exact ⟨hE.1, (OddWheelSpan.vertexComplete_union.mp hE.2.1).1,
      (OddWheelSpan.vertexComplete_union.mp hE.2.2).1⟩
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hce a b h1 h2 hva hvb hab
  · obtain ⟨e1, e2, e3⟩ := hce b a h1 h2 hvb hva (OddWheelSpan.oppositeWheelParity_symm hab)
    exact ⟨e1.symm, e3, e2⟩

/-! ### Locating the neighbours of `v` relative to one of them -/

/-- If the only positions carrying neighbours of `v` in one full turn round the rim, starting at
`k`, are `k` and `k + M`, then `v` has at most the two corresponding neighbours on the rim. -/
theorem nbr_in_two (hC : IsHoleList G C) (hn : 0 < C.length) {k M : ℕ}
    (hint : ∀ t, 0 < t → t < M → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t))
    (hrest : ∀ t, M < t → t < C.length → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t))
    {u : V} (huC : u ∈ C) (hvu : G.Adj v u) :
    u = (C[k % C.length]'(Nat.mod_lt _ hn)) ∨ u = (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) := by
  obtain ⟨j, hj, hju⟩ := List.getElem_of_mem huC
  have hspec : (k + (j + C.length - k % C.length) % C.length) % C.length = j % C.length :=
    offset_spec hn k j
  have htlt : (j + C.length - k % C.length) % C.length < C.length := Nat.mod_lt _ hn
  have hkt : (k + (j + C.length - k % C.length) % C.length) % C.length = j := by
    rw [hspec, Nat.mod_eq_of_lt hj]
  have hcv : SegmentBasics.CycVert G ({v} : Set V) C
      (k + (j + C.length - k % C.length) % C.length) := by
    rw [nbr_getElem_iff hn]
    have he : (C[(k + (j + C.length - k % C.length) % C.length) % C.length]'(Nat.mod_lt _ hn))
        = (C[j]'hj) := (List.Nodup.getElem_inj_iff hC.2.1).mpr hkt
    rw [he, hju]
    exact hvu.symm
  rcases (show (j + C.length - k % C.length) % C.length = 0 ∨
      (0 < (j + C.length - k % C.length) % C.length ∧
        (j + C.length - k % C.length) % C.length < M) ∨
      (j + C.length - k % C.length) % C.length = M ∨
      (M < (j + C.length - k % C.length) % C.length ∧
        (j + C.length - k % C.length) % C.length < C.length) by omega) with h | h | h | h
  · left
    rw [← hju]
    refine ((List.Nodup.getElem_inj_iff hC.2.1).mpr ?_).symm
    rw [← hkt, h, Nat.add_zero]
  · exact absurd hcv (hint _ h.1 h.2)
  · right
    rw [← hju]
    refine ((List.Nodup.getElem_inj_iff hC.2.1).mpr ?_).symm
    rw [← hkt, h]
  · exact absurd hcv (hrest _ h.1 h.2)

/-! ### The gap next to a neighbour whose wheel-parity class is a singleton -/

/-- **The engine behind the second and third bullets.**

PAPER: *"Choose `i > 1` minimum such that `v` is adjacent to `p_i`; then `i < n`, so by (1),
`i = 2`."*

If `v` has at least three neighbours on the rim and `a` is the only neighbour in its
wheel-parity class, then every gap between cyclically consecutive neighbours of `v` having `a`
as one end has length `1`: the two ends necessarily have opposite wheel-parity, and no interior
position is a neighbour, so claim (1) applies.  Having three neighbours is what rules out the
degenerate gaps of length `C.length - 1` and `C.length`, for which the arc is not a path. -/
theorem gap_eq_one (hC : IsHoleList G C) (hn : 0 < C.length) (hn6 : 6 ≤ C.length)
    (hcl : OddWheelSpan.Claim1 G C Y v)
    {a : V} (hsingle : ∀ u ∈ C, G.Adj v u → u ≠ a → ¬ SameWheelParity G C Y u a)
    {x₁ x₂ x₃ : V} (h1 : x₁ ∈ C ∧ G.Adj v x₁) (h2 : x₂ ∈ C ∧ G.Adj v x₂)
    (h3 : x₃ ∈ C ∧ G.Adj v x₃) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃)
    {k M : ℕ} (hM1 : 1 ≤ M) (hMn : M ≤ C.length)
    (hk : SegmentBasics.CycVert G ({v} : Set V) C k)
    (hkM : SegmentBasics.CycVert G ({v} : Set V) C (k + M))
    (hint : ∀ t, 0 < t → t < M → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t))
    (ha : (C[k % C.length]'(Nat.mod_lt _ hn)) = a ∨
          (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) = a) :
    M = 1 := by
  have hxk : G.Adj (C[k % C.length]'(Nat.mod_lt _ hn)) v := (nbr_getElem_iff hn k).mp hk
  have hxkM : G.Adj (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) v :=
    (nbr_getElem_iff hn (k + M)).mp hkM
  have hmemk : (C[k % C.length]'(Nat.mod_lt _ hn)) ∈ C := List.getElem_mem _
  have hmemkM : (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) ∈ C := List.getElem_mem _
  -- three neighbours rule out the two degenerate gap lengths
  have hMle : M + 2 ≤ C.length := by
    by_contra hcon
    have hrest : ∀ t, M < t → t < C.length →
        ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t) := by
      intro t ht1 ht2; omega
    have e1 := nbr_in_two hC hn hint hrest h1.1 h1.2
    have e2 := nbr_in_two hC hn hint hrest h2.1 h2.2
    have e3 := nbr_in_two hC hn hint hrest h3.1 h3.2
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2 <;> rcases e3 with e3 | e3
    · exact h12 (e1.trans e2.symm)
    · exact h12 (e1.trans e2.symm)
    · exact h13 (e1.trans e3.symm)
    · exact h23 (e2.trans e3.symm)
    · exact h23 (e2.trans e3.symm)
    · exact h13 (e1.trans e3.symm)
    · exact h12 (e1.trans e2.symm)
    · exact h12 (e1.trans e2.symm)
  -- the two ends of the gap are distinct
  have hne : (C[k % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) := by
    refine HoleBasics.hole_ne_of_ne_index hC _ _ ?_
    intro hcon
    have h1' : (k + 0) % C.length = (k + M) % C.length := by rw [Nat.add_zero]; exact hcon
    have h2' : (0 : ℕ) % C.length = M % C.length := Nat.ModEq.add_left_cancel' k h1'
    rw [Nat.zero_mod, Nat.mod_eq_of_lt (show M < C.length by omega)] at h2'
    omega
  -- and they have opposite wheel-parity, since only `a` lies in its class
  have hopp : OppositeWheelParity G C Y (C[k % C.length]'(Nat.mod_lt _ hn))
      (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) := by
    refine ⟨hne, hmemk, hmemkM, ?_⟩
    intro hs
    rcases ha with ha | ha
    · have hne2 : (C[(k + M) % C.length]'(Nat.mod_lt _ hn)) ≠ a := by
        rw [← ha]; exact fun he => hne he.symm
      refine hsingle _ hmemkM hxkM.symm hne2 ?_
      rw [← ha]
      exact WheelParity.sameWheelParity_symm hs
    · have hne2 : (C[k % C.length]'(Nat.mod_lt _ hn)) ≠ a := by
        rw [← ha]; exact hne
      refine hsingle _ hmemk hxk.symm hne2 ?_
      rw [← ha]
      exact hs
  exact hcl k M _ _ hM1 hMle (List.getElem?_eq_getElem (Nat.mod_lt _ hn))
    (List.getElem?_eq_getElem (Nat.mod_lt _ hn)) hxk.symm hxkM.symm hint hopp

/-! ### Walking to the next and previous neighbour of `v` -/

/-- The next position carrying a neighbour of `v`, going forwards from a position that carries
one. -/
theorem exists_next (hn : 0 < C.length) {k : ℕ}
    (hk : SegmentBasics.CycVert G ({v} : Set V) C k) :
    ∃ M : ℕ, 1 ≤ M ∧ M ≤ C.length ∧ SegmentBasics.CycVert G ({v} : Set V) C (k + M) ∧
      ∀ t, 0 < t → t < M → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t) := by
  classical
  have hper : SegmentBasics.CycVert G ({v} : Set V) C (k + C.length) :=
    (nbr_congr (Nat.add_mod_right k C.length)).mpr hk
  have hex : ∃ j : ℕ, SegmentBasics.CycVert G ({v} : Set V) C (k + (j + 1)) := by
    refine ⟨C.length - 1, ?_⟩
    rw [show C.length - 1 + 1 = C.length from by omega]
    exact hper
  refine ⟨Nat.find hex + 1, by omega, ?_, Nat.find_spec hex, ?_⟩
  · have hle : Nat.find hex ≤ C.length - 1 :=
      Nat.find_min' hex (by rw [show C.length - 1 + 1 = C.length from by omega]; exact hper)
    omega
  · intro t ht0 htM
    obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
    exact Nat.find_min hex (by omega)

/-- The previous position carrying a neighbour of `v`, going backwards from a position that
carries one. -/
theorem exists_prev (hn : 0 < C.length) {k : ℕ}
    (hk : SegmentBasics.CycVert G ({v} : Set V) C k) :
    ∃ M : ℕ, 1 ≤ M ∧ M ≤ C.length ∧
      SegmentBasics.CycVert G ({v} : Set V) C (k + C.length - M) ∧
      ∀ t, 0 < t → t < M → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + C.length - t) := by
  classical
  have hex : ∃ j : ℕ, SegmentBasics.CycVert G ({v} : Set V) C (k + C.length - (j + 1)) := by
    refine ⟨C.length - 1, ?_⟩
    rw [show k + C.length - (C.length - 1 + 1) = k from by omega]
    exact hk
  refine ⟨Nat.find hex + 1, by omega, ?_, Nat.find_spec hex, ?_⟩
  · have hle : Nat.find hex ≤ C.length - 1 :=
      Nat.find_min' hex (by rw [show k + C.length - (C.length - 1 + 1) = k from by omega]; exact hk)
    omega
  · intro t ht0 htM
    obtain ⟨j, rfl⟩ : ∃ j, t = j + 1 := ⟨t - 1, by omega⟩
    exact Nat.find_min hex (by omega)

/-- Three cyclically consecutive vertices of the rim, as a literal list. -/
theorem take_three_eq (hn : 0 < C.length) (h3 : 3 ≤ C.length) (k : ℕ) :
    (C.rotate k).take 3 = [C[k % C.length]'(Nat.mod_lt _ hn),
      C[(k + 1) % C.length]'(Nat.mod_lt _ hn), C[(k + 2) % C.length]'(Nat.mod_lt _ hn)] := by
  have hlen : ((C.rotate k).take 3).length = 3 := by
    simp only [List.length_take, List.length_rotate]; omega
  refine List.ext_getElem (by rw [hlen]; simp) ?_
  intro i h1 h2
  rw [SegmentBasics.arc_getElem hn h1]
  have hi3 : i < 3 := h2
  interval_cases i <;> simp

/-! ### Bullet 2 -/

/-- **Bullet 2.**  PAPER: *"there is a 3-vertex path `p₁-p₂-p₃` in `C`, such that `p₁, p₂, p₃`
are all `Y ∪ {v}`-complete, and every other neighbour of `v` in `C` has the same wheel-parity as
`p₁`."*

PAPER (proof, printed p. 97): *"Choose `i > 1` minimum such that `v` is adjacent to `p_i`; then
`i < n`, so by (1), `i = 2`.  So `p₂` is `Y ∪ {v}`-complete.  If `v` has a third neighbour in `C`
then similarly `pₙ` is `Y ∪ {v}`-complete and the theorem holds."*

Here `a` plays the role of the paper's `p₁` — the unique neighbour of `v` in its wheel-parity
class — and the 3-vertex path is `pₙ-p₁-p₂`, i.e. `a` flanked by its two rim neighbours. -/
theorem bullet_two [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V}
    (hcl : OddWheelSpan.Claim1 G C Y v) {a : V} (haC : a ∈ C) (hva : G.Adj v a)
    (hsingle : ∀ u ∈ C, G.Adj v u → u ≠ a → ¬ SameWheelParity G C Y u a)
    {x₁ x₂ x₃ : V} (h1 : x₁ ∈ C ∧ G.Adj v x₁) (h2 : x₂ ∈ C ∧ G.Adj v x₂)
    (h3 : x₃ ∈ C ∧ G.Adj v x₃) (h12 : x₁ ≠ x₂) (h13 : x₁ ≠ x₃) (h23 : x₂ ≠ x₃) :
    ∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
      (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
      VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
      VertexComplete G p₃ (Y ∪ {v}) ∧
      ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁ := by
  classical
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  have hnd : C.Nodup := hC.2.1
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  obtain ⟨ia, hia_lt, hia_eq⟩ := List.getElem_of_mem haC
  have hia_mod : ia % C.length = ia := Nat.mod_eq_of_lt hia_lt
  have hxa : (C[ia % C.length]'(Nat.mod_lt _ hn)) = a :=
    ((List.Nodup.getElem_inj_iff hnd).mpr hia_mod).trans hia_eq
  have hNia : SegmentBasics.CycVert G ({v} : Set V) C ia := by
    rw [nbr_getElem_iff hn, hxa]; exact hva.symm
  -- the cyclic successor of `a` is a neighbour of `v`
  obtain ⟨Mf, hMf1, hMfn, hMfnb, hMfint⟩ := exists_next hn hNia
  have hMf : Mf = 1 :=
    gap_eq_one hC hn hn6 hcl hsingle h1 h2 h3 h12 h13 h23 hMf1 hMfn hNia hMfnb hMfint (Or.inl hxa)
  subst hMf
  -- the cyclic predecessor of `a` is a neighbour of `v`
  obtain ⟨Mb, hMb1, hMbn, hMbnb, hMbint⟩ := exists_prev hn hNia
  have hMb : Mb = 1 := by
    refine gap_eq_one hC hn hn6 hcl hsingle h1 h2 h3 h12 h13 h23 hMb1 hMbn hMbnb ?_ ?_ ?_
    · rw [show ia + C.length - Mb + Mb = ia + C.length from by omega]
      exact (nbr_congr (Nat.add_mod_right ia C.length)).mpr hNia
    · intro t ht0 htM
      rw [show ia + C.length - Mb + t = ia + C.length - (Mb - t) from by omega]
      exact hMbint (Mb - t) (by omega) (by omega)
    · right
      have hidx : (ia + C.length - Mb + Mb) % C.length = ia % C.length := by
        rw [show ia + C.length - Mb + Mb = ia + C.length from by omega]
        exact Nat.add_mod_right ia C.length
      exact ((List.Nodup.getElem_inj_iff hnd).mpr hidx).trans hxa
  subst hMb
  set k₀ : ℕ := ia + C.length - 1 with hk₀
  have hidx2 : (k₀ + 1) % C.length = ia % C.length := by
    rw [show k₀ + 1 = ia + C.length from by omega]
    exact Nat.add_mod_right ia C.length
  have hidx3 : (k₀ + 2) % C.length = (ia + 1) % C.length := by
    rw [show k₀ + 2 = (ia + 1) + C.length from by omega]
    exact Nat.add_mod_right (ia + 1) C.length
  have hp₂ : (C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn)) = a :=
    ((List.Nodup.getElem_inj_iff hnd).mpr hidx2).trans hxa
  have hp₁nb : SegmentBasics.CycVert G ({v} : Set V) C k₀ := hMbnb
  have hp₂nb : SegmentBasics.CycVert G ({v} : Set V) C (k₀ + 1) := (nbr_congr hidx2).mpr hNia
  have hp₃nb : SegmentBasics.CycVert G ({v} : Set V) C (k₀ + 2) := (nbr_congr hidx3).mpr hMfnb
  have hadj12 : G.Adj (C[k₀ % C.length]'(Nat.mod_lt _ hn))
      (C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn)) := YEdgeConfiguration.adj_of_succ_pos hC hn k₀
  have hadj23 : G.Adj (C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn))
      (C[(k₀ + 1 + 1) % C.length]'(Nat.mod_lt _ hn)) :=
    YEdgeConfiguration.adj_of_succ_pos hC hn (k₀ + 1)
  have hp₁C : (C[k₀ % C.length]'(Nat.mod_lt _ hn)) ∈ C := List.getElem_mem _
  have hp₃C : (C[(k₀ + 2) % C.length]'(Nat.mod_lt _ hn)) ∈ C := List.getElem_mem _
  have hvp₁ : G.Adj v (C[k₀ % C.length]'(Nat.mod_lt _ hn)) :=
    ((nbr_getElem_iff hn k₀).mp hp₁nb).symm
  have hvp₃ : G.Adj v (C[(k₀ + 2) % C.length]'(Nat.mod_lt _ hn)) :=
    ((nbr_getElem_iff hn (k₀ + 2)).mp hp₃nb).symm
  have hp₁a : (C[k₀ % C.length]'(Nat.mod_lt _ hn)) ≠ a := by rw [← hp₂]; exact hadj12.ne
  have hp₃a : (C[(k₀ + 2) % C.length]'(Nat.mod_lt _ hn)) ≠ a := by
    rw [← hp₂]; exact fun he => hadj23.ne he.symm
  have hopp12 : OppositeWheelParity G C Y (C[k₀ % C.length]'(Nat.mod_lt _ hn))
      (C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn)) := by
    refine ⟨hadj12.ne, hp₁C, by rw [hp₂]; exact haC, ?_⟩
    rw [hp₂]
    exact hsingle _ hp₁C hvp₁ hp₁a
  have hopp23 : OppositeWheelParity G C Y (C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn))
      (C[(k₀ + 1 + 1) % C.length]'(Nat.mod_lt _ hn)) := by
    refine ⟨hadj23.ne, by rw [hp₂]; exact haC, hp₃C, ?_⟩
    rw [hp₂]
    intro hs
    exact hsingle _ hp₃C hvp₃ hp₃a (WheelParity.sameWheelParity_symm hs)
  -- both edges of the 3-vertex path are `Y ∪ {v}`-complete
  have hedge : ∀ k : ℕ, SegmentBasics.CycVert G ({v} : Set V) C k →
      SegmentBasics.CycVert G ({v} : Set V) C (k + 1) →
      OppositeWheelParity G C Y (C[k % C.length]'(Nat.mod_lt _ hn))
        (C[(k + 1) % C.length]'(Nat.mod_lt _ hn)) →
      VertexComplete G (C[k % C.length]'(Nat.mod_lt _ hn)) (Y ∪ {v}) ∧
        VertexComplete G (C[(k + 1) % C.length]'(Nat.mod_lt _ hn)) (Y ∪ {v}) := by
    intro k hk hk1 hopp
    obtain ⟨t, ht, hcyc⟩ := OddWheelSpan.exists_ext_edge hC heven hcl (L := 1) (k := k) le_rfl
      (by omega) (List.getElem?_eq_getElem (Nat.mod_lt _ hn))
      (List.getElem?_eq_getElem (Nat.mod_lt _ hn))
      ((nbr_getElem_iff hn k).mp hk).symm ((nbr_getElem_iff hn (k + 1)).mp hk1).symm hopp
    have ht0 : t = 0 := by omega
    subst ht0
    obtain ⟨x, y, hx, hy, hE⟩ := hcyc
    have hx' : C[k % C.length]? = some x := hx
    have hy' : C[(k + 1) % C.length]? = some y := hy
    have ex : x = (C[k % C.length]'(Nat.mod_lt _ hn)) :=
      Option.some_injective _ (hx'.symm.trans (List.getElem?_eq_getElem (Nat.mod_lt _ hn)))
    have ey : y = (C[(k + 1) % C.length]'(Nat.mod_lt _ hn)) :=
      Option.some_injective _ (hy'.symm.trans (List.getElem?_eq_getElem (Nat.mod_lt _ hn)))
    rw [ex, ey] at hE
    exact ⟨hE.2.1, hE.2.2⟩
  obtain ⟨hcp₁, hcp₂⟩ := hedge k₀ hp₁nb hp₂nb hopp12
  obtain ⟨-, hcp₃⟩ := hedge (k₀ + 1) hp₂nb hp₃nb hopp23
  refine ⟨C[k₀ % C.length]'(Nat.mod_lt _ hn), C[(k₀ + 1) % C.length]'(Nat.mod_lt _ hn),
    C[(k₀ + 2) % C.length]'(Nat.mod_lt _ hn), ?_, ⟨k₀, Or.inl ?_⟩, hcp₁, hcp₂, hcp₃, ?_⟩
  · have hpl := WheelParity.isPathList_rotate_take hC (show 1 ≤ 3 by omega)
      (show 3 + 1 ≤ C.length by omega) (k := k₀)
    rwa [take_three_eq hn (by omega) k₀] at hpl
  · rw [← take_three_eq hn (by omega) k₀]
    exact List.take_prefix _ _
  · intro u huC hvu hu1 hu2 hu3
    have hua : u ≠ a := by rw [← hp₂]; exact hu2
    have hπua : π u ≠ π a := fun he => hsingle u huC hvu hua ((hπ u a huC haC hua).mpr he)
    have hπ1a : π (C[k₀ % C.length]'(Nat.mod_lt _ hn)) ≠ π a := fun he =>
      hsingle _ hp₁C hvp₁ hp₁a ((hπ _ a hp₁C haC hp₁a).mpr he)
    refine (hπ u _ huC hp₁C hu1).mpr ?_
    have h2u := hπ2 u
    have h2a := hπ2 a
    have h21 := hπ2 (C[k₀ % C.length]'(Nat.mod_lt _ hn))
    omega

/-! ### Bullet 3: two vertex-disjoint arcs make `(C, Y ∪ {v})` a wheel -/

private theorem edgeComplete_of_cycEdge (hn : 0 < C.length) {W : Set V} {m : ℕ}
    (h : WheelParity.CycEdge G W C m) :
    EdgeComplete G W (C[m % C.length]'(Nat.mod_lt _ hn))
      (C[(m + 1) % C.length]'(Nat.mod_lt _ hn)) := by
  obtain ⟨x, y, hx, hy, hE⟩ := h
  rw [List.getElem?_eq_getElem (Nat.mod_lt _ hn)] at hx hy
  rw [Option.some_injective _ hx, Option.some_injective _ hy]
  exact hE

private theorem pos_ne (hC : IsHoleList G C) (hn : 0 < C.length) (base : ℕ) {i j : ℕ}
    (hij : i < j) (hjn : j - i < C.length) :
    (C[(base + i) % C.length]'(Nat.mod_lt _ hn)) ≠ (C[(base + j) % C.length]'(Nat.mod_lt _ hn)) := by
  refine HoleBasics.hole_ne_of_ne_index hC _ _ ?_
  intro hcon
  have h1 : i % C.length = j % C.length := Nat.ModEq.add_left_cancel' base hcon
  have h2 : (j - i) % C.length = 0 % C.length := by
    have h3 : (i + (j - i)) % C.length = (i + 0) % C.length := by
      rw [show i + (j - i) = j from by omega, Nat.add_zero]
      exact h1.symm
    exact Nat.ModEq.add_left_cancel' i h3
  rw [Nat.mod_eq_of_lt hjn, Nat.zero_mod] at h2
  omega

/-- **Bullet 3.**  PAPER: *"Then there are two disjoint paths as in (1), and therefore from (1)
there are two disjoint `Y ∪ {v}`-complete edges in `C`, and so `(C, Y ∪ {v})` is a wheel."*

The two paths are given here as two arcs `[base+s, base+e]` and `[base+s', base+e']` of the rim
that do not overlap (`e ≤ s'`) and together span less than a full turn (`e' - s < C.length`). -/
theorem wheel_of_two_arcs [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V} (hvC : v ∉ C) (hvY : v ∉ Y)
    (hvnc : ¬ VertexComplete G v Y) (hcl : OddWheelSpan.Claim1 G C Y v)
    (base : ℕ) {s e s' e' : ℕ}
    (hse : s < e) (hes : e < s') (hse' : s' < e') (hspan : e' - s < C.length)
    (hns : SegmentBasics.CycVert G ({v} : Set V) C (base + s))
    (hne : SegmentBasics.CycVert G ({v} : Set V) C (base + e))
    (hns' : SegmentBasics.CycVert G ({v} : Set V) C (base + s'))
    (hne' : SegmentBasics.CycVert G ({v} : Set V) C (base + e'))
    (hopp1 : OppositeWheelParity G C Y (C[(base + s) % C.length]'(Nat.mod_lt _ (by
      have := hw.1.2; omega)))
      (C[(base + e) % C.length]'(Nat.mod_lt _ (by have := hw.1.2; omega))))
    (hopp2 : OppositeWheelParity G C Y (C[(base + s') % C.length]'(Nat.mod_lt _ (by
      have := hw.1.2; omega)))
      (C[(base + e') % C.length]'(Nat.mod_lt _ (by have := hw.1.2; omega)))) :
    IsWheel G C (Y ∪ {v}) := by
  classical
  have hC : IsHoleList G C := hw.1.1
  have hlen6 : 6 ≤ holeLength C := hw.1.2
  have hn6 : 6 ≤ C.length := hlen6
  have hn : 0 < C.length := by omega
  have hYanti : AnticonnectedSet G Y := hw.2.1.2.1
  have hCY : ∀ u ∈ C, u ∉ Y := hw.2.1.2.2
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  -- the enlarged hub is a legitimate hub
  have hWne : (Y ∪ {v} : Set V).Nonempty := ⟨v, Or.inr rfl⟩
  have hCW : ∀ u ∈ C, u ∉ (Y ∪ {v} : Set V) := by
    intro u hu hmem
    rcases hmem with h | h
    · exact hCY u hu h
    · exact hvC (by rw [← Set.mem_singleton_iff.mp h]; exact hu)
  have hWanti : AnticonnectedSet G (Y ∪ {v} : Set V) := by
    obtain ⟨y₀, hy₀Y, hy₀⟩ : ∃ y₀ ∈ Y, ¬ G.Adj v y₀ := by
      by_contra hcon
      push Not at hcon
      exact hvnc hcon
    exact ConnectedSetUnionAttach.connectedSet_union_singleton hYanti
      ⟨y₀, hy₀Y, ⟨fun h => hvY (by rw [h]; exact hy₀Y), hy₀⟩⟩
  -- an extended-complete edge on each arc
  obtain ⟨t₁, ht₁, hce₁⟩ := OddWheelSpan.exists_ext_edge hC heven hcl (L := e - s)
    (k := base + s) (by omega) (by omega) (List.getElem?_eq_getElem (Nat.mod_lt _ hn))
    (by rw [show base + s + (e - s) = base + e from by omega]
        exact List.getElem?_eq_getElem (Nat.mod_lt _ hn))
    ((nbr_getElem_iff hn (base + s)).mp hns).symm
    ((nbr_getElem_iff hn (base + e)).mp hne).symm hopp1
  obtain ⟨t₂, ht₂, hce₂⟩ := OddWheelSpan.exists_ext_edge hC heven hcl (L := e' - s')
    (k := base + s') (by omega) (by omega) (List.getElem?_eq_getElem (Nat.mod_lt _ hn))
    (by rw [show base + s' + (e' - s') = base + e' from by omega]
        exact List.getElem?_eq_getElem (Nat.mod_lt _ hn))
    ((nbr_getElem_iff hn (base + s')).mp hns').symm
    ((nbr_getElem_iff hn (base + e')).mp hne').symm hopp2
  -- the two edges are disjoint
  have hb1 : s + t₁ < e := by omega
  have hb2 : s' + t₂ < e' := by omega
  have hE₁ := edgeComplete_of_cycEdge hn hce₁
  have hE₂ := edgeComplete_of_cycEdge hn hce₂
  rw [show base + s + t₁ = base + (s + t₁) from by omega] at hE₁
  rw [show base + (s + t₁) + 1 = base + (s + t₁ + 1) from by omega] at hE₁
  rw [show base + s' + t₂ = base + (s' + t₂) from by omega] at hE₂
  rw [show base + (s' + t₂) + 1 = base + (s' + t₂ + 1) from by omega] at hE₂
  refine ⟨⟨hC, hlen6⟩, ⟨hWne, hWanti, hCW⟩,
    C[(base + (s + t₁)) % C.length]'(Nat.mod_lt _ hn),
    C[(base + (s + t₁ + 1)) % C.length]'(Nat.mod_lt _ hn),
    C[(base + (s' + t₂)) % C.length]'(Nat.mod_lt _ hn),
    C[(base + (s' + t₂ + 1)) % C.length]'(Nat.mod_lt _ hn),
    List.getElem_mem _, List.getElem_mem _, List.getElem_mem _, List.getElem_mem _,
    hE₁, hE₂, ?_, ?_, ?_, ?_⟩
  · exact pos_ne hC hn base (by omega) (by omega)
  · exact pos_ne hC hn base (by omega) (by omega)
  · exact pos_ne hC hn base (by omega) (by omega)
  · exact pos_ne hC hn base (by omega) (by omega)

/-- Every vertex of the rim occupies a cyclic offset `< C.length` from any given base. -/
theorem exists_offset (hC : IsHoleList G C) (hn : 0 < C.length) (base : ℕ) {u : V}
    (hu : u ∈ C) : ∃ d, d < C.length ∧ (C[(base + d) % C.length]'(Nat.mod_lt _ hn)) = u := by
  obtain ⟨j, hj, hju⟩ := List.getElem_of_mem hu
  refine ⟨(j + C.length - base % C.length) % C.length, Nat.mod_lt _ hn, ?_⟩
  have hkt : (base + (j + C.length - base % C.length) % C.length) % C.length = j := by
    rw [offset_spec hn base j, Nat.mod_eq_of_lt hj]
  exact ((List.Nodup.getElem_inj_iff hC.2.1).mpr hkt).trans hju

/-- **Bullet 3.**  PAPER: *"Suppose that `v` has at least four neighbours in `C`, two with the
same wheel-parity, and two others with the opposite wheel-parity.  Then there are two disjoint
paths as in (1), and therefore from (1) there are two disjoint `Y ∪ {v}`-complete edges in `C`,
and so `(C, Y ∪ {v})` is a wheel and the theorem holds."*

Reading the four neighbours as cyclic offsets from `x₁`, the two required arcs are found by a
single case split on where `x₂` sits relative to the two `y`'s. -/
theorem bullet_three [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V} (hvC : v ∉ C) (hvY : v ∉ Y)
    (hvnc : ¬ VertexComplete G v Y) (hcl : OddWheelSpan.Claim1 G C Y v)
    (π : V → ℕ) (hπ2 : ∀ z : V, π z < 2)
    (hπ : ∀ z w : V, z ∈ C → w ∈ C → z ≠ w → (SameWheelParity G C Y z w ↔ π z = π w))
    {x₁ x₂ y₁ y₂ : V}
    (hx₁ : x₁ ∈ C ∧ G.Adj v x₁) (hx₂ : x₂ ∈ C ∧ G.Adj v x₂)
    (hy₁ : y₁ ∈ C ∧ G.Adj v y₁) (hy₂ : y₂ ∈ C ∧ G.Adj v y₂)
    (hxne : x₁ ≠ x₂) (hyne : y₁ ≠ y₂)
    (hpx : π x₁ = π x₂) (hpy : π y₁ = π y₂) (hpxy : π x₁ ≠ π y₁) :
    IsWheel G C (Y ∪ {v}) := by
  classical
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have hn : 0 < C.length := by omega
  -- the base is the position of `x₁`
  obtain ⟨b₀, hb₀lt, hb₀eq⟩ := exists_offset hC hn 0 hx₁.1
  -- offsets of the other three neighbours from `x₁`
  obtain ⟨o₂, ho₂lt, ho₂eq⟩ := exists_offset hC hn b₀ hx₂.1
  obtain ⟨f₁, hf₁lt, hf₁eq⟩ := exists_offset hC hn b₀ hy₁.1
  obtain ⟨f₂, hf₂lt, hf₂eq⟩ := exists_offset hC hn b₀ hy₂.1
  have hb₀x : (C[(b₀ + 0) % C.length]'(Nat.mod_lt _ hn)) = x₁ := by
    rw [Nat.add_zero]
    have h0 : (0 + b₀) % C.length = b₀ % C.length := by rw [Nat.zero_add]
    exact ((List.Nodup.getElem_inj_iff hC.2.1).mpr h0.symm).trans hb₀eq
  -- offsets determine the vertex, so distinct vertices have distinct offsets
  have hoff_inj : ∀ d d' : ℕ, d < C.length → d' < C.length →
      (C[(b₀ + d) % C.length]'(Nat.mod_lt _ hn)) = (C[(b₀ + d') % C.length]'(Nat.mod_lt _ hn)) →
      d = d' := by
    intro d d' hd hd' he
    have h1 : (b₀ + d) % C.length = (b₀ + d') % C.length :=
      (List.Nodup.getElem_inj_iff hC.2.1).mp he
    have h2 : d % C.length = d' % C.length := Nat.ModEq.add_left_cancel' b₀ h1
    rw [Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hd'] at h2
    exact h2
  have hxy₁ : x₁ ≠ y₁ := fun he => hpxy (by rw [he])
  have hxy₂ : x₁ ≠ y₂ := fun he => hpxy (by rw [he, hpy])
  have hx₂y₁ : x₂ ≠ y₁ := fun he => hpxy (by rw [hpx, he])
  have hx₂y₂ : x₂ ≠ y₂ := fun he => hpxy (by rw [hpx, he, hpy])
  have h0o₂ : (0 : ℕ) ≠ o₂ := fun he => hxne (by rw [← hb₀x, he, ho₂eq])
  have h0f₁ : (0 : ℕ) ≠ f₁ := fun he => hxy₁ (by rw [← hb₀x, he, hf₁eq])
  have h0f₂ : (0 : ℕ) ≠ f₂ := fun he => hxy₂ (by rw [← hb₀x, he, hf₂eq])
  have ho₂f₁ : o₂ ≠ f₁ := fun he => hx₂y₁ (by rw [← ho₂eq, he, hf₁eq])
  have ho₂f₂ : o₂ ≠ f₂ := fun he => hx₂y₂ (by rw [← ho₂eq, he, hf₂eq])
  have hf₁f₂ : f₁ ≠ f₂ := fun he => hyne (by rw [← hf₁eq, he, hf₂eq])
  -- neighbours of `v` at each of the four offsets, and at the full turn
  have hnb : ∀ (d : ℕ) (u : V), (C[(b₀ + d) % C.length]'(Nat.mod_lt _ hn)) = u → G.Adj v u →
      SegmentBasics.CycVert G ({v} : Set V) C (b₀ + d) := by
    intro d u he hvu
    rw [nbr_getElem_iff hn, he]
    exact hvu.symm
  have hnbn : SegmentBasics.CycVert G ({v} : Set V) C (b₀ + C.length) := by
    refine (nbr_congr ?_).mpr (hnb 0 x₁ hb₀x hx₁.2)
    rw [Nat.add_zero, Nat.add_mod_right]
  have hnb0 := hnb 0 x₁ hb₀x hx₁.2
  have hnb2 := hnb o₂ x₂ ho₂eq hx₂.2
  have hnbf₁ := hnb f₁ y₁ hf₁eq hy₁.2
  have hnbf₂ := hnb f₂ y₂ hf₂eq hy₂.2
  -- the two wheel-parity classes, as an `OppositeWheelParity` fact at each offset pair
  have hoppXY : ∀ (d f : ℕ) (u w : V),
      (C[(b₀ + d) % C.length]'(Nat.mod_lt _ hn)) = u →
      (C[(b₀ + f) % C.length]'(Nat.mod_lt _ hn)) = w →
      u ∈ C → w ∈ C → π u ≠ π w →
      OppositeWheelParity G C Y (C[(b₀ + d) % C.length]'(Nat.mod_lt _ hn))
        (C[(b₀ + f) % C.length]'(Nat.mod_lt _ hn)) := by
    intro d f u w hu hw huC hwC hne
    rw [hu, hw]
    exact ⟨fun he => hne (by rw [he]), huC, hwC, fun hs => hne ((hπ u w huC hwC
      (fun he => hne (by rw [he]))).mp hs)⟩
  rcases Nat.lt_or_ge f₁ f₂ with hf | hf
  · -- `f₁ < f₂`
    rcases Nat.lt_or_ge o₂ f₁ with ho | ho
    · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := o₂) (e := f₁) (s' := f₂)
        (e' := C.length) ho (by omega) (by omega) (by omega) hnb2 hnbf₁ hnbf₂ hnbn
        (hoppXY o₂ f₁ x₂ y₁ ho₂eq hf₁eq hx₂.1 hy₁.1 (by omega))
        (hoppXY f₂ C.length y₂ x₁ hf₂eq (by
          refine ((List.Nodup.getElem_inj_iff hC.2.1).mpr ?_).trans hb₀x
          rw [Nat.add_zero, Nat.add_mod_right]) hy₂.1 hx₁.1 (by omega))
    · rcases Nat.lt_or_ge o₂ f₂ with ho' | ho'
      · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := 0) (e := f₁) (s' := o₂)
          (e' := f₂) (by omega) (by omega) (by omega) (by omega) hnb0 hnbf₁ hnb2 hnbf₂
          (hoppXY 0 f₁ x₁ y₁ hb₀x hf₁eq hx₁.1 hy₁.1 (by omega))
          (hoppXY o₂ f₂ x₂ y₂ ho₂eq hf₂eq hx₂.1 hy₂.1 (by omega))
      · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := 0) (e := f₁) (s' := f₂)
          (e' := o₂) (by omega) (by omega) (by omega) (by omega) hnb0 hnbf₁ hnbf₂ hnb2
          (hoppXY 0 f₁ x₁ y₁ hb₀x hf₁eq hx₁.1 hy₁.1 (by omega))
          (hoppXY f₂ o₂ y₂ x₂ hf₂eq ho₂eq hy₂.1 hx₂.1 (by omega))
  · -- `f₂ < f₁`
    rcases Nat.lt_or_ge o₂ f₂ with ho | ho
    · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := o₂) (e := f₂) (s' := f₁)
        (e' := C.length) ho (by omega) (by omega) (by omega) hnb2 hnbf₂ hnbf₁ hnbn
        (hoppXY o₂ f₂ x₂ y₂ ho₂eq hf₂eq hx₂.1 hy₂.1 (by omega))
        (hoppXY f₁ C.length y₁ x₁ hf₁eq (by
          refine ((List.Nodup.getElem_inj_iff hC.2.1).mpr ?_).trans hb₀x
          rw [Nat.add_zero, Nat.add_mod_right]) hy₁.1 hx₁.1 (by omega))
    · rcases Nat.lt_or_ge o₂ f₁ with ho' | ho'
      · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := 0) (e := f₂) (s' := o₂)
          (e' := f₁) (by omega) (by omega) (by omega) (by omega) hnb0 hnbf₂ hnb2 hnbf₁
          (hoppXY 0 f₂ x₁ y₂ hb₀x hf₂eq hx₁.1 hy₂.1 (by omega))
          (hoppXY o₂ f₁ x₂ y₁ ho₂eq hf₁eq hx₂.1 hy₁.1 (by omega))
      · exact wheel_of_two_arcs hBerge hw hvC hvY hvnc hcl b₀ (s := 0) (e := f₂) (s' := f₁)
          (e' := o₂) (by omega) (by omega) (by omega) (by omega) hnb0 hnbf₂ hnbf₁ hnb2
          (hoppXY 0 f₂ x₁ y₂ hb₀x hf₂eq hx₁.1 hy₂.1 (by omega))
          (hoppXY f₁ o₂ y₁ x₂ hf₁eq ho₂eq hy₁.1 hx₂.1 (by omega))

/-! ### The second assertion of 16.1 -/

/-- **The second assertion of 16.1**, from claim (1).

PAPER: *"Moreover, either: `v` has only two neighbours in `C`, and they are adjacent and both
`Y`-complete, or there is a 3-vertex path `p₁-p₂-p₃` in `C`, such that `p₁, p₂, p₃` are all
`Y ∪ {v}`-complete, and every other neighbour of `v` in `C` has the same wheel-parity as `p₁`,
or `(C, Y ∪ {v})` is a wheel."* -/
theorem second_assertion [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V} (hvC : v ∉ C) (hvY : v ∉ Y)
    (hvnc : ¬ VertexComplete G v Y) (hcl : OddWheelSpan.Claim1 G C Y v)
    {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b) :
    (∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ {u : V | u ∈ C ∧ G.Adj v u} = {a₁, a₂} ∧
        G.Adj a₁ a₂ ∧ VertexComplete G a₁ Y ∧ VertexComplete G a₂ Y) ∨
      (∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
          (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
          VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
          VertexComplete G p₃ (Y ∪ {v}) ∧
          ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
      IsWheel G C (Y ∪ {v}) := by
  classical
  have hC : IsHoleList G C := hw.1.1
  have hn6 : 6 ≤ C.length := hw.1.2
  have heven : Even (WheelParity.cycCount G Y C C.length) :=
    WheelBasics.even_cycCount_of_wheel hBerge hw
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hC heven
  have haC : a ∈ C := hab.2.1
  have hbC : b ∈ C := hab.2.2.1
  have hpab : π a ≠ π b := fun he => hab.2.2.2 ((hπ a b haC hbC hab.1).mpr he)
  -- the two bullets that need a singleton wheel-parity class
  have hsingleton : ∀ c : V, c ∈ C → G.Adj v c →
      (∀ u ∈ C, G.Adj v u → u ≠ c → ¬ SameWheelParity G C Y u c) →
      (∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ {u : V | u ∈ C ∧ G.Adj v u} = {a₁, a₂} ∧
          G.Adj a₁ a₂ ∧ VertexComplete G a₁ Y ∧ VertexComplete G a₂ Y) ∨
        (∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
            (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
            VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
            VertexComplete G p₃ (Y ∪ {v}) ∧
            ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) := by
    intro c hcC hvc hsingle
    by_cases hthird : ∃ w, w ∈ C ∧ G.Adj v w ∧ w ≠ a ∧ w ≠ b
    · obtain ⟨w, hwC, hvw, hwa, hwb⟩ := hthird
      exact Or.inr (bullet_two hBerge hw hcl hcC hvc hsingle ⟨haC, hva⟩ ⟨hbC, hvb⟩ ⟨hwC, hvw⟩
        hab.1 (fun he => hwa he.symm) (fun he => hwb he.symm))
    · push Not at hthird
      have honly : ∀ u ∈ C, G.Adj v u → u = a ∨ u = b := by
        intro u huC hvu
        by_cases hua : u = a
        · exact Or.inl hua
        · exact Or.inr (hthird u huC hvu hua)
      obtain ⟨hadj, hca, hcb⟩ := bullet_one hBerge hw hcl hva hvb hab honly
      refine Or.inl ⟨a, b, hab.1, ?_, hadj, hca, hcb⟩
      ext u
      constructor
      · rintro ⟨huC, hvu⟩
        rcases honly u huC hvu with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · rintro (rfl | rfl)
        · exact ⟨haC, hva⟩
        · exact ⟨hbC, hvb⟩
  by_cases hSa : ∃ u, u ∈ C ∧ G.Adj v u ∧ u ≠ a ∧ π u = π a
  · by_cases hSb : ∃ u, u ∈ C ∧ G.Adj v u ∧ u ≠ b ∧ π u = π b
    · obtain ⟨u₁, hu₁C, hvu₁, hu₁a, hpu₁⟩ := hSa
      obtain ⟨u₂, hu₂C, hvu₂, hu₂b, hpu₂⟩ := hSb
      exact Or.inr (Or.inr (bullet_three hBerge hw hvC hvY hvnc hcl π hπ2 hπ
        ⟨haC, hva⟩ ⟨hu₁C, hvu₁⟩ ⟨hbC, hvb⟩ ⟨hu₂C, hvu₂⟩
        (fun he => hu₁a he.symm) (fun he => hu₂b he.symm) hpu₁.symm hpu₂.symm hpab))
    · push Not at hSb
      exact Or.imp_right Or.inl (hsingleton b hbC hvb (by
        intro u huC hvu hub hs
        exact hSb u huC hvu hub ((hπ u b huC hbC hub).mp hs)))
  · push Not at hSa
    exact Or.imp_right Or.inl (hsingleton a haC hva (by
      intro u huC hvu hua hs
      exact hSa u huC hvu hua ((hπ u a huC haC hua).mp hs)))

/-- **16.1, modulo claim (1) of its proof.**

Both conclusions of 16.1, assembled from `OddWheelSpan.first_assertion` and `second_assertion`.
The conclusion is byte-identical to that of `Workspace.Statements.S16.SPGT.thm_16_1`, so all
that stands between this and a proof of 16.1 is a proof of `OddWheelSpan.Claim1`. -/
theorem thm_16_1_of_claim1 [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) {v : V} (hvC : v ∉ C) (hvY : v ∉ Y)
    (hvnc : ¬ VertexComplete G v Y) (hcl : OddWheelSpan.Claim1 G C Y v)
    {a b : V} (hva : G.Adj v a) (hvb : G.Adj v b)
    (hab : OppositeWheelParity G C Y a b) :
    (∀ P : List V, IsPathList G P →
        (∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k) →
        (IsPathFrom G P a b ∨ IsPathFrom G P b a) →
        ∃ x ∈ P, ∃ y ∈ P, EdgeComplete G (Y ∪ {v}) x y) ∧
    ((∃ a₁ a₂ : V, a₁ ≠ a₂ ∧ {u : V | u ∈ C ∧ G.Adj v u} = {a₁, a₂} ∧
          G.Adj a₁ a₂ ∧ VertexComplete G a₁ Y ∧ VertexComplete G a₂ Y) ∨
      (∃ p₁ p₂ p₃ : V, IsPathList G [p₁, p₂, p₃] ∧
          (∃ k : ℕ, [p₁, p₂, p₃] <+: C.rotate k ∨ [p₃, p₂, p₁] <+: C.rotate k) ∧
          VertexComplete G p₁ (Y ∪ {v}) ∧ VertexComplete G p₂ (Y ∪ {v}) ∧
          VertexComplete G p₃ (Y ∪ {v}) ∧
          ∀ u ∈ C, G.Adj v u → u ≠ p₁ → u ≠ p₂ → u ≠ p₃ → SameWheelParity G C Y u p₁) ∨
      IsWheel G C (Y ∪ {v})) :=
  ⟨OddWheelSpan.first_assertion hBerge hw hcl hva hvb hab,
    second_assertion hBerge hw hvC hvY hvnc hcl hva hvb hab⟩

end Workspace.ProofLemmas.OddWheelTrichotomy
