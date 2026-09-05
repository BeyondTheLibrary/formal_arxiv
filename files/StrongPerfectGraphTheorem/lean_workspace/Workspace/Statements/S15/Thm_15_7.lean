/-  Proof attempt for statement 15.7 of Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem* (printed p. 95).

    PRINTED PROOF (verbatim):

      "Assume that |V(C) ∩ V(D)| ≥ 3; then by taking complements if necessary, we may
       assume that there are three vertices in V(C) ∩ V(D) such that exactly one pair
       of them is adjacent.  Hence we can number the vertices of C as p₁,…,p_m in
       order, and the vertices of D as p₁,q₁,…,q_n,p₂,p_k for some k with 4 ≤ k ≤ m−1.
       (Possibly the hole and antihole also share some fourth vertex.)  Hence the
       antipath p₁-q₁-⋯-q_n-p₂ has length ≥ 4 and even.  The vertex p_k is complete to
       {q₁,…,q_n}, and different from p₃, p_m, contrary to 15.6.  This proves 15.7."

    The Lean proof follows that script literally:

      * `hole_no_triangle`         — a hole has no triangle; this is what rules out
                                     "no pair adjacent" (applied to `D` in `Gᶜ`) and
                                     "all three pairs adjacent" (applied to `C` in `G`),
                                     so exactly one or exactly two pairs are adjacent.
      * the eight-way case split   — "by taking complements if necessary": when two pairs
                                     are adjacent we pass to `Gᶜ`, where `C` and `D` swap
                                     roles and exactly one pair is adjacent.
      * `exists_rotate_adj_pair`   — "we can number the vertices of C as p₁,…,p_m in order"
                                     with the adjacent pair first.
      * `antipath_through`         — "the vertices of D as p₁,q₁,…,q_n,p₂,p_k": deleting
                                     `p_k` from the antihole leaves the antipath
                                     `p₁-q₁-⋯-q_n-p₂`.
      * evenness of `|V(D)|`       — "has length ≥ 4 and even".
      * `thm_15_6`                 — "The vertex p_k is complete to {q₁,…,q_n}, and
                                     different from p₃, p_m, contrary to 15.6."
-/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.HoleMinusVertexPath
import Workspace.Statements.S15.Thm_15_6

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Cyclic index arithmetic -/

private theorem succ_mod_eq157 {n i : ℕ} (hi : i < n) :
    (i + 1) % n = if i + 1 = n then 0 else i + 1 := by
  by_cases h : i + 1 = n
  · simp [h]
  · rw [if_neg h, Nat.mod_eq_of_lt (by omega)]

/-- A cycle of length `≥ 4` has no triangle: three pairwise distinct indices cannot be
pairwise cyclically consecutive. -/
private theorem no_tri_arith157 {n i j k : ℕ} (h4 : 4 ≤ n) (hi : i < n) (hj : j < n)
    (hk : k < n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (e1 : j = (i + 1) % n ∨ i = (j + 1) % n)
    (e2 : k = (j + 1) % n ∨ j = (k + 1) % n)
    (e3 : k = (i + 1) % n ∨ i = (k + 1) % n) : False := by
  rw [succ_mod_eq157 hi, succ_mod_eq157 hj] at e1
  rw [succ_mod_eq157 hj, succ_mod_eq157 hk] at e2
  rw [succ_mod_eq157 hi, succ_mod_eq157 hk] at e3
  split_ifs at e1 e2 e3 <;> omega

/-- **No triangle on a hole.**  Used twice: on `C` in `G` (three vertices of a hole are
never pairwise adjacent) and on `D` in `Gᶜ` (three vertices of an antihole are never
pairwise non-adjacent). -/
private theorem hole_no_triangle {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    {x y z : V} (hx : x ∈ C) (hy : y ∈ C) (hz : z ∈ C)
    (hxy : G.Adj x y) (hyz : G.Adj y z) (hxz : G.Adj x z) : False := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  obtain ⟨k, hk, hkz⟩ := List.getElem_of_mem hz
  subst hix; subst hjy; subst hkz
  refine no_tri_arith157 hC.1 hi hj hk ?_ ?_ ?_
    ((HoleBasics.hole_adj_iff hC hi hj).mp hxy)
    ((HoleBasics.hole_adj_iff hC hj hk).mp hyz)
    ((HoleBasics.hole_adj_iff hC hi hk).mp hxz)
  · rintro rfl; exact G.irrefl hxy
  · rintro rfl; exact G.irrefl hxz
  · rintro rfl; exact G.irrefl hyz

/-! ### "we can number the vertices of `C` as `p₁, …, p_m` in order" -/

/-- Two adjacent vertices of a hole can be rotated to positions `0` and `1` (in one of
the two orders). -/
private theorem exists_rotate_adj_pair {G : SimpleGraph V} {C : List V}
    (hC : IsHoleList G C) {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hxy : G.Adj x y) :
    ∃ r : ℕ, ∀ (h0 : 0 < (C.rotate r).length) (h1 : 1 < (C.rotate r).length),
      (((C.rotate r)[0]'h0) = x ∧ ((C.rotate r)[1]'h1) = y) ∨
        (((C.rotate r)[0]'h0) = y ∧ ((C.rotate r)[1]'h1) = x) := by
  obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
  obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
  subst hix; subst hjy
  rcases (HoleBasics.hole_adj_iff hC hi hj).mp hxy with h | h
  · refine ⟨i, fun h0 h1 => Or.inl ⟨?_, ?_⟩⟩
    · simp only [List.getElem_rotate]
      exact HoleArithmetic.getElem_congr_idx C _ hi
        (by rw [Nat.zero_add, Nat.mod_eq_of_lt hi])
    · simp only [List.getElem_rotate]
      exact HoleArithmetic.getElem_congr_idx C _ hj (by rw [Nat.add_comm]; exact h.symm)
  · refine ⟨j, fun h0 h1 => Or.inr ⟨?_, ?_⟩⟩
    · simp only [List.getElem_rotate]
      exact HoleArithmetic.getElem_congr_idx C _ hj
        (by rw [Nat.zero_add, Nat.mod_eq_of_lt hj])
    · simp only [List.getElem_rotate]
      exact HoleArithmetic.getElem_congr_idx C _ hi (by rw [Nat.add_comm]; exact h.symm)

/-! ### "the vertices of `D` as `p₁, q₁, …, q_n, p₂, p_k`" -/

/-- Deleting a vertex `z` from a hole leaves a path joining the two neighbours `a`, `b`
of `z` on the hole, whose interior consists of vertices of the hole distinct from `z`
and non-adjacent to `z`. -/
private theorem antipath_through {K : SimpleGraph V} {D : List V} (hD : IsHoleList K D)
    (h5 : 5 ≤ D.length) {z a b : V} (hzD : z ∈ D) (haD : a ∈ D) (hbD : b ∈ D)
    (hab : a ≠ b) (hza : K.Adj z a) (hzb : K.Adj z b) :
    ∃ Q : List V, IsPathFrom K Q a b ∧ Q.length = D.length - 1 ∧
      ∀ u ∈ SPGT.interior Q, u ∈ D ∧ u ≠ z ∧ ¬ K.Adj z u := by
  obtain ⟨r, hr⟩ := HoleArithmetic.exists_rotate_head hzD
  have hR : IsHoleList K (D.rotate r) := HoleBasics.isHoleList_rotate hD r
  have hRlen : (D.rotate r).length = D.length := by simp
  have hR5 : 5 ≤ (D.rotate r).length := by omega
  have hR0 : ((D.rotate r)[0]'(by omega)) = z := hr (by omega)
  have hmemR : ∀ u : V, u ∈ D.rotate r ↔ u ∈ D := fun u => List.mem_rotate
  -- the two neighbours of `z` on the hole are its cyclic predecessor and successor
  obtain ⟨ia, hia, hiaa⟩ := List.getElem_of_mem ((hmemR a).mpr haD)
  obtain ⟨ib, hib, hibb⟩ := List.getElem_of_mem ((hmemR b).mpr hbD)
  have hca : ia = 1 ∨ ia = (D.rotate r).length - 1 := by
    refine (HoleMinusVertexPath.adj_head_iff hR hR5 hia).mp ?_
    rw [hR0, hiaa]; exact hza
  have hcb : ib = 1 ∨ ib = (D.rotate r).length - 1 := by
    refine (HoleMinusVertexPath.adj_head_iff hR hR5 hib).mp ?_
    rw [hR0, hibb]; exact hzb
  have hiab : ia ≠ ib := by
    intro h
    apply hab
    rw [← hiaa, ← hibb]
    exact HoleArithmetic.getElem_congr_idx (D.rotate r) hia hib h
  -- the interior of the deleted hole
  have hint : ∀ u ∈ SPGT.interior (D.rotate r).tail, u ∈ D ∧ u ≠ z ∧ ¬ K.Adj z u := by
    intro u hu
    obtain ⟨huR, hu0, hu1, hu2⟩ :=
      (HoleMinusVertexPath.mem_interior_tail_iff hR hR5 u).mp hu
    refine ⟨(hmemR u).mp huR, ?_, ?_⟩
    · rw [← hR0]; exact hu0
    · intro hadj
      obtain ⟨m, hm, hmu⟩ := List.getElem_of_mem huR
      have : m = 1 ∨ m = (D.rotate r).length - 1 := by
        refine (HoleMinusVertexPath.adj_head_iff hR hR5 hm).mp ?_
        rw [hR0, hmu]; exact hadj
      rcases this with h | h
      · exact hu1 (by rw [← hmu]; exact HoleArithmetic.getElem_congr_idx _ hm (by omega) h)
      · exact hu2 (by rw [← hmu]; exact HoleArithmetic.getElem_congr_idx _ hm (by omega) h)
  have htailpath := HoleMinusVertexPath.isPathFrom_tail hR hR5
  have htaillen : (D.rotate r).tail.length = D.length - 1 := by
    simp only [List.length_tail]; omega
  rcases hca with h1 | h1
  · -- `a` is the successor of `z`, `b` the predecessor
    have h2 : ib = (D.rotate r).length - 1 := by omega
    have ea : ((D.rotate r)[1]'(by omega)) = a := by
      refine Eq.trans ?_ hiaa
      exact HoleArithmetic.getElem_congr_idx _ (by omega) hia h1.symm
    have eb : ((D.rotate r)[(D.rotate r).length - 1]'(by omega)) = b := by
      refine Eq.trans ?_ hibb
      exact HoleArithmetic.getElem_congr_idx _ (by omega) hib h2.symm
    refine ⟨(D.rotate r).tail, ?_, htaillen, hint⟩
    rw [← ea, ← eb]
    exact htailpath
  · -- `b` is the successor of `z`, `a` the predecessor
    have h2 : ib = 1 := by omega
    have ea : ((D.rotate r)[(D.rotate r).length - 1]'(by omega)) = a := by
      refine Eq.trans ?_ hiaa
      exact HoleArithmetic.getElem_congr_idx _ (by omega) hia h1.symm
    have eb : ((D.rotate r)[1]'(by omega)) = b := by
      refine Eq.trans ?_ hibb
      exact HoleArithmetic.getElem_congr_idx _ (by omega) hib h2.symm
    refine ⟨(D.rotate r).tail.reverse, ?_, by rw [List.length_reverse]; exact htaillen, ?_⟩
    · rw [← ea, ← eb]
      exact PathBasics.isPathFrom_reverse htailpath
    · intro u hu
      exact hint u (PathBasics.mem_interior_reverse.mp hu)

/-! ### The heart of the printed argument -/

/-- The printed proof, once the numbering has been fixed: `a = p₁`, `b = p₂` are the
adjacent pair at the front of the hole `C`, and `z = p_k` is the third shared vertex. -/
private theorem core (G : SimpleGraph V) (hG : InF6 G) (C D : List V)
    (hC : IsHoleList G C) (hCn : 6 ≤ C.length)
    (hD : IsHoleList Gᶜ D) (hDn : 6 ≤ D.length) (hDeven : Even D.length)
    (a b z : V)
    (ha : ∀ h : 0 < C.length, ((C)[0]'h) = a)
    (hb : ∀ h : 1 < C.length, ((C)[1]'h) = b)
    (hab : G.Adj a b) (haD : a ∈ D) (hbD : b ∈ D)
    (hzC : z ∈ C) (hzD : z ∈ D)
    (haz : ¬ G.Adj a z) (hbz : ¬ G.Adj b z)
    (hza : z ≠ a) (hzb : z ≠ b) : False := by
  -- `z` is `Gᶜ`-adjacent to both `a` and `b`
  have hcza : Gᶜ.Adj z a := by
    rw [SimpleGraph.compl_adj]; exact ⟨hza, fun h => haz h.symm⟩
  have hczb : Gᶜ.Adj z b := by
    rw [SimpleGraph.compl_adj]; exact ⟨hzb, fun h => hbz h.symm⟩
  -- "the vertices of D as p₁, q₁, …, q_n, p₂, p_k": delete `p_k = z` from the antihole
  obtain ⟨Q, hQ, hQlen, hQint⟩ :=
    antipath_through hD (by omega) hzD haD hbD hab.ne hcza hczb
  -- "has length ≥ 4 and even"
  have hQlen4 : 4 ≤ pathLength Q := by simp only [pathLength]; omega
  have hQeven : Even (pathLength Q) := by
    obtain ⟨t, ht⟩ := hDeven
    exact ⟨t - 1, by simp only [pathLength]; omega⟩
  have hQanti : IsAntipathFrom G Q ((C)[0]'(by omega)) ((C)[1]'(by omega)) := by
    rw [ha, hb]; exact hQ
  -- `p_k ∈ {p₃, …, p_m}`
  have hzdrop : z ∈ C.drop 2 := by
    obtain ⟨k, hk, hkz⟩ := List.getElem_of_mem hzC
    have hk0 : k ≠ 0 := by
      rintro rfl; exact hza (hkz.symm.trans (ha hk))
    have hk1 : k ≠ 1 := by
      rintro rfl; exact hzb (hkz.symm.trans (hb hk))
    have hlen2 : k - 2 < (C.drop 2).length := by
      simp only [List.length_drop]; omega
    have hget : ((C.drop 2)[k - 2]'hlen2) = z := by
      rw [List.getElem_drop]
      exact (HoleArithmetic.getElem_congr_idx C _ hk (by omega)).trans hkz
    exact hget ▸ List.getElem_mem hlen2
  -- "The vertex p_k is complete to {q₁, …, q_n}"
  have hcomplete : VertexComplete G z {x : V | x ∈ (SPGT.interior Q).dropLast} := by
    intro u hu
    have hu' : u ∈ SPGT.interior Q := List.dropLast_subset _ hu
    obtain ⟨-, hune, hunadj⟩ := hQint u hu'
    rw [SimpleGraph.compl_adj] at hunadj
    push_neg at hunadj
    exact hunadj (Ne.symm hune)
  -- "contrary to 15.6"
  obtain ⟨-, h2⟩ :=
    thm_15_6 G hG C C.length hC rfl (by omega) Q hQanti hQlen4 hQeven
  rcases h2 z hzdrop (Or.inl hcomplete) with h | h
  · -- "different from p₃"
    apply hbz
    rw [h, ← hb (by omega)]
    exact HoleBasics.hole_adj_succ hC (by omega)
  · -- "different from p_m"
    apply haz
    rw [h, ← ha (by omega)]
    exact (HoleBasics.hole_adj_wrap hC).symm

/-- `core` with the numbering of the hole `C` still to be chosen. -/
private theorem key (G : SimpleGraph V) (hG : InF6 G) (C D : List V)
    (hC : IsHoleList G C) (hCn : 6 ≤ C.length)
    (hD : IsHoleList Gᶜ D) (hDn : 6 ≤ D.length) (hDeven : Even D.length)
    (a b z : V) (haC : a ∈ C) (hbC : b ∈ C) (hzC : z ∈ C)
    (haD : a ∈ D) (hbD : b ∈ D) (hzD : z ∈ D)
    (hab : G.Adj a b) (haz : ¬ G.Adj a z) (hbz : ¬ G.Adj b z)
    (hza : z ≠ a) (hzb : z ≠ b) : False := by
  obtain ⟨r, hr⟩ := exists_rotate_adj_pair hC haC hbC hab
  have hCr : IsHoleList G (C.rotate r) := HoleBasics.isHoleList_rotate hC r
  have hlen : (C.rotate r).length = C.length := by simp
  have hzr : z ∈ C.rotate r := List.mem_rotate.mpr hzC
  rcases hr (by omega) (by omega) with ⟨e0, e1⟩ | ⟨e0, e1⟩
  · exact core G hG (C.rotate r) D hCr (by omega) hD hDn hDeven a b z
      (fun _ => e0) (fun _ => e1) hab haD hbD hzr hzD haz hbz hza hzb
  · exact core G hG (C.rotate r) D hCr (by omega) hD hDn hDeven b a z
      (fun _ => e0) (fun _ => e1) hab.symm hbD haD hzr hzD hbz haz hzb hza

/-- **15.7** (printed p. 95)

PAPER: *"Let `G ∈ F₆`.  Let `C` be a hole of length `> 4` and `D` an antihole of length `> 4`.
Then `|V(C) ∩ V(D)| ≤ 2`."*

Transcription notes.

* The hole `C` and the antihole `D` are given as the lists of their vertices in cyclic order;
  `V(C)` is `{w | w ∈ C}` and the *length* of either is its number of vertices,
  `holeLength = List.length`.
* `|V(C) ∩ V(D)|` is `Set.ncard` of the intersection (honest here: the ambient vertex type is
  a `Fintype`). -/
theorem thm_15_7 (G : SimpleGraph V) (hG : InF6 G)
    (C D : List V)
    (hC : IsHoleList G C) (hCl : 4 < holeLength C)
    (hD : IsAntiholeList G D) (hDl : 4 < holeLength D) :
    ({w : V | w ∈ C} ∩ {w : V | w ∈ D}).ncard ≤ 2 := by
  have hBerge : Berge G := hG.1.1.1
  have hCeven : Even C.length := by
    have := hBerge.1 C hC; simpa [holeLength] using this
  have hDeven : Even D.length := by
    have := hBerge.2 D hD; simpa [holeLength] using this
  have hCn : 6 ≤ C.length := by
    obtain ⟨t, ht⟩ := hCeven
    simp only [holeLength] at hCl
    omega
  have hDn : 6 ≤ D.length := by
    obtain ⟨t, ht⟩ := hDeven
    simp only [holeLength] at hDl
    omega
  have hG' : InF6 Gᶜ := ClassLemmas.inF6_compl.mpr hG
  have hCc : IsHoleList (Gᶜ)ᶜ C := by rw [compl_compl]; exact hC
  have hDc : IsHoleList Gᶜ D := hD
  -- "Assume that |V(C) ∩ V(D)| ≥ 3"
  by_contra hcon
  have hfin : ({w : V | w ∈ C} ∩ {w : V | w ∈ D}).Finite := Set.toFinite _
  obtain ⟨x, y, z, hxs, hys, hzs, hxy', hxz', hyz'⟩ :=
    (Set.two_lt_ncard_iff hfin).mp (by omega)
  have hxC : x ∈ C := hxs.1
  have hxD : x ∈ D := hxs.2
  have hyC : y ∈ C := hys.1
  have hyD : y ∈ D := hys.2
  have hzC : z ∈ C := hzs.1
  have hzD : z ∈ D := hzs.2
  have cadj : ∀ {u v : V}, u ≠ v → ¬ G.Adj u v → Gᶜ.Adj u v := by
    intro u v h1 h2; rw [SimpleGraph.compl_adj]; exact ⟨h1, h2⟩
  have cnadj : ∀ {u v : V}, G.Adj u v → ¬ Gᶜ.Adj u v := by
    intro u v h hc; rw [SimpleGraph.compl_adj] at hc; exact hc.2 h
  -- "there are three vertices … such that exactly one pair of them is adjacent",
  -- after "taking complements if necessary"
  by_cases hxy : G.Adj x y
  · by_cases hxz : G.Adj x z
    · by_cases hyz : G.Adj y z
      · exact hole_no_triangle hC hxC hyC hzC hxy hyz hxz
      · -- in `Gᶜ`: only the pair `y, z` is adjacent
        exact key Gᶜ hG' D C hDc hDn hCc hCn hCeven y z x
          hyD hzD hxD hyC hzC hxC (cadj hyz' hyz) (cnadj hxy.symm) (cnadj hxz.symm)
          hxy' hxz'
    · by_cases hyz : G.Adj y z
      · -- in `Gᶜ`: only the pair `x, z` is adjacent
        exact key Gᶜ hG' D C hDc hDn hCc hCn hCeven x z y
          hxD hzD hyD hxC hzC hyC (cadj hxz' hxz) (cnadj hxy) (cnadj hyz.symm)
          (Ne.symm hxy') hyz'
      · -- only the pair `x, y` is adjacent
        exact key G hG C D hC hCn hDc hDn hDeven x y z
          hxC hyC hzC hxD hyD hzD hxy hxz hyz (Ne.symm hxz') (Ne.symm hyz')
  · by_cases hxz : G.Adj x z
    · by_cases hyz : G.Adj y z
      · -- in `Gᶜ`: only the pair `x, y` is adjacent
        exact key Gᶜ hG' D C hDc hDn hCc hCn hCeven x y z
          hxD hyD hzD hxC hyC hzC (cadj hxy' hxy) (cnadj hxz) (cnadj hyz)
          (Ne.symm hxz') (Ne.symm hyz')
      · -- only the pair `x, z` is adjacent
        exact key G hG C D hC hCn hDc hDn hDeven x z y
          hxC hzC hyC hxD hzD hyD hxz hxy (fun h => hyz h.symm) (Ne.symm hxy') hyz'
    · by_cases hyz : G.Adj y z
      · -- only the pair `y, z` is adjacent
        exact key G hG C D hC hCn hDc hDn hDeven y z x
          hyC hzC hxC hyD hzD hxD hyz (fun h => hxy h.symm) (fun h => hxz h.symm)
          hxy' hxz'
      · -- no pair adjacent: a triangle of the antihole `D` in `Gᶜ`
        exact hole_no_triangle hDc hxD hyD hzD (cadj hxy' hxy) (cadj hyz' hyz)
          (cadj hxz' hxz)

end SPGT

end Workspace.Statements.S15
