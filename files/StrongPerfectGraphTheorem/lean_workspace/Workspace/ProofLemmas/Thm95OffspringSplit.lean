import Workspace.ProofLemmas.Thm95OffspringDefs
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm114Aux

/-!
# "Every `Tⱼ`-antirung has one end in `U` and the other in `V`"

PAPER (9.5(1), printed p. 52).  The two ends `xⱼ ∈ Xⱼ` and `yⱼ ∈ Yⱼ` of a `Tⱼ`-antirung are each
adjacent to exactly one of `f₁, f_k`; the sentence quoted asserts that they are adjacent to
different ones.

The proof is two holes, according to the length of the antirung `Q` (which is odd).

* If `Q` has length at least `3` and both its ends are adjacent to `f₁`, then in `Ḡ` the vertex
  `f_k` is adjacent to both ends of `Q` and to none of its interior (the interior lies in `Zⱼ`,
  which is complete to `f_k`), so `f_k` together with `Q` is an odd hole of `Ḡ`.

* If `Q` has length `1`, take any rung `a-P-b` of any strip `Sᵢ`.  The strip and `Tⱼ` are
  parallel or co-parallel, so the two ends of `Q` are, in some order, the only neighbours of `a`
  and of `b` on `Q`; and `f₁` has no neighbour on `P`.  So `f₁` together with `Q` and `P` closes
  an odd hole of `G`, of length `|P| + 4`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95OffspringSplit

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The two ends of a rung, read off without destructuring the strip. -/
theorem rung_ends {G : SimpleGraph V} (Sx : Set V × Set V × Set V) (p : List V)
    (hp : IsSRung G Sx p) : ∃ a b : V, IsPathFrom G p a b ∧ a ∈ Sx.1 ∧ b ∈ Sx.2.2 := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨a, b, hpath, ha, hb, -, -, -⟩ := hp
  exact ⟨a, b, hpath, ha, hb⟩

/-- The interior of a rung lies in the middle set of the strip. -/
theorem rung_interior {G : SimpleGraph V} (Sx : Set V × Set V × Set V) (p : List V)
    (hp : IsSRung G Sx p) : ∀ v ∈ SPGT.interior p, v ∈ Sx.2.1 := by
  obtain ⟨A, C, B⟩ := Sx
  obtain ⟨a, b, -, -, -, -, -, hint⟩ := hp
  exact hint

/-- **PAPER (9.5(1), p. 52):** the two ends of a `Tⱼ`-antirung are not adjacent to the same one
of `f₁, f_k`.  Here `t` is that common neighbour and `t'` the other end of `F`. -/
theorem ends_not_same_side {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (j : Fin n) {Q : List V} {x y t t' : V}
    (hQ : IsSRung Gxᶜ (T j) Q) (hQxy : IsPathFrom Gxᶜ Q x y)
    (htF : t ∈ F) (ht'F : t' ∈ F)
    (htx : Gx.Adj t x) (hty : Gx.Adj t y)
    (ht'x : ¬ Gx.Adj t' x) (ht'y : ¬ Gx.Adj t' y)
    (ht'z : ∀ z ∈ (T j).2.1, Gx.Adj t' z) : False := by
  classical
  have hQodd : Odd (pathLength Q) := hL.2.2.2.2.2.2.1 j Q hQ
  have hQmemV : ∀ v ∈ Q, v ∈ stripVertices (T j) := fun v hv =>
    mem_stripVertices_of_mem_srung hQ hv
  have hQmemL : ∀ v ∈ Q, v ∈ striationVertices S T := fun v hv =>
    StriationCompl.stripVertices_T_subset S T j (hQmemV v hv)
  have hxQ : x ∈ Q := (PathBasics.isPathFrom_ends_mem hQxy).1
  have hyQ : y ∈ Q := (PathBasics.isPathFrom_ends_mem hQxy).2
  have hQlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQxy.1
  have hintZ : ∀ v ∈ SPGT.interior Q, v ∈ (T j).2.1 := rung_interior (T j) Q hQ
  by_cases hlen1 : pathLength Q = 1
  · -- The antirung is a single nonedge of `G`; close a hole through a rung of `S i₀`.
    obtain ⟨hm2, -⟩ : 2 ≤ m ∧ 2 ≤ n := ⟨hL.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.1⟩
    let i₀ : Fin m := ⟨0, by omega⟩
    obtain ⟨p, hp⟩ := Thm95GapBasics.exists_rung (hL.1 i₀)
    obtain ⟨a, b, hpab, haA, hbB⟩ := rung_ends (S i₀) p hp
    have hab : a ≠ b := fun h =>
      Set.disjoint_left.mp (Thm95GapBasics.strip_ends_disjoint (hL.1 i₀)) haA (h ▸ hbB)
    obtain ⟨z, hzQ, z', hz'Q, ⟨hazAdj, hzOnly⟩, hbz'Adj, hz'Only⟩ :=
      Thm95GapBasics.rung_anchor (hL.2.2.2.2.2.2.2.2.2.2.2.1 i₀ j) hp hpab hQ
    have hzz' : z ≠ z' := by
      rintro rfl
      exact absurd hbz'Adj (hzOnly b (PathBasics.isPathFrom_ends_mem hpab).2 (Ne.symm hab))
    -- `Q` has exactly the two vertices `x, y`.
    have hQtwo : ∀ v ∈ Q, v = x ∨ v = y := by
      intro v hv
      by_contra hc
      rw [not_or] at hc
      have hvi : v ∈ SPGT.interior Q :=
        (PathBasics.mem_interior_iff_of_pathFrom hQxy).mpr ⟨hv, hc.1, hc.2⟩
      have : (SPGT.interior Q).length = 0 := by
        rw [PathBasics.interior_length]; omega
      rw [List.length_eq_zero_iff] at this
      rw [this] at hvi
      exact absurd hvi (by simp)
    have hxy : ¬ Gx.Adj x y := by
      have h := PathBasics.isPathFrom_ends_adj_of_length_one hQxy hlen1
      exact ((SimpleGraph.compl_adj Gx x y).mp h).2
    have hzz'nadj : ¬ Gx.Adj z z' := by
      rcases hQtwo z hzQ with hz | hz <;> rcases hQtwo z' hz'Q with hz2 | hz2
      · exact absurd (hz.trans hz2.symm) hzz'
      · subst hz; subst hz2; exact hxy
      · subst hz; subst hz2; exact fun hc => hxy hc.symm
      · exact absurd (hz.trans hz2.symm) hzz'
    -- `t` is adjacent to both ends of `Q` and to no vertex of the rung.
    have htz : Gx.Adj t z := by rcases hQtwo z hzQ with rfl | rfl; exacts [htx, hty]
    have htz' : Gx.Adj t z' := by rcases hQtwo z' hz'Q with rfl | rfl; exacts [htx, hty]
    have htp : ∀ v ∈ p, ¬ Gx.Adj t v := fun v hv =>
      hnoS i₀ t htF v (KnotFromTwist.mem_stripVertices_of_isSRung hp hv)
    have hpT : ∀ v ∈ p, v ∉ stripVertices (T j) := fun v hv hvT =>
      Set.disjoint_left.mp (hL.2.2.2.2.1 i₀ j)
        (KnotFromTwist.mem_stripVertices_of_isSRung hp hv) hvT
    have htne : ∀ v ∈ Q, t ≠ v := by
      intro v hv h
      subst h
      exact hFsub htF (hQmemL t hv)
    have htz'ne : t ≠ z' := htne z' hz'Q
    have htzne : t ≠ z := htne z hzQ
    have hR : IsPathFrom Gx [z', t, z] z' z := by
      refine ⟨Thm114Aux.isPathList_three ?_ htz'.symm htz (fun h => hzz'nadj h.symm), rfl, rfl⟩
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        or_false, not_or, and_true]
      exact ⟨⟨Ne.symm htz'ne, Ne.symm hzz'⟩, htzne, not_false⟩
    have hdisj : ∀ u ∈ p, u ∉ [z', t, z] := by
      intro u hu hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact hpT u hu (hQmemV _ hz'Q)
      · exact hFsub htF (StriationCompl.stripVertices_S_subset S T i₀
          (KnotFromTwist.mem_stripVertices_of_isSRung hp hu))
      · exact hpT u hu (hQmemV _ hzQ)
    have hcross : ∀ u ∈ p, ∀ w ∈ [z', t, z],
        (Gx.Adj u w ↔ (u = b ∧ w = z') ∨ (u = a ∧ w = z)) := by
      intro u hu w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl
      · constructor
        · intro hadj
          by_cases hub : u = b
          · exact Or.inl ⟨hub, rfl⟩
          · exact absurd hadj (hz'Only u hu hub)
        · rintro (⟨hub, -⟩ | ⟨-, h⟩)
          · exact hub ▸ hbz'Adj
          · exact absurd h.symm hzz'
      · constructor
        · intro hadj; exact absurd hadj.symm (htp u hu)
        · rintro (⟨-, h⟩ | ⟨-, h⟩)
          · exact absurd h htz'ne
          · exact absurd h htzne
      · constructor
        · intro hadj
          by_cases hua : u = a
          · exact Or.inr ⟨hua, rfl⟩
          · exact absurd hadj (hzOnly u hu hua)
        · rintro (⟨-, h⟩ | ⟨hua, -⟩)
          · exact absurd h.symm (Ne.symm hzz')
          · exact hua ▸ hazAdj
    have hhole : IsHoleList Gx (p ++ [z', t, z]) := by
      refine PathGlue.glue_hole hpab hR hdisj hcross ?_
      have := PathBasics.path_length_pos hpab.1
      simp only [List.length_cons, List.length_nil]
      omega
    have hpodd : Odd (pathLength p) := hL.2.2.2.2.2.1 i₀ p hp
    have hplen : p.length = pathLength p + 1 := PathBasics.length_eq_pathLength_add_one hpab.1
    have heven := hG.1 _ hhole
    rw [holeLength, List.length_append] at heven
    simp only [List.length_cons, List.length_nil] at heven
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at hpodd
    omega
  · -- The antirung is long; close an odd hole of `Ḡ` through `t'`.
    have hQ2 : 2 ≤ pathLength Q := by
      obtain ⟨k, hk⟩ := hQodd
      omega
    have ht'Q : t' ∉ Q := fun h => hFsub ht'F (hQmemL t' h)
    have ht'ne : ∀ v ∈ Q, t' ≠ v := fun v hv h => ht'Q (h ▸ hv)
    have hadjx : Gxᶜ.Adj t' x := (SimpleGraph.compl_adj Gx t' x).mpr ⟨ht'ne x hxQ, ht'x⟩
    have hadjy : Gxᶜ.Adj t' y := (SimpleGraph.compl_adj Gx t' y).mpr ⟨ht'ne y hyQ, ht'y⟩
    have hintno : ∀ v ∈ SPGT.interior Q, ¬ Gxᶜ.Adj t' v := by
      intro v hv hadj
      exact ((SimpleGraph.compl_adj Gx t' v).mp hadj).2 (ht'z v (hintZ v hv))
    have hhole : IsHoleList Gxᶜ (t' :: Q) :=
      PrismBasics.isHoleList_of_path_add_vertex hQxy hQ2 hadjx hadjy ht'Q hintno
    have heven := hG.2 _ hhole
    rw [holeLength] at heven
    simp only [List.length_cons] at heven
    rw [Nat.even_iff] at heven
    rw [Nat.odd_iff] at hQodd
    omega

end Workspace.ProofLemmas.Thm95OffspringSplit
