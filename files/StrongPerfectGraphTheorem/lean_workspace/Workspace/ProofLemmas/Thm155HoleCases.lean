import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.HoleArc
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm155SixHoleEndgame
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S13.Thm_13_6

/-!
# 15.5 — the two cases of the printed proof

PAPER (printed p. 96, proof of 15.5): *"The claim is trivial if `C` has length 4,
so we assume it has length `≥ 6`.  Let the vertices of `C` be `p₁,…,pₙ` in order,
and let `P` be `p₁-⋯-p_k` say, where `3 ≤ k < n`.  Assume `k` is even.  Then by
13.6 applied to `P` we deduce that `P` has length 3, so `k = 4`.  By 2.2 every
`X`-complete vertex is adjacent to one of `p₂,p₃`, so there are none in the
interior of the odd path `p₄-p₅-⋯-pₙ-p₁`.  By 13.6 this path also has length 3, so
`n = 6`.  Let `Q` be the shortest antipath with interior in `X`, joining either
`p₂,p₃` or `p₅,p₆`.  From the symmetry we may assume its vertices are
`p₂-q₁-⋯-q_m-p₃` say.  Then `Q` is odd since it can be completed to an antihole via
`p₃-p₁-p₄-p₂`; and since `p₅-p₂-Q-p₃-p₅` is therefore not an antihole, it follows
that `p₅` (and similarly `p₆`) has a nonneighbour in the interior of `Q`.  From the
choice of `Q` it follows that `p₅, p₆` both have exactly one nonneighbour in the
interior of `Q`; one is nonadjacent to `q₁` and the other to `q_m`.  Suppose that
`m > 2`.  If `p₅` is nonadjacent to `q₁` then the three antipaths `q₁-⋯-q_m`,
`p₅-p₃`, `p₂-p₆` form a long prism in `G`, contrary to `G ∈ F₆`; while if `p₅` is
nonadjacent to `q_m` then `q₁-⋯-q_m`, `p₆-p₃`, `p₂-p₅` form a long prism, again a
contradiction.  So `m = 2`.  But then `G|{p₁-⋯-p₆, q₁, q₂}` is `L(K₃,₃ \ e)` if
`p₅` is nonadjacent to `q₁`, and a double diamond if `p₅` is nonadjacent to `q₂`,
again contrary to `G ∈ F₆`.  This proves 15.5."*

The printed proof opens by splitting on the length of the hole.  Since `G ∈ F₆` is
Berge, `holeLength C` is even and at least `4`, so the split *"length 4"* /
*"length `≥ 6`"* is exhaustive; that bookkeeping is the assembly, in
`Workspace.Statements.S15.Thm_15_5`.  This module carries the two branches.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm155HoleCases

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"The claim is trivial if `C` has length 4"*: a path in a hole of length `4`
that has length `> 1` must be the three-vertex path, of length `2`. -/
theorem even_of_holeLength_four (G : SimpleGraph V)
    (C : List V) (hC : IsHoleList G C) (h4 : holeLength C = 4)
    (P : List V) (hP : IsPathList G P)
    (hPC : ∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k)
    (hPlen : 1 < pathLength P) :
    Even (pathLength P) := by
  obtain ⟨k, hk⟩ := hPC
  have hDhole : IsHoleList G (C.rotate k) :=
    Workspace.ProofLemmas.HoleBasics.isHoleList_rotate hC k
  have hDlen : (C.rotate k).length = 4 := by rw [List.length_rotate]; exact h4
  have hPl : pathLength P = P.length - 1 := rfl
  have hP3 : 3 ≤ P.length := by omega
  have main : ∀ R : List V, IsPathList G R → R <+: C.rotate k → R.length = P.length →
      P.length = 3 := by
    intro R hR hpre hlen
    have hle : R.length ≤ (C.rotate k).length := hpre.length_le
    by_contra hne
    have hR4 : R.length = 4 := by omega
    have hRD : R = C.rotate k := hpre.eq_of_length (by omega)
    subst hRD
    exact Workspace.ProofLemmas.PathBasics.path_ends_not_adj hR (by omega)
      (Workspace.ProofLemmas.HoleBasics.hole_adj_wrap hDhole).symm
  have h3 : P.length = 3 := by
    rcases hk with hk | hk
    · exact main P hP hk rfl
    · exact main P.reverse (Workspace.ProofLemmas.PathBasics.isPathList_reverse hP) hk (by simp)
  have h2 : pathLength P = 2 := by omega
  rw [h2]
  exact even_two

private theorem no_complete_edge_of_interior_not_complete {G : SimpleGraph V}
    {P : List V} {u v : V} {X : Set V} (hP : IsPathFrom G P u v)
    (hPlen : 1 < pathLength P)
    (hint : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w X) :
    ¬ ∃ a ∈ P, ∃ b ∈ P, EdgeComplete G X a b := by
  rintro ⟨a, ha, b, hb, hab, hca, hcb⟩
  have hia : a ∉ SPGT.interior P := fun h => hint a h hca
  have hib : b ∉ SPGT.interior P := fun h => hint b h hcb
  have hea : a = u ∨ a = v := by
    by_contra hn
    push Not at hn
    exact hia ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨ha, hn.1, hn.2⟩)
  have heb : b = u ∨ b = v := by
    by_contra hn
    push Not at hn
    exact hib ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hb, hn.1, hn.2⟩)
  have hlen : 3 ≤ P.length := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hPlen
    omega
  have h0 : P[0]'(by omega) = u :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hn : P[P.length - 1]'(by omega) = v :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hends : ¬ G.Adj u v := by
    rw [← h0, ← hn]
    exact Workspace.ProofLemmas.PathBasics.path_ends_not_adj hP.1 hlen
  rcases hea with rfl | rfl <;> rcases heb with rfl | rfl
  · exact G.irrefl hab
  · exact hends hab
  · exact hends hab.symm
  · exact G.irrefl hab

/-- The main argument after choosing the orientation of the hole for which `P`
is an initial segment. -/
private theorem even_of_prefix_ge_six (G : SimpleGraph V) (hG : InF6 G)
    (D : List V) (hD : IsHoleList G D) (h6 : 6 ≤ holeLength D)
    (X : Set V) (hXD : ∀ x ∈ X, x ∉ D) (hXanti : AnticonnectedSet G X)
    (P : List V) (u v : V) (hP : IsPathFrom G P u v) (hpre : P <+: D)
    (hPlen : 1 < pathLength P)
    (hu : VertexComplete G u X) (hv : VertexComplete G v X)
    (hint : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w X) :
    Even (pathLength P) := by
  classical
  by_contra hnotEven
  have hPodd : Odd (pathLength P) := Nat.not_even_iff_odd.mp hnotEven
  have hXP : X ⊆ {w : V | w ∈ P}ᶜ := by
    intro x hxX hxP
    exact hXD x hxX (hpre.subset hxP)
  have hnoedge : ¬ ∃ a ∈ P, ∃ b ∈ P, EdgeComplete G X a b :=
    no_complete_edge_of_interior_not_complete hP hPlen hint
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6
      G hG.1 P u v hP hPodd X hXP hXanti hu hv with
    hedge | ⟨hP3, c, d, hcd, Q₁, hQ₁, -, hQ₁int⟩
  · exact hnoedge hedge
  have hP4 : P.length = 4 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hP3
    omega
  obtain ⟨p₀, p₁, p₂, p₃, hPeq⟩ := Workspace.ProofLemmas.PrismBasics.length_eq_four hP4
  have hPint : SPGT.interior P = [p₁, p₂] := by rw [hPeq]; rfl
  have hcd' : p₁ = c ∧ p₂ = d := by
    have : ([p₁, p₂] : List V) = [c, d] := by rw [← hPint, hcd]
    simpa using this
  obtain ⟨rfl, rfl⟩ := hcd'
  have hu₀ : u = p₀ := by
    have hh := hP.2.1
    rw [hPeq] at hh
    simpa using hh.symm
  have hv₃ : v = p₃ := by
    have hh := hP.2.2
    rw [hPeq] at hh
    simpa using hh.symm
  have hp₀X : VertexComplete G p₀ X := by simpa [hu₀] using hu
  have hp₃X : VertexComplete G p₃ X := by simpa [hv₃] using hv
  obtain ⟨T, hPT⟩ := hpre
  have hDshape : D = [p₀, p₁, p₂, p₃] ++ T := by
    rw [← hPT, hPeq]
  have hDlen : D.length = T.length + 4 := by simp [hDshape]
  have h6len : 6 ≤ D.length := by simpa [holeLength] using h6
  have hT2 : 2 ≤ T.length := by
    omega
  let R := (D.rotate 3).take (D.length - 2)
  have hRshape : R = p₃ :: (T ++ [p₀]) := by
    have hlit :
        (([p₀, p₁, p₂, p₃] ++ T).rotate 3).take
            (([p₀, p₁, p₂, p₃] ++ T).length - 2) =
          p₃ :: (T ++ [p₀]) := by
      have hrot :
          ([p₀, p₁, p₂, p₃] ++ T).rotate 3 =
            p₃ :: (T ++ [p₀, p₁, p₂]) := by
        rw [List.rotate_eq_drop_append_take]
        · simp
        · simp
      rw [hrot]
      have hlen :
          ([p₀, p₁, p₂, p₃] ++ T).length - 2 = T.length + 2 := by
        simp
      rw [hlen]
      simp [List.take_append]
    simpa only [R, hDshape] using hlit
  have hDr : IsHoleList G (D.rotate 3) :=
    Workspace.ProofLemmas.HoleBasics.isHoleList_rotate hD 3
  have hRlist : IsPathList G R := by
    dsimp [R]
    apply Workspace.ProofLemmas.HoleArc.hole_take_isPathList hDr
    · omega
    · rw [List.length_rotate]
      omega
  have hR : IsPathFrom G R p₃ p₀ := by
    refine ⟨hRlist, ?_, ?_⟩
    · rw [hRshape]
      simp
    · rw [hRshape]
      change ((p₃ :: T) ++ [p₀]).getLast? = some p₀
      exact List.getLast?_concat
  have hRint : SPGT.interior R = T := by
    rw [hRshape]
    simp [Workspace.Types.Core.SPGT.interior]
  have hDeven : Even D.length := by
    simpa [holeLength] using (hG.1.1.1).1 D hD
  have hRodd : Odd (pathLength R) := by
    have hlenR : pathLength R = T.length + 1 := by
      rw [hRshape, Workspace.ProofLemmas.PathBasics.pathLength_eq]
      simp
    rw [hlenR]
    rcases hDeven with ⟨k, hk⟩
    refine ⟨k - 2, ?_⟩
    omega
  have hRX : X ⊆ {w : V | w ∈ R}ᶜ := by
    intro x hxX hxR
    apply hXD x hxX
    have hxrot : x ∈ D.rotate 3 := List.mem_of_mem_take (by simpa [R] using hxR)
    exact List.mem_rotate.mp hxrot

  -- A vertex of the complementary arc cannot see either internal vertex of `P`.
  have hTnot : ∀ w ∈ T, ¬ G.Adj w p₁ ∧ ¬ G.Adj w p₂ := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
    have hi : 4 + j < D.length := by omega
    have h1 : 1 < D.length := by omega
    have h2 : 2 < D.length := by omega
    have hget (i : ℕ) (hi' : i < T.length) :
        D[4 + i]'(by omega) = T[i]'hi' := by
      calc
        D[4 + i]'(by omega) =
            ([p₀, p₁, p₂, p₃] ++ T)[4 + i]'(by simp; omega) :=
          getElem_congr hDshape rfl (by omega)
        _ = T[i]'hi' := by
          rw [List.getElem_append_right (by simp)]
          congr 1
          norm_num
    have hp1get : D[1]'h1 = p₁ :=
      (getElem_congr hDshape rfl h1).trans (by simp)
    have hp2get : D[2]'h2 = p₂ :=
      (getElem_congr hDshape rfl h2).trans (by simp)
    constructor
    · intro ha
      have hh := (Workspace.ProofLemmas.HoleBasics.hole_adj_iff hD hi h1).mp (by
        rw [hget j hj, hp1get]
        exact ha)
      by_cases he : 4 + j + 1 = D.length
      · rw [he, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hh
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hh
        omega
    · intro ha
      have hh := (Workspace.ProofLemmas.HoleBasics.hole_adj_iff hD hi h2).mp (by
        rw [hget j hj, hp2get]
        exact ha)
      by_cases he : 4 + j + 1 = D.length
      · rw [he, Nat.mod_self, Nat.mod_eq_of_lt (by omega)] at hh
        omega
      · rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hh
        omega

  have hPdisj : ∀ w ∈ P, w ∉ X := by
    intro w hw hwX
    exact hXP hwX hw
  have h22 := _root_.Workspace.Statements.S02.SPGT.thm_2_2
    G hG.1.1.1 X hXanti P u v hP hPdisj hPodd hu hv hnoedge
  have hintR : ∀ w ∈ SPGT.interior R, ¬ VertexComplete G w X := by
    intro w hw hcomplete
    have hwT : w ∈ T := by simpa [hRint] using hw
    obtain ⟨z, hz, hwz⟩ := h22 w hcomplete
    rw [hPint] at hz
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl
    · exact (hTnot w hwT).1 hwz
    · exact (hTnot w hwT).2 hwz
  have hRlen : 1 < pathLength R := by
    rw [hRshape, Workspace.ProofLemmas.PathBasics.pathLength_eq]
    simp
    omega
  have hRnoedge : ¬ ∃ a ∈ R, ∃ b ∈ R, EdgeComplete G X a b :=
    no_complete_edge_of_interior_not_complete hR hRlen hintR
  rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6
      G hG.1 R p₃ p₀ hR hRodd X hRX hXanti hp₃X hp₀X with
    hedge | ⟨hR3, c, d, hcd, Q₂, hQ₂, -, hQ₂int⟩
  · exact hRnoedge hedge
  have hTlen : T.length = 2 := by
    rw [hRshape, Workspace.ProofLemmas.PathBasics.pathLength_eq] at hR3
    simp at hR3
    omega
  obtain ⟨p₄, p₅, hTeq⟩ := Workspace.ProofLemmas.PathGlue.length_eq_two hTlen
  have hcd' : p₄ = c ∧ p₅ = d := by
    have hh : ([p₄, p₅] : List V) = [c, d] := by
      rw [← hTeq, ← hRint, hcd]
    simpa using hh
  obtain ⟨rfl, rfl⟩ := hcd'
  have hD6 : D.length = 6 := by omega
  let p : Fin 6 → V := fun i => D[i.val]'(by omega)
  have hp_inj : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    exact (List.Nodup.getElem_inj_iff hD.2.1).mp hij
  have hp_adj : ∀ i j, G.Adj (p i) (p j) ↔
      (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6) := by
    intro i j
    simpa [p, hD6] using hD.2.2 i.val j.val (by omega) (by omega)
  have hpX : ∀ i, p i ∉ X := by
    intro i hiX
    exact hXD _ hiX (List.getElem_mem (by omega))
  have hp0 : p 0 = p₀ := by simp [p, hDshape]
  have hp1 : p 1 = p₁ := by simp [p, hDshape]
  have hp2 : p 2 = p₂ := by simp [p, hDshape]
  have hp3 : p 3 = p₃ := by simp [p, hDshape]
  have hp4 : p 4 = p₄ := by simp [p, hDshape, hTeq]
  have hp5 : p 5 = p₅ := by simp [p, hDshape, hTeq]
  exact Workspace.ProofLemmas.Thm155SixHoleEndgame.six_hole_endgame_absurd
    hG p hp_inj hp_adj X hXanti hpX
    (by simpa [hp0] using hp₀X) (by simpa [hp3] using hp₃X)
    ⟨Q₁, by simpa [hp1, hp2] using hQ₁, hQ₁int⟩
    ⟨Q₂, by simpa [hp4, hp5] using hQ₂, hQ₂int⟩

/-- The main case, *"so we assume it has length `≥ 6`"*: the whole remainder of the
printed proof of 15.5 (13.6 twice, 2.2, the shortest antipath `Q`, the long-prism
case `m > 2`, and the `L(K₃,₃ \ e)` / double-diamond case `m = 2`). -/
theorem even_of_holeLength_ge_six (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (hC : IsHoleList G C) (h6 : 6 ≤ holeLength C)
    (X : Set V) (hXC : ∀ x ∈ X, x ∉ C) (hXanti : AnticonnectedSet G X)
    (P : List V) (u v : V) (hP : IsPathFrom G P u v)
    (hPC : ∃ k : ℕ, P <+: C.rotate k ∨ P.reverse <+: C.rotate k)
    (hPlen : 1 < pathLength P)
    (hu : VertexComplete G u X) (hv : VertexComplete G v X)
    (hint : ∀ w ∈ SPGT.interior P, ¬ VertexComplete G w X) :
    Even (pathLength P) := by
  obtain ⟨k, hpre | hpre⟩ := hPC
  · exact even_of_prefix_ge_six G hG (C.rotate k)
      (Workspace.ProofLemmas.HoleBasics.isHoleList_rotate hC k)
      (by simpa [holeLength] using h6)
      X (by
        intro x hxX hxC
        exact hXC x hxX (Workspace.ProofLemmas.HoleBasics.mem_rotate_iff.mp hxC))
      hXanti P u v hP hpre hPlen hu hv hint
  · have hrev := even_of_prefix_ge_six G hG (C.rotate k)
      (Workspace.ProofLemmas.HoleBasics.isHoleList_rotate hC k)
      (by simpa [holeLength] using h6)
      X (by
        intro x hxX hxC
        exact hXC x hxX (Workspace.ProofLemmas.HoleBasics.mem_rotate_iff.mp hxC))
      hXanti P.reverse v u
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hP) hpre
      (by simpa [Workspace.ProofLemmas.PathBasics.pathLength_reverse] using hPlen)
      hv hu (by
        intro w hw
        exact hint w (Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hw))
    simpa [Workspace.ProofLemmas.PathBasics.pathLength_reverse] using hrev

end Workspace.ProofLemmas.Thm155HoleCases
