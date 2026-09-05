/-  Proof attempt 1 for `Thm224LeapExclusion`.

    PAPER (22.4, final paragraph, printed p. 138):

      "By 2.10 `X_t` contains a leap or a hat.  If it contains a leap, there are
       nonadjacent vertices in `X_t`, joined by an odd path of length ≥ 5 with interior
       in `{u₁,…,u_i, x_{t+1}}`, and consequently with no internal vertex `Y`-complete.
       Since both its ends are `Y`-complete, this contradicts 13.6."

    Reproduced step for step.  Write `H = z-y-u₁-⋯-u_{k+1}-x_{t+1}-z` for the endgame hole
    (the paper's `i` is our `k+1`), `M = u₁-⋯-u_{k+1}-x_{t+1}` for the arc of `H` obtained by
    deleting `z` and `y`, and `q = x_{t+1}`.

    * A leap at the edge `zy` is by definition a leap for the path `H \ zy`, which is the
      rotation `y-u₁-⋯-u_{k+1}-q-z` of `H`; the *other* orientation (`H \ yz` read from `z`
      round to `y`) is impossible for list reasons, since the rotation of `H` beginning at
      `z` ends at `q ≠ y`.
    * The six leap edges say exactly that `a` is adjacent to `y`, `u₁`, `z` and to nothing
      else of the hole, and `b` is adjacent to `y`, `q`, `z` and to nothing else.  Hence
      `a-u₁-⋯-u_{k+1}-q-b` is an induced path — the paper's "odd path with interior in
      `{u₁,…,u_i,x_{t+1}}`".
    * Its length is `k+3`; the hole has length `k+4`, which is `≥ 6` by hypothesis and even
      because `G` is Berge, so the path has length `≥ 5` and is odd.
    * Its ends `a, b ∈ X_t` are `Y`-complete because `X_t` is complete to `Y`; no internal
      vertex is `Y`-complete (the `uᵢ` by the choice of the `u`-path, `q` by claim (4)); and
      `Y` misses the path entirely.  So 13.6 applies and returns a `Y`-complete edge of the
      path — but the only `Y`-complete vertices are the two nonadjacent ends.  Contradiction.
-/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm224ClaimsDefs
import Workspace.ProofLemmas.Thm224WheelTailConsequences
import Workspace.ProofLemmas.Thm224Claim4
import Workspace.ProofLemmas.Thm224MinimalNeighborHole
import Workspace.Statements.S13.Thm_13_6
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.KiteTailBasics

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm224LeapExclusion

open Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio.SPGT
open Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm224Claims

/-- A rotation of a list with no repeated vertex is determined by its first vertex. -/
private theorem rotate_index_eq {V : Type*} {H : List V} (hnd : H.Nodup)
    {i j : ℕ} (hj : j < H.length) {w : V}
    (hhead : (H.rotate i).head? = some w) (hjw : H[j]'hj = w) :
    H.rotate i = H.rotate j := by
  have hpos : 0 < H.length := by omega
  have hmod : i % H.length < H.length := Nat.mod_lt _ hpos
  have hg : (H.rotate i).head? = H[(0 + i) % H.length]? := by
    rw [List.head?_eq_getElem?, List.getElem?_rotate hpos]
  rw [hg, Nat.zero_add, List.getElem?_eq_getElem hmod] at hhead
  have heq : H[i % H.length]'hmod = w := Option.some.inj hhead
  have hij : i % H.length = j := hnd.getElem_inj_iff.mp (heq.trans hjw.symm)
  rw [← List.rotate_mod H i, hij]

/-- Positions `2,…,k+3` of a cycle of length `k+4` are cyclically consecutive exactly when
they are consecutive: the wrap-around edge of the cycle has been cut away. -/
private theorem arc_adj_iff {k i j : ℕ} (hi : i < k + 2) (hj : j < k + 2) :
    ((j + 2 = (i + 2 + 1) % (k + 4) ∨ i + 2 = (j + 2 + 1) % (k + 4))
      ↔ (i + 1 = j ∨ j + 1 = i)) := by
  have e1 : (i + 2 + 1) % (k + 4) = if i + 3 = k + 4 then 0 else i + 3 := by
    split_ifs with h
    · rw [show i + 2 + 1 = k + 4 by omega, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  have e2 : (j + 2 + 1) % (k + 4) = if j + 3 = k + 4 then 0 else j + 3 := by
    split_ifs with h
    · rw [show j + 2 + 1 = k + 4 by omega, Nat.mod_self]
    · exact Nat.mod_eq_of_lt (by omega)
  rw [e1, e2]
  clear e1 e2
  split_ifs with h1 h2 h2 <;>
    (try simp only [false_or, or_false, false_iff]) <;> omega

/-- In the 22.4 endgame, the least-neighbour hole admits neither orientation
of a leap in `wheelSystemX x t` at its edge `z-y`. -/
theorem thm224LeapExclusion
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : InF8 G)
    {C T R u : List V} {Y A₀ : Set V} {z y : V} {x : ℕ → V} {t : ℕ}
    (hopt : OptimalWheel G C Y)
    (hT : IsTail G C Y z (x 0) (x 1) T)
    (hTshape : T = z :: y :: R)
    (hA₀ : A₀ = {v : V | v ∈ C} \ {z, x 0, x 1})
    (hhub : IsHubForWheelSystem G z A₀ x (t + 1) (Y ∪ {y}))
    (hcon : VertexAnticomplete G y (wheelSystemA G z A₀ x t ∪ {x (t + 1)}))
    (hu : IsUPath G z A₀ x t Y T y u)
    (hlen : Even u.length)
    (hadj : ∃ v ∈ u.dropLast, G.Adj (x (t + 1)) v)
    (hXt : ∀ v ∈ u.dropLast, ¬ VertexComplete G v (wheelSystemX x t))
    {k : ℕ} (hk : k < u.dropLast.length)
    (hkadj : G.Adj (x (t + 1)) (u.dropLast[k]'hk))
    (hkmin : ∀ (j : ℕ) (hj : j < k),
      ¬ G.Adj (x (t + 1)) (u.dropLast[j]'(lt_trans hj hk)))
    (hH :
      let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
      IsHoleList G H ∧
      6 ≤ holeLength H ∧
      (∀ w ∈ H, w ∉ wheelSystemX x t) ∧
      (∀ w ∈ H, VertexComplete G w (wheelSystemX x t) ↔ w = z ∨ w = y)) :
    let H := [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
    ¬ ∃ a ∈ wheelSystemX x t, ∃ b ∈ wheelSystemX x t,
      IsLeapForHole G H z y a b ∨ IsLeapForHole G H y z a b := by
  classical
  obtain ⟨hhole, hlen6, hnotX, hXcomp⟩ := hH
  show ¬ ∃ a ∈ wheelSystemX x t, ∃ b ∈ wheelSystemX x t,
      IsLeapForHole G ([z, y] ++ u.take (k + 1) ++ [x (t + 1)]) z y a b ∨
      IsLeapForHole G ([z, y] ++ u.take (k + 1) ++ [x (t + 1)]) y z a b
  have hHeq : [z, y] ++ u.take (k + 1) ++ [x (t + 1)]
      = z :: y :: (u.take (k + 1) ++ [x (t + 1)]) := by simp
  rw [hHeq] at hhole hlen6 hnotX hXcomp ⊢
  set M : List V := u.take (k + 1) ++ [x (t + 1)] with hMdef
  -- basic bookkeeping about the length of `M`
  have hdl : u.dropLast.length = u.length - 1 := List.length_dropLast
  have hulen : k + 2 ≤ u.length := by omega
  have hMlen : M.length = k + 2 := by
    rw [hMdef]
    simp only [List.length_append, List.length_take, List.length_singleton]
    omega
  have hk2 : 2 ≤ k := by
    have h := hlen6
    simp only [holeLength, List.length_cons, hMlen] at h
    omega
  -- `G` is Berge, so the hole has even length, so `k` is even.
  have hBerge : Berge G := hG.1.1.1.1.1
  have hkeven : Even k := by
    have h := hBerge.1 _ hhole
    simp only [holeLength, List.length_cons, hMlen] at h
    obtain ⟨m, hm⟩ := h
    exact ⟨m - 2, by omega⟩
  -- nodup bookkeeping
  have hnd : (z :: y :: M).Nodup := hhole.2.1
  have hyM : y ∉ M := (List.nodup_cons.mp ((List.nodup_cons.mp hnd).2)).1
  have hzM : z ∉ M := fun hz => (List.nodup_cons.mp hnd).1 (by simp [hz])
  have hzy : z ≠ y := by
    intro h; exact (List.nodup_cons.mp hnd).1 (by simp [h])
  have hMnd : M.Nodup := (List.nodup_cons.mp ((List.nodup_cons.mp hnd).2)).2
  -- the consequences bundle of §22.4
  have hcons :=
    Workspace.ProofLemmas.Thm224WheelTailConsequences.thm224WheelTailConsequences
      hG hopt hT hTshape hA₀ hhub hcon hu
  obtain ⟨ht1, hframe, hA₀sub, hAne, hAconn, hzA, hAnoX, hxNbr,
      hXne, hXanti, hXqne, hXqanti, hqX, hqYy, hqXnc, hzXq,
      hzYy, hXY, hyX, hAY, hpathzy, hzu, hyu, -⟩ := hcons
  -- `M` is an induced path of `G`: a proper arc of the hole.
  have hMpath : IsPathList G M := by
    obtain ⟨h4, hnd', hadj'⟩ := hhole
    refine ⟨?_, hMnd, ?_⟩
    · intro h
      rw [h] at hMlen
      simp at hMlen
    · intro i j hi hj
      rw [hMlen] at hi hj
      have hlenH : (z :: y :: M).length = k + 4 := by
        simp only [List.length_cons, hMlen]
      have hi' : i + 2 < (z :: y :: M).length := by rw [hlenH]; omega
      have hj' : j + 2 < (z :: y :: M).length := by rw [hlenH]; omega
      have e := hadj' (i + 2) (j + 2) hi' hj'
      simp only [List.getElem_cons_succ, hlenH] at e
      rw [e]
      exact arc_adj_iff hi hj
  -- `M` misses `Y` entirely, and no vertex of `M` is `Y`-complete.
  have hMnotY : ∀ w ∈ M, w ∉ Y := by
    intro w hw hwY
    have hwH : w ∈ (z :: y :: M) := by simp [hw]
    have hwz : w ≠ z := by rintro rfl; exact hzM hw
    have hwy : w ≠ y := by rintro rfl; exact hyM hw
    have hcomp : VertexComplete G w (wheelSystemX x t) := by
      intro v hv
      exact (hXY v hv w hwY).symm
    rcases (hXcomp w hwH).mp hcomp with h | h
    · exact hwz h
    · exact hwy h
  have hMnotYC : ∀ w ∈ M, ¬ VertexComplete G w Y := by
    intro w hw
    rw [hMdef] at hw
    rcases List.mem_append.mp hw with h | h
    · exact hu.2.2.2.2 w (List.mem_of_mem_take h)
    · rw [List.mem_singleton] at h
      subst h
      exact Workspace.ProofLemmas.Thm224Claim4.claim4 hG hopt hT hTshape hA₀ hhub hcon
        hu hlen hadj
  -- `Y` is anticonnected.
  have hYanti : AnticonnectedSet G Y :=
    KiteTailBasics.wheel_hub_anticonnected (KiteTailBasics.tail_isWheel hT)
  -- now the leap
  rintro ⟨a, haX, b, hbX, hleap⟩
  have haH : a ∉ (z :: y :: M) := fun h => hnotX a h haX
  have hbH : b ∉ (z :: y :: M) := fun h => hnotX b h hbX
  have haz : a ≠ z := by rintro rfl; exact haH (by simp)
  have hay : a ≠ y := by rintro rfl; exact haH (by simp)
  have hbz : b ≠ z := by rintro rfl; exact hbH (by simp)
  have hby : b ≠ y := by rintro rfl; exact hbH (by simp)
  have haM : a ∉ M := fun h => haH (by simp [h])
  have hbM : b ∉ M := fun h => hbH (by simp [h])
  rcases hleap with hleap | hleap
  · -- the genuine orientation: `H \ zy` runs from `y` round to `z`
    obtain ⟨-, i, hhd, hlst, hpl, hplen2, hab, hnab, hAdjA, hAdjB⟩ := hleap
    have hrot : (z :: y :: M).rotate i = (z :: y :: M).rotate 1 :=
      rotate_index_eq hnd (j := 1) (by simp) hhd (by simp)
    rw [hrot] at hpl hAdjA hAdjB
    have hProt : (z :: y :: M).rotate 1 = y :: (M ++ [z]) := by
      rw [List.rotate_cons_succ]
      simp
    rw [hProt] at hAdjA hAdjB
    have hPlen : (y :: (M ++ [z])).length = k + 4 := by simp [hMlen]
    -- translate the leap conditions from `G \ zy` to `G`
    have hbridge : ∀ (c w : V), c ≠ z → c ≠ y →
        ((G.deleteEdges {s(z, y)}).Adj c w ↔ G.Adj c w) := by
      intro c w hcz hcy
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff]
      rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact hcz h1
      · exact hcy h1
    have hPmid : ∀ (m : ℕ) (hm : m < M.length) (h2 : m + 1 < (y :: (M ++ [z])).length),
        (y :: (M ++ [z]))[m + 1]'h2 = M[m]'hm := by
      intro m hm h2
      simp only [List.getElem_cons_succ]
      exact List.getElem_append_left hm
    -- `a` is adjacent to the first vertex of `M` and to no other vertex of `M`
    have hM0lt : (0 : ℕ) < M.length := by omega
    have hMklt : k + 1 < M.length := by omega
    have hAM : G.Adj a (M[0]'hM0lt) := by
      have hi1 : (0 : ℕ) + 1 < (y :: (M ++ [z])).length := by omega
      have h := (hAdjA (0 + 1) hi1).mpr (Or.inr (Or.inl rfl))
      rw [hPmid 0 hM0lt hi1] at h
      exact (hbridge a _ haz hay).mp h
    have hAnotM : ∀ (m : ℕ) (hm : m < M.length), m ≠ 0 → ¬ G.Adj a (M[m]'hm) := by
      intro m hm hm0 hcontra
      have hmk : m < k + 2 := by rw [hMlen] at hm; exact hm
      have hi1 : m + 1 < (y :: (M ++ [z])).length := by omega
      have h := (hAdjA (m + 1) hi1).mp
        (by rw [hPmid m hm hi1]; exact (hbridge a _ haz hay).mpr hcontra)
      rw [hPlen] at h
      omega
    have hBM : G.Adj b (M[k + 1]'hMklt) := by
      have hi1 : (k + 1) + 1 < (y :: (M ++ [z])).length := by omega
      have h := (hAdjB ((k + 1) + 1) hi1).mpr (Or.inr (Or.inl (by omega)))
      rw [hPmid (k + 1) hMklt hi1] at h
      exact (hbridge b _ hbz hby).mp h
    have hBnotM : ∀ (m : ℕ) (hm : m < M.length), m ≠ k + 1 → ¬ G.Adj b (M[m]'hm) := by
      intro m hm hmne hcontra
      have hmk : m < k + 2 := by rw [hMlen] at hm; exact hm
      have hi1 : m + 1 < (y :: (M ++ [z])).length := by omega
      have h := (hAdjB (m + 1) hi1).mp
        (by rw [hPmid m hm hi1]; exact (hbridge b _ hbz hby).mpr hcontra)
      rw [hPlen] at h
      omega
    have hnab' : ¬ G.Adj a b := fun h => hnab ((hbridge a b haz hay).mpr h)
    -- assemble the path `a-u₁-⋯-u_{k+1}-q-b`
    have hMhead : M.head? = some (M[0]'hM0lt) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hM0lt]
    have hMlast : M.getLast? = some (M[k + 1]'hMklt) := by
      rw [List.getLast?_eq_getElem?, show M.length - 1 = k + 1 by omega,
        List.getElem?_eq_getElem hMklt]
    have hMfrom : IsPathFrom G M (M[0]'hM0lt) (M[k + 1]'hMklt) := ⟨hMpath, hMhead, hMlast⟩
    have hAother : ∀ w ∈ M, w ≠ (M[0]'hM0lt) → ¬ G.Adj a w := by
      intro w hw hw0
      obtain ⟨m, hm, hmw⟩ := List.getElem_of_mem hw
      subst hmw
      refine hAnotM m hm ?_
      rintro rfl
      exact hw0 rfl
    have hBother : ∀ w ∈ M, w ≠ (M[k + 1]'hMklt) → ¬ G.Adj b w := by
      intro w hw hwk
      obtain ⟨m, hm, hmw⟩ := List.getElem_of_mem hw
      subst hmw
      refine hBnotM m hm ?_
      rintro rfl
      exact hwk rfl
    have hP' : IsPathFrom G (a :: (M ++ [b])) a b :=
      PathAttach.isPathFrom_cons_concat hMfrom hAM hBM hnab' hab haM hbM hAother hBother
    have hP'len : pathLength (a :: (M ++ [b])) = k + 3 := by
      rw [PathAttach.pathLength_cons_append_singleton, hMlen]
    have hP'odd : Odd (pathLength (a :: (M ++ [b]))) := by
      rw [hP'len]
      obtain ⟨m, hm⟩ := hkeven
      exact ⟨m + 1, by omega⟩
    -- the two ends are `Y`-complete, and nothing else on the path is
    have haY : VertexComplete G a Y := hXY a haX
    have hbY : VertexComplete G b Y := hXY b hbX
    have hYP : Y ⊆ {v : V | v ∈ (a :: (M ++ [b]))}ᶜ := by
      intro w hw hmem
      simp only [Set.mem_setOf_eq] at hmem
      rcases List.mem_cons.mp hmem with rfl | hm
      · exact G.irrefl (haY w hw)
      · rcases List.mem_append.mp hm with hm' | hm'
        · exact hMnotY w hm' hw
        · rw [List.mem_singleton] at hm'
          subst hm'
          exact G.irrefl (hbY w hw)
    have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1.1
      (a :: (M ++ [b])) a b hP' hP'odd Y hYP hYanti haY hbY
    rcases h136 with ⟨w1, hw1, w2, hw2, hedge⟩ | ⟨hl3, -⟩
    · have hclass : ∀ w ∈ (a :: (M ++ [b])), VertexComplete G w Y → w = a ∨ w = b := by
        intro w hw hwc
        rcases List.mem_cons.mp hw with rfl | hm
        · exact Or.inl rfl
        · rcases List.mem_append.mp hm with hm' | hm'
          · exact absurd hwc (hMnotYC w hm')
          · rw [List.mem_singleton] at hm'
            exact Or.inr hm'
      rcases hclass w1 hw1 hedge.2.1 with rfl | rfl <;>
        rcases hclass w2 hw2 hedge.2.2 with rfl | rfl
      · exact G.irrefl hedge.1
      · exact hnab' hedge.1
      · exact hnab' hedge.1.symm
      · exact G.irrefl hedge.1
    · rw [hP'len] at hl3
      omega
  · -- the impossible orientation: the rotation beginning at `z` ends at `x (t+1) ≠ y`
    obtain ⟨-, i, hhd, hlst, -⟩ := hleap
    have hrot : (z :: y :: M).rotate i = (z :: y :: M).rotate 0 :=
      rotate_index_eq hnd (j := 0) (by simp) hhd (by simp)
    rw [hrot, List.rotate_zero] at hlst
    -- the rotation beginning at `z` is `H` itself, so its last vertex would have to be `y`;
    -- but `y` sits at position 1 of the hole, and the hole has length `k + 4 ≥ 6`.
    have hlenH : (z :: y :: M).length = k + 4 := by
      simp only [List.length_cons, hMlen]
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (z :: y :: M).length - 1 < (z :: y :: M).length by
        omega)] at hlst
    have hy1 : (z :: y :: M)[1]'(by omega) = y := by simp
    have hidx := hnd.getElem_inj_iff.mp ((Option.some.inj hlst).trans hy1.symm)
    omega

end Workspace.ProofLemmas.Thm224LeapExclusion
