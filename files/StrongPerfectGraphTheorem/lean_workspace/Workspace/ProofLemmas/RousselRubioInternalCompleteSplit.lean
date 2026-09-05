import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

/-! ### Private helpers for the two Berge contradictions of §3.1 and §3.2 -/

/-- §3.1.  A leap `a, b ∈ T` for an induced path `Q` of odd length `≥ 3`, together with
a `T`-complete vertex `x` outside `T` and outside `Q` which misses every entry
`Q[1], …, Q[|Q|-2]`, closes the induced path `a-Q[1]-⋯-Q[|Q|-2]-b` into an induced
odd cycle of `G` through `x`.  That contradicts Bergeness. -/
private theorem leapOddHoleAbsurd {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Berge G) {T : Set V} {Q : List V} {a b : V}
    (ha : a ∈ T) (hb : b ∈ T)
    (hleap : IsLeapForPath G Q a b)
    (hodd : Odd (pathLength Q)) (h3 : 3 ≤ pathLength Q)
    {x : V} (hxT : VertexComplete G x T) (hxnT : x ∉ T) (hxQ : x ∉ Q)
    (hxmid : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k + 2 ≤ Q.length →
      ¬ G.Adj x (Q[k]'hk)) :
    False := by
  obtain ⟨hpl, h2, hab, hnab, hA, hB⟩ := hleap
  have hn : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hpl
  have hn4 : 4 ≤ Q.length := by
    have := Nat.odd_iff.mp hodd
    omega
  -- `a` is not a vertex of `Q`: it would have three neighbours on `Q`.
  have haQ : a ∉ Q := by
    intro hmem
    obtain ⟨k, hk, hka⟩ := List.mem_iff_getElem.mp hmem
    have h0 : G.Adj a (Q[0]'(by omega)) := (hA 0 (by omega)).mpr (Or.inl rfl)
    have h1 : G.Adj a (Q[1]'(by omega)) := (hA 1 (by omega)).mpr (Or.inr (Or.inl rfl))
    rw [← hka] at h0 h1
    have e0 := (PathBasics.path_adj_iff hpl hk (show 0 < Q.length by omega)).mp h0
    have e1 := (PathBasics.path_adj_iff hpl hk (show 1 < Q.length by omega)).mp h1
    omega
  have hbQ : b ∉ Q := by
    intro hmem
    obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.mp hmem
    have h0 : G.Adj b (Q[0]'(by omega)) := (hB 0 (by omega)).mpr (Or.inl rfl)
    have h1 : G.Adj b (Q[Q.length - 1]'(by omega)) :=
      (hB (Q.length - 1) (by omega)).mpr (Or.inr (Or.inr rfl))
    rw [← hkb] at h0 h1
    have e0 := (PathBasics.path_adj_iff hpl hk (show 0 < Q.length by omega)).mp h0
    have e1 := (PathBasics.path_adj_iff hpl hk (show Q.length - 1 < Q.length by omega)).mp h1
    omega
  -- the stretch `Q[1] … Q[|Q|-2]`
  have hj1 : (1 : ℕ) < Q.length - 2 := by omega
  have hj2 : Q.length - 2 < Q.length := by omega
  have hmidP : IsPathFrom G ((Q.drop 1).take ((Q.length - 2) - 1 + 1))
      (Q[1]'(by omega)) (Q[Q.length - 2]'hj2) :=
    PathBasics.isPathFrom_slice hpl hj1 hj2
  have hmidlen : ((Q.drop 1).take ((Q.length - 2) - 1 + 1)).length = Q.length - 2 := by
    rw [PathBasics.length_slice Q (le_of_lt hj1) hj2]
    omega
  have hmidmem : ∀ y ∈ (Q.drop 1).take ((Q.length - 2) - 1 + 1),
      ∃ (k : ℕ) (hk : k < Q.length), 1 ≤ k ∧ k ≤ Q.length - 2 ∧ Q[k]'hk = y := by
    intro y hy
    exact (PathBasics.mem_slice_iff Q (le_of_lt hj1) hj2).mp hy
  have hadja : G.Adj a (Q[1]'(by omega)) := (hA 1 (by omega)).mpr (Or.inr (Or.inl rfl))
  have hadjb : G.Adj b (Q[Q.length - 2]'hj2) :=
    (hB (Q.length - 2) hj2).mpr (Or.inr (Or.inl rfl))
  have hamid : a ∉ (Q.drop 1).take ((Q.length - 2) - 1 + 1) := by
    intro hy
    obtain ⟨k, hk, -, -, hkq⟩ := hmidmem a hy
    exact haQ (hkq ▸ List.getElem_mem hk)
  have hbmid : b ∉ (Q.drop 1).take ((Q.length - 2) - 1 + 1) := by
    intro hy
    obtain ⟨k, hk, -, -, hkq⟩ := hmidmem b hy
    exact hbQ (hkq ▸ List.getElem_mem hk)
  have hothera : ∀ y ∈ (Q.drop 1).take ((Q.length - 2) - 1 + 1),
      y ≠ (Q[1]'(by omega)) → ¬ G.Adj a y := by
    intro y hy hyne hadj
    obtain ⟨k, hk, hk1, hk2, hkq⟩ := hmidmem y hy
    subst hkq
    have hcase := (hA k hk).mp hadj
    have hkne : k ≠ 1 := by
      intro h
      subst h
      exact hyne rfl
    omega
  have hotherb : ∀ y ∈ (Q.drop 1).take ((Q.length - 2) - 1 + 1),
      y ≠ (Q[Q.length - 2]'hj2) → ¬ G.Adj b y := by
    intro y hy hyne hadj
    obtain ⟨k, hk, hk1, hk2, hkq⟩ := hmidmem y hy
    subst hkq
    have hcase := (hB k hk).mp hadj
    have hkne : k ≠ Q.length - 2 := by
      intro h
      subst h
      exact hyne rfl
    omega
  have hW : IsPathFrom G (a :: (((Q.drop 1).take ((Q.length - 2) - 1 + 1)) ++ [b])) a b :=
    PathAttach.isPathFrom_cons_concat hmidP hadja hadjb hnab hab hamid hbmid hothera hotherb
  have hWlen : (a :: (((Q.drop 1).take ((Q.length - 2) - 1 + 1)) ++ [b])).length = Q.length := by
    rw [PathAttach.length_cons_append_singleton]
    omega
  have hxW : x ∉ (a :: (((Q.drop 1).take ((Q.length - 2) - 1 + 1)) ++ [b])) := by
    intro hmem
    rcases PathAttach.mem_cons_append_singleton.mp hmem with h | h | h
    · exact hxnT (by rw [h]; exact ha)
    · obtain ⟨k, hk, -, -, hkq⟩ := hmidmem x h
      exact hxQ (hkq ▸ List.getElem_mem hk)
    · exact hxnT (by rw [h]; exact hb)
  have hint : ∀ y ∈ SPGT.interior (a :: (((Q.drop 1).take ((Q.length - 2) - 1 + 1)) ++ [b])),
      ¬ G.Adj x y := by
    intro y hy
    rw [show SPGT.interior (a :: (((Q.drop 1).take ((Q.length - 2) - 1 + 1)) ++ [b]))
        = (Q.drop 1).take ((Q.length - 2) - 1 + 1) by simp [SPGT.interior]] at hy
    obtain ⟨k, hk, hk1, hk2, hkq⟩ := hmidmem y hy
    subst hkq
    exact hxmid k hk hk1 (by omega)
  have heven := PrismBasics.even_of_path_closed_by_vertex hG hW (by omega) hxW
    (hxT a ha) (hxT b hb) hint
  rw [hWlen, Nat.even_iff] at heven
  have := Nat.odd_iff.mp hodd
  omega

/-- §3.2.  An odd antipath `Q` joining two `G`-adjacent vertices `c, d`, with interior
inside `T`, closes into an induced odd cycle of `Gᶜ` through any `T`-complete vertex
`x ∉ T` that misses `c` and `d` in `G`.  That contradicts Bergeness. -/
private theorem antipathOddAntiholeAbsurd {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Berge G) {T : Set V} {Q : List V} {c d : V}
    (hcd : G.Adj c d) (hQ : IsAntipathFrom G Q c d) (hodd : Odd (pathLength Q))
    (hQT : ∀ w ∈ SPGT.interior Q, w ∈ T)
    {x : V} (hxT : VertexComplete G x T) (hxnT : x ∉ T)
    (hxc : x ≠ c) (hxd : x ≠ d) (hnc : ¬ G.Adj x c) (hnd : ¬ G.Adj x d) :
    False := by
  have hpl : IsPathList Gᶜ Q := hQ.1
  have hlen : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hpl
  have hodd' : pathLength Q % 2 = 1 := Nat.odd_iff.mp hodd
  have hne1 : pathLength Q ≠ 1 := by
    intro h
    have hadj : Gᶜ.Adj c d := PathBasics.isPathFrom_ends_adj_of_length_one hQ h
    exact ((G.compl_adj c d).mp hadj).2 hcd
  have hxQ : x ∉ Q := by
    intro hmem
    exact hxnT (hQT x ((PathBasics.mem_interior_iff_of_pathFrom hQ).mpr ⟨hmem, hxc, hxd⟩))
  have hint : ∀ y ∈ SPGT.interior Q, G.Adj x y := fun y hy => hxT y (hQT y hy)
  have heven := PrismBasics.even_of_antipath_closed_by_vertex' hG hQ (by omega) hxQ
    hxc hxd hnc hnd hint
  rw [Nat.even_iff] at heven
  omega

/-- The internal-`T`-complete-vertex case of the strengthened
Roussel--Rubio parity induction. -/
theorem RousselRubioInternalCompleteSplit
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (T : Set V)
    (hT : AnticonnectedSet G T) (P : List V) (r s : V)
    (hP : IsPathFrom G P r s) (hPT : ∀ w ∈ P, w ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoLeap : ¬ (
      Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b))
    (hnoAntipath : ¬ (
      pathLength P = 3 ∧
        ∃ c d : V, SPGT.interior P = [c, d] ∧
          ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
            ∀ w ∈ SPGT.interior Q, w ∈ T))
    (j : ℕ) (hjpos : 0 < j) (hjlt : j < pathLength P)
    (z : V) (hz : P[j]? = some z) (hzComplete : VertexComplete G z T)
    (hLeft :
      (({i : ℕ | i + 1 < (P.take (j + 1)).length ∧
          ∃ u v : V, (P.take (j + 1))[i]? = some u ∧
            (P.take (j + 1))[i + 1]? = some v ∧
              EdgeComplete G T u v} : Set ℕ).ncard % 2 =
          pathLength (P.take (j + 1)) % 2) ∨
        (Odd (pathLength (P.take (j + 1))) ∧
          3 ≤ pathLength (P.take (j + 1)) ∧
          ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G (P.take (j + 1)) a b) ∨
        (pathLength (P.take (j + 1)) = 3 ∧
          ∃ c d : V, SPGT.interior (P.take (j + 1)) = [c, d] ∧
            ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
              ∀ w ∈ SPGT.interior Q, w ∈ T))
    (hRight :
      (({i : ℕ | i + 1 < (P.drop j).length ∧
          ∃ u v : V, (P.drop j)[i]? = some u ∧
            (P.drop j)[i + 1]? = some v ∧
              EdgeComplete G T u v} : Set ℕ).ncard % 2 =
          pathLength (P.drop j) % 2) ∨
        (Odd (pathLength (P.drop j)) ∧ 3 ≤ pathLength (P.drop j) ∧
          ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G (P.drop j) a b) ∨
        (pathLength (P.drop j) = 3 ∧
          ∃ c d : V, SPGT.interior (P.drop j) = [c, d] ∧
            ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
              ∀ w ∈ SPGT.interior Q, w ∈ T)) :
    (({i : ℕ | i + 1 < P.length ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ).ncard % 2 = pathLength P % 2) := by
  classical
  obtain ⟨hpath, hhead, hlast⟩ := hP
  have hpos : 0 < P.length := PathBasics.path_length_pos hpath
  have hlenP : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hpath
  have hnd : P.Nodup := hpath.2.1
  have hjP : j < P.length := by omega
  have hj1P : j + 1 < P.length := by omega
  have hrE : P[0]'hpos = r := PathBasics.getElem_zero_of_head? hhead hpos
  have hsE : P[P.length - 1]'(by omega) = s := PathBasics.getElem_last_of_getLast? hlast hpos
  have hzE : P[j]'hjP = z := by
    rw [List.getElem?_eq_getElem hjP] at hz
    exact Option.some_injective _ hz
  have hrT : r ∉ T := hPT r (PathBasics.head_mem hhead)
  have hsT : s ∉ T := hPT s (PathBasics.getLast_mem hlast)
  -- the two contiguous subpaths
  have hPLlen : (P.take (j + 1)).length = j + 1 := by rw [List.length_take]; omega
  have hPRlen : (P.drop j).length = P.length - j := List.length_drop
  have hPLpl : pathLength (P.take (j + 1)) = j := by
    have h : pathLength (P.take (j + 1)) = (P.take (j + 1)).length - 1 := rfl
    omega
  have hPRpl : pathLength (P.drop j) = pathLength P - j := by
    have h : pathLength (P.drop j) = (P.drop j).length - 1 := rfl
    omega
  have hPL : IsPathFrom G (P.take (j + 1)) r z := by
    refine ⟨PathBasics.isPathList_take hpath (by omega), ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_take_of_lt (show 0 < j + 1 by omega),
        ← List.head?_eq_getElem?]
      exact hhead
    · rw [List.getLast?_eq_getElem?, hPLlen]
      simp only [Nat.add_sub_cancel]
      rw [List.getElem?_take_of_lt (show j < j + 1 by omega)]
      exact hz
  have hPR : IsPathFrom G (P.drop j) z s := by
    refine ⟨PathBasics.isPathList_drop hpath (by omega), ?_, ?_⟩
    · rw [List.head?_eq_getElem?, List.getElem?_drop]
      simpa using hz
    · rw [List.getLast?_eq_getElem?, hPRlen, List.getElem?_drop,
        show j + (P.length - j - 1) = P.length - 1 from by omega,
        ← List.getLast?_eq_getElem?]
      exact hlast
  -- index decoders for the two subpaths
  have hmemL : ∀ y : V, y ∈ P.take (j + 1) →
      ∃ (k : ℕ) (hk : k < P.length), k ≤ j ∧ P[k]'hk = y := by
    intro y hy
    obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hy
    have hkj : k < j + 1 := by omega
    refine ⟨k, by omega, by omega, ?_⟩
    rw [← hky]
    simp
  have hmemR : ∀ y : V, y ∈ P.drop j →
      ∃ (k : ℕ) (hk : k < P.length), j ≤ k ∧ P[k]'hk = y := by
    intro y hy
    obtain ⟨k, hk, hky⟩ := List.mem_iff_getElem.mp hy
    have hkb : k < P.length - j := by omega
    refine ⟨j + k, by omega, by omega, ?_⟩
    rw [← hky]
    simp
  -- §3.1: the left subpath cannot return a leap
  have hLeftNoLeap : ¬ (Odd (pathLength (P.take (j + 1))) ∧
      3 ≤ pathLength (P.take (j + 1)) ∧
      ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G (P.take (j + 1)) a b) := by
    rintro ⟨hoddL, h3L, a, ha, b, hb, hleap⟩
    refine leapOddHoleAbsurd hG ha hb hleap hoddL h3L hs hsT ?_ ?_
    · intro hmem
      obtain ⟨k, hk, hkj, hkq⟩ := hmemL s hmem
      have hkeq : k = P.length - 1 := hnd.getElem_inj_iff.mp (hkq.trans hsE.symm)
      omega
    · intro k hk hk1 hk2 hadj
      have hkP : k < P.length := by omega
      have heq : (P.take (j + 1))[k]'hk = P[k]'hkP := by simp
      rw [heq, ← hsE] at hadj
      have hcase :=
        (PathBasics.path_adj_iff hpath (show P.length - 1 < P.length by omega) hkP).mp hadj
      omega
  -- §3.2: the left subpath cannot return an antipath
  have hLeftNoAnti : ¬ (pathLength (P.take (j + 1)) = 3 ∧
      ∃ c d : V, SPGT.interior (P.take (j + 1)) = [c, d] ∧
        ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
          ∀ w ∈ SPGT.interior Q, w ∈ T) := by
    rintro ⟨h3L, c, d, hIeq, Q, hQ, hQodd, hQT⟩
    have hj3 : j = 3 := by omega
    have hcI : c ∈ SPGT.interior (P.take (j + 1)) := by rw [hIeq]; simp
    have hdI : d ∈ SPGT.interior (P.take (j + 1)) := by rw [hIeq]; simp
    have hIndup : (SPGT.interior (P.take (j + 1))).Nodup :=
      List.Nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _))
        (PathBasics.path_nodup hPL.1)
    have hcdne : c ≠ d := by
      rw [hIeq] at hIndup
      simpa using hIndup
    have hcmem := (PathBasics.mem_interior_iff_of_pathFrom hPL).mp hcI
    have hdmem := (PathBasics.mem_interior_iff_of_pathFrom hPL).mp hdI
    obtain ⟨kc, hkc, hkcj, hkcq⟩ := hmemL c hcmem.1
    obtain ⟨kd, hkd, hkdj, hkdq⟩ := hmemL d hdmem.1
    have hkc0 : kc ≠ 0 := by
      intro h; subst h; exact hcmem.2.1 (hkcq.symm.trans hrE)
    have hkcJ : kc ≠ j := by
      intro h; subst h; exact hcmem.2.2 (hkcq.symm.trans hzE)
    have hkd0 : kd ≠ 0 := by
      intro h; subst h; exact hdmem.2.1 (hkdq.symm.trans hrE)
    have hkdJ : kd ≠ j := by
      intro h; subst h; exact hdmem.2.2 (hkdq.symm.trans hzE)
    have hkne : kc ≠ kd := by
      intro h; subst h; exact hcdne (hkcq.symm.trans hkdq)
    -- `kc, kd ∈ {1, 2}`, so `c` and `d` are consecutive on `P`
    have hcdadj : G.Adj c d := by
      rw [← hkcq, ← hkdq]
      exact (PathBasics.path_adj_iff hpath hkc hkd).mpr (by omega)
    have hsc : s ≠ c := by
      intro h
      have : P.length - 1 = kc :=
        hnd.getElem_inj_iff.mp (hsE.trans (h.trans hkcq.symm))
      omega
    have hsd : s ≠ d := by
      intro h
      have : P.length - 1 = kd :=
        hnd.getElem_inj_iff.mp (hsE.trans (h.trans hkdq.symm))
      omega
    have hnsc : ¬ G.Adj s c := by
      rw [← hkcq, ← hsE]
      intro hadj
      have hcase :=
        (PathBasics.path_adj_iff hpath (show P.length - 1 < P.length by omega) hkc).mp hadj
      omega
    have hnsd : ¬ G.Adj s d := by
      rw [← hkdq, ← hsE]
      intro hadj
      have hcase :=
        (PathBasics.path_adj_iff hpath (show P.length - 1 < P.length by omega) hkd).mp hadj
      omega
    exact antipathOddAntiholeAbsurd hG hcdadj hQ hQodd hQT hs hsT hsc hsd hnsc hnsd
  -- §3.1 mirrored: the right subpath cannot return a leap
  have hRightNoLeap : ¬ (Odd (pathLength (P.drop j)) ∧ 3 ≤ pathLength (P.drop j) ∧
      ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G (P.drop j) a b) := by
    rintro ⟨hoddR, h3R, a, ha, b, hb, hleap⟩
    refine leapOddHoleAbsurd hG ha hb hleap hoddR h3R hr hrT ?_ ?_
    · intro hmem
      obtain ⟨k, hk, hkj, hkq⟩ := hmemR r hmem
      have hkeq : k = 0 := hnd.getElem_inj_iff.mp (hkq.trans hrE.symm)
      omega
    · intro k hk hk1 hk2 hadj
      have hkP : j + k < P.length := by omega
      have heq : (P.drop j)[k]'hk = P[j + k]'hkP := by simp
      rw [heq, ← hrE] at hadj
      have hcase := (PathBasics.path_adj_iff hpath hpos hkP).mp hadj
      omega
  -- §3.2 mirrored: the right subpath cannot return an antipath
  have hRightNoAnti : ¬ (pathLength (P.drop j) = 3 ∧
      ∃ c d : V, SPGT.interior (P.drop j) = [c, d] ∧
        ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
          ∀ w ∈ SPGT.interior Q, w ∈ T) := by
    rintro ⟨h3R, c, d, hIeq, Q, hQ, hQodd, hQT⟩
    have hlenEq : pathLength P = j + 3 := by omega
    have hcI : c ∈ SPGT.interior (P.drop j) := by rw [hIeq]; simp
    have hdI : d ∈ SPGT.interior (P.drop j) := by rw [hIeq]; simp
    have hIndup : (SPGT.interior (P.drop j)).Nodup :=
      List.Nodup.sublist ((List.dropLast_sublist _).trans (List.tail_sublist _))
        (PathBasics.path_nodup hPR.1)
    have hcdne : c ≠ d := by
      rw [hIeq] at hIndup
      simpa using hIndup
    have hcmem := (PathBasics.mem_interior_iff_of_pathFrom hPR).mp hcI
    have hdmem := (PathBasics.mem_interior_iff_of_pathFrom hPR).mp hdI
    obtain ⟨kc, hkc, hkcj, hkcq⟩ := hmemR c hcmem.1
    obtain ⟨kd, hkd, hkdj, hkdq⟩ := hmemR d hdmem.1
    have hkcJ : kc ≠ j := by
      intro h; subst h; exact hcmem.2.1 (hkcq.symm.trans hzE)
    have hkcL : kc ≠ P.length - 1 := by
      intro h; subst h; exact hcmem.2.2 (hkcq.symm.trans hsE)
    have hkdJ : kd ≠ j := by
      intro h; subst h; exact hdmem.2.1 (hkdq.symm.trans hzE)
    have hkdL : kd ≠ P.length - 1 := by
      intro h; subst h; exact hdmem.2.2 (hkdq.symm.trans hsE)
    have hkne : kc ≠ kd := by
      intro h; subst h; exact hcdne (hkcq.symm.trans hkdq)
    have hcdadj : G.Adj c d := by
      rw [← hkcq, ← hkdq]
      exact (PathBasics.path_adj_iff hpath hkc hkd).mpr (by omega)
    have hrc : r ≠ c := by
      intro h
      have : (0 : ℕ) = kc := hnd.getElem_inj_iff.mp (hrE.trans (h.trans hkcq.symm))
      omega
    have hrd : r ≠ d := by
      intro h
      have : (0 : ℕ) = kd := hnd.getElem_inj_iff.mp (hrE.trans (h.trans hkdq.symm))
      omega
    have hnrc : ¬ G.Adj r c := by
      rw [← hkcq, ← hrE]
      intro hadj
      have hcase := (PathBasics.path_adj_iff hpath hpos hkc).mp hadj
      omega
    have hnrd : ¬ G.Adj r d := by
      rw [← hkdq, ← hrE]
      intro hadj
      have hcase := (PathBasics.path_adj_iff hpath hpos hkd).mp hadj
      omega
    exact antipathOddAntiholeAbsurd hG hcdadj hQ hQodd hQT hr hrT hrc hrd hnrc hnrd
  -- §3.3: the two parity conclusions
  have hLpar : (({i : ℕ | i + 1 < (P.take (j + 1)).length ∧
      ∃ u v : V, (P.take (j + 1))[i]? = some u ∧
        (P.take (j + 1))[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ).ncard % 2 =
      pathLength (P.take (j + 1)) % 2) := by
    rcases hLeft with h | h | h
    · exact h
    · exact absurd h hLeftNoLeap
    · exact absurd h hLeftNoAnti
  have hRpar : (({i : ℕ | i + 1 < (P.drop j).length ∧
      ∃ u v : V, (P.drop j)[i]? = some u ∧
        (P.drop j)[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ).ncard % 2 = pathLength (P.drop j) % 2) := by
    rcases hRight with h | h | h
    · exact h
    · exact absurd h hRightNoLeap
    · exact absurd h hRightNoAnti
  -- transfer the two index sets to index sets of `P`
  have hLset : ({i : ℕ | i + 1 < (P.take (j + 1)).length ∧
      ∃ u v : V, (P.take (j + 1))[i]? = some u ∧
        (P.take (j + 1))[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ)
      = {i : ℕ | i < j ∧
          ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧ EdgeComplete G T u v} := by
    ext i
    simp only [Set.mem_setOf_eq, hPLlen]
    constructor
    · rintro ⟨hi, u, v, hu, hv, hE⟩
      rw [List.getElem?_take_of_lt (show i < j + 1 by omega)] at hu
      rw [List.getElem?_take_of_lt (show i + 1 < j + 1 by omega)] at hv
      exact ⟨by omega, u, v, hu, hv, hE⟩
    · rintro ⟨hi, u, v, hu, hv, hE⟩
      refine ⟨by omega, u, v, ?_, ?_, hE⟩
      · rw [List.getElem?_take_of_lt (show i < j + 1 by omega)]; exact hu
      · rw [List.getElem?_take_of_lt (show i + 1 < j + 1 by omega)]; exact hv
  have hRset : ({i : ℕ | i + 1 < (P.drop j).length ∧
      ∃ u v : V, (P.drop j)[i]? = some u ∧
        (P.drop j)[i + 1]? = some v ∧
          EdgeComplete G T u v} : Set ℕ)
      = {i : ℕ | j + i + 1 < P.length ∧
          ∃ u v : V, P[j + i]? = some u ∧ P[j + i + 1]? = some v ∧
            EdgeComplete G T u v} := by
    ext i
    simp only [Set.mem_setOf_eq, hPRlen, List.getElem?_drop, ← Nat.add_assoc]
    constructor
    · rintro ⟨hi, hrest⟩; exact ⟨by omega, hrest⟩
    · rintro ⟨hi, hrest⟩; exact ⟨by omega, hrest⟩
  -- the two index sets partition the index set of `P`
  have hUnion : ({i : ℕ | i + 1 < P.length ∧
      ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
        EdgeComplete G T u v} : Set ℕ)
      = {i : ℕ | i < j ∧
          ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧ EdgeComplete G T u v}
        ∪ (fun i => j + i) ''
          {i : ℕ | j + i + 1 < P.length ∧
            ∃ u v : V, P[j + i]? = some u ∧ P[j + i + 1]? = some v ∧
              EdgeComplete G T u v} := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_image]
    constructor
    · rintro ⟨hi, hE⟩
      by_cases hij : i < j
      · exact Or.inl ⟨hij, hE⟩
      · refine Or.inr ⟨i - j, ?_, by omega⟩
        rw [show j + (i - j) = i from by omega]
        exact ⟨hi, hE⟩
    · rintro (⟨hij, hE⟩ | ⟨k, hk, hki⟩)
      · exact ⟨by omega, hE⟩
      · subst hki
        exact hk
  have hdisj : Disjoint
      ({i : ℕ | i < j ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧ EdgeComplete G T u v} : Set ℕ)
      ((fun i => j + i) ''
        {i : ℕ | j + i + 1 < P.length ∧
          ∃ u v : V, P[j + i]? = some u ∧ P[j + i + 1]? = some v ∧
            EdgeComplete G T u v}) := by
    rw [Set.disjoint_left]
    intro i hi himg
    obtain ⟨k, -, hki⟩ := himg
    have h1 : i < j := hi.1
    have h2 : j + k = i := hki
    omega
  have hfin1 : ({i : ℕ | i < j ∧
      ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧ EdgeComplete G T u v} : Set ℕ).Finite :=
    Set.Finite.subset (Set.finite_Iio j) (fun i hi => hi.1)
  have hfin2 : ((fun i => j + i) ''
      {i : ℕ | j + i + 1 < P.length ∧
        ∃ u v : V, P[j + i]? = some u ∧ P[j + i + 1]? = some v ∧
          EdgeComplete G T u v}).Finite := by
    refine Set.Finite.image _ (Set.Finite.subset (Set.finite_Iio P.length) ?_)
    intro i hi
    have h1 := hi.1
    simp only [Set.mem_Iio]
    omega
  rw [hLset, hPLpl] at hLpar
  rw [hRset, hPRpl] at hRpar
  rw [hUnion, Set.ncard_union_eq hdisj hfin1 hfin2,
    Set.ncard_image_of_injective _ (add_right_injective j)]
  omega

end Workspace.ProofLemmas
