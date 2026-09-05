import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm85EnlargeStripBySet
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm84RungEndDictionary

/-!
# 8.5, claim (2): the path through `F` and the enlargement of the strip system

PAPER (proof of 8.5, claim (2), printed p. 42):

*"The minimality of `F` implies that there is a path `P` with `V(P) = F`, with ends `p₁, p₂`
such that `p₁` is complete to `N_v \ N_vu`, and no other vertex of `P` has any neighbours in
`N_v \ N_vu`, and `p₂` is adjacent to `x`, and no other vertex of `P` has any neighbours in
`S_uv \ N_v`.  But then we can add `p₁` to `N_v` and `F` to `S_uv`, contradicting the maximality
of `(S,N)`."*

`path_structure` is the first sentence and `Thm85EnlargeStripBySet.thm85EnlargeStripBySet` is
the second; the module glues the old `uv`-rung through `x` to the path `P` to supply the one
axiom (*"every vertex of the new `S_uv` is in a new `uv`-rung"*) that the enlargement lemma
takes as a hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm85Claim2Maximality

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]

/-- A stretch of a path, with named ends, allowing the one-vertex stretch `i = j`. -/
theorem isPathFrom_slice' {G : SimpleGraph V} {p : List V} (h : IsPathList G p) {i j : ℕ}
    (hij : i ≤ j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) :=
  ⟨PathBasics.isPathList_take (PathBasics.isPathList_drop h (by omega)) (by omega),
    PathBasics.head?_slice p hij hj, PathBasics.getLast?_slice p hij hj⟩

/-- **A vertex of `S_uv \ N_v` and a vertex of `N_v \ S_uv` never form a local pair.**  The
first lies in `N_w` only for `w = u`, and `N_u ∩ N_v ⊆ S_uv`; and the two lie in different
strips. -/
theorem pair_not_local {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V}
    {N : U → Set V} (hSN : IsJStripSystem G J S N) {u v : U} (huv : J.Adj u v)
    {z w : V} (hzS : z ∈ S u v) (hzN : z ∉ N v) (hwN : w ∈ N v) (hwS : w ∉ S u v) :
    ¬ LocalForStripSystem J S N ({z, w} : Set V) := by
  rintro (⟨c, hc⟩ | ⟨c, d, hcd, hsub⟩)
  · have hzc : z ∈ N c := hc (by simp)
    have hwc : w ∈ N c := hc (by simp)
    have hcu : c = u := by
      by_contra hcon
      have hcv : c ≠ v := by rintro rfl; exact hzN hzc
      have h0 : z ∈ S u v ∩ N c := ⟨hzS, hzc⟩
      rw [StripSystemBasics.strip_inter_N_eq_empty hSN huv hcon hcv] at h0
      exact h0
    subst hcu
    exact hwS (StripSystemBasics.N_inter_N_subset_strip hSN huv.ne huv ⟨hwc, hwN⟩)
  · have h1 : s(u, v) = s(c, d) :=
      StripSystemBasics.edge_eq_of_mem_strips hSN huv hcd hzS (hsub (by simp))
    have h2 : S c d = S u v := by
      rcases Sym2.eq_iff.mp h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact StripSystemBasics.strip_symm hSN hcd
    exact hwS (h2 ▸ hsub (by simp))

/-- **Minimality forbids a proper stretch of the path from carrying a non-local pair.**

If `F` is the vertex set of the path `P` and two vertices `a`, `b` forming a non-local pair
attach to the stretch of `P` between positions `i` and `j`, then that stretch is all of `P`; so
no position outside `[i,j]` can exist. -/
theorem subpath_not_all (G : SimpleGraph V) (J : SimpleGraph U) (S : U → U → Set V)
    (N : U → Set V) (F : Set V)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (P : List V) (hP : IsPathList G P) (hPF : F = {z : V | z ∈ P})
    (i j : ℕ) (hij : i ≤ j) (hj : j < P.length)
    (k : ℕ) (hk : k < P.length) (hkout : k < i ∨ j < k)
    (a b : V) (haV : a ∈ stripSystemVertices J S) (hbV : b ∈ stripSystemVertices J S)
    (hpair : ¬ LocalForStripSystem J S N ({a, b} : Set V))
    (hai : G.Adj a (P[i]'(by omega))) (hbj : G.Adj b (P[j]'hj)) : False := by
  classical
  set F₁ : Set V := {z : V | z ∈ (P.drop i).take (j - i + 1)} with hF₁
  have hslice : IsPathList G ((P.drop i).take (j - i + 1)) :=
    PathBasics.isPathList_take (PathBasics.isPathList_drop hP (by omega)) (by omega)
  have hsub : F₁ ⊆ F := by
    intro z hz
    rw [hPF]
    obtain ⟨m, hm, -, -, hmz⟩ := (PathBasics.mem_slice_iff P hij hj).mp hz
    rw [← hmz]
    exact List.getElem_mem hm
  have hiF₁ : (P[i]'(by omega)) ∈ F₁ :=
    (PathBasics.mem_slice_iff P hij hj).mpr ⟨i, by omega, le_rfl, hij, rfl⟩
  have hjF₁ : (P[j]'hj) ∈ F₁ :=
    (PathBasics.mem_slice_iff P hij hj).mpr ⟨j, hj, hij, le_rfl, rfl⟩
  have hnotlocal : ¬ LocalForStripSystem J S N
      (attachments G F₁ (stripSystemVertices J S)) := by
    intro hloc
    apply hpair
    have haA : a ∈ attachments G F₁ (stripSystemVertices J S) := ⟨haV, _, hiF₁, hai⟩
    have hbA : b ∈ attachments G F₁ (stripSystemVertices J S) := ⟨hbV, _, hjF₁, hbj⟩
    rcases hloc with ⟨c, hc⟩ | ⟨c, d, hcd, hcsub⟩
    · exact Or.inl ⟨c, by rintro y (rfl | rfl); exacts [hc haA, hc hbA]⟩
    · exact Or.inr ⟨c, d, hcd, by rintro y (rfl | rfl); exacts [hcsub haA, hcsub hbA]⟩
  have hF₁F : F₁ = F :=
    hFmin F₁ hsub (KiteTailBasics.connectedSet_of_isPathList hslice) hnotlocal
  have hkF : (P[k]'hk) ∈ F := by rw [hPF]; exact List.getElem_mem hk
  rw [← hF₁F] at hkF
  obtain ⟨m, hm, hmi, hmj, hmk⟩ := (PathBasics.mem_slice_iff P hij hj).mp hkF
  have : m = k := hP.2.1.getElem_inj_iff.mp hmk
  omega

/-- Rewriting the index of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- **"The minimality of `F` implies that there is a path `P` with `V(P) = F`, with ends
`p₁, p₂` such that `p₁` is complete to `N_v \ N_vu`, and no other vertex of `P` has any
neighbours in `N_v \ N_vu`, and `p₂` is adjacent to `x`, and no other vertex of `P` has any
neighbours in `S_uv \ N_v`."**  (Proof of 8.5, claim (2), printed p. 42.) -/
theorem path_structure
    (G : SimpleGraph V) (J : SimpleGraph U) (S : U → U → Set V) (N : U → Set V)
    (hSN : IsJStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (u v : U) (huv : J.Adj u v)
    (x y0 : V)
    (hxF : ∃ f ∈ F, G.Adj x f) (hxS : x ∈ S u v) (hxNv : x ∉ N v)
    (hy0F : ∃ f ∈ F, G.Adj y0 f) (hy0N : y0 ∈ N v) (hy0S : y0 ∉ S u v) :
    ∃ (P : List V) (p1 p2 : V), IsPathFrom G P p2 p1 ∧ F = {z : V | z ∈ P} ∧
      (∀ z : V, z ∈ S u v → z ∉ N v → ∀ f ∈ F, G.Adj z f → f = p2) ∧
      (∀ y : V, y ∈ N v → y ∉ S u v → ∀ f ∈ F, G.Adj y f → f = p1) := by
  classical
  have hxV : x ∈ stripSystemVertices J S :=
    StripSystemBasics.strip_subset_vertices huv hxS
  have hy0V : y0 ∈ stripSystemVertices J S :=
    StripSystemBasics.N_subset_vertices hSN v hy0N
  have hxFn : x ∉ F := fun h => (hFcompl h) hxV
  have hy0Fn : y0 ∉ F := fun h => (hFcompl h) hy0V
  have hne : x ≠ y0 := fun h => hy0S (h ▸ hxS)
  have hxSvu : x ∈ S v u := by rw [← StripSystemBasics.strip_symm hSN huv]; exact hxS
  have hnadj : ¬ G.Adj x y0 := by
    have h1 := StripSystemBasics.N_subset_iUnion hSN v hy0N
    simp only [Set.mem_iUnion] at h1
    obtain ⟨a, hva, hy0Sa⟩ := h1
    have hau : a ≠ u := by
      rintro rfl
      exact hy0S (by rw [StripSystemBasics.strip_symm hSN huv]; exact hy0Sa)
    intro hadj
    obtain ⟨-, hno⟩ := hSN.2.2.2.2.2.1 v u a huv.symm hva (Ne.symm hau)
    exact hxNv (hno x hxSvu y0 hy0Sa hadj).1
  obtain ⟨p, hp, h3, hint, hconn, -, -⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn hne hnadj hxFn hy0Fn hxF hy0F
  have hplen : 0 < p.length := by omega
  have hp0 : p[0]'hplen = x := PathBasics.getElem_zero_of_head? hp.2.1 hplen
  have hplast : p[p.length - 1]'(by omega) = y0 :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hplen
  have hPfrom : IsPathFrom G (SPGT.interior p) (p[1]'(by omega)) (p[p.length - 2]'(by omega)) :=
    PathGlue.isPathFrom_interior hp.1 h3
  set P : List V := SPGT.interior p with hPdef
  set p2 : V := p[1]'(by omega) with hp2def
  set p1 : V := p[p.length - 2]'(by omega) with hp1def
  have hxp2 : G.Adj x p2 := by
    have h := PathBasics.path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
    rwa [show p[0]'(by omega) = x from hp0, gidx p (show 0 + 1 = 1 by omega)] at h
  have hy0p1 : G.Adj p1 y0 := by
    have h := PathBasics.path_adj_succ hp.1 (show p.length - 2 + 1 < p.length by omega)
    rwa [gidx p (show p.length - 2 + 1 = p.length - 1 by omega) (by omega) (by omega),
      hplast] at h
  have hPlen : 0 < P.length := PathBasics.path_length_pos hPfrom.1
  have hP0 : P[0]'hPlen = p2 := PathBasics.getElem_zero_of_head? hPfrom.2.1 hPlen
  have hPlast : P[P.length - 1]'(by omega) = p1 :=
    PathBasics.getElem_last_of_getLast? hPfrom.2.2 hPlen
  have hPF : {z : V | z ∈ P} = F := by
    refine hFmin {z : V | z ∈ P} hint hconn ?_
    intro hloc
    apply pair_not_local hSN huv hxS hxNv hy0N hy0S
    have haA : x ∈ attachments G {z : V | z ∈ P} (stripSystemVertices J S) :=
      ⟨hxV, p2, by rw [← hP0]; exact List.getElem_mem hPlen, hxp2⟩
    have hbA : y0 ∈ attachments G {z : V | z ∈ P} (stripSystemVertices J S) :=
      ⟨hy0V, p1, by rw [← hPlast]; exact List.getElem_mem (by omega), hy0p1.symm⟩
    rcases hloc with ⟨c, hc⟩ | ⟨c, d, hcd, hcsub⟩
    · exact Or.inl ⟨c, by rintro y (rfl | rfl); exacts [hc haA, hc hbA]⟩
    · exact Or.inr ⟨c, d, hcd, by rintro y (rfl | rfl); exacts [hcsub haA, hcsub hbA]⟩
  refine ⟨P, p1, p2, hPfrom, hPF.symm, ?_, ?_⟩
  · intro z hzS hzN f hfF hadj
    by_contra hfne
    have hfP : f ∈ P := by rw [← hPF] at hfF; exact hfF
    obtain ⟨i, hi, hif⟩ := List.mem_iff_getElem.mp hfP
    have hi0 : i ≠ 0 := by
      rintro rfl
      exact hfne (by rw [← hif, hP0])
    exact subpath_not_all G J S N F hFmin P hPfrom.1 hPF.symm i (P.length - 1)
      (by omega) (by omega) 0 hPlen (Or.inl (by omega)) z y0
      (StripSystemBasics.strip_subset_vertices huv hzS) hy0V
      (pair_not_local hSN huv hzS hzN hy0N hy0S)
      (by rw [hif]; exact hadj) (by rw [hPlast]; exact hy0p1.symm)
  · intro y hyN hyS f hfF hadj
    by_contra hfne
    have hfP : f ∈ P := by rw [← hPF] at hfF; exact hfF
    obtain ⟨i, hi, hif⟩ := List.mem_iff_getElem.mp hfP
    have hilast : i ≠ P.length - 1 := by
      rintro rfl
      exact hfne (by rw [← hif, hPlast])
    exact subpath_not_all G J S N F hFmin P hPfrom.1 hPF.symm 0 i
      (by omega) hi (P.length - 1) (by omega) (Or.inr (by omega)) x y
      hxV (StripSystemBasics.N_subset_vertices hSN v hyN)
      (pair_not_local hSN huv hxS hxNv hyN hyS)
      (by rw [hP0]; exact hxp2) (by rw [hif]; exact hadj)

/-- **"But then we can add `p₁` to `N_v` and `F` to `S_uv`, contradicting the maximality of
`(S,N)`."**  (Proof of 8.5, claim (2), printed p. 42.) -/
theorem contradiction_of_identity
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hmax : MaximalStripSystem G J S N)
    (F : Set V) (hFcompl : F ⊆ (stripSystemVertices J S)ᶜ) (hFne : F.Nonempty)
    (hFconn : ConnectedSet G F)
    (hFmin : ∀ F₁ : Set V, F₁ ⊆ F → ConnectedSet G F₁ →
      ¬ LocalForStripSystem J S N (attachments G F₁ (stripSystemVertices J S)) → F₁ = F)
    (u v : U) (huv : J.Adj u v) (x : V)
    (hxX : x ∈ attachments G F (stripSystemVertices J S))
    (hxS : x ∈ S u v) (hxNv : x ∉ N v)
    (hidentity : attachments G F (stripSystemVertices J S) \ S u v = N v \ S u v) :
    False := by
  classical
  have hXtoN : ∀ z : V, z ∈ attachments G F (stripSystemVertices J S) → z ∉ S u v →
      z ∈ N v := by
    intro z hz hzS
    have h : z ∈ N v \ S u v := by rw [← hidentity]; exact ⟨hz, hzS⟩
    exact h.1
  have hNtoX : ∀ z : V, z ∈ N v → z ∉ S u v →
      z ∈ attachments G F (stripSystemVertices J S) := by
    intro z hz hzS
    have : z ∈ attachments G F (stripSystemVertices J S) \ S u v := by
      rw [hidentity]; exact ⟨hz, hzS⟩
    exact this.1
  have hFdisj : Disjoint F (stripSystemVertices J S) :=
    Set.disjoint_left.mpr fun f hf hfV => (hFcompl hf) hfV
  have hFV : ∀ f ∈ F, f ∉ stripSystemVertices J S := fun f hf => hFcompl hf
  -- a second neighbour of `v`, and an attachment in its strip
  obtain ⟨w, hw⟩ : (J.neighborSet v \ {u}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    have := Workspace.ProofLemmas.Thm84RungEndDictionary.two_le_ncard_diff
      (a := u) (SubdivisionCounting.three_le_degree_of_three_connected J hJ v)
    omega
  have hvw : J.Adj v w := hw.1
  have hwu : w ≠ u := hw.2
  have hsne : s(v, w) ≠ s(u, v) := by
    intro hc
    rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact huv.ne h1.symm
    · exact hwu h2
  obtain ⟨y0, hy0N, hy0Sw⟩ := StripSystemBasics.Nuv_nonempty hSN hvw
  have hy0S : y0 ∉ S u v := fun h =>
    Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN hvw huv hsne) hy0Sw h
  have hy0X : y0 ∈ attachments G F (stripSystemVertices J S) := hNtoX y0 hy0N hy0S
  -- the path through `F`
  obtain ⟨P, p1, p2, hPfrom, hFP, claim3, claim4⟩ :=
    path_structure G J S N hSN F hFcompl hFconn hFmin u v huv x y0 hxX.2 hxS hxNv
      hy0X.2 hy0N hy0S
  have hPsubF : ∀ z ∈ P, z ∈ F := fun z hz => by rw [hFP]; exact hz
  have hp1F : p1 ∈ F := by rw [hFP]; exact List.mem_of_getLast? hPfrom.2.2
  have hp2F : p2 ∈ F := by rw [hFP]; exact List.mem_of_mem_head? hPfrom.2.1
  -- the enlarged system
  set S' : U → U → Set V := fun a b => if s(a, b) = s(u, v) then S u v ∪ F else S a b
    with hS'def
  set N' : U → Set V := fun c => if c = v then N v ∪ {p1} else N c with hN'def
  have hSuv' : S' u v = S u v ∪ F := if_pos rfl
  have hSvu' : S' v u = S u v ∪ F := if_pos Sym2.eq_swap
  have hS'other : ∀ a b : U, J.Adj a b → s(a, b) ≠ s(u, v) → S' a b = S a b := by
    intro a b _ h; exact if_neg h
  have hNu' : N' u = N u := if_neg huv.ne
  have hNv' : N' v = N v ∪ {p1} := if_pos rfl
  have hN'other : ∀ c : U, c ≠ u → c ≠ v → N' c = N c := by
    intro c _ h; exact if_neg h
  -- old rungs are still rungs
  have holdrung : ∀ R : List V, IsUVRung G J S N u v R → IsUVRung G J S' N' u v R := by
    rintro R ⟨-, s, t, hpath, hsub, hs, ht⟩
    refine ⟨huv, s, t, hpath, ?_, ?_, ?_⟩
    · intro y hy; rw [hSuv']; exact Or.inl (hsub y hy)
    · intro y hy; rw [hNu']; exact hs y hy
    · intro y hy
      rw [hNv']
      constructor
      · rintro (h | h)
        · exact (ht y hy).mp h
        · exfalso
          have hyp : y = p1 := h
          exact hFV p1 hp1F
            (StripSystemBasics.strip_subset_vertices huv (hyp ▸ hsub y hy))
      · intro h; exact Or.inl ((ht y hy).mpr h)
  -- the new rung carrying `F`
  obtain ⟨fx, hfxF, hxfx⟩ := hxX.2
  have hxp2 : G.Adj x p2 := by
    have h := claim3 x hxS hxNv fx hfxF hxfx
    rw [← h]; exact hxfx
  obtain ⟨R0, hR0, hxR0⟩ := StripSystemBasics.exists_rung hSN huv hxS
  obtain ⟨-, s0, t0, hp0, hsub0, hs0, ht0⟩ := hR0
  have hR0len : 0 < R0.length := PathBasics.path_length_pos hp0.1
  have hR0last : R0[R0.length - 1]'(by omega) = t0 :=
    PathBasics.getElem_last_of_getLast? hp0.2.2 hR0len
  have hR00 : R0[0]'hR0len = s0 := PathBasics.getElem_zero_of_head? hp0.2.1 hR0len
  obtain ⟨jx, hjx, hjxx⟩ := List.mem_iff_getElem.mp hxR0
  have hjxlast : jx < R0.length - 1 := by
    rcases Nat.lt_or_ge jx (R0.length - 1) with h | h
    · exact h
    · exfalso
      have hje : jx = R0.length - 1 := by omega
      refine hxNv ((ht0 x hxR0).mpr ?_)
      rw [← hjxx, ← hR0last]
      exact gidx R0 hje hjx (by omega)
  have hex : ∃ i, ∃ h : i < R0.length, G.Adj (R0[i]'h) p2 :=
    ⟨jx, hjx, by rw [hjxx]; exact hxp2⟩
  obtain ⟨hklt, hkadj⟩ := Nat.find_spec hex
  set k := Nat.find hex with hkdef
  have hkjx : k ≤ jx := Nat.find_le ⟨hjx, by rw [hjxx]; exact hxp2⟩
  have hkmin : ∀ m : ℕ, m < k → ¬ ∃ h : m < R0.length, G.Adj (R0[m]'h) p2 :=
    fun m hm => Nat.find_min hex hm
  set Rpre : List V := (R0.drop 0).take (k - 0 + 1) with hRpredef
  have hRpre : IsPathFrom G Rpre (R0[0]'hR0len) (R0[k]'hklt) :=
    isPathFrom_slice' hp0.1 (Nat.zero_le k) hklt
  have hpremem : ∀ y ∈ Rpre, ∃ (m : ℕ) (hm : m < R0.length), m ≤ k ∧ R0[m]'hm = y := by
    intro y hy
    obtain ⟨m, hm, -, hmk, hmy⟩ := (PathBasics.mem_slice_iff R0 (Nat.zero_le k) hklt).mp hy
    exact ⟨m, hm, hmk, hmy⟩
  have hpreS : ∀ y ∈ Rpre, y ∈ S u v ∧ y ∉ N v := by
    intro y hy
    obtain ⟨m, hm, hmk, hmy⟩ := hpremem y hy
    have hyR0 : y ∈ R0 := by rw [← hmy]; exact List.getElem_mem hm
    refine ⟨hsub0 y hyR0, ?_⟩
    intro hyN
    have hyt : y = t0 := (ht0 y hyR0).mp hyN
    have : R0[m]'hm = R0[R0.length - 1]'(by omega) := by rw [hmy, hyt, hR0last]
    have hmeq : m = R0.length - 1 := hp0.1.2.1.getElem_inj_iff.mp this
    omega
  have hdisj : ∀ y ∈ Rpre, y ∉ P := by
    intro y hy hyP
    exact hFV y (hPsubF y hyP)
      (StripSystemBasics.strip_subset_vertices huv (hpreS y hy).1)
  have hcross : ∀ y ∈ Rpre, ∀ z ∈ P, (G.Adj y z ↔ (y = R0[k]'hklt ∧ z = p2)) := by
    intro y hy z hz
    constructor
    · intro hadj
      have hzF : z ∈ F := hPsubF z hz
      have hzp2 : z = p2 := claim3 y (hpreS y hy).1 (hpreS y hy).2 z hzF hadj
      obtain ⟨m, hm, hmk, hmy⟩ := hpremem y hy
      have hQm : ∃ h : m < R0.length, G.Adj (R0[m]'h) p2 := ⟨hm, by rw [hmy, ← hzp2]; exact hadj⟩
      have hkm : k ≤ m := by
        by_contra hc
        exact hkmin m (by omega) hQm
      have : m = k := by omega
      exact ⟨by rw [← hmy]; exact gidx R0 this hm hklt, hzp2⟩
    · rintro ⟨rfl, rfl⟩; exact hkadj
  have hglue : IsPathFrom G (Rpre ++ P) (R0[0]'hR0len) p1 :=
    PathGlue.glue_path hRpre hPfrom hdisj hcross
  have hnewrung : IsUVRung G J S' N' u v (Rpre ++ P) := by
    refine ⟨huv, R0[0]'hR0len, p1, hglue, ?_, ?_, ?_⟩
    · intro y hy
      rw [hSuv']
      rcases List.mem_append.mp hy with h | h
      · exact Or.inl (hpreS y h).1
      · exact Or.inr (hPsubF y h)
    · intro y hy
      rw [hNu']
      rcases List.mem_append.mp hy with h | h
      · obtain ⟨m, hm, hmk, hmy⟩ := hpremem y h
        have hyR0 : y ∈ R0 := by rw [← hmy]; exact List.getElem_mem hm
        rw [hs0 y hyR0, hR00]
      · constructor
        · intro hh
          exact absurd (StripSystemBasics.N_subset_vertices hSN u hh)
            (hFV y (hPsubF y h))
        · intro hh
          exfalso
          refine hFV y (hPsubF y h) ?_
          rw [hh, hR00]
          exact StripSystemBasics.strip_subset_vertices huv (hsub0 s0 (List.mem_of_mem_head? hp0.2.1))
    · intro y hy
      rw [hNv']
      rcases List.mem_append.mp hy with h | h
      · constructor
        · rintro (hh | hh)
          · exact absurd hh (hpreS y h).2
          · exfalso
            have hyp : y = p1 := hh
            exact hFV p1 hp1F
              (StripSystemBasics.strip_subset_vertices huv (hyp ▸ (hpreS y h).1))
        · intro hh
          exfalso
          exact hFV p1 hp1F
            (StripSystemBasics.strip_subset_vertices huv (hh ▸ (hpreS y h).1))
      · constructor
        · rintro (hh | hh)
          · exact absurd (StripSystemBasics.N_subset_vertices hSN v hh) (hFV y (hPsubF y h))
          · exact hh
        · intro hh; exact Or.inr hh
  have hcover : ∀ z ∈ S u v ∪ F, ∃ R : List V, IsUVRung G J S' N' u v R ∧ z ∈ R := by
    rintro z (hz | hz)
    · obtain ⟨R, hR, hzR⟩ := StripSystemBasics.exists_rung hSN huv hz
      exact ⟨R, holdrung R hR, hzR⟩
    · refine ⟨Rpre ++ P, hnewrung, List.mem_append.mpr (Or.inr ?_)⟩
      rw [hFP] at hz; exact hz
  refine Workspace.ProofLemmas.Thm85EnlargeStripBySet.thm85EnlargeStripBySet
    G J S N hSN hmax u v huv F hFne hFdisj ∅ {p1} (by simp) (by simpa using hp1F)
    S' N' hSuv' hSvu' hS'other (by rw [hNu']; simp) hNv' hN'other ?_ ?_ ?_ hcover
  · intro f hf a b hab hne y hy hadj
    right
    have hyV : y ∈ stripSystemVertices J S := StripSystemBasics.strip_subset_vertices hab hy
    have hyX : y ∈ attachments G F (stripSystemVertices J S) := ⟨hyV, f, hf, hadj.symm⟩
    have hyS : y ∉ S u v := fun hc =>
      hne (StripSystemBasics.edge_eq_of_mem_strips hSN hab huv hy hc)
    have hyN : y ∈ N v := hXtoN y hyX hyS
    exact ⟨by simpa using claim4 y hyN hyS f hf hadj.symm, hyN⟩
  · intro a _ _ p hp
    exact absurd hp (by simp)
  · intro a hva hau p hp y hy
    have hp' : p = p1 := hp
    subst hp'
    have hsne' : s(v, a) ≠ s(u, v) := by
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact huv.ne h1.symm
      · exact hau h2
    have hyS : y ∉ S u v := fun h =>
      Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN hva huv hsne') hy.2 h
    have hyX := hNtoX y hy.1 hyS
    obtain ⟨g, hgF, hyg⟩ := hyX.2
    have hg := claim4 y hy.1 hyS g hgF hyg
    have h2 : G.Adj y p := by rw [← hg]; exact hyg
    exact h2.symm

end Workspace.ProofLemmas.Thm85Claim2Maximality
