import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm81CycleEven
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm84K4CaseDegenerate
import Workspace.ProofLemmas.Thm85EndgameNotions
import Workspace.ProofLemmas.Thm85EndgameK4Shape
import Workspace.ProofLemmas.Thm85EndgameOptimalChoice
import Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapHole

/-!
# 8.5, the closing paragraph for `n = 1`: where `f₁` meets a cross rung

Setting: `J = K₄` on `{h,i,j,k}`, the path `F` of the proof of 8.5 is the single vertex `f₁`,
and `R` is a choice of rungs whose traversal is `hi`.  Call `hj`, `hk`, `ij`, `ik` the *cross*
edges — the four edges of `J` that meet `hi` in exactly one vertex.

The theorem below says that on the cross edge `hj`, **every** `hj`-rung `L` has its end in
`N_h` as its unique vertex adjacent to `f₁`.  This is the sentence

*"From (4) it follows that exactly one vertex of `R` is in `X`, one of its ends; say the end in
`N_h`"* (printed p. 45),

read for an arbitrary rung, and it is what the printed argument uses when it lets the rungs on
the cross edges vary.

## How the proof goes

Change `R` on the single edge `hj` to take `L` there, and let `pq` be a traversal of the
changed choice.  The changed choice still selects `R j k` on the edge `jk`, and that rung is
anticomplete to `f₁` because `jk` is disjoint from the traversal `hi` of `R`.  So neither `j`
nor `k` can be an end of `pq` unless `pq = jk` itself: an end of a traversal sees a neighbour of
`f₁` on every incident edge except the traversal edge.  Hence `pq` is `hi` or `jk`.

* If `pq = hi`, the first bullet of claim (4) applied to the edge `hj` is the conclusion.
* If `pq = jk`, then reading claim (4) for `pq = jk` and for `hi` on the three edges `ij`, `ik`,
  `hk` identifies the two ends of each of those three rungs, so all three have length `0`.  The
  four rungs of `R` round the cycle `h-j-i-k-h` then have even total length, so `R h j` has even
  length; and the printed odd hole `f₁-r_hj-R_hj-r_jh-r_ji-f₁` forbids it from being even and
  nonzero.  So all four of those rungs have length `0`, the appearance formed by `R` is
  degenerate, and that contradicts claim (1).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapCross

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas.Thm85EndgameNotions

variable {V U : Type*}

/-- With `f₁ = f_n` a traversal may be read in either direction. -/
theorem traversal_swap {G : SimpleGraph V} {J : SimpleGraph U} {N : U → Set V}
    {F : Set V} {f₁ : V} {R : U → U → List V} {p q : U}
    (hT : IsTraversal G J N F f₁ f₁ R p q) : IsTraversal G J N F f₁ f₁ R q p := by
  refine ⟨hT.1.symm, hT.2.2.1, hT.2.1, ?_⟩
  intro u v huv hnd2
  refine hT.2.2.2 u v huv ?_
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
    and_true, not_or] at hnd2 ⊢
  tauto

/-- **"From (4) it follows that exactly one vertex of `R` is in `X`, one of its ends; say the
end in `N_h`"** (printed p. 45), for an arbitrary `hj`-rung. -/
theorem cross_rung_end [Fintype V] [DecidableEq V] [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    (F : Set V) (f₁ : V) (hf₁F : f₁ ∈ F) (hf₁out : f₁ ∉ stripSystemVertices J S)
    (hclaim1 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (Rc : U → U → List V) (K : Set V)
        (phi : H.lineGraph ≃g G.induce K),
        K = ⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ Rc a b} →
        FormsLineGraph G J S N Rc H →
        (∀ y ∈ F, ¬ SaturatesLineGraph H
            {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet,
              (↑(phi ⟨e, he⟩) : V) ∈ G.neighborSet y}) ∧
        (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateAppearance J H))
    (hclaim4 : ∀ Rc : U → U → List V,
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc →
      ∃ p q : U, IsTraversal G J N F f₁ f₁ Rc p q)
    (hclaim5 : ∀ Rc : U → U → List V, RungChoice G J S N Rc →
      BroadChoice G J S N (attachments G F (stripSystemVertices J S)) Rc)
    (h i j k : U) (hnd : [h, i, j, k].Nodup)
    (hcover : ∀ c : U, c = h ∨ c = i ∨ c = j ∨ c = k)
    (hall : ∀ u v : U, u ≠ v → (u = h ∨ u = i ∨ u = j ∨ u = k) →
      (v = h ∨ v = i ∨ v = j ∨ v = k) → J.Adj u v)
    (R : U → U → List V) (hR : RungChoice G J S N R)
    (htrav : IsTraversal G J N F f₁ f₁ R h i)
    (L : List V) (hL : IsUVRung G J S N h j L) :
    ∃ r : V, r ∈ L ∧ r ∈ N h ∧ UniqueEdgeBetween G {x : V | x ∈ L} F r f₁ := by
  classical
  have hd : h ≠ i ∧ h ≠ j ∧ h ≠ k ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or] at hnd
    tauto
  obtain ⟨ehi, ehj, ehk, eij, eik, ejk⟩ := hd
  have mh : h = h ∨ h = i ∨ h = j ∨ h = k := Or.inl rfl
  have mi : i = h ∨ i = i ∨ i = j ∨ i = k := Or.inr (Or.inl rfl)
  have mj : j = h ∨ j = i ∨ j = j ∨ j = k := Or.inr (Or.inr (Or.inl rfl))
  have mk : k = h ∨ k = i ∨ k = j ∨ k = k := Or.inr (Or.inr (Or.inr rfl))
  have hhi : J.Adj h i := hall h i ehi mh mi
  have hhj : J.Adj h j := hall h j ehj mh mj
  have hhk : J.Adj h k := hall h k ehk mh mk
  have hij : J.Adj i j := hall i j eij mi mj
  have hik : J.Adj i k := hall i k eik mi mk
  have hjk : J.Adj j k := hall j k ejk mj mk
  -- the rung of `R` on `jk` is anticomplete to `f₁`
  have hndjk : [j, k, h, i].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      and_true, not_or]
    tauto
  have hjkanti : Anticomplete G {x : V | x ∈ R j k} F := htrav.2.2.2 j k hjk hndjk
  -- change the choice on the edge `hj` to take `L`
  obtain ⟨Rc, hRc, hRchj, hRceq⟩ :=
    Thm85EndgameOptimalChoice.exists_rung_choice_replacing hSN R hR hhj hL
  obtain ⟨p, q, htrav₂⟩ := hclaim4 Rc (hclaim5 Rc hRc)
  have hpq : p ≠ q := htrav₂.1.ne
  have hRcjk : Rc j k = R j k := by
    refine hRceq j k hjk ?_
    intro hc
    rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact ehj h1.symm
    · exact ehk h2.symm
  have hRckj : Rc k j = R k j := by
    refine hRceq k j hjk.symm ?_
    intro hc
    rcases Sym2.eq_iff.mp hc with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ehk h1.symm
    · exact ejk h1.symm
  -- an end of a traversal sees a neighbour of `f₁` on every incident edge but its own
  have hpj : p = j → q = k := by
    intro hp
    by_contra hqk
    obtain ⟨r, hrR, -, hu⟩ := htrav₂.2.1 k (fun hc => hqk hc.symm) (by rw [hp]; exact hjk)
    rw [hp, hRcjk] at hrR
    exact hjkanti r hrR f₁ hf₁F hu.2.2.1
  have hpk : p = k → q = j := by
    intro hp
    by_contra hqj
    obtain ⟨r, hrR, -, hu⟩ := htrav₂.2.1 j (fun hc => hqj hc.symm) (by rw [hp]; exact hjk.symm)
    rw [hp, hRckj, hR.2 j k hjk, List.mem_reverse] at hrR
    exact hjkanti r hrR f₁ hf₁F hu.2.2.1
  have hqj : q = j → p = k := by
    intro hq
    by_contra hpk'
    obtain ⟨r, hrR, -, hu⟩ := htrav₂.2.2.1 k (fun hc => hpk' hc.symm) (by rw [hq]; exact hjk)
    rw [hq, hRcjk] at hrR
    exact hjkanti r hrR f₁ hf₁F hu.2.2.1
  have hqk : q = k → p = j := by
    intro hq
    by_contra hpj'
    obtain ⟨r, hrR, -, hu⟩ := htrav₂.2.2.1 j (fun hc => hpj' hc.symm) (by rw [hq]; exact hjk.symm)
    rw [hq, hRckj, hR.2 j k hjk, List.mem_reverse] at hrR
    exact hjkanti r hrR f₁ hf₁F hu.2.2.1
  -- so the traversal of the changed choice is `hi` or `jk`
  have key : s(p, q) = s(h, i) ∨ s(p, q) = s(j, k) := by
    by_cases hp1 : p = j
    · exact Or.inr (by rw [hp1, hpj hp1])
    by_cases hp2 : p = k
    · exact Or.inr (by rw [hp2, hpk hp2]; exact Sym2.eq_swap)
    by_cases hq1 : q = j
    · exact absurd (hqj hq1) hp2
    by_cases hq2 : q = k
    · exact absurd (hqk hq2) hp1
    have hpin : p = h ∨ p = i := by
      rcases hcover p with a | a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · exact absurd a hp1
      · exact absurd a hp2
    have hqin : q = h ∨ q = i := by
      rcases hcover q with a | a | a | a
      · exact Or.inl a
      · exact Or.inr a
      · exact absurd a hq1
      · exact absurd a hq2
    refine Or.inl ?_
    rcases hpin with hp | hp <;> rcases hqin with hq | hq
    · exact absurd (hp.trans hq.symm) hpq
    · rw [hp, hq]
    · rw [hp, hq]; exact Sym2.eq_swap
    · exact absurd (hp.trans hq.symm) hpq
  rcases key with hkey | hkey
  · -- the traversal is `hi` again: the first bullet on the edge `hj` is what we want
    have htrav₃ : IsTraversal G J N F f₁ f₁ Rc h i := by
      rcases Sym2.eq_iff.mp hkey with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at htrav₂; exact htrav₂
      · have hsw := traversal_swap htrav₂
        rw [e1, e2] at hsw
        exact hsw
    obtain ⟨r, hrR, hrN, hu⟩ := htrav₃.2.1 j (fun hc => eij hc.symm) hhj
    rw [hRchj] at hrR hu
    exact ⟨r, hrR, hrN, hu⟩
  · -- the traversal is `jk`: the three other cross rungs of `R` collapse
    exfalso
    have htrav₃ : IsTraversal G J N F f₁ f₁ Rc j k := by
      rcases Sym2.eq_iff.mp hkey with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [e1, e2] at htrav₂; exact htrav₂
      · have hsw := traversal_swap htrav₂
        rw [e1, e2] at hsw
        exact hsw
    -- an edge of the changed choice other than `hj` is unchanged
    have hRcne : ∀ u v : U, J.Adj u v → ¬ (u = h ∧ v = j) → ¬ (u = j ∧ v = h) →
        Rc u v = R u v := by
      intro u v huv h1 h2
      refine hRceq u v huv ?_
      intro hc
      rcases Sym2.eq_iff.mp hc with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact h1 ⟨e1, e2⟩
      · exact h2 ⟨e1, e2⟩
    -- `R i j` has length `0`
    have hRcji : Rc j i = R j i :=
      hRcne j i hij.symm (fun hc => ehj hc.1.symm) (fun hc => ehi hc.2.symm)
    obtain ⟨r₁, hr₁R, hr₁N, hu₁⟩ := htrav₃.2.1 i eik hij.symm
    rw [hRcji] at hr₁R hu₁
    obtain ⟨r₁', hr₁'R, hr₁'N, hu₁'⟩ := htrav.2.2.1 j (fun hc => ehj hc.symm) hij
    have hr₁'mem : r₁' ∈ {x : V | x ∈ R j i} := by
      show r₁' ∈ R j i
      rw [hR.2 i j hij, List.mem_reverse]
      exact hr₁'R
    have hr₁eq : r₁' = r₁ := (hu₁.2.2.2 r₁' hr₁'mem f₁ hf₁F hu₁'.2.2.1).1
    have hz_ij : pathLength (R i j) = 0 :=
      Thm85EndgameK4Shape.zero_rung_of_common_end (hR.1 i j hij) hr₁'R hr₁'N
        (by rw [hr₁eq]; exact hr₁N)
    -- `R i k` has length `0`
    have hRcki : Rc k i = R k i :=
      hRcne k i hik.symm (fun hc => ehk hc.1.symm) (fun hc => ejk hc.1.symm)
    obtain ⟨r₂, hr₂R, hr₂N, hu₂⟩ := htrav₃.2.2.1 i eij hik.symm
    rw [hRcki] at hr₂R hu₂
    obtain ⟨r₂', hr₂'R, hr₂'N, hu₂'⟩ := htrav.2.2.1 k (fun hc => ehk hc.symm) hik
    have hr₂'mem : r₂' ∈ {x : V | x ∈ R k i} := by
      show r₂' ∈ R k i
      rw [hR.2 i k hik, List.mem_reverse]
      exact hr₂'R
    have hr₂eq : r₂' = r₂ := (hu₂.2.2.2 r₂' hr₂'mem f₁ hf₁F hu₂'.2.2.1).1
    have hz_ik : pathLength (R i k) = 0 :=
      Thm85EndgameK4Shape.zero_rung_of_common_end (hR.1 i k hik) hr₂'R hr₂'N
        (by rw [hr₂eq]; exact hr₂N)
    -- `R h k` has length `0`
    have hRckh : Rc k h = R k h :=
      hRcne k h hhk.symm (fun hc => ehk hc.1.symm) (fun hc => ejk hc.1.symm)
    obtain ⟨r₃, hr₃R, hr₃N, hu₃⟩ := htrav₃.2.2.1 h ehj hhk.symm
    rw [hRckh] at hr₃R hu₃
    obtain ⟨r₃', hr₃'R, hr₃'N, hu₃'⟩ := htrav.2.1 k (fun hc => eik hc.symm) hhk
    have hr₃'mem : r₃' ∈ {x : V | x ∈ R k h} := by
      show r₃' ∈ R k h
      rw [hR.2 h k hhk, List.mem_reverse]
      exact hr₃'R
    have hr₃eq : r₃' = r₃ := (hu₃.2.2.2 r₃' hr₃'mem f₁ hf₁F hu₃'.2.2.1).1
    have hz_hk : pathLength (R h k) = 0 :=
      Thm85EndgameK4Shape.zero_rung_of_common_end (hR.1 h k hhk) hr₃'R hr₃'N
        (by rw [hr₃eq]; exact hr₃N)
    -- the four rungs of `R` round the cycle `h-j-i-k-h`
    have hzip : ([h, j, i, k] : List U).zip (([h, j, i, k] : List U).rotate 1)
        = [(h, j), (j, i), (i, k), (k, h)] := by
      simp [List.rotate_cons_succ]
    have hnd4 : ([h, j, i, k] : List U).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
        not_false_eq_true, and_true, not_or, or_false]
      exact ⟨⟨ehj, ehi, ehk⟩, ⟨fun hc => eij hc.symm, ejk⟩, eik⟩
    have hadj4 : ∀ pr ∈ ([h, j, i, k] : List U).zip (([h, j, i, k] : List U).rotate 1),
        J.Adj pr.1 pr.2 := by
      rw [hzip]
      intro pr hpr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpr
      rcases hpr with rfl | rfl | rfl | rfl
      · exact hhj
      · exact hij.symm
      · exact hik
      · exact hhk.symm
    have heven := Thm81CycleEven.even_cycle_sum G hG J S N hSN [h, j, i, k]
      (by simp) hnd4 hadj4 R (fun pr hpr => hR.1 pr.1 pr.2 (hadj4 pr hpr))
    rw [hzip] at heven
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      List.length_cons, List.length_nil] at heven
    have hji : pathLength (R j i) = pathLength (R i j) := by
      rw [hR.2 i j hij, PathBasics.pathLength_reverse]
    have hkh : pathLength (R k h) = pathLength (R h k) := by
      rw [hR.2 h k hhk, PathBasics.pathLength_reverse]
    rw [hji, hkh, hz_ij, hz_ik, hz_hk] at heven
    have hevenhj : Even (pathLength (R h j)) := by
      rcases heven with ⟨m, hm⟩
      exact ⟨m - 2, by omega⟩
    -- the printed odd hole forbids a nonzero even `hj`-rung
    have hz_hj : pathLength (R h j) = 0 := by
      by_contra hne
      have hpos : 0 < pathLength (R h j) := Nat.pos_of_ne_zero hne
      obtain ⟨r₀, hr₀R, hr₀N, hu₀⟩ := htrav.2.1 j (fun hc => eij hc.symm) hhj
      have hr₁S : r₁ ∈ S i j :=
        StripSystemBasics.rung_subset_strip (hR.1 i j hij) r₁
          (by rw [hR.2 i j hij, List.mem_reverse] at hr₁R; exact hr₁R)
      have hodd := Thm85EndgamePathTwoVerticesGapHole.odd_of_pos hG hSN hij ehi
        (hR.1 h j hhj) hf₁out hr₀R hr₀N hu₀.2.2.1
        (fun x hx hadj => (hu₀.2.2.2 x hx f₁ hf₁F hadj).1)
        hr₁N hr₁S hu₁.2.2.1 hpos
      exact (Nat.not_odd_iff_even.mpr hevenhj) hodd
    -- all four rungs round the cycle have length `0`, so the appearance is degenerate
    obtain ⟨n, H, hForms⟩ :=
      Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph G hG J hJ S N hSN R hR.1 hR.2
    have hcover4 : ∀ u : U, u = h ∨ u = j ∨ u = i ∨ u = k := by
      intro u
      rcases hcover u with a | a | a | a
      · exact Or.inl a
      · exact Or.inr (Or.inr (Or.inl a))
      · exact Or.inr (Or.inl a)
      · exact Or.inr (Or.inr (Or.inr a))
    have hdegen : DegenerateAppearance J H :=
      Thm84K4CaseDegenerate.degenerate_of_zero_four_cycle hJ hSN hForms hK4 hnd4 hcover4
        hhj hij.symm hik hhk.symm hz_hj (by rw [hji]; exact hz_ij) hz_ik
        (by rw [hkh]; exact hz_hk)
    obtain ⟨-, hiso⟩ := hForms.2
    obtain ⟨phi⟩ := hiso
    exact (hclaim1 n H R _ phi rfl hForms).2 hK4 hdegen

end Workspace.ProofLemmas.Thm85EndgamePathTwoVerticesGapCross
