import Workspace.Types.Core
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.DeletedWitnessIsUnique

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.Types.ShapeFromUniqueAttachment

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm244Shapes

private theorem pathSet_sdiff_first
    {V : Type*} {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : 2 ≤ p.length) :
    ConnectedSet G ({w : V | w ∈ p} \ {a}) := by
  rcases p with _ | ⟨x, t⟩
  · simp at hlen
  · have hxa : x = a := by simpa using hp.2.1
    subst x
    have hnt : a ∉ t := (List.nodup_cons.mp hp.1.2.1).1
    have ht : IsPathList G t := by
      have htpos : 0 < t.length := by
        simp only [List.length_cons] at hlen
        omega
      simpa using Workspace.ProofLemmas.PathBasics.isPathList_drop hp.1 (k := 1) (by
        simpa using htpos)
    convert Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList ht using 1
    ext w
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff, List.mem_cons]
    constructor
    · rintro ⟨hw, hwa⟩
      rcases hw with hwa' | hw
      · exact absurd hwa' hwa
      · exact hw
    · intro hw
      exact ⟨Or.inr hw, fun h => hnt (h ▸ hw)⟩

private theorem pathSet_sdiff_last
    {V : Type*} {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : 2 ≤ p.length) :
    ConnectedSet G ({w : V | w ∈ p} \ {b}) := by
  have hr := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hp
  have hc := pathSet_sdiff_first hr (by simpa using hlen)
  simpa using hc

private theorem pathFrom_dropLast
    {V : Type*} {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : 2 ≤ p.length) :
    IsPathFrom G p.dropLast a (p[p.length - 2]'(by omega)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [List.dropLast_eq_take]
    exact Workspace.ProofLemmas.PathBasics.isPathList_take hp.1 (by omega)
  · have h0 : p[0]'(by omega) = a :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
    have hh := Workspace.ProofLemmas.PathBasics.head?_slice p
      (i := 0) (j := p.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : p.length - 2 - 0 + 1 = p.length - 1 := by omega
    rw [he] at hh
    simpa [h0] using hh
  · have hl := Workspace.ProofLemmas.PathBasics.getLast?_slice p
      (i := 0) (j := p.length - 2) (by omega) (by omega)
    rw [List.dropLast_eq_take]
    have he : p.length - 2 - 0 + 1 = p.length - 1 := by omega
    rw [he] at hl
    exact hl

theorem shapeFromUniqueAttachment
    {V : Type*} [Fintype V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V) (v : Fin 3 → V)
    (hv : ∀ i : Fin 3, v i ∈ F ∧ v i ∈ N i)
    (hpair : ∀ i j : Fin 3, i ≠ j → v i ≠ v j)
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ x ∈ S, x ∈ N i) → F.ncard ≤ S.ncard)
    (hfixed : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, v i ∈ S) → S = F)
    (Q R : List V) (z : V) (s : ℕ)
    (hQ : IsPathFrom G Q (v 0) (v 1))
    (hQF : ∀ w ∈ Q, w ∈ F)
    (hR : IsPathFrom G R (v 2) z)
    (hRF : ∀ w ∈ R, w ∈ F)
    (hv2Q : v 2 ∉ Q)
    (hzQ : z ∈ Q)
    (hRlen : 2 ≤ R.length)
    (hinter : {w : V | w ∈ R} ∩ {w : V | w ∈ Q} = {z})
    (hcover : F = {w : V | w ∈ Q} ∪ {w : V | w ∈ R})
    (hclean : ∀ (t d : ℕ) (ht : t + 2 < R.length) (hd : d < Q.length),
      ¬ G.Adj (R[t]'(by omega)) (Q[d]'hd))
    (hs : s < Q.length)
    (hzs : z = Q[s]'hs)
    (hattach : ∀ (d : ℕ) (hd : d < Q.length),
      G.Adj (R[R.length - 2]'(by omega)) (Q[d]'hd) ↔ d = s) :
    (∃ u : V, ∃ P : Fin 3 → List V, Spider G F N v u P) ∨
    (∃ i j k : Fin 3, ∃ P : List V, ∃ a b : V, ThroughPath G F N i j k P a b) := by
  classical
  have hQlen : 2 ≤ Q.length := by
    have hne := hpair 0 1 (by decide)
    by_contra hc
    have hlen : Q.length = 1 := by
      have := Workspace.ProofLemmas.PathBasics.path_length_pos hQ.1
      omega
    obtain ⟨q, rfl⟩ := List.length_eq_one_iff.mp hlen
    have e0 : q = v 0 := by simpa using hQ.2.1
    have e1 : q = v 1 := by simpa using hQ.2.2
    exact hne (e0.symm.trans e1)
  have hRz : R[R.length - 1]'(by omega) = z :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
  have hRpre := pathFrom_dropLast hR hRlen
  have hcross : ∀ x ∈ R.dropLast, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = R[R.length - 2]'(by omega) ∧ y = Q[s]'hs)) := by
    intro x hx y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_iff_getElem.mp hx
    obtain ⟨d, hd, rfl⟩ := List.mem_iff_getElem.mp hy
    have htR : t < R.length - 1 := by simpa using ht
    simp only [List.getElem_dropLast]
    by_cases hty : t = R.length - 2
    · subst t
      rw [hattach d hd]
      constructor
      · intro h
        constructor
        · rfl
        · subst d; rfl
      · rintro ⟨-, he⟩
        exact hQ.1.2.1.getElem_inj_iff.mp he
    · have hlt : t + 2 < R.length := by omega
      have hn := hclean t d hlt hd
      constructor
      · exact fun hadj => absurd hadj hn
      · rintro ⟨he, -⟩
        have het := hR.1.2.1.getElem_inj_iff.mp he
        exact absurd het hty
  have hdisj : ∀ x ∈ R.dropLast, x ∉ Q := by
    intro x hxR hxQ
    have hxR' : x ∈ R := List.mem_of_mem_dropLast hxR
    have hxI : x ∈ ({w : V | w ∈ R} ∩ {w : V | w ∈ Q}) := ⟨hxR', hxQ⟩
    rw [hinter] at hxI
    have hxz : x = z := by simpa using hxI
    subst x
    obtain ⟨t, ht, he⟩ := List.mem_iff_getElem.mp hxR
    have htR : t < R.length - 1 := by simpa using ht
    simp only [List.getElem_dropLast] at he
    have := hR.1.2.1.getElem_inj_iff.mp (he.trans hRz.symm)
    omega
  by_cases hleft : s = 0
  · subst s
    have hQ0 : Q[0]'hs = v 0 :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 hs
    have hT := Workspace.ProofLemmas.PathGlue.glue_path hRpre hQ hdisj (by
      intro x hx y hy
      simpa [hQ0] using hcross x hx y hy)
    have hTcover : F = {w : V | w ∈ R.dropLast ++ Q} := by
      rw [hcover]
      ext w
      simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append]
      constructor
      · rintro (hwQ | hwR)
        · exact Or.inr hwQ
        · by_cases hwz : w = z
          · subst w; exact Or.inr hzQ
          · exact Or.inl (List.mem_dropLast_of_mem_of_ne_getLast hwR (by
              have hget : R.getLast (Workspace.ProofLemmas.PathBasics.path_ne_nil hR.1) = z := by
                rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
                exact hR.2.2
              simpa [hget] using hwz))
      · rintro (hwR | hwQ)
        · exact Or.inr (List.mem_of_mem_dropLast hwR)
        · exact Or.inl hwQ
    have hfirst : ConnectedSet G (F \ {v 2}) := by
      rw [hTcover]
      exact pathSet_sdiff_first hT (by simp; omega)
    have hlast : ConnectedSet G (F \ {v 1}) := by
      rw [hTcover]
      exact pathSet_sdiff_last hT (by simp; omega)
    right
    refine ⟨2, 1, 0, R.dropLast ++ Q, v 2, v 1, ?_⟩
    refine ⟨by decide, by decide, by decide, hT, ?_, (hv 2).2, (hv 1).2, ?_, ?_, ?_⟩
    · intro w hw
      rw [hTcover]
      exact hw
    · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
        G F N v hv hpair hmin 2 hfirst
    · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
        G F N v hv hpair hmin 1 hlast
    · refine ⟨v 0, ?_, (hv 0).2⟩
      simp only [List.mem_append]
      exact Or.inr (Workspace.ProofLemmas.PathBasics.head_mem hQ.2.1)
  · by_cases hright : s + 1 = Q.length
    · have hsLast : s = Q.length - 1 := by omega
      have hQs : Q[s]'hs = v 1 := by
        exact (hQ.1.2.1.getElem_inj_iff.mpr hsLast).trans
          (Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega))
      have hQr := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hQ
      have hcross' : ∀ x ∈ R.dropLast, ∀ y ∈ Q.reverse,
          (G.Adj x y ↔ (x = R[R.length - 2]'(by omega) ∧ y = v 1)) := by
        intro x hx y hy
        have hyQ : y ∈ Q := by simpa using hy
        simpa [hQs] using hcross x hx y hyQ
      have hdisj' : ∀ x ∈ R.dropLast, x ∉ Q.reverse := by
        intro x hx hy
        exact hdisj x hx (by simpa using hy)
      have hT := Workspace.ProofLemmas.PathGlue.glue_path hRpre hQr hdisj' hcross'
      have hTcover : F = {w : V | w ∈ R.dropLast ++ Q.reverse} := by
        rw [hcover]
        ext w
        simp only [Set.mem_union, Set.mem_setOf_eq, List.mem_append, List.mem_reverse]
        constructor
        · rintro (hwQ | hwR)
          · exact Or.inr hwQ
          · by_cases hwz : w = z
            · subst w; exact Or.inr hzQ
            · exact Or.inl (List.mem_dropLast_of_mem_of_ne_getLast hwR (by
                have hget : R.getLast (Workspace.ProofLemmas.PathBasics.path_ne_nil hR.1) = z := by
                  rw [← Option.some_inj, ← List.getLast?_eq_some_getLast]
                  exact hR.2.2
                simpa [hget] using hwz))
        · rintro (hwR | hwQ)
          · exact Or.inr (List.mem_of_mem_dropLast hwR)
          · exact Or.inl hwQ
      have hfirst : ConnectedSet G (F \ {v 2}) := by
        rw [hTcover]
        exact pathSet_sdiff_first hT (by simp; omega)
      have hlast : ConnectedSet G (F \ {v 0}) := by
        rw [hTcover]
        exact pathSet_sdiff_last hT (by simp; omega)
      right
      refine ⟨2, 0, 1, R.dropLast ++ Q.reverse, v 2, v 0, ?_⟩
      refine ⟨by decide, by decide, by decide, hT, ?_, (hv 2).2, (hv 0).2, ?_, ?_, ?_⟩
      · intro w hw
        rw [hTcover]
        exact hw
      · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
          G F N v hv hpair hmin 2 hfirst
      · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
          G F N v hv hpair hmin 0 hlast
      · refine ⟨v 1, ?_, (hv 1).2⟩
        simp only [List.mem_append, List.mem_reverse]
        exact Or.inr (Workspace.ProofLemmas.PathBasics.getLast_mem hQ.2.2)
    · have hspos : 0 < s := by omega
      have hsint : s + 1 < Q.length := by omega
      have hz0 : z ≠ v 0 := by
        intro he
        have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
        have he' : Q[s]'hs = Q[0]'(by omega) := by rw [← hzs, he, ← h0]
        have := hQ.1.2.1.getElem_inj_iff.mp he'
        omega
      have hz1 : z ≠ v 1 := by
        intro he
        have hlast := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
        have he' : Q[s]'hs = Q[Q.length - 1]'(by omega) := by rw [← hzs, he, ← hlast]
        have := hQ.1.2.1.getElem_inj_iff.mp he'
        omega
      have hz2 : z ≠ v 2 := by
        intro he
        apply hv2Q
        rw [← he]
        exact hzQ
      have hv0R : v 0 ∉ R := by
        intro hvR
        have hvQ := Workspace.ProofLemmas.PathBasics.head_mem hQ.2.1
        have hi : v 0 ∈ ({w : V | w ∈ R} ∩ {w : V | w ∈ Q}) := ⟨hvR, hvQ⟩
        rw [hinter] at hi
        have heq : v 0 = z := by simpa using hi
        exact hz0 heq.symm
      have hv1R : v 1 ∉ R := by
        intro hvR
        have hvQ := Workspace.ProofLemmas.PathBasics.getLast_mem hQ.2.2
        have hi : v 1 ∈ ({w : V | w ∈ R} ∩ {w : V | w ∈ Q}) := ⟨hvR, hvQ⟩
        rw [hinter] at hi
        have heq : v 1 = z := by simpa using hi
        exact hz1 heq.symm
      have hQconn : ConnectedSet G {w : V | w ∈ Q} :=
        Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQ.1
      have hRconn : ConnectedSet G {w : V | w ∈ R} :=
        Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1
      have hdel0 : ConnectedSet G (F \ {v 0}) := by
        have hA := pathSet_sdiff_first hQ hQlen
        have hU := Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hA hRconn
          (Or.inl ⟨z, ⟨hzQ, hz0⟩, Workspace.ProofLemmas.PathBasics.getLast_mem hR.2.2⟩)
        convert hU using 1
        ext w
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq]
        rw [hcover]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hwQ | hwR, hwne⟩
          · exact Or.inl ⟨hwQ, hwne⟩
          · exact Or.inr hwR
        · rintro (⟨hwQ, hwne⟩ | hwR)
          · exact ⟨Or.inl hwQ, hwne⟩
          · exact ⟨Or.inr hwR, fun he => hv0R (he ▸ hwR)⟩
      have hdel1 : ConnectedSet G (F \ {v 1}) := by
        have hA := pathSet_sdiff_last hQ hQlen
        have hU := Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hA hRconn
          (Or.inl ⟨z, ⟨hzQ, hz1⟩, Workspace.ProofLemmas.PathBasics.getLast_mem hR.2.2⟩)
        convert hU using 1
        ext w
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq]
        rw [hcover]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hwQ | hwR, hwne⟩
          · exact Or.inl ⟨hwQ, hwne⟩
          · exact Or.inr hwR
        · rintro (⟨hwQ, hwne⟩ | hwR)
          · exact ⟨Or.inl hwQ, hwne⟩
          · exact ⟨Or.inr hwR, fun he => hv1R (he ▸ hwR)⟩
      have hdel2 : ConnectedSet G (F \ {v 2}) := by
        have hB := pathSet_sdiff_first hR hRlen
        have hU := Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hQconn hB
          (Or.inl ⟨z, hzQ, ⟨Workspace.ProofLemmas.PathBasics.getLast_mem hR.2.2, hz2⟩⟩)
        convert hU using 1
        ext w
        simp only [Set.mem_diff, Set.mem_singleton_iff, Set.mem_union, Set.mem_setOf_eq]
        rw [hcover]
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro ⟨hwQ | hwR, hwne⟩
          · exact Or.inl hwQ
          · exact Or.inr ⟨hwR, hwne⟩
        · rintro (hwQ | ⟨hwR, hwne⟩)
          · exact ⟨Or.inl hwQ, fun he => hv2Q (he ▸ hwQ)⟩
          · exact ⟨Or.inr hwR, hwne⟩
      have huniq : ∀ i : Fin 3, ∀ w ∈ F, w ∈ N i → w = v i := by
        intro i
        fin_cases i
        · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
            G F N v hv hpair hmin 0 hdel0
        · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
            G F N v hv hpair hmin 1 hdel1
        · exact Workspace.Types.DeletedWitnessIsUnique.deletedWitnessIsUnique
            G F N v hv hpair hmin 2 hdel2
      have hP0 : IsPathFrom G (Q.take (s + 1)) (v 0) z := by
        have hp := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hQ.1
          (i := 0) (j := s) hspos hs
        have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
        simpa [h0, ← hzs] using hp
      have hP1 : IsPathFrom G (Q.drop s).reverse (v 1) z := by
        have hp := Workspace.ProofLemmas.PathBasics.isPathFrom_slice hQ.1
          (i := s) (j := Q.length - 1) (by omega) (by omega)
        have hlast := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
        have hpr := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hp
        have he : Q.length - 1 - s + 1 = (Q.drop s).length := by
          simp only [List.length_drop]
          omega
        rw [he, List.take_length] at hpr
        simpa [hlast, ← hzs] using hpr
      have hsepQ : ∀ a ∈ Q.take (s + 1), ∀ b ∈ (Q.drop s).reverse,
          a ≠ z → b ≠ z → a ≠ b ∧ ¬ G.Adj a b := by
        intro a ha b hb haz hbz
        obtain ⟨ia, hia, hea⟩ := List.mem_iff_getElem.mp ha
        have hiaQ : ia < Q.length := by
          rw [List.length_take] at hia
          omega
        have heaQ : Q[ia]'hiaQ = a := by
          simpa only [List.getElem_take] using hea
        have hb' : b ∈ Q.drop s := by simpa using hb
        obtain ⟨ib, hib, heb⟩ := List.mem_iff_getElem.mp hb'
        have hibQ : s + ib < Q.length := by
          simp only [List.length_drop] at hib
          omega
        have hebQ : Q[s + ib]'hibQ = b := by
          simpa only [List.getElem_drop] using heb
        have hiale : ia ≤ s := by rw [List.length_take] at hia; omega
        have hiane : ia ≠ s := by
          intro he
          apply haz
          have heq : Q[ia]'hiaQ = Q[s]'hs := hQ.1.2.1.getElem_inj_iff.mpr he
          exact heaQ.symm.trans (heq.trans hzs.symm)
        have hibpos : 0 < ib := by
          by_contra hc
          have he : ib = 0 := by omega
          apply hbz
          have heq : Q[s + ib]'hibQ = Q[s]'hs :=
            hQ.1.2.1.getElem_inj_iff.mpr (by omega)
          exact hebQ.symm.trans (heq.trans hzs.symm)
        constructor
        · intro he
          have hi := hQ.1.2.1.getElem_inj_iff.mp (heaQ.trans (he.trans hebQ.symm))
          omega
        · intro hadj
          have hadj' : G.Adj (Q[ia]'hiaQ) (Q[s + ib]'hibQ) := by
            simpa [heaQ, hebQ] using hadj
          rcases (Workspace.ProofLemmas.PathBasics.path_adj_iff hQ.1 hiaQ hibQ).mp hadj' with h | h
          · omega
          · omega
      have hsepRQ : ∀ a ∈ R, ∀ b ∈ Q, a ≠ z → b ≠ z →
          a ≠ b ∧ ¬ G.Adj a b := by
        intro a ha b hb haz hbz
        obtain ⟨ia, hia, hea⟩ := List.mem_iff_getElem.mp ha
        obtain ⟨ib, hib, heb⟩ := List.mem_iff_getElem.mp hb
        have hianlast : ia ≠ R.length - 1 := by
          intro he
          apply haz
          have heq : R[ia]'hia = R[R.length - 1]'(by omega) :=
            hR.1.2.1.getElem_inj_iff.mpr he
          exact hea.symm.trans (heq.trans hRz)
        have hiaBefore : ia < R.length - 1 := by omega
        have hibne : ib ≠ s := by
          intro he
          apply hbz
          have heq : Q[ib]'hib = Q[s]'hs := hQ.1.2.1.getElem_inj_iff.mpr he
          exact heb.symm.trans (heq.trans hzs.symm)
        constructor
        · intro heab
          have hi : a ∈ ({w : V | w ∈ R} ∩ {w : V | w ∈ Q}) := ⟨ha, heab ▸ hb⟩
          rw [hinter] at hi
          exact haz (by simpa using hi)
        · by_cases hiy : ia = R.length - 2
          · intro hadj
            have hadj' : G.Adj (R[R.length - 2]'(by omega)) (Q[ib]'hib) := by
              simpa [← hea, ← heb, hiy] using hadj
            exact hibne ((hattach ib hib).mp hadj')
          · have hiClean : ia + 2 < R.length := by omega
            intro hadj
            apply hclean ia ib hiClean hib
            simpa [hea, heb] using hadj
      left
      refine ⟨z, fun i => if i = 0 then Q.take (s + 1)
        else if i = 1 then (Q.drop s).reverse else R, ?_⟩
      refine ⟨fun i => (hv i).2, huniq, ?_, ?_, ?_, ?_⟩
      · intro i
        fin_cases i <;> simp [hz0, hz1, hz2]
      · intro i
        fin_cases i
        · simpa using hP0
        · simpa using hP1
        · simpa using hR
      · intro i w hw
        fin_cases i
        · apply hQF w
          exact (List.take_sublist (s + 1) Q).subset (by simpa using hw)
        · apply hQF w
          exact (List.drop_sublist s Q).subset (by simpa using hw)
        · exact hRF w (by simpa using hw)
      · intro i j hij a ha b hb haz hbz
        fin_cases i <;> fin_cases j
        all_goals simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte] at ha hb
        all_goals try { exact absurd rfl hij }
        · exact hsepQ a ha b hb haz hbz
        · have h := hsepRQ b hb a ((List.take_sublist (s + 1) Q).subset ha) hbz haz
          exact ⟨h.1.symm, fun hadj => h.2 hadj.symm⟩
        · have h := hsepQ b hb a ha hbz haz
          exact ⟨h.1.symm, fun hadj => h.2 hadj.symm⟩
        · have h := hsepRQ b hb a ((List.drop_sublist s Q).subset (by simpa using ha)) hbz haz
          exact ⟨h.1.symm, fun hadj => h.2 hadj.symm⟩
        · exact hsepRQ a ha b ((List.take_sublist (s + 1) Q).subset hb) haz hbz
        · exact hsepRQ a ha b ((List.drop_sublist s Q).subset (by simpa using hb)) haz hbz

end Workspace.Types.ShapeFromUniqueAttachment
