import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.LK33eAppearance

/-!
# The exceptional six-hole endgame in 15.5

This packages the last paragraph of the printed proof of 15.5.  The six rim vertices are
`p 0, ..., p 5`; `p 0` and `p 3` are `X`-complete, and antipaths with interior in `X` join
both opposite rim edges `p 1 p 2` and `p 4 p 5`.  Choosing a shortest such antipath forces
its two opposite rim attachments to occur at its two ends.  A longer interior gives a long
prism in the complement; an interior of size two gives either `L(K₃,₃ \ e)` or a double
diamond.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm155SixHoleEndgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT

variable {V : Type*}

private theorem eq_cons_interior_append_of_isPathFrom {G : SimpleGraph V} {P : List V}
    {a b : V} (hP : IsPathFrom G P a b) (hab : a ≠ b) :
    P = a :: (interior P ++ [b]) := by
  rcases P with _ | ⟨x, l⟩
  · simp [IsPathFrom, IsPathList] at hP
  · have hxa : x = a := by simpa using hP.2.1
    subst x
    have hl : l ≠ [] := by
      intro he
      subst l
      have : a = b := by simpa using hP.2.2
      exact hab this
    have hlast : l.getLast? = some b := by
      have h := hP.2.2
      rwa [List.getLast?_cons_of_ne_nil hl] at h
    simp only [Workspace.Types.Core.SPGT.interior, List.tail_cons]
    rw [List.dropLast_append_getLast? b hlast]

private theorem adj_head_interior {H : SimpleGraph V} {P : List V} {a b x : V}
    (hP : IsPathFrom H P a b) (h3 : 3 ≤ P.length) (hx : x ∈ interior P) :
    (H.Adj a x ↔ x = P[1]'(by omega)) := by
  have hpos : 0 < P.length := by omega
  have h0 : P[0]'hpos = a := PathBasics.getElem_zero_of_head? hP.2.1 hpos
  obtain ⟨i, hi, hi1, hi2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hx
  constructor
  · intro hadj
    rw [← h0] at hadj
    exact hP.1.2.1.getElem_inj_iff.mpr (by
      rcases (PathBasics.path_adj_iff hP.1 hpos hi).mp hadj with h | h <;> omega)
  · intro he
    have hi' : i = 1 := hP.1.2.1.getElem_inj_iff.mp he
    rw [← h0]
    exact (PathBasics.path_adj_iff hP.1 hpos hi).mpr (by omega)

private theorem adj_last_interior {H : SimpleGraph V} {P : List V} {a b x : V}
    (hP : IsPathFrom H P a b) (h3 : 3 ≤ P.length) (hx : x ∈ interior P) :
    (H.Adj b x ↔ x = P[P.length - 2]'(by omega)) := by
  have hpos : 0 < P.length := by omega
  have hlast : P[P.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  obtain ⟨i, hi, hi1, hi2, rfl⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hx
  constructor
  · intro hadj
    rw [← hlast] at hadj
    exact hP.1.2.1.getElem_inj_iff.mpr (by
      rcases (PathBasics.path_adj_iff hP.1 (by omega) hi).mp hadj with h | h <;> omega)
  · intro he
    have hi' : i = P.length - 2 := hP.1.2.1.getElem_inj_iff.mp he
    rw [← hlast]
    exact (PathBasics.path_adj_iff hP.1 (by omega) hi).mpr (by omega)

/- A shortest path between either of two pairs, when both vertices of the other pair attach
somewhere to its interior, forces the two attachments to be the two opposite ends. -/
private theorem shortest_cross_attachments
    {H : SimpleGraph V} {q : List V} (hq : IsPathList H q) (hqpos : 0 < q.length)
    {W : Set V} (hqW : ∀ z ∈ q, z ∈ W)
    {c d : V} (hcd : ¬ H.Adj c d) (hcne : c ≠ d) (hcq : c ∉ q) (hdq : d ∉ q)
    (hcn : ∃ i : ℕ, ∃ hi : i < q.length, H.Adj c (q[i]'hi))
    (hdn : ∃ i : ℕ, ∃ hi : i < q.length, H.Adj d (q[i]'hi))
    (hmin : ∀ S : List V, IsPathFrom H S c d →
      (∀ z ∈ interior S, z ∈ W) → q.length + 1 ≤ pathLength S) :
    ((H.Adj c (q[0]'hqpos) ∧
        (∀ i : ℕ, ∀ hi : i < q.length, 0 < i → ¬ H.Adj c (q[i]'hi))) ∧
      (H.Adj d (q[q.length - 1]'(by omega)) ∧
        (∀ i : ℕ, ∀ hi : i < q.length, i + 1 < q.length → ¬ H.Adj d (q[i]'hi)))) ∨
    ((H.Adj d (q[0]'hqpos) ∧
        (∀ i : ℕ, ∀ hi : i < q.length, 0 < i → ¬ H.Adj d (q[i]'hi))) ∧
      (H.Adj c (q[q.length - 1]'(by omega)) ∧
        (∀ i : ℕ, ∀ hi : i < q.length, i + 1 < q.length → ¬ H.Adj c (q[i]'hi)))) := by
  classical
  let Cross := fun n : ℕ => ∃ i : ℕ, ∃ hi : i < q.length,
    ∃ j : ℕ, ∃ hj : j < q.length, i ≤ j ∧
      ((H.Adj c (q[i]'hi) ∧ H.Adj d (q[j]'hj)) ∨
        (H.Adj d (q[i]'hi) ∧ H.Adj c (q[j]'hj))) ∧ j - i = n
  have hex : ∃ n, Cross n := by
    obtain ⟨i, hi, hci⟩ := hcn
    obtain ⟨j, hj, hdj⟩ := hdn
    rcases le_total i j with hij | hji
    · exact ⟨j - i, i, hi, j, hj, hij, Or.inl ⟨hci, hdj⟩, rfl⟩
    · exact ⟨i - j, j, hj, i, hi, hji, Or.inr ⟨hdj, hci⟩, rfl⟩
  let n := Nat.find hex
  obtain ⟨i, hi, j, hj, hij, horient, hn⟩ := Nat.find_spec hex
  have hspan_min : ∀ i' : ℕ, ∀ hi' : i' < q.length,
      ∀ j' : ℕ, ∀ hj' : j' < q.length, i' ≤ j' →
      ((H.Adj c (q[i']'hi') ∧ H.Adj d (q[j']'hj')) ∨
        (H.Adj d (q[i']'hi') ∧ H.Adj c (q[j']'hj'))) → n ≤ j' - i' := by
    intro i' hi' j' hj' hij' ho'
    exact Nat.find_min' hex ⟨i', hi', j', hj', hij', ho', rfl⟩
  have finish (c₀ d₀ : V)
      (hpair : (c₀ = c ∧ d₀ = d) ∨ (c₀ = d ∧ d₀ = c))
      (hci : H.Adj c₀ (q[i]'hi)) (hdj : H.Adj d₀ (q[j]'hj)) :
      (H.Adj c₀ (q[0]'hqpos) ∧
          ∀ r : ℕ, ∀ hr : r < q.length, 0 < r → ¬ H.Adj c₀ (q[r]'hr)) ∧
        (H.Adj d₀ (q[q.length - 1]'(by omega)) ∧
          ∀ r : ℕ, ∀ hr : r < q.length, r + 1 < q.length →
            ¬ H.Adj d₀ (q[r]'hr)) := by
    have orient (r : ℕ) (hr : r < q.length) (s : ℕ) (hs : s < q.length)
        (hrs : r ≤ s) (hcr : H.Adj c₀ (q[r]'hr)) (hds : H.Adj d₀ (q[s]'hs)) :
        (H.Adj c (q[r]'hr) ∧ H.Adj d (q[s]'hs)) ∨
          (H.Adj d (q[r]'hr) ∧ H.Adj c (q[s]'hs)) := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl ⟨hcr, hds⟩
      · exact Or.inr ⟨hcr, hds⟩
    let R := (q.drop i).take (j - i + 1)
    have hRlen : R.length = j - i + 1 := by
      exact PathBasics.length_slice q hij hj
    have hR : IsPathFrom H R (q[i]'hi) (q[j]'hj) := by
      refine ⟨PathBasics.isPathList_take (PathBasics.isPathList_drop hq hi) (by omega), ?_, ?_⟩
      · exact PathBasics.head?_slice q hij hj
      · exact PathBasics.getLast?_slice q hij hj
    have hcR : c₀ ∉ R := by
      intro hm
      have hmq : c₀ ∈ q := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hcq hmq
      · exact hdq hmq
    have hdR : d₀ ∉ R := by
      intro hm
      have hmq : d₀ ∈ q := List.mem_of_mem_drop (List.mem_of_mem_take hm)
      rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hdq hmq
      · exact hcq hmq
    have hcother : ∀ z ∈ R, z ≠ q[i]'hi → ¬ H.Adj c₀ z := by
      intro z hz hzi hcz
      obtain ⟨r, hr, hir, hrj, hrz⟩ := (PathBasics.mem_slice_iff q hij hj).mp hz
      have hir' : i < r := by
        by_contra hnri
        have hre : r = i := by omega
        subst r
        exact hzi hrz.symm
      have ho := orient r hr j hj (by omega) (by simpa only [hrz] using hcz) hdj
      have hm := hspan_min r hr j hj (by omega) ho
      omega
    have hdother : ∀ z ∈ R, z ≠ q[j]'hj → ¬ H.Adj d₀ z := by
      intro z hz hzj hdz
      obtain ⟨r, hr, hir, hrj, hrz⟩ := (PathBasics.mem_slice_iff q hij hj).mp hz
      have hrj' : r < j := by
        by_contra hnrj
        have hre : r = j := by omega
        subst r
        exact hzj hrz.symm
      have ho := orient i hi r hr (by omega) hci (by simpa only [hrz] using hdz)
      have hm := hspan_min i hi r hr (by omega) ho
      omega
    have hcd₀ : ¬ H.Adj c₀ d₀ := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcd
      · exact fun hh => hcd hh.symm
    have hcne₀ : c₀ ≠ d₀ := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcne
      · exact hcne.symm
    have hS : IsPathFrom H (c₀ :: (R ++ [d₀])) c₀ d₀ :=
      PathAttach.isPathFrom_cons_concat hR hci hdj hcd₀ hcne₀ hcR hdR hcother hdother
    have hSint : ∀ z ∈ interior (c₀ :: (R ++ [d₀])), z ∈ W := by
      intro z hz
      have hzR : z ∈ R := by simpa [R, Workspace.Types.Core.SPGT.interior] using hz
      exact hqW z (List.mem_of_mem_drop (List.mem_of_mem_take hzR))
    have hSlength : pathLength (c₀ :: (R ++ [d₀])) = j - i + 2 := by
      rw [PathAttach.pathLength_cons_append_singleton, hRlen]
    have hlower : q.length + 1 ≤ pathLength (c₀ :: (R ++ [d₀])) := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hmin _ hS hSint
      · have hm := hmin _ (PathBasics.isPathFrom_reverse hS) (by
          intro z hz
          exact hSint z (PathBasics.mem_interior_reverse.mp hz))
        simpa only [PathBasics.pathLength_reverse] using hm
    have hspan : j - i = q.length - 1 := by
      rw [hSlength] at hlower
      omega
    have hi0 : i = 0 := by omega
    have hjlast : j + 1 = q.length := by omega
    have hcfirst : H.Adj c₀ (q[0]'hqpos) := by
      have he : q[i]'hi = q[0]'hqpos := hq.2.1.getElem_inj_iff.mpr hi0
      rwa [← he]
    have hdlast : H.Adj d₀ (q[q.length - 1]'(by omega)) := by
      have he : q[j]'hj = q[q.length - 1]'(by omega) :=
        hq.2.1.getElem_inj_iff.mpr (by omega)
      rwa [← he]
    refine ⟨⟨hcfirst, ?_⟩, hdlast, ?_⟩
    · intro r hr hrpos hcr
      have ho := orient r hr j hj (by omega) hcr hdj
      have hm := hspan_min r hr j hj (by omega) ho
      omega
    · intro r hr hrlast hdr
      have ho := orient i hi r hr (by omega) hci hdr
      have hm := hspan_min i hi r hr (by omega) ho
      omega
  rcases horient with ho | ho
  · have h := finish c d (Or.inl ⟨rfl, rfl⟩) ho.1 ho.2
    exact Or.inl h
  · have h := finish d c (Or.inr ⟨rfl, rfl⟩) ho.1 ho.2
    exact Or.inr h

set_option maxHeartbeats 10000000 in
private theorem minimal_gap_absurd [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : InF6 G) (p : Fin 6 → V) (hp_inj : Function.Injective p)
    (hp_adj : ∀ i j, G.Adj (p i) (p j) ↔
      (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6))
    (X : Set V) (hXanti : AnticonnectedSet G X) (hpX : ∀ i, p i ∉ X)
    (hp0X : VertexComplete G (p 0) X) (hp3X : VertexComplete G (p 3) X)
    (Q : List V) (hQ : IsAntipathFrom G Q (p 1) (p 2))
    (hQint : ∀ z ∈ interior Q, z ∈ X)
    (hmin : ∀ S : List V,
      ((IsAntipathFrom G S (p 1) (p 2) ∨ IsAntipathFrom G S (p 4) (p 5)) ∧
        (∀ z ∈ interior S, z ∈ X)) → pathLength Q ≤ pathLength S) : False := by
  classical
  have hBerge : Berge G := hG.1.1.1
  have pne (i j : Fin 6) (hij : i ≠ j) : p i ≠ p j := hp_inj.ne hij
  have padj (i j : Fin 6)
      (h : j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6) : G.Adj (p i) (p j) :=
    (hp_adj i j).mpr h
  have pnadj (i j : Fin 6)
      (h : ¬ (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6)) :
      ¬ G.Adj (p i) (p j) := fun ha => h ((hp_adj i j).mp ha)
  have cp (i j : Fin 6) (hne : i ≠ j)
      (hn : ¬ (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6)) :
      Gᶜ.Adj (p i) (p j) := ⟨pne i j hne, pnadj i j hn⟩
  have h12 : G.Adj (p 1) (p 2) := padj 1 2 (by decide)
  have h45 : G.Adj (p 4) (p 5) := padj 4 5 (by decide)
  have hQ3 : 3 ≤ Q.length := AntiholeCompletion.three_le_length_of_antipath hQ h12
  let q := interior Q
  have hshape : Q = p 1 :: (q ++ [p 2]) :=
    eq_cons_interior_append_of_isPathFrom hQ (pne 1 2 (by decide))
  have hQe : IsAntipathFrom G (p 1 :: (q ++ [p 2])) (p 1) (p 2) := by
    rw [← hshape]
    exact hQ
  have hQeint : interior (p 1 :: (q ++ [p 2])) = q := by
    simp [Workspace.Types.Core.SPGT.interior]
  have hQlen : Q.length = q.length + 2 := by rw [hshape]; simp
  have hqpos : 0 < q.length := by omega
  have hQefirst : (p 1 :: (q ++ [p 2]))[1]'(by simp) = q[0]'hqpos := by
    simp [List.getElem_append_left hqpos]
  have hQelast :
      (p 1 :: (q ++ [p 2]))[(p 1 :: (q ++ [p 2])).length - 2]'(by simp) =
        q[q.length - 1]'(by omega) := by
    have hidx : (p 1 :: (q ++ [p 2])).length - 2 = (q.length - 1) + 1 := by
      simp
      omega
    have hc := List.getElem_cons_succ (p 1) (q ++ [p 2]) (q.length - 1) (by simp)
    have ha : (q ++ [p 2])[q.length - 1]'(by simp) =
        q[q.length - 1]'(by omega) :=
      List.getElem_append_left (bs := [p 2]) (show q.length - 1 < q.length by omega)
    exact (getElem_congr rfl hidx (by simp)).trans (hc.trans ha)
  have hqpath : IsPathList Gᶜ q := (PathGlue.isPathFrom_interior hQ.1 hQ3).1
  have hqX : ∀ z ∈ q, z ∈ X := by simpa [q] using hQint
  have hQL : pathLength Q = q.length + 1 := by
    rw [hshape, PathAttach.pathLength_cons_append_singleton]

  -- The fixed antipath through the two `X`-complete opposite rim vertices makes `Q` odd.
  let R : List V := [p 1, p 3, p 0, p 2]
  have hR : IsAntipathFrom G R (p 1) (p 2) := by
    refine ⟨PathGlue.isPathList_four ?_ (cp 1 3 (by decide) (by decide))
      (cp 3 0 (by decide) (by decide)) (cp 0 2 (by decide) (by decide)) ?_ ?_ ?_, rfl,
      by simp [R]⟩
    · simp [R, pne 1 3 (by decide), pne 1 0 (by decide), pne 1 2 (by decide),
        pne 3 0 (by decide), pne 3 2 (by decide), pne 0 2 (by decide)]
    · intro h; exact h.2 (padj 1 0 (by decide))
    · intro h; exact h.2 h12
    · intro h; exact h.2 (padj 3 2 (by decide))
  have hRX : Disjoint ({p 3, p 0} : Set V) X := by
    apply Set.disjoint_left.mpr
    intro z hz hzx
    rcases hz with rfl | rfl
    · exact hpX 3 hzx
    · exact hpX 0 hzx
  have hRXcomp : Complete G ({p 3, p 0} : Set V) X := by
    intro z hz
    rcases hz with rfl | rfl
    · exact hp3X
    · exact hp0X
  have hRint : ∀ z ∈ interior R, z ∈ ({p 3, p 0} : Set V) := by
    intro z hz
    simpa [R, Workspace.Types.Core.SPGT.interior] using hz
  have hQodd : Odd (pathLength Q) := by
    have he := AntiholeCompletion.even_add_pathLength_of_two_antipaths hBerge hRX hRXcomp h12
      (by simp [pne 1 3 (by decide), pne 1 0 (by decide)])
      (by simp [pne 2 3 (by decide), pne 2 0 (by decide)])
      (hpX 1) (hpX 2) hQ hQint hR hRint
    have hRl : pathLength R = 3 := by rfl
    rw [hRl, Nat.even_iff] at he
    rw [Nat.odd_iff]
    omega

  have miss (r : Fin 6) (hr1 : r ≠ 1) (hr2 : r ≠ 2)
      (hn1 : ¬ G.Adj (p r) (p 1)) (hn2 : ¬ G.Adj (p r) (p 2)) :
      ∃ z ∈ q, ¬ G.Adj (p r) z := by
    by_contra hn
    push Not at hn
    have heven := AntiholeCompletion.even_pathLength_of_witness hBerge h12
      (X := {z : V | z ∈ q}) (z := p r) (fun z hz => hn z hz)
      hn1 hn2 (pne r 1 hr1) (pne r 2 hr2) hQ (by simpa [q])
    exact Nat.not_even_iff_odd.mpr hQodd heven
  have hmiss4 : ∃ z ∈ q, ¬ G.Adj (p 4) z :=
    miss 4 (by decide) (by decide) (pnadj 4 1 (by decide)) (pnadj 4 2 (by decide))
  have hmiss5 : ∃ z ∈ q, ¬ G.Adj (p 5) z :=
    miss 5 (by decide) (by decide) (pnadj 5 1 (by decide)) (pnadj 5 2 (by decide))
  have hcnot : p 4 ∉ q := fun hm => hpX 4 (hqX _ hm)
  have hdnot : p 5 ∉ q := fun hm => hpX 5 (hqX _ hm)
  have hcn : ∃ i : ℕ, ∃ hi : i < q.length, Gᶜ.Adj (p 4) (q[i]'hi) := by
    obtain ⟨z, hz, hnz⟩ := hmiss4
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    exact ⟨i, hi, fun he => hcnot (he ▸ List.getElem_mem hi), hnz⟩
  have hdn : ∃ i : ℕ, ∃ hi : i < q.length, Gᶜ.Adj (p 5) (q[i]'hi) := by
    obtain ⟨z, hz, hnz⟩ := hmiss5
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
    exact ⟨i, hi, fun he => hdnot (he ▸ List.getElem_mem hi), hnz⟩
  have hcrossMin : ∀ S : List V, IsAntipathFrom G S (p 4) (p 5) →
      (∀ z ∈ interior S, z ∈ X) → q.length + 1 ≤ pathLength S := by
    intro S hS hSint
    rw [← hQL]
    exact hmin S ⟨Or.inr hS, hSint⟩
  have hattach := shortest_cross_attachments hqpath hqpos hqX
    (fun hc => hc.2 h45) (pne 4 5 (by decide)) hcnot hdnot hcn hdn hcrossMin

  have finish (c d : V)
      (hpair : (c = p 4 ∧ d = p 5) ∨ (c = p 5 ∧ d = p 4))
      (hc : Gᶜ.Adj c (q[0]'hqpos) ∧
        ∀ i : ℕ, ∀ hi : i < q.length, 0 < i → ¬ Gᶜ.Adj c (q[i]'hi))
      (hd : Gᶜ.Adj d (q[q.length - 1]'(by omega)) ∧
        ∀ i : ℕ, ∀ hi : i < q.length, i + 1 < q.length → ¬ Gᶜ.Adj d (q[i]'hi)) : False := by
    have hcX : c ∉ X := by
      rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hpX 4
      · exact hpX 5
    have hdX : d ∉ X := by
      rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact hpX 5
      · exact hpX 4
    have hc1 : Gᶜ.Adj c (p 1) := by
      rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact cp 4 1 (by decide) (by decide)
      · exact cp 5 1 (by decide) (by decide)
    have hc2 : Gᶜ.Adj c (p 2) := by
      rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact cp 4 2 (by decide) (by decide)
      · exact cp 5 2 (by decide) (by decide)
    have hd1 : Gᶜ.Adj d (p 1) := by
      rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact cp 5 1 (by decide) (by decide)
      · exact cp 4 1 (by decide) (by decide)
    have hd2 : Gᶜ.Adj d (p 2) := by
      rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact cp 5 2 (by decide) (by decide)
      · exact cp 4 2 (by decide) (by decide)
    have hcdG : G.Adj c d := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h45
      · exact h45.symm
    have hcne : c ≠ d := hcdG.ne
    have hc2ne : c ≠ p 2 := hc2.ne
    have hd1ne : d ≠ p 1 := hd1.ne
    have hqfrom : IsPathFrom Gᶜ q (q[0]'hqpos) (q[q.length - 1]'(by omega)) := by
      refine ⟨hqpath, ?_, ?_⟩
      · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hqpos]
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
    by_cases hqle : q.length ≤ 2
    · have hqoddlen : Odd (q.length + 1) := by rw [← hQL]; exact hQodd
      have hq2 : q.length = 2 := by
        rw [Nat.odd_iff] at hqoddlen
        omega
      obtain ⟨r, s, hqrs⟩ := PathGlue.length_eq_two hq2
      have hrX : r ∈ X := by apply hqX; simp [hqrs]
      have hsX : s ∈ X := by apply hqX; simp [hqrs]
      have hrsC : Gᶜ.Adj r s := by
        have hh := PathBasics.path_adj_succ hqpath (i := 0) (by simpa [hqrs])
        simpa [hqrs] using hh
      have hrne : r ≠ s := hrsC.1
      have prne (i : Fin 6) : p i ≠ r := fun he => hpX i (he ▸ hrX)
      have psne (i : Fin 6) : p i ≠ s := fun he => hpX i (he ▸ hsX)
      have hQliteral : IsPathFrom Gᶜ [p 1, r, s, p 2] (p 1) (p 2) := by
        simpa [hqrs] using hQe
      have hp1rC : Gᶜ.Adj (p 1) r :=
        PathBasics.path_adj_succ hQliteral.1 (i := 0) (by simp)
      have hrsC' : Gᶜ.Adj r s :=
        PathBasics.path_adj_succ hQliteral.1 (i := 1) (by simp)
      have hsp2C : Gᶜ.Adj s (p 2) :=
        PathBasics.path_adj_succ hQliteral.1 (i := 2) (by simp)
      have hp1s : G.Adj (p 1) s := by
        by_contra hn
        exact PathBasics.path_not_adj_of_gap hQliteral.1 (i := 0) (j := 2)
          (by simp) (by simp) (by omega) (by omega) ⟨psne 1, hn⟩
      have hrp2 : G.Adj r (p 2) := by
        by_contra hn
        exact PathBasics.path_not_adj_of_gap hQliteral.1 (i := 1) (j := 3)
          (by simp) (by simp) (by omega) (by omega) ⟨(prne 2).symm, hn⟩
      have hcrC : Gᶜ.Adj c r := by simpa [hqrs] using hc.1
      have hcs : G.Adj c s := by
        by_contra hn
        have hh : Gᶜ.Adj c s := ⟨fun he => hcX (he ▸ hsX), hn⟩
        exact hc.2 1 (by simpa [hqrs]) (by omega) (by simpa [hqrs] using hh)
      have hdr : G.Adj d r := by
        by_contra hn
        have hh : Gᶜ.Adj d r := ⟨fun he => hdX (he ▸ hrX), hn⟩
        exact hd.2 0 (by simpa [hqrs]) (by simp [hqrs]) (by simpa [hqrs] using hh)
      have hdsC : Gᶜ.Adj d s := by
        have hh := hd.1
        simpa [hqrs] using hh
      have hp0r := hp0X r hrX
      have hp0s := hp0X s hsX
      have hp3r := hp3X r hrX
      have hp3s := hp3X s hsX
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · -- This pairing is `L(K₃,₃ \ e)`.
        have contra := LK33eAppearance.not_inF3_of_LK33e
          (G := G)
          (fun a => (![![p 0, r, p 5], ![s, p 3, p 4], ![p 1, p 2, p 0]] :
            Fin 3 → Fin 3 → V) a.1 a.2)
          (by
            rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb hab
            have ha' : ¬ (a₁ = 2 ∧ a₂ = 2) := by
              rintro ⟨h₁, h₂⟩; exact ha (Prod.ext h₁ h₂)
            have hb' : ¬ (b₁ = 2 ∧ b₂ = 2) := by
              rintro ⟨h₁, h₂⟩; exact hb (Prod.ext h₁ h₂)
            have hab' : ¬ (a₁ = b₁ ∧ a₂ = b₂) := by
              rintro ⟨h₁, h₂⟩; exact hab (Prod.ext h₁ h₂)
            fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
              norm_num [Fin.ext_iff] at ha' <;>
              norm_num [Fin.ext_iff] at hb' <;>
              norm_num [Fin.ext_iff] at hab' <;>
              simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
              norm_num [Fin.ext_iff] <;>
              first
                | exact hp_inj.ne (by decide)
                | exact prne _
                | exact (prne _).symm
                | exact psne _
                | exact (psne _).symm
                | exact hrne
                | exact hrne.symm)
          (by
            have a01 := padj 0 1 (by decide); have a05 := padj 0 5 (by decide)
            have a12 := padj 1 2 (by decide); have a23 := padj 2 3 (by decide)
            have a34 := padj 3 4 (by decide); have a45 := padj 4 5 (by decide)
            have n02 := pnadj 0 2 (by decide); have n03 := pnadj 0 3 (by decide)
            have n04 := pnadj 0 4 (by decide); have n13 := pnadj 1 3 (by decide)
            have n14 := pnadj 1 4 (by decide); have n15 := pnadj 1 5 (by decide)
            have n24 := pnadj 2 4 (by decide); have n25 := pnadj 2 5 (by decide)
            have n35 := pnadj 3 5 (by decide)
            have a10 := a01.symm; have a50 := a05.symm; have a21 := a12.symm
            have a32 := a23.symm; have a43 := a34.symm; have a54 := a45.symm
            have n20 : ¬ G.Adj (p 2) (p 0) := fun h => n02 h.symm
            have n30 : ¬ G.Adj (p 3) (p 0) := fun h => n03 h.symm
            have n40 : ¬ G.Adj (p 4) (p 0) := fun h => n04 h.symm
            have n31 : ¬ G.Adj (p 3) (p 1) := fun h => n13 h.symm
            have n41 : ¬ G.Adj (p 4) (p 1) := fun h => n14 h.symm
            have n51 : ¬ G.Adj (p 5) (p 1) := fun h => n15 h.symm
            have n42 : ¬ G.Adj (p 4) (p 2) := fun h => n24 h.symm
            have n52 : ¬ G.Adj (p 5) (p 2) := fun h => n25 h.symm
            have n53 : ¬ G.Adj (p 5) (p 3) := fun h => n35 h.symm
            have rp0 := hp0r.symm; have rp3 := hp3r.symm; have rp5 := hdr.symm
            have sp0 := hp0s.symm; have sp3 := hp3s.symm; have sp4 := hcs.symm
            have nrp1 : ¬ G.Adj r (p 1) := fun h => hp1rC.2 h.symm
            have nrp4 : ¬ G.Adj r (p 4) := fun h => hcrC.2 h.symm
            have nsp2 : ¬ G.Adj s (p 2) := hsp2C.2
            have nsp5 : ¬ G.Adj s (p 5) := fun h => hdsC.2 h.symm
            have nrs : ¬ G.Adj r s := hrsC.2
            have nsr : ¬ G.Adj s r := fun h => hrsC.2 h.symm
            rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ha hb hab
            have ha' : ¬ (a₁ = 2 ∧ a₂ = 2) := by
              rintro ⟨h₁, h₂⟩; exact ha (Prod.ext h₁ h₂)
            have hb' : ¬ (b₁ = 2 ∧ b₂ = 2) := by
              rintro ⟨h₁, h₂⟩; exact hb (Prod.ext h₁ h₂)
            have hab' : ¬ (a₁ = b₁ ∧ a₂ = b₂) := by
              rintro ⟨h₁, h₂⟩; exact hab (Prod.ext h₁ h₂)
            fin_cases a₁ <;> fin_cases a₂ <;> fin_cases b₁ <;> fin_cases b₂ <;>
              norm_num [Fin.ext_iff] at ha' <;>
              norm_num [Fin.ext_iff] at hb' <;>
              norm_num [Fin.ext_iff] at hab' <;>
              simp only [Matrix.cons_val_zero', Matrix.cons_val_succ'] <;>
              norm_num [Fin.ext_iff] <;>
              first
                | exact (by assumption)
                | exact G.symm (by assumption)
                | exact fun h => (by have := G.symm h; contradiction))
        exact contra hG.1.1
      · -- The other pairing is a double diamond.
        apply hG.2
        refine ⟨p 0, s, p 1, p 5, r, p 3, p 2, p 4, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [List.nodup_cons, List.mem_cons, List.mem_singleton,
            List.not_mem_nil, or_false, not_or]
          constructor
          · exact ⟨psne 0, pne 0 1 (by decide), pne 0 5 (by decide), prne 0,
              pne 0 3 (by decide), pne 0 2 (by decide), pne 0 4 (by decide)⟩
          constructor
          · exact ⟨(psne 1).symm, (psne 5).symm, hrne.symm, (psne 3).symm,
              (psne 2).symm, (psne 4).symm⟩
          constructor
          · exact ⟨pne 1 5 (by decide), prne 1, pne 1 3 (by decide),
              pne 1 2 (by decide), pne 1 4 (by decide)⟩
          constructor
          · exact ⟨prne 5, pne 5 3 (by decide), pne 5 2 (by decide),
              pne 5 4 (by decide)⟩
          constructor
          · exact ⟨(prne 3).symm, (prne 2).symm, (prne 4).symm⟩
          constructor
          · exact ⟨pne 3 2 (by decide), pne 3 4 (by decide)⟩
          exact ⟨pne 2 4 (by decide), by simp⟩
        · exact ⟨hp0s, padj 0 1 (by decide), padj 0 5 (by decide), hp1s.symm,
            hcs.symm, pnadj 1 5 (by decide)⟩
        · exact ⟨hp3r.symm, hrp2, hdr.symm, padj 3 2 (by decide), padj 3 4 (by decide),
            pnadj 2 4 (by decide)⟩
        · exact ⟨hp0r, hp3s.symm, h12, h45.symm⟩
        · exact ⟨pnadj 0 3 (by decide), pnadj 0 2 (by decide), pnadj 0 4 (by decide),
            by exact fun hh => hrsC.2 hh.symm,
            hsp2C.2,
            by exact fun hh => hdsC.2 hh.symm,
            hp1rC.2, pnadj 1 3 (by decide), pnadj 1 4 (by decide),
            hcrC.2, pnadj 5 3 (by decide), pnadj 5 2 (by decide)⟩
    · -- More than two internal vertices gives a long prism in `Gᶜ`.
      have hq3 : 3 ≤ q.length := by omega
      let r := q[0]'hqpos
      let s := q[q.length - 1]'(by omega)
      have hrX : r ∈ X := by simpa [r] using hqX _ (List.getElem_mem hqpos)
      have hsX : s ∈ X := by simpa [s] using hqX _ (List.getElem_mem (by omega))
      have hrsne : r ≠ s := by
        simpa [r, s] using PathBasics.path_ne_of_ne_index hqpath hqpos (by omega) (by omega)
      have prne (i : Fin 6) : p i ≠ r := fun he => hpX i (he ▸ hrX)
      have psne (i : Fin 6) : p i ≠ s := fun he => hpX i (he ▸ hsX)
      have hQe3 : 3 ≤ (p 1 :: (q ++ [p 2])).length := by
        simp only [List.length_cons, List.length_append, List.length_singleton]
        omega
      have hrp1 : Gᶜ.Adj r (p 1) := by
        have hh := (adj_head_interior hQe hQe3
          (by rw [hQeint]; exact List.getElem_mem hqpos)).mpr ?_
        · exact hh.symm
        · rw [hQefirst]
      have hsp2 : Gᶜ.Adj s (p 2) := by
        have hsmem : s ∈ interior (p 1 :: (q ++ [p 2])) := by
          rw [hQeint]
          exact List.getElem_mem (show q.length - 1 < q.length by omega)
        have hh := (adj_last_interior hQe hQe3 hsmem).mpr ?_
        · exact hh.symm
        · exact (by simpa [s] using hQelast.symm)
      have hP2 : IsPathFrom Gᶜ [c, p 2] c (p 2) :=
        ⟨PathBasics.isPathList_pair hc2, rfl, by simp⟩
      have hP3 : IsPathFrom Gᶜ [p 1, d] (p 1) d :=
        ⟨PathBasics.isPathList_pair hd1.symm, rfl, by simp⟩
      have e12 : ∀ z ∈ q, ∀ w ∈ [c, p 2],
          (Gᶜ.Adj z w ↔ (z = r ∧ w = c) ∨ (z = s ∧ w = p 2)) := by
        intro z hz w hw
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          by_cases hi0 : i = 0
          · subst i; exact iff_of_true hc.1.symm (Or.inl ⟨rfl, rfl⟩)
          · exact iff_of_false (fun hh => hc.2 i hi (by omega) hh.symm) (by
              rintro (⟨he, -⟩ | ⟨he, hh⟩)
              · exact hi0 (hqpath.2.1.getElem_inj_iff.mp he)
              · exact hc2ne hh)
        · constructor
          · intro hh
            have he := (adj_last_interior hQe hQe3
              (by rw [hQeint]; exact hz)).mp hh.symm
            exact Or.inr ⟨he.trans (by simpa using hQelast), rfl⟩
          · rintro (⟨-, he⟩ | ⟨rfl, -⟩)
            · exact absurd he.symm hc2ne
            · exact hsp2
      have e13 : ∀ z ∈ q, ∀ w ∈ [p 1, d],
          (Gᶜ.Adj z w ↔ (z = r ∧ w = p 1) ∨ (z = s ∧ w = d)) := by
        intro z hz w hw
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · constructor
          · intro hh
            have he := (adj_head_interior hQe hQe3
              (by rw [hQeint]; exact hz)).mp hh.symm
            exact Or.inl ⟨he.trans (by rw [hQefirst]), rfl⟩
          · rintro (⟨rfl, -⟩ | ⟨-, he⟩)
            · exact hrp1
            · exact absurd he.symm hd1ne
        · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hz
          by_cases hil : i + 1 = q.length
          · have he : q[i]'hi = s := hqpath.2.1.getElem_inj_iff.mpr (by omega)
            exact iff_of_true (by rw [he]; exact hd.1.symm) (Or.inr ⟨he, rfl⟩)
          · exact iff_of_false (fun hh => hd.2 i hi (by omega) hh.symm) (by
              rintro (⟨he, hh⟩ | ⟨he, -⟩)
              · exact hd1ne hh
              · exact hil (by
                  have := hqpath.2.1.getElem_inj_iff.mp he
                  omega))
      have e23 : ∀ z ∈ [c, p 2], ∀ w ∈ [p 1, d],
          (Gᶜ.Adj z w ↔ (z = c ∧ w = p 1) ∨ (z = p 2 ∧ w = d)) := by
        intro z hz w hw
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hz hw
        rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
        · exact iff_of_true hc1 (Or.inl ⟨rfl, rfl⟩)
        · exact iff_of_false (fun hh => hh.2 hcdG) (by
            rintro (⟨-, he⟩ | ⟨he, -⟩)
            · exact hd1ne he
            · exact hc2ne he)
        · exact iff_of_false (fun hh => hh.2 h12.symm) (by
            rintro (⟨he, -⟩ | ⟨-, he⟩)
            · exact hc2ne he.symm
            · exact hd1ne he.symm)
        · exact iff_of_true hd2.symm (Or.inr ⟨rfl, rfl⟩)
      have hlong := PrismBasics.formPrism_mk
        (G := Gᶜ) (P₁ := q) (P₂ := [c, p 2]) (P₃ := [p 1, d])
        hc.1.symm hrp1 hc1 hsp2 hd.1.symm hd2.symm
        hrsne (prne 2).symm (by
          rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact (prne 5).symm
          · exact (prne 4).symm)
        (by
          rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact psne 4
          · exact psne 5)
        (by
          rcases hpair with ⟨rfl, -⟩ | ⟨rfl, -⟩
          · exact pne 4 2 (by decide)
          · exact pne 5 2 (by decide))
        hcne
        (psne 1) (pne 1 2 (by decide)) (by
          rcases hpair with ⟨-, rfl⟩ | ⟨-, rfl⟩
          · exact pne 1 5 (by decide)
          · exact pne 1 4 (by decide))
        hqfrom hP2 hP3 e12 e13 e23 (Or.inl (by simp [pathLength]; omega))
      exact hG.1.2.2 hlong
  rcases hattach with h | h
  · exact finish (p 4) (p 5) (Or.inl ⟨rfl, rfl⟩) h.1 h.2
  · exact finish (p 5) (p 4) (Or.inr ⟨rfl, rfl⟩) h.1 h.2

/-- The last, six-hole configuration of the proof of 15.5.  The two antipaths
are the ones supplied by the two applications of 13.6; choosing a globally
shortest one licenses the attachment argument in `minimal_gap_absurd`. -/
theorem six_hole_endgame_absurd [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (hG : InF6 G) (p : Fin 6 → V) (hp_inj : Function.Injective p)
    (hp_adj : ∀ i j, G.Adj (p i) (p j) ↔
      (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6))
    (X : Set V) (hXanti : AnticonnectedSet G X) (hpX : ∀ i, p i ∉ X)
    (hp0X : VertexComplete G (p 0) X) (hp3X : VertexComplete G (p 3) X)
    (hA : ∃ Q : List V, IsAntipathFrom G Q (p 1) (p 2) ∧
      ∀ z ∈ interior Q, z ∈ X)
    (hB : ∃ Q : List V, IsAntipathFrom G Q (p 4) (p 5) ∧
      ∀ z ∈ interior Q, z ∈ X) : False := by
  classical
  let Good := fun Q : List V =>
    (IsAntipathFrom G Q (p 1) (p 2) ∨ IsAntipathFrom G Q (p 4) (p 5)) ∧
      ∀ z ∈ interior Q, z ∈ X
  have hex : ∃ n : ℕ, ∃ Q : List V, Good Q ∧ pathLength Q = n := by
    obtain ⟨Q, hQ, hi⟩ := hA
    exact ⟨pathLength Q, Q, ⟨Or.inl hQ, hi⟩, rfl⟩
  obtain ⟨Q, hQ, hQlen⟩ := Nat.find_spec hex
  have hmin : ∀ S : List V, Good S → pathLength Q ≤ pathLength S := by
    intro S hS
    rw [hQlen]
    exact Nat.find_min' hex ⟨S, hS, rfl⟩
  rcases hQ with ⟨hQ | hQ, hQint⟩
  · exact minimal_gap_absurd hG p hp_inj hp_adj X hXanti hpX hp0X hp3X
      Q hQ hQint hmin
  · let p' : Fin 6 → V := ![p 3, p 4, p 5, p 0, p 1, p 2]
    have hp'_inj : Function.Injective p' := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp [p'] at hij ⊢
      all_goals exact hp_inj.ne (by decide) hij
    have hp'_adj : ∀ i j, G.Adj (p' i) (p' j) ↔
        (j.val = (i.val + 1) % 6 ∨ i.val = (j.val + 1) % 6) := by
      intro i j
      fin_cases i <;> fin_cases j <;> simp [p']
      all_goals
        first
          | exact (hp_adj _ _).mpr (by decide)
          | exact fun h => by have hh := (hp_adj _ _).mp h; norm_num at hh
    have hp'X : ∀ i, p' i ∉ X := by
      intro i; fin_cases i <;> simp [p', hpX]
    have hmin' : ∀ S : List V,
        ((IsAntipathFrom G S (p' 1) (p' 2) ∨ IsAntipathFrom G S (p' 4) (p' 5)) ∧
          (∀ z ∈ interior S, z ∈ X)) →
        pathLength Q ≤ pathLength S := by
      intro S hS
      apply hmin S
      rcases hS with ⟨h | h, hi⟩
      · exact ⟨Or.inr (by simpa [p'] using h), hi⟩
      · exact ⟨Or.inl (by simpa [p'] using h), hi⟩
    exact minimal_gap_absurd hG p' hp'_inj hp'_adj X hXanti hp'X
      (by simpa [p'] using hp3X) (by simpa [p'] using hp0X)
      Q (by simpa [p'] using hQ) hQint hmin'

end Workspace.ProofLemmas.Thm155SixHoleEndgame
