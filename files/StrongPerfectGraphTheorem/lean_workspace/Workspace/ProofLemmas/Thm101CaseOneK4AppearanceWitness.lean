import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm101ThetaOfPrism
import Workspace.ProofLemmas.Thm101ThetaAddBranch
import Workspace.ProofLemmas.Thm101ThetaBranchVerticesAreK4
import Workspace.ProofLemmas.Thm101ThetaBipartite
import Workspace.ProofLemmas.Thm101ThetaNondegenerate
import Workspace.Statements.S07.Thm_7_2

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData

private theorem mem_of_mem_trackEdges {W : Type*} {q : List W} {e : Sym2 W}
    (he : e ∈ trackEdges q) {w : W} (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

/-- The two host-graph edges representing adjacent vertices of one prism rung meet at an
internal point of the corresponding theta track, and these are exactly the two edges incident
with that point. -/
private theorem thetaAttachmentPoint
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {K : Set V} {m : ℕ} {Theta : SimpleGraph (Fin m)}
    {x y : Fin m} {Q : Fin 3 → List (Fin m)}
    (phi : Theta.lineGraph ≃g G.induce K)
    (hTheta : IsThetaDatum Theta x y Q)
    {i : Fin 3} {R : List V}
    (hQR : (Q i).length = R.length + 1)
    (hcorr : ∀ (k : ℕ) (hk : k + 1 < (Q i).length),
      ∃ he : s((Q i)[k]'(by omega), (Q i)[k + 1]'hk) ∈ Theta.edgeSet,
        R[k]? = some (↑(phi ⟨_, he⟩) : V))
    (hR : IsPathList G R) {u u' : V}
    (hu : u ∈ R) (hu' : u' ∈ R) (huu' : G.Adj u u') :
    ∃ z : Fin m, z ∈ trackInterior (Q i) ∧
      ∀ e : Theta.edgeSet,
        z ∈ (e : Sym2 (Fin m)) ↔ ((↑(phi e) : V) = u ∨ (↑(phi e) : V) = u') := by
  classical
  obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu
  obtain ⟨k, hk, hku⟩ := List.mem_iff_getElem.mp hu'
  have hadj : G.Adj (R[j]'hj) (R[k]'hk) := by simpa [hju, hku] using huu'
  have hjk := (Workspace.ProofLemmas.PathBasics.path_adj_iff hR hj hk).mp hadj
  obtain ⟨hxy, htrack, hlen, hdisj, hint, hcover, hedges⟩ := hTheta
  have forward : ∀ (p q : ℕ) (hp : p < R.length) (hq : q < R.length)
      (v v' : V), R[p]'hp = v → R[q]'hq = v' → p + 1 = q →
      ∃ z : Fin m, z ∈ trackInterior (Q i) ∧
        ∀ e : Theta.edgeSet,
          z ∈ (e : Sym2 (Fin m)) ↔ ((↑(phi e) : V) = v ∨ (↑(phi e) : V) = v') := by
    intro p q hp hq v v' hpv hqv hpq
    subst q
    have hpQ : p + 1 < (Q i).length := by rw [hQR]; omega
    have hp2Q : p + 2 < (Q i).length := by rw [hQR]; omega
    let z : Fin m := (Q i)[p + 1]'hpQ
    have hz : z ∈ trackInterior (Q i) := by
      exact Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem (Q i) p hp2Q
    obtain ⟨hep, hmapp⟩ := hcorr p hpQ
    obtain ⟨heq, hmapq⟩ := hcorr (p + 1) hp2Q
    let ep : Theta.edgeSet :=
      ⟨s((Q i)[p]'(by omega), (Q i)[p + 1]'hpQ), hep⟩
    let eq : Theta.edgeSet :=
      ⟨s((Q i)[p + 1]'hpQ, (Q i)[p + 2]'hp2Q), heq⟩
    have hphiEp : (↑(phi ep) : V) = v := by
      have hm := hmapp
      rw [List.getElem?_eq_getElem hp] at hm
      exact (Option.some_injective _ hm).symm.trans hpv
    have hphiEq : (↑(phi eq) : V) = v' := by
      have hm := hmapq
      rw [List.getElem?_eq_getElem hq] at hm
      exact (Option.some_injective _ hm).symm.trans hqv
    refine ⟨z, hz, ?_⟩
    intro e
    constructor
    · intro hze
      have heUnion : (e : Sym2 (Fin m)) ∈ ⋃ r : Fin 3, trackEdges (Q r) := by
        rw [← hedges]
        exact e.property
      simp only [Set.mem_iUnion] at heUnion
      obtain ⟨r, her⟩ := heUnion
      have hzQr : z ∈ Q r := mem_of_mem_trackEdges her hze
      have hri : r = i := by
        by_contra hne
        exact hdisj i r (fun h => hne h.symm) z hz hzQr
      subst r
      obtain ⟨t, ht, het⟩ := her
      have hends : z = (Q i)[t]'(by omega) ∨ z = (Q i)[t + 1]'ht := by
        rw [het] at hze
        exact Sym2.mem_iff.mp hze
      have hnd : (Q i).Nodup := (htrack i).1.2.1
      have hindex : t = p ∨ t = p + 1 := by
        rcases hends with h | h
        · have heqIndex : p + 1 = t := hnd.getElem_inj_iff.mp h
          exact Or.inr heqIndex.symm
        · have heqIndex : p + 1 = t + 1 := hnd.getElem_inj_iff.mp h
          exact Or.inl (by omega)
      rcases hindex with rfl | htp
      · left
        have heEp : e = ep := by
          apply Subtype.ext
          exact het
        rw [heEp]
        exact hphiEp
      · right
        have htEq : t = p + 1 := htp
        subst t
        have heEq : e = eq := by
          apply Subtype.ext
          exact het
        rw [heEq]
        exact hphiEq
    · rintro (hmap | hmap)
      · have heEp : e = ep := by
          apply phi.injective
          apply Subtype.ext
          exact hmap.trans hphiEp.symm
        rw [heEp]
        exact Sym2.mem_mk_right _ _
      · have heEq : e = eq := by
          apply phi.injective
          apply Subtype.ext
          exact hmap.trans hphiEq.symm
        rw [heEq]
        exact Sym2.mem_mk_left _ _
  rcases hjk with hjk | hkj
  · exact forward j k hj hk u u' hju hku hjk
  · obtain ⟨z, hz, hinc⟩ := forward k j hk hj u' u hku hju hkj
    refine ⟨z, hz, ?_⟩
    intro e
    rw [hinc e]
    tauto

theorem Thm101CaseOneK4AppearanceWitness
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K : Set V) (f : List V) (f₁ fn u u' w w' : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hf : IsPathFrom G f f₁ fn)
    (hfK : ∀ x ∈ f, x ∈ Kᶜ)
    (hfNonmajor : ∀ x ∈ f, ¬ MajorForPrism G a b x)
    (hu : u ∈ R 0) (hu' : u' ∈ R 0) (huu' : G.Adj u u')
    (hf₁u : G.Adj f₁ u) (hf₁u' : G.Adj f₁ u')
    (hw : w ∈ R 1) (hw' : w' ∈ R 1) (hww' : G.Adj w w')
    (hfnw : G.Adj fn w) (hfnw' : G.Adj fn w')
    (hother : ∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
      (x = f₁ ∧ (k = u ∨ k = u')) ∨ (x = fn ∧ (k = w ∨ k = w'))) :
    ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (K' : Set V),
      K' = K ∪ {x : V | x ∈ f} ∧
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
      (NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∨
        (DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ∧
          pathLength (R 0) = 1 ∧ pathLength (R 1) = 1)) := by
  classical
  obtain ⟨Theta, x, y, Q, phi, hTheta⟩ :=
    Thm101ThetaOfPrism G a b R K hprism hK
  have hR0 : IsPathFrom G (R 0) (a 0) (b 0) := hprism.2.2.2.1
  have hR1 : IsPathFrom G (R 1) (a 1) (b 1) := hprism.2.2.2.2.1
  obtain ⟨z, hz, hzinc⟩ := thetaAttachmentPoint phi hTheta.1
    (hTheta.2.1 0) (hTheta.2.2 0) hR0.1 hu hu' huu'
  obtain ⟨z', hz', hz'inc⟩ := thetaAttachmentPoint phi hTheta.1
    (hTheta.2.1 1) (hTheta.2.2 1) hR1.1 hw hw' hww'
  obtain ⟨hxy, htracks, hlengths, hdisjoint, hinteriors, hcover, hedges⟩ := hTheta.1
  have hzQ0 : z ∈ Q 0 :=
    List.mem_of_mem_tail (List.mem_of_mem_dropLast hz)
  have hz'Q1 : z' ∈ Q 1 :=
    List.mem_of_mem_tail (List.mem_of_mem_dropLast hz')
  have hzz' : z ≠ z' := by
    intro heq
    apply hdisjoint 0 1 (by decide) z hz
    rw [heq]
    exact hz'Q1
  have hznadj : ¬ Theta.Adj z z' := by
    intro hadj
    have hedge : s(z, z') ∈ Theta.edgeSet := (SimpleGraph.mem_edgeSet Theta).mpr hadj
    rw [hedges] at hedge
    simp only [Set.mem_iUnion] at hedge
    obtain ⟨i, hi⟩ := hedge
    have hzQi : z ∈ Q i := mem_of_mem_trackEdges hi (Sym2.mem_mk_left _ _)
    have hz'Qi : z' ∈ Q i := mem_of_mem_trackEdges hi (Sym2.mem_mk_right _ _)
    have hi0 : i = 0 := by
      by_contra hne
      exact hdisjoint 0 i (fun h => hne h.symm) z hz hzQi
    subst i
    exact hdisjoint 1 0 (by decide) z' hz' hz'Qi
  have huK : u ∈ K := by
    rw [hK]
    exact Or.inl (Or.inl hu)
  have hu'K : u' ∈ K := by
    rw [hK]
    exact Or.inl (Or.inl hu')
  have hwK : w ∈ K := by
    rw [hK]
    exact Or.inl (Or.inr hw)
  have hw'K : w' ∈ K := by
    rw [hK]
    exact Or.inl (Or.inr hw')
  obtain ⟨H, rho, p, psi, hext, hplen⟩ :=
    Thm101ThetaAddBranch G K _ Theta phi z z' hzz' hznadj
      f f₁ fn u u' w w' hf hfK huK hu'K hwK hw'K huu' hww'
      hf₁u hf₁u' hfnw hfnw' hother hzinc hz'inc
  have hbranch :=
    Thm101ThetaBranchVerticesAreK4 Theta x y Q
      ⟨hxy, htracks, hlengths, hdisjoint, hinteriors, hcover, hedges⟩
      z z' hz hz' H rho p hext
  have h72 := Workspace.Statements.S07.SPGT.thm_7_2 G hG a b (R 0) (R 1) (R 2) hprism
  have hbip :=
    Thm101ThetaBipartite G hG a b R K hprism hK h72 _ Theta x y Q phi hTheta
      z z' hz hz' f f₁ fn u u' w w' hf hfK hfNonmajor
      hu hu' huu' hf₁u hf₁u' hw hw' hww' hfnw hfnw' hother hzinc hz'inc
      _ H rho p hext hplen
  have hRtwo : ∀ i : Fin 3, 2 ≤ (R i).length := by
    intro i
    have hpath : IsPathFrom G (R i) (a i) (b i) := by
      fin_cases i
      · exact hprism.2.2.2.1
      · exact hprism.2.2.2.2.1
      · exact hprism.2.2.2.2.2.1
    have hpos : 0 < (R i).length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos hpath.1
    by_contra hlt
    have hone : (R i).length = 1 := by omega
    obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hone
    have haeq : c = a i := by simpa [hc] using hpath.2.1
    have hbeq : c = b i := by simpa [hc] using hpath.2.2
    exact hprism.2.2.1 i i (haeq.symm.trans hbeq)
  have hnondeg :=
    Thm101ThetaNondegenerate R hRtwo _ _ Theta x y Q
      ⟨hxy, htracks, hlengths, hdisjoint, hinteriors, hcover, hedges⟩
      hTheta.2.1 z z' hz hz' H rho p hext hbranch.1
  refine ⟨_, H, K ∪ {x : V | x ∈ f}, rfl, ?_, ?_⟩
  · exact ⟨⟨hbranch.2, hbip⟩, ⟨psi⟩⟩
  · rcases hnondeg with hnondeg | hlens
    · exact Or.inl hnondeg
    · by_cases hdeg : DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H
      · exact Or.inr ⟨hdeg, hlens⟩
      · exact Or.inl hdeg

end Workspace.ProofLemmas
