import Workspace.Types.Core
import Workspace.ProofLemmas.CriticalImperfectComplement

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

universe u v

private theorem cliqueNum_le_of_embedding_attempt_4
    {U : Type u} {V : Type v} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {G : SimpleGraph U} {H : SimpleGraph V} (f : G ↪g H) :
    G.cliqueNum ≤ H.cliqueNum := by
  obtain ⟨s, hs⟩ := G.exists_isNClique_cliqueNum
  rw [← hs.card_eq]
  have hclique : H.IsClique (s.map f.toEmbedding) := by
    intro x hx y hy hxy
    rcases Finset.mem_map.1 hx with ⟨x', hx', rfl⟩
    rcases Finset.mem_map.1 hy with ⟨y', hy', rfl⟩
    exact f.map_adj_iff.mpr
      (hs.isClique hx' hy' (fun h => hxy (congrArg f h)))
  simpa using hclique.card_le_cliqueNum

private theorem cliqueNum_eq_of_iso_attempt_4
    {U : Type u} {V : Type v} [Fintype U] [DecidableEq U] [Fintype V] [DecidableEq V]
    {G : SimpleGraph U} {H : SimpleGraph V} (e : G ≃g H) :
    G.cliqueNum = H.cliqueNum := by
  exact le_antisymm
    (cliqueNum_le_of_embedding_attempt_4 e.toEmbedding)
    (cliqueNum_le_of_embedding_attempt_4 e.symm.toEmbedding)

private theorem perfect_colorable_cliqueNum_attempt_4
    {U : Type u} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) (hGperfect : SPGT.IsPerfect G) :
    G.Colorable G.cliqueNum := by
  have hIcolor : (G.induce Set.univ).Colorable (G.induce Set.univ).cliqueNum := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
    exact le_of_eq (hGperfect Set.univ)
  have htransport : G.Colorable (G.induce Set.univ).cliqueNum :=
    SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso G).symm.toHom hIcolor
  have homega : (G.induce Set.univ).cliqueNum = G.cliqueNum :=
    cliqueNum_eq_of_iso_attempt_4 (SimpleGraph.induceUnivIso G)
  simpa only [homega] using htransport

private theorem perfect_chromaticNumber_eq_cliqueNum_attempt_4
    {U : Type u} [Fintype U] [DecidableEq U]
    (G : SimpleGraph U) (hGperfect : SPGT.IsPerfect G) :
    G.chromaticNumber = (G.cliqueNum : ℕ∞) := by
  exact le_antisymm
    (perfect_colorable_cliqueNum_attempt_4 G hGperfect).chromaticNumber_le
    SimpleGraph.cliqueNum_le_chromaticNumber

/-- In a finite graph that is nonperfect while every proper induced subgraph is
perfect, no distinct vertex pair has the second open neighborhood (with the
first vertex removed) contained in the first open neighborhood (with the
second vertex removed). -/
theorem NoDominatedPairInCriticalImperfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hKnonperfect : ¬ SPGT.IsPerfect K)
    (hKproper : ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (K.induce X))
    (p q : W) (hpq : p ≠ q) :
    ¬ ((K.neighborSet q \ ({p} : Set W)) ⊆
      (K.neighborSet p \ ({q} : Set W))) := by
  classical
  have no_dominated_nonadjacent :
      ∀ (G : SimpleGraph W),
        ¬ SPGT.IsPerfect G →
        (∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (G.induce X)) →
        ∀ (a b : W), a ≠ b → ¬ G.Adj a b →
          ((G.neighborSet b \ ({a} : Set W)) ⊆
            (G.neighborSet a \ ({b} : Set W))) → False := by
    intro G hGnonperfect hGproper a b hab hnonadj hdom
    let S : Set W := ({b} : Set W)ᶜ
    have hSproper : S ≠ Set.univ := by
      intro hS
      have hbS : b ∈ S := by
        rw [hS]
        exact Set.mem_univ b
      simp [S] at hbS
    have hSperfect : SPGT.IsPerfect (G.induce S) := hGproper S hSproper
    have hSclique : (G.induce S).cliqueNum ≤ G.cliqueNum :=
      cliqueNum_le_of_embedding_attempt_4 (SimpleGraph.Embedding.induce S)
    have hScolor : (G.induce S).Colorable G.cliqueNum :=
      (perfect_colorable_cliqueNum_attempt_4 (G.induce S) hSperfect).mono hSclique
    obtain ⟨C⟩ := hScolor
    let aS : S := ⟨a, by simpa [S] using hab⟩
    let color : W → Fin G.cliqueNum := fun x =>
      if hx : x = b then C aS else C ⟨x, by simpa [S] using hx⟩
    have hGcolor : G.Colorable G.cliqueNum := by
      refine ⟨SimpleGraph.Coloring.mk color ?_⟩
      intro x y hxy
      by_cases hxb : x = b
      · subst x
        by_cases hyb : y = b
        · subst y
          exact (G.irrefl hxy).elim
        · have hya : y ≠ a := by
            intro hya
            subst y
            exact hnonadj hxy.symm
          have hay : G.Adj a y := by
            exact (hdom ⟨hxy, by simpa using hya⟩).1
          have hayS : (G.induce S).Adj aS ⟨y, by simpa [S] using hyb⟩ :=
            (SimpleGraph.induce_adj).mpr hay
          simpa [color, hyb] using C.valid hayS
      · by_cases hyb : y = b
        · subst y
          have hxa : x ≠ a := by
            intro hxa
            subst x
            exact hnonadj hxy
          have hax : G.Adj a x := by
            exact (hdom ⟨hxy.symm, by simpa using hxa⟩).1
          have haxS : (G.induce S).Adj aS ⟨x, by simpa [S] using hxb⟩ :=
            (SimpleGraph.induce_adj).mpr hax
          simpa [color, hxb] using (C.valid haxS).symm
        · have hxyS : (G.induce S).Adj
              ⟨x, by simpa [S] using hxb⟩ ⟨y, by simpa [S] using hyb⟩ :=
            (SimpleGraph.induce_adj).mpr hxy
          simpa [color, hxb, hyb] using C.valid hxyS
    apply hGnonperfect
    intro X
    by_cases hX : X = Set.univ
    · subst X
      have htransport : (G.induce Set.univ).Colorable G.cliqueNum :=
        SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso G).toHom hGcolor
      have homega : (G.induce Set.univ).cliqueNum = G.cliqueNum :=
        cliqueNum_eq_of_iso_attempt_4 (SimpleGraph.induceUnivIso G)
      have hIcolor : (G.induce Set.univ).Colorable (G.induce Set.univ).cliqueNum := by
        simpa only [homega] using htransport
      exact le_antisymm hIcolor.chromaticNumber_le SimpleGraph.cliqueNum_le_chromaticNumber
    · exact perfect_chromaticNumber_eq_cliqueNum_attempt_4 (G.induce X) (hGproper X hX)
  intro hdom
  by_cases hpqadj : K.Adj p q
  · rcases CriticalImperfectComplement K hKnonperfect hKproper with ⟨hCnonperfect, hCproper⟩
    apply no_dominated_nonadjacent Kᶜ hCnonperfect hCproper q p hpq.symm
    · intro hqp
      exact hqp.2 hpqadj.symm
    · intro z hz
      rcases hz with ⟨hzp, hzq⟩
      have hcomp_pz : p ≠ z ∧ ¬ K.Adj p z := hzp
      refine ⟨?_, ?_⟩
      · change q ≠ z ∧ ¬ K.Adj q z
        constructor
        · intro hqz
          subst z
          exact hzq (by simp)
        · intro hqz
          have hznp : z ≠ p := by
            intro hzp'
            exact hcomp_pz.1 hzp'.symm
          have hdom' := hdom ⟨hqz, by simpa using hznp⟩
          exact hcomp_pz.2 hdom'.1
      · intro hzp'
        exact hcomp_pz.1 hzp'.symm
  · exact no_dominated_nonadjacent K hKnonperfect hKproper p q hpq hpqadj hdom

end Workspace.ProofLemmas
