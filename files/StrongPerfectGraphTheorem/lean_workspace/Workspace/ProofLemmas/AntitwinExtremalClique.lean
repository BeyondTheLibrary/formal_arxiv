import Workspace.Types.Core
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.ColorableSplitJoin
import Workspace.ProofLemmas.IsoTransport

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- A critical-imperfect antitwin pair has a nonempty clique on its `v`-side
that is maximal against vertices on either antitwin side. -/
theorem AntitwinExtremalClique
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (hKnonperfect : ¬ SPGT.IsPerfect K)
    (hKproper : ∀ X : Set W, X ≠ Set.univ → SPGT.IsPerfect (K.induce X))
    (u v : W) (huv : u ≠ v)
    (hanti : ∀ z : W, z ≠ u → z ≠ v →
      Xor' (K.Adj z u) (K.Adj z v)) :
    ∃ D : Set W,
      D ⊆ {z : W | z ≠ u ∧ z ≠ v ∧ K.Adj z v} ∧
      D.Nonempty ∧
      K.IsClique D ∧
      ∀ z : W,
        z ∈ (({x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x u} ∪
          {x : W | x ≠ u ∧ x ≠ v ∧ K.Adj x v}) \ D) →
        ∃ d ∈ D, ¬ K.Adj z d := by
  classical
  let ω := K.cliqueNum
  have hnotcolor : ¬ K.Colorable ω := by
    intro hcolor
    apply hKnonperfect
    intro X
    by_cases hX : X = Set.univ
    · subst X
      have htransport : (K.induce Set.univ).Colorable ω :=
        SimpleGraph.Colorable.of_hom (SimpleGraph.induceUnivIso K).toHom hcolor
      have homega : (K.induce Set.univ).cliqueNum = ω := by
        simpa [ω] using
          Workspace.ProofLemmas.IsoTransport.cliqueNum_iso
            (SimpleGraph.induceUnivIso K)
      have hIcolor : (K.induce Set.univ).Colorable
          (K.induce Set.univ).cliqueNum := by
        simpa only [homega] using htransport
      exact le_antisymm hIcolor.chromaticNumber_le
        SimpleGraph.cliqueNum_le_chromaticNumber
    · exact CliqueNumOfInducedSet.chromaticNumber_eq_cliqueNum_of_isPerfect
        (K.induce X) (hKproper X hX)
  have hωpos : 0 < ω := by
    have hclique : K.IsClique (↑({u} : Finset W) : Set W) := by simp
    have hle := hclique.card_le_cliqueNum
    simpa [ω] using hle
  have hωtwo : 2 ≤ ω := by
    by_contra h
    have hωone : ω = 1 := by omega
    apply hnotcolor
    refine ⟨SimpleGraph.Coloring.mk (fun _ => (⟨0, hωpos⟩ : Fin ω)) ?_⟩
    intro a b hab
    exfalso
    have hclique : K.IsClique (↑({a, b} : Finset W) : Set W) := by
      rw [Finset.coe_insert, Finset.coe_singleton, SimpleGraph.isClique_pair]
      intro _
      exact hab
    have hle := hclique.card_le_cliqueNum
    have habne : a ≠ b := K.ne_of_adj hab
    rw [Finset.card_pair habne] at hle
    have : 2 ≤ ω := by simpa [ω] using hle
    omega
  let Xv : Set W := {x | x ≠ v}
  have hXvproper : Xv ≠ Set.univ := by
    intro h
    have : v ∈ Xv := h.symm ▸ Set.mem_univ v
    exact this rfl
  have hXvperfect : SPGT.IsPerfect (K.induce Xv) := hKproper Xv hXvproper
  have hinduce_le : ∀ X : Set W, (K.induce X).cliqueNum ≤ ω := by
    intro X
    obtain ⟨Q, hQX, hQclique, hQcard⟩ :=
      CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K X
    rw [← hQcard]
    simpa [ω] using hQclique.card_le_cliqueNum
  have hXvomega : (K.induce Xv).cliqueNum ≤ ω := by
    exact hinduce_le Xv
  obtain ⟨c⟩ :=
    (CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect
      (K.induce Xv) hXvperfect).mono hXvomega
  have huXv : u ∈ Xv := by simpa [Xv] using huv
  let i₀ : Fin ω := c ⟨u, huXv⟩
  let T : Set W := {x | ∃ hx : x ∈ Xv, c ⟨x, hx⟩ = i₀}
  have huT : u ∈ T := ⟨huXv, rfl⟩
  have hvnotT : v ∉ T := by
    rintro ⟨hvXv, -⟩
    exact hvXv rfl
  have hTstable : ∀ a ∈ T, ∀ b ∈ T, a ≠ b → ¬ K.Adj a b := by
    rintro a ⟨haXv, ha⟩ b ⟨hbXv, hb⟩ habne hab
    exact c.valid ((SimpleGraph.induce_adj).mpr hab) (ha.trans hb.symm)
  have hTcolor : (K.induce T).Colorable 1 := by
    refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) ?_⟩
    intro a b hab
    exact (hTstable a a.2 b b.2 (K.ne_of_adj hab) hab).elim
  let XT : Set W := Tᶜ
  have hXTproper : XT ≠ Set.univ := by
    intro h
    have : u ∈ XT := h.symm ▸ Set.mem_univ u
    exact this huT
  have hXTperfect : SPGT.IsPerfect (K.induce XT) := hKproper XT hXTproper
  have hXTomega_le : (K.induce XT).cliqueNum ≤ ω := by
    exact hinduce_le XT
  have hXTnotlow : ¬ (K.induce XT).Colorable (ω - 1) := by
    intro hlow
    have hcov : T ∪ XT = Set.univ := by simp [XT]
    have hdisj : Disjoint T XT := by
      rw [Set.disjoint_left]
      intro x hxT hxXT
      exact hxXT hxT
    have hjoined := ColorableSplitJoin.colorable_add_of_partition K hcov hdisj
      hTcolor hlow
    have hsum : 1 + (ω - 1) = ω := by omega
    apply hnotcolor
    simpa [hsum] using hjoined
  have hXTomega_ge : ω ≤ (K.induce XT).cliqueNum := by
    by_contra h
    have hsmall : (K.induce XT).cliqueNum ≤ ω - 1 := by omega
    exact hXTnotlow
      ((CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect
        (K.induce XT) hXTperfect).mono hsmall)
  have hXTomega : (K.induce XT).cliqueNum = ω :=
    le_antisymm hXTomega_le hXTomega_ge
  obtain ⟨Dplus, hDplusXT, hDplusClique, hDplusCard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K XT
  rw [hXTomega] at hDplusCard
  let Y : Set W := (T ∪ {v})ᶜ
  let C₀ := {i : Fin ω // i ≠ i₀}
  have hYcolor : (K.induce Y).Colorable (ω - 1) := by
    have hYXv : Y ⊆ Xv := by
      intro z hz
      have hzv : z ≠ v := by
        intro hzv
        apply hz
        exact Or.inr (by simpa [hzv])
      simpa [Xv] using hzv
    let liftY : Y → Xv := fun z => ⟨z.1, hYXv z.2⟩
    let cy : (K.induce Y).Coloring C₀ := SimpleGraph.Coloring.mk
      (fun z => ⟨c (liftY z), by
        intro heq
        apply z.2
        apply Or.inl
        exact ⟨hYXv z.2, heq⟩⟩)
      (by
        intro a b hab
        intro heq
        apply c.valid (show (K.induce Xv).Adj (liftY a) (liftY b) from hab)
        exact congrArg Subtype.val heq)
    have hcard : Fintype.card C₀ = ω - 1 := by
      simpa [C₀] using (Set.card_ne_eq i₀)
    simpa [C₀, hcard] using cy.colorable
  have hYomega_le : (K.induce Y).cliqueNum ≤ ω - 1 := by
    obtain ⟨Q, hQ⟩ := (K.induce Y).exists_isNClique_cliqueNum
    rw [← hQ.card_eq]
    exact hQ.isClique.card_le_of_colorable hYcolor
  have hvDplus : v ∈ Dplus := by
    by_contra hv
    have hDplusY : (↑Dplus : Set W) ⊆ Y := by
      intro d hd
      have hdXT := hDplusXT hd
      have hdnotT : d ∉ T := hdXT
      have hdv : d ≠ v := by
        intro hdv
        subst d
        exact hv hd
      simpa [Y, hdnotT, hdv]
    have hcardle := CliqueNumOfInducedSet.card_le_cliqueNum_induce
      K hDplusY hDplusClique
    omega
  let Dfin := Dplus.erase v
  let D : Set W := ↑Dfin
  have hDcard : Dfin.card = ω - 1 := by
    dsimp [Dfin]
    rw [Finset.card_erase_of_mem hvDplus, hDplusCard]
  have hDnonempty : D.Nonempty := by
    have hpos : 0 < Dfin.card := by omega
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hpos
    exact ⟨d, hd⟩
  have hDclique : K.IsClique D := by
    apply hDplusClique.subset
    intro d hd
    exact (Finset.mem_erase.mp hd).2
  have hDsub : D ⊆ {z : W | z ≠ u ∧ z ≠ v ∧ K.Adj z v} := by
    intro d hd
    have hdplus : d ∈ Dplus := (Finset.mem_erase.mp hd).2
    have hdnotv : d ≠ v := (Finset.mem_erase.mp hd).1
    have hdnotT : d ∉ T := hDplusXT hdplus
    have hdnotu : d ≠ u := by
      intro hdu
      subst d
      exact hdnotT huT
    exact ⟨hdnotu, hdnotv,
      hDplusClique hdplus hvDplus hdnotv⟩
  refine ⟨D, hDsub, hDnonempty, hDclique, ?_⟩
  intro z hz
  by_contra hnone
  push_neg at hnone
  rcases hz.1 with hzP | hzQ
  · have hznotD : z ∉ D := hz.2
    have hznotT : z ∉ T := by
      rintro ⟨hzXv, hzc⟩
      exact c.valid ((SimpleGraph.induce_adj).mpr hzP.2.2)
        (hzc.trans rfl.symm)
    have hzv : z ≠ v := hzP.2.1
    have hinsertY : (↑(insert z Dfin) : Set W) ⊆ Y := by
      intro x hx
      have hx' : x ∈ insert z Dfin := hx
      rw [Finset.mem_insert] at hx'
      rcases hx' with rfl | hx
      · simpa [Y, hznotT, hzv]
      · have hxplus : x ∈ Dplus := (Finset.mem_erase.mp hx).2
        have hxnotT : x ∉ T := hDplusXT hxplus
        have hxv : x ≠ v := (Finset.mem_erase.mp hx).1
        simpa [Y, hxnotT, hxv]
    have hinsertClique : K.IsClique (↑(insert z Dfin) : Set W) := by
      rw [Finset.coe_insert]
      exact K.isClique_insert_of_notMem hznotD |>.2 ⟨hDclique, by
        intro d hd
        exact hnone d hd⟩
    have hle := CliqueNumOfInducedSet.card_le_cliqueNum_induce
      K hinsertY hinsertClique
    have hcard : (insert z Dfin).card = ω := by
      rw [Finset.card_insert_of_notMem hznotD, hDcard]
      omega
    omega
  · have hznotD : z ∉ D := hz.2
    have hznotplus : z ∉ Dplus := by
      intro hzplus
      by_cases hzv : z = v
      · subst z
        exact hzQ.2.1 rfl
      · exact hznotD (Finset.mem_erase.mpr ⟨hzv, hzplus⟩)
    have hinsertClique : K.IsClique (↑(insert z Dplus) : Set W) := by
      rw [Finset.coe_insert]
      refine K.isClique_insert_of_notMem hznotplus |>.2 ⟨hDplusClique, ?_⟩
      intro d hd
      by_cases hdv : d = v
      · subst d
        exact hzQ.2.2
      · exact hnone d (Finset.mem_erase.mpr ⟨hdv, hd⟩)
    have hle := hinsertClique.card_le_cliqueNum
    have hcard : (insert z Dplus).card = ω + 1 := by
      rw [Finset.card_insert_of_notMem hznotplus, hDplusCard]
    simp only [hcard, ω] at hle
    omega

end Workspace.ProofLemmas
