import Workspace.Types.Core
import Workspace.ProofLemmas.IndependentSetColoringExtension

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- A finite graph is perfect if every nonempty induced subgraph admits an
independent set meeting every maximum clique. -/
theorem StableMaximumCliqueTransversalsImplyPerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (htransversal :
      ∀ (X : Set W), Nonempty X →
        ∃ S : Set X,
          (K.induce X).IsIndepSet S ∧
            ∀ Q : Finset X,
              (K.induce X).IsClique (↑Q : Set X) →
                Q.card = (K.induce X).cliqueNum →
                  ∃ q : X, q ∈ Q ∧ q ∈ S) :
    IsPerfect K := by
  classical
  intro X
  apply le_antisymm
  · rw [SimpleGraph.chromaticNumber_le_iff_colorable]
    let motive := fun n : ℕ =>
      ∀ Y : Set W, Nat.card Y = n →
        (K.induce Y).Colorable (K.induce Y).cliqueNum
    have hcolor : ∀ n : ℕ, motive n := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro Y hcard
          by_cases hY : Nonempty Y
          · obtain ⟨S, hS, hhit⟩ := htransversal Y hY
            obtain ⟨Q₀, hQ₀⟩ :=
              SimpleGraph.exists_isNClique_cliqueNum (G := K.induce Y)
            obtain ⟨s, -, hsS⟩ := hhit Q₀ hQ₀.1 hQ₀.2
            let R : Set W :=
              {w | ∃ hw : w ∈ Y, (⟨w, hw⟩ : Y) ∉ S}
            have hRY : R ⊆ Y := by
              intro w hw
              exact hw.choose
            have hRYproper : R ⊂ Y := by
              refine Set.ssubset_iff_subset_ne.mpr ⟨hRY, ?_⟩
              intro hEq
              have hsR : (s : W) ∈ R := by
                rw [hEq]
                exact s.2
              change ∃ hw : (s : W) ∈ Y, (⟨(s : W), hw⟩ : Y) ∉ S at hsR
              obtain ⟨hw, hnS⟩ := hsR
              apply hnS
              convert hsS using 1
            have hcardR : Nat.card R < n := by
              rw [← hcard]
              exact Set.Finite.card_lt_card (Set.toFinite Y) hRYproper
            have hcR : (K.induce R).Colorable (K.induce R).cliqueNum := by
              have hsmall := ih (Nat.card R) hcardR
              dsimp [motive] at hsmall
              exact hsmall R rfl
            obtain ⟨cR⟩ := hcR
            let e : (K.induce R) ↪g (K.induce Y) := K.induceHomOfLE hRY
            obtain ⟨QR, hQR⟩ :=
              SimpleGraph.exists_isNClique_cliqueNum (G := K.induce R)
            let Q : Finset Y := QR.map e.toEmbedding
            have hQcard : Q.card = (K.induce R).cliqueNum := by
              simpa [Q] using hQR.2
            have hQclique : (K.induce Y).IsClique (↑Q : Set Y) := by
              intro a ha b hb hab
              simp only [Q, Finset.mem_coe, Finset.mem_map] at ha hb
              obtain ⟨a', ha', rfl⟩ := ha
              obtain ⟨b', hb', rfl⟩ := hb
              have hab' : a' ≠ b' := fun hEq => hab (congrArg e hEq)
              exact e.map_rel_iff'.2 (hQR.1 (by simpa using ha') (by simpa using hb') hab')
            have hclique_le :
                (K.induce R).cliqueNum ≤ (K.induce Y).cliqueNum := by
              rw [← hQcard]
              exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hQclique)
            have hclique_ne :
                (K.induce R).cliqueNum ≠ (K.induce Y).cliqueNum := by
              intro heq
              obtain ⟨q, hqQ, hqS⟩ := hhit Q hQclique (hQcard.trans heq)
              simp only [Q, Finset.mem_map] at hqQ
              obtain ⟨r, -, hrq⟩ := hqQ
              have hrnot : e r ∉ S := by
                obtain ⟨hw, hnS⟩ := r.2
                intro herS
                apply hnS
                convert herS using 1
              exact hrnot (hrq ▸ hqS)
            have hclique_lt :
                (K.induce R).cliqueNum < (K.induce Y).cliqueNum :=
              lt_of_le_of_ne hclique_le hclique_ne
            let toR (y : Y) (hy : y ∉ S) : R := ⟨y.1, ⟨y.2, hy⟩⟩
            have hc : (K.induce Y).Colorable ((K.induce R).cliqueNum + 1) :=
              IndependentSetColoringExtension K Y R S hS cR toR (by
                intro a b ha hb hab
                exact hab)
            exact hc.mono (Nat.succ_le_iff.mpr hclique_lt)
          · haveI : IsEmpty Y := not_nonempty_iff.mp hY
            exact SimpleGraph.Colorable.of_isEmpty _
    exact hcolor (Nat.card X) X rfl
  · exact SimpleGraph.cliqueNum_le_chromaticNumber

end Workspace.ProofLemmas
