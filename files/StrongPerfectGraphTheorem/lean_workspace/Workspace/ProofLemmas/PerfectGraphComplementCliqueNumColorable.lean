import Workspace.ProofLemmas.PerfectInducedSubgraph
import Workspace.ProofLemmas.PerfectGraphMaximumStableSetHittingClique

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

universe u

private theorem complementCliqueNumColorable_aux :
    ∀ n : ℕ, ∀ {W : Type u} [Fintype W] [DecidableEq W],
      Fintype.card W = n →
        ∀ (H : SimpleGraph W), IsPerfect H → Hᶜ.Colorable Hᶜ.cliqueNum := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro W _ _ hcard H hH
      cases isEmpty_or_nonempty W with
      | inl hEmpty =>
          letI : IsEmpty W := hEmpty
          exact ⟨SimpleGraph.Coloring.ofIsEmpty⟩
      | inr hNonempty =>
          letI : Nonempty W := hNonempty
          obtain ⟨C, hCclique, hChit⟩ :=
            PerfectGraphMaximumStableSetHittingClique H hH
          obtain ⟨Amax, hAmax⟩ :=
            SimpleGraph.exists_isNClique_cliqueNum (G := Hᶜ)
          have hAmaxInd : H.IsIndepSet (↑Amax : Set W) :=
            (SimpleGraph.isClique_compl (G := H)).mp hAmax.1
          obtain ⟨x, hxC, _⟩ := hChit Amax hAmaxInd hAmax.2
          let R : Set W := (↑C : Set W)ᶜ
          let J : SimpleGraph R := H.induce R
          have hxR : x ∉ R := by
            simp only [R, Set.mem_compl_iff, Finset.mem_coe]
            exact not_not_intro hxC
          have hRcard : Fintype.card R < n := by
            rw [← hcard]
            exact Fintype.card_subtype_lt hxR
          have hJperfect : IsPerfect J := PerfectInducedSubgraph H R hH
          have hJcolor : Jᶜ.Colorable Jᶜ.cliqueNum :=
            ih (Fintype.card R) hRcard (W := R) rfl J hJperfect
          let q : ℕ := Jᶜ.cliqueNum
          obtain ⟨S, hS⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := Jᶜ)
          let A : Finset W := S.map ⟨Subtype.val, Subtype.val_injective⟩
          have hAcard : A.card = q := by
            simp only [A, Finset.card_map, q]
            exact hS.2
          have hAclique : Hᶜ.IsClique (↑A : Set W) := by
            intro a ha b hb hab
            simp only [A, Finset.coe_map, Function.Embedding.coeFn_mk,
              Set.mem_image, Finset.mem_coe] at ha hb
            obtain ⟨a', ha', rfl⟩ := ha
            obtain ⟨b', hb', rfl⟩ := hb
            have hab' : a' ≠ b' := fun e => hab (congrArg Subtype.val e)
            have hadj := hS.1 (by simpa using ha') (by simpa using hb') hab'
            simpa [J, SimpleGraph.compl_adj, Subtype.ext_iff] using hadj
          have hAind : H.IsIndepSet (↑A : Set W) :=
            (SimpleGraph.isClique_compl (G := H)).mp hAclique
          have hq_lt : q < Hᶜ.cliqueNum := by
            have hq_le : q ≤ Hᶜ.cliqueNum := by
              rw [← hAcard]
              exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hAclique)
            refine lt_of_le_of_ne hq_le ?_
            intro heq
            have hAmaxcard : A.card = Hᶜ.cliqueNum := hAcard.trans heq
            obtain ⟨y, hyC, hyA⟩ := hChit A hAind hAmaxcard
            have hyR : y ∈ R := by
              simp only [A, Finset.mem_map] at hyA
              obtain ⟨z, hzS, rfl⟩ := hyA
              exact z.property
            exact (hyR hyC)
          obtain ⟨cJ⟩ := hJcolor
          refine ⟨SimpleGraph.Coloring.mk (fun v : W =>
            if hv : v ∈ R then
              ⟨(cJ ⟨v, hv⟩).val,
                lt_of_lt_of_le (cJ ⟨v, hv⟩).isLt
                  (by simpa [q] using Nat.le_of_lt hq_lt)⟩
            else ⟨q, hq_lt⟩) ?_⟩
          intro a b hab
          by_cases haR : a ∈ R
          · by_cases hbR : b ∈ R
            · intro hcol
              have hadjJ : Jᶜ.Adj ⟨a, haR⟩ ⟨b, hbR⟩ := by
                dsimp only [J]
                rw [SimpleGraph.compl_adj] at hab ⊢
                exact ⟨fun e => hab.1 (congrArg Subtype.val e), hab.2⟩
              apply cJ.valid hadjJ
              apply Fin.ext
              have hval := congrArg Fin.val hcol
              simpa [haR, hbR] using hval
            · intro hcol
              have hval := congrArg Fin.val hcol
              have heq : (cJ ⟨a, haR⟩).val = q := by simpa [haR, hbR] using hval
              have hne : (cJ ⟨a, haR⟩).val ≠ q := by
                simpa [q] using (cJ ⟨a, haR⟩).isLt.ne
              exact hne heq
          · by_cases hbR : b ∈ R
            · intro hcol
              have hval := congrArg Fin.val hcol
              have heq : q = (cJ ⟨b, hbR⟩).val := by simpa [haR, hbR] using hval
              have hne : q ≠ (cJ ⟨b, hbR⟩).val := by
                simpa [q] using (cJ ⟨b, hbR⟩).isLt.ne'
              exact hne heq
            · intro _
              have haC : a ∈ C := by simpa [R] using haR
              have hbC : b ∈ C := by simpa [R] using hbR
              rw [SimpleGraph.compl_adj] at hab
              exact hab.2
                (hCclique (by simpa using haC) (by simpa using hbC) hab.1)

/-- The complement of a finite perfect graph is colorable with its clique
number of colors. -/
theorem PerfectGraphComplementCliqueNumColorable
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hH : IsPerfect H) :
    Hᶜ.Colorable Hᶜ.cliqueNum := by
  exact complementCliqueNumColorable_aux (Fintype.card W) rfl H hH

end Workspace.ProofLemmas
