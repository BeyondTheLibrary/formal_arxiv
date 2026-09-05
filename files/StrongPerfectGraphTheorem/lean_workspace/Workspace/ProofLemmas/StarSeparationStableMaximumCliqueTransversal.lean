import Workspace.Types.Core
import Workspace.ProofLemmas.ColorClassHitsAllMaximumCliques
import Workspace.ProofLemmas.CliqueNumOfInducedSet

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT

/-- §3 of the detailed proof, for one side of the star separation.

If `U` induces a perfect subgraph and the centre `v` lies in `U`, then the colour
class of `v` in an optimal colouring of `K|U`, pushed back down to `V` along
`Subtype.val`, is a stable subset of `U` containing `v` which meets every maximum
clique of `K` that happens to lie inside `U`.

The last clause is §5.2: a maximum clique `Q ⊆ U` of `K` witnesses
`ω(K) ≤ ω(K|U)`, while `ω(K|U) ≤ ω(K)` always holds, so `Q` is *also* a maximum
clique of `K|U` and `ColorClassHitsAllMaximumCliques` applies to it. -/
private theorem sideTransversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (U : Set V) (v : V) (hvU : v ∈ U)
    (hperf : IsPerfect (K.induce U)) :
    ∃ T : Set V, v ∈ T ∧ T ⊆ U ∧ K.IsIndepSet T ∧
      ∀ Q : Finset V, K.IsClique (↑Q : Set V) → Q.card = K.cliqueNum →
        (↑Q : Set V) ⊆ U → ∃ q : V, q ∈ Q ∧ q ∈ T := by
  classical
  -- §3.1: perfectness of `K|U` gives `χ(K|U) = ω(K|U)`.
  have hchi : (K.induce U).chromaticNumber = (((K.induce U).cliqueNum : ℕ) : ℕ∞) :=
    CliqueNumOfInducedSet.chromaticNumber_eq_cliqueNum_of_isPerfect (K.induce U) hperf
  -- §3.2: select the colour class of the centre.
  obtain ⟨T', hvT', hT'ind, hT'hit⟩ :=
    ColorClassHitsAllMaximumCliques (K.induce U) ⟨v, hvU⟩ hchi
  -- §3.3: move it back to `V`.
  refine ⟨Subtype.val '' T', ⟨⟨v, hvU⟩, hvT', rfl⟩, ?_, ?_, ?_⟩
  · rintro z ⟨w, -, rfl⟩
    exact w.2
  · rintro p ⟨p', hp', rfl⟩ q ⟨q', hq', rfl⟩ hpq
    exact hT'ind hp' hq' (fun h => hpq (congrArg Subtype.val h))
  · intro Q hQclique hQcard hQU
    -- carry `Q` up into the subtype `↥U`
    set Q' : Finset ↥U :=
      Q.attach.map ⟨fun a => ⟨a.1, hQU (by simp)⟩,
        by intro a b hab; exact Subtype.ext (by simpa using hab)⟩ with hQ'
    have hcard : Q'.card = Q.card := by
      rw [hQ', Finset.card_map, Finset.card_attach]
    have hclique : (K.induce U).IsClique (↑Q' : Set ↥U) := by
      rintro a ha b hb hab
      simp only [hQ', Finset.coe_map, Set.mem_image, Finset.mem_coe,
        Finset.mem_attach, Function.Embedding.coeFn_mk] at ha hb
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      have hxy : (x : V) ≠ (y : V) := fun h => hab (Subtype.ext h)
      exact hQclique (by simp) (by simp) hxy
    -- `ω(K|U) ≤ ω(K)` because every clique of `K|U` projects to a clique of `K`
    have hle1 : (K.induce U).cliqueNum ≤ K.cliqueNum := by
      obtain ⟨K0, hK0U, hK0clique, hK0card⟩ :=
        CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K U
      rw [← hK0card]
      exact SimpleGraph.IsClique.card_le_cliqueNum (tc := hK0clique)
    have hle2 : Q.card ≤ (K.induce U).cliqueNum :=
      CliqueNumOfInducedSet.card_le_cliqueNum_induce K hQU hQclique
    have hQ'card : Q'.card = (K.induce U).cliqueNum := by
      rw [hcard]; omega
    obtain ⟨q', hq'Q, hq'T⟩ := hT'hit Q' hclique hQ'card
    refine ⟨q'.1, ?_, ⟨q', hq'T, rfl⟩⟩
    rw [hQ'] at hq'Q
    simp only [Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      true_and] at hq'Q
    obtain ⟨x, hx⟩ := hq'Q
    have hval : (q' : V) = (x : V) := by rw [← hx]
    rw [hval]
    exact x.2

/-- Two perfect sides of a star separation yield a stable set through the
centre that meets every maximum clique. -/
theorem StarSeparationStableMaximumCliqueTransversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (K : SimpleGraph V) (X Y B : Set V) (v : V)
    (hvB : v ∈ B)
    (hcover : (X ∪ Y) ∪ B = Set.univ)
    (hXYdisj : Disjoint X Y)
    (hXYanti : Anticomplete K X Y)
    (hcenter : ∀ b ∈ B, b ≠ v → K.Adj v b)
    (hperfectX : IsPerfect (K.induce (X ∪ B)))
    (hperfectY : IsPerfect (K.induce (Y ∪ B))) :
    ∃ S : Set V, v ∈ S ∧ K.IsIndepSet S ∧
      ∀ Q : Finset V, K.IsClique (↑Q : Set V) → Q.card = K.cliqueNum →
        ∃ q : V, q ∈ Q ∧ q ∈ S := by
  classical
  -- §3: one centre colour class on each side.
  obtain ⟨TX, hvTX, hTXU, hTXind, hTXhit⟩ :=
    sideTransversal K (X ∪ B) v (Or.inr hvB) hperfectX
  obtain ⟨TY, hvTY, hTYU, hTYind, hTYhit⟩ :=
    sideTransversal K (Y ∪ B) v (Or.inr hvB) hperfectY
  -- §4.2: a centre colour class contains no other vertex of `B`.
  have hTXB : ∀ b ∈ TX, b ∈ B → b = v := by
    intro b hbT hbB
    by_contra hbv
    exact hTXind hvTX hbT (fun h => hbv h.symm) (hcenter b hbB hbv)
  have hTYB : ∀ b ∈ TY, b ∈ B → b = v := by
    intro b hbT hbB
    by_contra hbv
    exact hTYind hvTY hbT (fun h => hbv h.symm) (hcenter b hbB hbv)
  -- §4.3: cross pairs.
  have hcross : ∀ p ∈ TX, ∀ q ∈ TY, p ≠ q → ¬ K.Adj p q := by
    intro p hp q hq hpq
    by_cases hpB : p ∈ B
    · have hpv : p = v := hTXB p hp hpB
      rw [hpv]
      have hvq : v ≠ q := by rw [← hpv]; exact hpq
      exact hTYind hvTY hq hvq
    · have hpX : p ∈ X := by
        rcases (Set.mem_union p X B).mp (hTXU hp) with h | h
        · exact h
        · exact absurd h hpB
      by_cases hqB : q ∈ B
      · have hqv : q = v := hTYB q hq hqB
        rw [hqv]
        have hpv : p ≠ v := by rw [← hqv]; exact hpq
        exact hTXind hp hvTX hpv
      · have hqY : q ∈ Y := by
          rcases (Set.mem_union q Y B).mp (hTYU hq) with h | h
          · exact h
          · exact absurd h hqB
        exact hXYanti p hpX q hqY
  refine ⟨TX ∪ TY, Or.inl hvTX, ?_, ?_⟩
  · -- §4: the glued set is stable.
    intro p hp q hq hpq
    rcases (Set.mem_union p TX TY).mp hp with hp | hp <;>
      rcases (Set.mem_union q TX TY).mp hq with hq | hq
    · exact hTXind hp hq hpq
    · exact hcross p hp q hq hpq
    · exact fun hadj => hcross q hq p hp (Ne.symm hpq) hadj.symm
    · exact hTYind hp hq hpq
  · -- §5: the glued set meets every maximum clique.
    intro Q hQclique hQcard
    by_cases hQX : ∃ x, x ∈ Q ∧ x ∈ X
    · -- §5.1, first case: `Q ⊆ X ∪ B`.
      obtain ⟨x, hxQ, hxX⟩ := hQX
      have hQU : (↑Q : Set V) ⊆ X ∪ B := by
        intro z hz
        have hzc : z ∈ (X ∪ Y) ∪ B := by rw [hcover]; trivial
        rcases (Set.mem_union z (X ∪ Y) B).mp hzc with hzXY | hzB
        · rcases (Set.mem_union z X Y).mp hzXY with hzX | hzY
          · exact Or.inl hzX
          · exfalso
            have hxz : x ≠ z := by
              rintro rfl
              exact Set.disjoint_left.mp hXYdisj hxX hzY
            exact hXYanti x hxX z hzY (hQclique (by simpa using hxQ) hz hxz)
        · exact Or.inr hzB
      obtain ⟨q, hqQ, hqT⟩ := hTXhit Q hQclique hQcard hQU
      exact ⟨q, hqQ, Or.inl hqT⟩
    · -- §5.1, second case: `Q ⊆ Y ∪ B`.
      have hQU : (↑Q : Set V) ⊆ Y ∪ B := by
        intro z hz
        have hzc : z ∈ (X ∪ Y) ∪ B := by rw [hcover]; trivial
        rcases (Set.mem_union z (X ∪ Y) B).mp hzc with hzXY | hzB
        · rcases (Set.mem_union z X Y).mp hzXY with hzX | hzY
          · exact absurd ⟨z, by simpa using hz, hzX⟩ hQX
          · exact Or.inl hzY
        · exact Or.inr hzB
      obtain ⟨q, hqQ, hqT⟩ := hTYhit Q hQclique hQcard hQU
      exact ⟨q, hqQ, Or.inr hqT⟩

end Workspace.ProofLemmas
