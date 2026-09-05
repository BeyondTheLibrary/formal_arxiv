import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Overshadowed
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph
import Workspace.ProofLemmas.Thm84RungEndDictionary
import Workspace.ProofLemmas.Thm84FormsLineGraphSymmetric
import Workspace.ProofLemmas.Thm84AdjacentChoices
import Workspace.ProofLemmas.Thm84ForkCountForcesK4
import Workspace.ProofLemmas.Thm84K4Case

/-!
# 8.4 — assembly

The printed proof (printed pp. 40–41, `paper/proofs/8_4.md`) runs in three movements, and this
file is the top-level assembly of exactly those three:

1. *"If every choice of rungs is saturated, then `X` saturates the strip system as required, so we
   may therefore assume that there is some choice of rungs that is not saturated."*  Contrapositive
   form, proved here as `unsaturatedChoice`: if `X` does **not** saturate the strip system then
   some choice of rungs is not saturated.  Two `J`-neighbours `v ≠ w` of a common `u` have
   `N_{uv} ⊄ X` and `N_{uw} ⊄ X`; the witnesses lie in `N_u`, hence are the `u`-ends of rungs
   `P` of `S_uv` and `Q` of `S_uw`; `TwoPrescribedSymmetricRungFamily` extends `P, Q` to a whole
   choice of rungs, `Thm84EveryChoiceFormsLineGraph` makes it form `L(H₁)`, and the rung-end
   dictionary identifies the two `X`-missing edges of `δ_{H₁}(ι u)`, so `X` does not saturate
   `L(H₁)`.
2. *"Hence there are two choices of rungs … so that the first is saturated and the second is not,
   differing only on one edge of `J`."* — `Thm84AdjacentChoices.adjacentChoices`, fed the saturated
   choice from the hypothesis `hsat` and the unsaturated choice from step 1.  The hypothesis
   `hsat` supplies only `FormsLineGraph` for its choice of rungs, so the edge-indexing clause
   (`R v u = (R u v).reverse`, the repaired reading of *"for each **edge** `uv` of `J`, choose a
   `uv`-rung"*) is recovered by `Thm84FormsLineGraphSymmetric.formsLineGraph_symm`.
3. *"Let us apply 5.7 to `H'` … and so `|V(J)| = 4`, and `J = K₄`."* —
   `Thm84ForkCountForcesK4.forkCountForcesK4`; and then the `J = K₄` endgame of printed pp. 41–42,
   *"Let `V(J) = {1,2,3,4}` … This proves 8.4."* — `Thm84K4Case.k4Case`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S08

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **"If every choice of rungs is saturated, then `X` saturates the strip system as required, so
we may therefore assume that there is some choice of rungs that is not saturated."**

The contrapositive, which is the form the proof of 8.4 uses. -/
private theorem unsaturatedChoice {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (X : Set V) (hSS : ¬ SaturatesStripSystem J S N X) :
    ∃ (n₁ : ℕ) (H₁ : SimpleGraph (Fin n₁)) (R₁ : U → U → List V)
      (φ₁ : H₁.lineGraph ≃g
        G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₁ u v})),
      FormsLineGraph G J S N R₁ H₁ ∧
      (∀ u v : U, J.Adj u v → R₁ v u = (R₁ u v).reverse) ∧
      ¬ SaturatesLineGraph H₁
        {e : Sym2 (Fin n₁) | ∃ he : e ∈ H₁.edgeSet, (↑(φ₁ ⟨e, he⟩) : V) ∈ X} := by
  classical
  -- Some `u ∈ V(J)` has two `J`-neighbours `v ≠ w` with `N_{uv} ⊄ X` and `N_{uw} ⊄ X`.
  have hex : ∃ u : U,
      ¬ {v : U | J.Adj u v ∧ ¬ (stripSystemNuv S N u v ⊆ X)}.Subsingleton := by
    by_contra h
    push_neg at h
    exact hSS h
  obtain ⟨u, hu⟩ := hex
  rw [Set.not_subsingleton_iff] at hu
  obtain ⟨v, hv, w, hw, hvw⟩ := hu
  obtain ⟨huv, hvX⟩ := hv
  obtain ⟨huw, hwX⟩ := hw
  obtain ⟨x, hxNuv, hx⟩ := Set.not_subset.mp hvX
  obtain ⟨x', hx'Nuw, hx'⟩ := Set.not_subset.mp hwX
  -- Each witness lies on a rung of its strip, and being in `N_u` it is that rung's `u`-end.
  obtain ⟨P, hP, hxP⟩ := hSN.2.2.2.1 u v huv x hxNuv.2
  obtain ⟨Q, hQ, hx'Q⟩ := hSN.2.2.2.1 u w huw x' hx'Nuw.2
  rcases hP with ⟨-, s, t, hPathP, hPStrip, hPNu, hPNv⟩
  rcases hQ with ⟨-, s', t', hPathQ, hQStrip, hQNu, hQNv⟩
  have hxs : x = s := (hPNu x hxP).1 hxNuv.1
  have hx's' : x' = s' := (hQNu x' hx'Q).1 hx'Nuw.1
  subst s
  subst s'
  -- Extend `P` and `Q` to a full (edge-indexed) choice of rungs, and form its line graph.
  obtain ⟨R, hR, hRsymm, hRuv, hRuw⟩ :=
    Workspace.ProofLemmas.TwoPrescribedSymmetricRungFamily
      G J S N hSN u v w huv huw hvw P Q
      ⟨huv, x, t, hPathP, hPStrip, hPNu, hPNv⟩
      ⟨huw, x', t', hPathQ, hQStrip, hQNu, hQNv⟩
  obtain ⟨n, H, hForms⟩ :=
    Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph
      G hG J hJ S N hSN R hR hRsymm
  obtain ⟨φ, ι, E, hιInj, hRange, hEdges, hIncident, hEInj, hEnd⟩ :=
    Workspace.ProofLemmas.Thm84RungEndDictionary.rungEndDictionary
      G J hJ S N hSN H R hForms
  refine ⟨n, H, R, φ, hForms, hRsymm, ?_⟩
  intro hSatLG
  -- `δ_H(ι u)` contains the two distinct edges indexed by `v` and by `w`, and `φ` carries them to
  -- the `u`-ends `x, x'`, neither of which is in `X`.
  have hPathRuv : IsPathFrom G (R u v) x t := by rw [hRuv]; exact hPathP
  have hPathRuw : IsPathFrom G (R u w) x' t' := by rw [hRuw]; exact hPathQ
  have hBranch : ι u ∈ branchVertices H := by rw [← hRange]; exact ⟨u, rfl⟩
  have heMissing : E u v ∈ incidentEdges H (ι u) \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
    refine ⟨?_, ?_⟩
    · rw [hIncident u]
      exact ⟨v, huv, rfl⟩
    · rintro ⟨he, heX⟩
      rw [hEnd u v huv he x t hPathRuv] at heX
      exact hx heX
  have hfMissing : E u w ∈ incidentEdges H (ι u) \
      {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
    refine ⟨?_, ?_⟩
    · rw [hIncident u]
      exact ⟨w, huw, rfl⟩
    · rintro ⟨he, heX⟩
      rw [hEnd u w huw he x' t' hPathRuw] at heX
      exact hx' heX
  exact hvw (hEInj u v w huv huw (hSatLG (ι u) hBranch heMissing hfMissing))


theorem thm_8_4 {U : Type*} [Fintype U] (G : SimpleGraph V) (hG : Berge G)
    (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (hnd : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) → NondegenerateStripSystem G J S N)
    (y : V) (hy : y ∉ stripSystemVertices J S)
    (X : Set V) (hX : X = G.neighborSet y)
    (hsat : ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V) (K : Set V)
        (φ : H.lineGraph ≃g G.induce K),
        K = (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}) ∧
        FormsLineGraph G J S N R H ∧
        SaturatesLineGraph H
          {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}) :
    SaturatesStripSystem J S N X ∨
    (∃ (m : ℕ) (J' : SimpleGraph (Fin m)), IsJEnlargement J J' ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H') ∨
    (Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))) ∧
      ∃ (n : ℕ) (H' : SimpleGraph (Fin n)) (K' : Set V) (φ' : H'.lineGraph ≃g G.induce K'),
        IsAppearance G J H' K' ∧ IsOvershadowedAppearance G H' K' φ') := by
  classical
  -- "If every choice of rungs is saturated, then `X` saturates the strip system as required."
  by_cases hSS : SaturatesStripSystem J S N X
  · exact Or.inl hSS
  -- "So we may therefore assume that there is some choice of rungs that is not saturated."
  obtain ⟨n₁, H₁, R₁, φ₁, hForms₁, hsym₁, hUnsat₁⟩ :=
    unsaturatedChoice G hG J hJ S N hSN X hSS
  -- The hypothesis supplies the saturated choice of rungs.
  obtain ⟨n₀, H₀, R₀, K₀, φ₀, hK₀, hForms₀, hSat₀⟩ := hsat
  subst hK₀
  have hsym₀ : ∀ u v : U, J.Adj u v → R₀ v u = (R₀ u v).reverse :=
    Workspace.ProofLemmas.Thm84FormsLineGraphSymmetric.formsLineGraph_symm
      G J hJ S N hSN H₀ R₀ hForms₀
  -- "Hence there are two choices of rungs … the first saturated and the second not, differing
  -- only on one edge of `J`."
  obtain ⟨a, b, n, H, R, φ, n', H', R', φ', hab, hForms, hsym, hForms', hsym',
      hSat, hUnsat, hdiff⟩ :=
    Workspace.ProofLemmas.Thm84AdjacentChoices.adjacentChoices
      G hG J hJ S N hSN X n₀ H₀ R₀ hForms₀ hsym₀ φ₀ hSat₀
      n₁ H₁ R₁ hForms₁ hsym₁ φ₁ hUnsat₁
  -- "Let us apply 5.7 to `H'` and `X ∩ E(H')` … and so `|V(J)| = 4`, and `J = K₄`."
  rcases Workspace.ProofLemmas.Thm84ForkCountForcesK4.forkCountForcesK4
      G hG J hJ S N hSN hnd y hy X hX a b hab n H R φ n' H' R' φ'
      hForms hsym hForms' hsym' hSat hUnsat hdiff with
    henl | hover | hK4
  · exact Or.inr (Or.inl henl)
  · exact Or.inr (Or.inr hover)
  -- "Let `V(J) = {1,2,3,4}` … This proves 8.4."
  · rcases Workspace.ProofLemmas.Thm84K4Case.k4Case
        G hG J hJ S N hSN hnd y hy X hX hK4 a b hab n H R φ n' H' R' φ'
        hForms hsym hForms' hsym' hSat hUnsat hdiff with
      henl | hover
    · exact Or.inr (Or.inl henl)
    · exact Or.inr (Or.inr hover)


end SPGT

end Workspace.Statements.S08
