import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.Thm86ClaimTwo

/-!
# The exceptional end sets in 8.6, claim (1)

This file packages the two finite choices made in the first claim of the proof of 8.6.  The
chosen edge is a strip not contained in `X`, if one exists.  At either end of that edge, the
saturation hypothesis leaves at most one exceptional incident strip.  Removing that one
`N_{uv}` from `N_u` gives the paper's union of `m - 1` good sets.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.NoMajorVerticesSetChoice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}

/-- Choose an edge whose strip is not contained in `X`, if such an edge exists. -/
theorem exists_selected_edge (hJ : IsKConnected J 3) (X : Set V) :
    ∃ b₁ b₂ : U, J.Adj b₁ b₂ ∧
      (S b₁ b₂ ⊆ X → stripSystemVertices J S ⊆ X) := by
  classical
  have hcard : 3 < Fintype.card U := hJ.1
  obtain ⟨u⟩ : Nonempty U := Fintype.card_pos_iff.mp (by omega : 0 < Fintype.card U)
  obtain ⟨v, huv⟩ :=
    Workspace.ProofLemmas.SubdivisionCounting.exists_adj_of_three_connected J hJ u
  by_cases hbad : ∃ a b : U, J.Adj a b ∧ ¬ S a b ⊆ X
  · obtain ⟨a, b, hab, hnsub⟩ := hbad
    exact ⟨a, b, hab, fun hsub => (hnsub hsub).elim⟩
  · refine ⟨u, v, huv, fun _ x hx => ?_⟩
    rw [Workspace.ProofLemmas.StripSystemBasics.mem_stripSystemVertices_iff] at hx
    obtain ⟨a, b, hab, hxS⟩ := hx
    by_contra hxX
    exact (not_exists.mp (not_exists.mp hbad a) b) ⟨hab, fun h => hxX (h hxS)⟩

/-- At a fixed vertex `u`, remove the unique bad `N_{ue}` if it exists.  What remains is
contained in the saturating set.  If no incident `N_{uw}` is bad, the prescribed fallback
neighbour is removed. -/
theorem exists_exceptional_end
    (hSN : IsJStripSystem G J S N) (X : Set V)
    (hsat : SaturatesStripSystem J S N X) {u fallback : U}
    (huf : J.Adj u fallback) :
    ∃ e : U, J.Adj u e ∧
      N u \ stripSystemNuv S N u e ⊆ X ∧
      ((∀ w : U, J.Adj u w → stripSystemNuv S N u w ⊆ X) → e = fallback) := by
  classical
  by_cases hbad : ∃ e : U, J.Adj u e ∧ ¬ stripSystemNuv S N u e ⊆ X
  · obtain ⟨e, hue, heBad⟩ := hbad
    refine ⟨e, hue, ?_, fun hall => (heBad (hall e hue)).elim⟩
    rintro z ⟨hzN, hzNot⟩
    obtain ⟨w, huw, hzNuw⟩ :=
      Workspace.ProofLemmas.StripSystemBasics.mem_Nuv_of_mem_N hSN hzN
    have hwe : w ≠ e := by
      intro h
      exact hzNot (h ▸ hzNuw)
    by_contra hzX
    have hwBad : ¬ stripSystemNuv S N u w ⊆ X := fun hsub => hzX (hsub hzNuw)
    exact hwe (hsat u ⟨huw, hwBad⟩ ⟨hue, heBad⟩)
  · refine ⟨fallback, huf, ?_, fun _ => rfl⟩
    rintro z ⟨hzN, -⟩
    obtain ⟨w, huw, hzNuw⟩ :=
      Workspace.ProofLemmas.StripSystemBasics.mem_Nuv_of_mem_N hSN hzN
    by_contra hzX
    exact (not_exists.mp hbad w) ⟨huw, fun h => hzX (h hzNuw)⟩

/-- The retained end set is nonempty because a 3-connected vertex has another incident edge. -/
theorem end_set_nonempty
    (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    {u e : U} (hue : J.Adj u e) :
    (N u \ stripSystemNuv S N u e).Nonempty := by
  have hdeg : 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  obtain ⟨w, huw, hwe⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet u) (by omega) e
  obtain ⟨z, hz⟩ := Workspace.ProofLemmas.StripSystemBasics.Nuv_nonempty hSN huw
  refine ⟨z, hz.1, ?_⟩
  intro hze
  exact hwe (Workspace.ProofLemmas.StripSystemBasics.Nuv_eq_of_mem hSN huw hue hz hze)

/-- Deleting the two ends of an edge from a 3-connected graph leaves an edge. -/
theorem exists_edge_avoiding_edge
    (hJ : IsKConnected J 3) {b₁ b₂ : U} (hb₁b₂ : J.Adj b₁ b₂) :
    ∃ c d : U, J.Adj c d ∧ c ≠ b₁ ∧ c ≠ b₂ ∧ d ≠ b₁ ∧ d ≠ b₂ := by
  have hcard2 : ({b₁, b₂} : Set U).ncard ≤ 2 := by
    have h := Set.ncard_insert_le b₁ ({b₂} : Set U)
    rw [Set.ncard_singleton] at h
    omega
  have hconn := hJ.2 ({b₁, b₂} : Set U) (by omega)
  have hcompl : 1 < (({b₁, b₂} : Set U)ᶜ).ncard := by
    have hsum := Set.ncard_add_ncard_compl ({b₁, b₂} : Set U)
    rw [Nat.card_eq_fintype_card] at hsum
    have hcard : 3 < Fintype.card U := hJ.1
    omega
  obtain ⟨a, ha⟩ : (({b₁, b₂} : Set U)ᶜ).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]
    omega
  obtain ⟨b, hb, hba⟩ := Set.exists_ne_of_one_lt_ncard hcompl a
  have hne : (⟨a, ha⟩ : ↑(({b₁, b₂} : Set U)ᶜ)) ≠ ⟨b, hb⟩ := fun h =>
    hba (congrArg (fun z : ↑(({b₁, b₂} : Set U)ᶜ) => (z : U)) h).symm
  obtain ⟨z, haz⟩ := Workspace.ProofLemmas.SubdivisionCounting.exists_adj_of_reachable
    (hconn.preconnected ⟨a, ha⟩ ⟨b, hb⟩) hne
  refine ⟨a, (z : U), haz, ?_, ?_, ?_, ?_⟩
  · intro h
    exact ha (by simp [h])
  · intro h
    exact ha (by simp [h])
  · intro h
    exact z.2 (by simp [h])
  · intro h
    exact z.2 (by simp [h])

end Workspace.ProofLemmas.NoMajorVerticesSetChoice
