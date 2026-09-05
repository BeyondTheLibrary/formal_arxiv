import Workspace.ProofLemmas.Thm61OddAddBranch
import Workspace.ProofLemmas.Thm61EvenEndgameHelpers

/-! Subdivision and parity of the branch added in 6.1(7). -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Workspace.ProofLemmas.Thm61OddBranchSubdivision
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData Workspace.ProofLemmas.SubdivisionCounting

/-- Paper, 6.1(7): "there is a `J`-enlargement that appears in the complement
of `G`." Replacing the added edge by its new branch gives a subdivision of
the graph with that edge added. -/
theorem subdivision_of_extension {m n : ℕ} (D : SimpleGraph (Fin m))
    (z z' : Fin m) (hne : z ≠ z') (hnadj : ¬ D.Adj z z')
    (H : SimpleGraph (Fin n)) (ρ : Fin m → Fin n) (p : List (Fin n))
    (hext : IsThetaBranchExtension D z z' H ρ p) :
    IsSubdivision (D ⊔ SimpleGraph.edge z z') H := by
  classical
  obtain ⟨hρ, hhom, hp, hplen, hint, hcover, hedges⟩ := hext
  let T : Fin m → Fin m → List (Fin n) := fun u v =>
    if u = z ∧ v = z' then p else if u = z' ∧ v = z then p.reverse else [ρ u, ρ v]
  have hT : T z z' = p := by simp [T]
  have hTr : T z' z = p.reverse := by simp [T, hne, hne.symm]
  have hTo : ∀ u v, D.Adj u v → T u v = [ρ u, ρ v] := by
    intro u v huv
    have h1 : ¬ (u = z ∧ v = z') := by rintro ⟨rfl, rfl⟩; exact hnadj huv
    have h2 : ¬ (u = z' ∧ v = z) := by rintro ⟨rfl, rfl⟩; exact hnadj huv.symm
    simp [T, h1, h2]
  have splitAdj : ∀ u v, (D ⊔ SimpleGraph.edge z z').Adj u v →
      D.Adj u v ∨ (u = z ∧ v = z') ∨ (u = z' ∧ v = z) := by
    intro u v h
    rcases h with h | h
    · exact Or.inl h
    · rw [SimpleGraph.edge_adj] at h
      exact Or.inr h.1
  have hpR : IsTrackFrom H p.reverse (ρ z') (ρ z) :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hp
  have hrev : ∀ u v, T v u = (T u v).reverse := by
    intro u v
    by_cases h1 : u = z ∧ v = z'
    · obtain ⟨rfl, rfl⟩ := h1; rw [hT, hTr]
    by_cases h2 : u = z' ∧ v = z
    · obtain ⟨rfl, rfl⟩ := h2; rw [hT, hTr, List.reverse_reverse]
    have h1' : ¬ (v = z ∧ u = z') := fun h => h2 ⟨h.2, h.1⟩
    have h2' : ¬ (v = z' ∧ u = z) := fun h => h1 ⟨h.2, h.1⟩
    simp [T, h1, h2, h1', h2']
  have noOld : ∀ u v w, w ∈ trackInterior (T u v) → w ∉ Set.range ρ := by
    intro u v w hw
    by_cases h1 : u = z ∧ v = z'
    · obtain ⟨rfl, rfl⟩ := h1; rw [hT] at hw; exact hint w hw
    by_cases h2 : u = z' ∧ v = z
    · obtain ⟨rfl, rfl⟩ := h2
      rw [hTr] at hw
      have hr := Workspace.ProofLemmas.TrackSlice.trackInterior_reverse p
      exact hint w (by simpa [hr] using hw)
    simp [T, h1, h2, trackInterior] at hw
  refine ⟨ρ, T, hρ, ?_, ?_, fun u v _ => hrev u v, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    rcases splitAdj u v huv with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [hTo u v huv]
      exact ⟨⟨by simp, by simp [hρ.ne huv.ne], by
        intro i hi
        have : i = 0 := by simp at hi; omega
        subst i; exact hhom u v huv⟩, rfl, rfl⟩
    · rw [hT]; exact hp
    · rw [hTr]; exact hpR
  · intro u v huv
    rcases splitAdj u v huv with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [hTo u v huv, trackLength]
    · rw [hT]; dsimp [trackLength]; omega
    · rw [hTr]; simp only [trackLength, List.length_reverse]; omega
  · intro u v u' v' _ _ hneE w hw hw'
    have hnot := noOld u v w hw
    have h1 : ¬ (u' = z ∧ v' = z') := by
      rintro ⟨huz, hvz⟩
      by_cases h : u = z ∧ v = z'
      · exact hneE (by rw [h.1, h.2, huz, hvz])
      by_cases h' : u = z' ∧ v = z
      · exact hneE (by rw [h'.1, h'.2, huz, hvz, Sym2.eq_swap])
      simp [T, h, h', trackInterior] at hw
    have h2 : ¬ (u' = z' ∧ v' = z) := by
      rintro ⟨huz, hvz⟩
      by_cases h : u = z ∧ v = z'
      · exact hneE (by rw [h.1, h.2, huz, hvz, Sym2.eq_swap])
      by_cases h' : u = z' ∧ v = z
      · exact hneE (by rw [h'.1, h'.2, huz, hvz])
      simp [T, h, h', trackInterior] at hw
    simp only [T, if_neg h1, if_neg h2, List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl
    · exact hnot ⟨u', rfl⟩
    · exact hnot ⟨v', rfl⟩
  · intro u v _ w hw; exact noOld u v w hw
  · intro w
    rcases hcover w with ⟨u, rfl⟩ | hw
    · exact Or.inl ⟨u, rfl⟩
    · exact Or.inr ⟨z, z', Or.inr (by simp [SimpleGraph.edge_adj, hne]), by rwa [hT]⟩
  · ext e
    rw [hedges]
    simp only [Set.mem_union, Set.mem_image, Set.mem_iUnion]
    constructor
    · rintro (⟨e, he, rfl⟩ | he)
      · induction e using Sym2.ind with
        | _ u v =>
          refine ⟨u, v, Or.inl he, ?_⟩
          rw [hTo u v he]
          exact ⟨0, by simp, by simp⟩
      · exact ⟨z, z', Or.inr (by simp [SimpleGraph.edge_adj, hne]), by rwa [hT]⟩
    · rintro ⟨u, v, huv, he⟩
      rcases splitAdj u v huv with huv | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · left
        rw [hTo u v huv] at he
        obtain ⟨i, hi, he⟩ := he
        have : i = 0 := by simp at hi; omega
        subst i
        exact ⟨s(u, v), huv, by simpa using he.symm⟩
      · right; rwa [hT] at he
      · right; rwa [hTr, trackEdges_reverse] at he

end Workspace.ProofLemmas.Thm61OddBranchSubdivision
