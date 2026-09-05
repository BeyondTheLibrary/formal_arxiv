import Workspace.Statements.S17.Thm_17_1
import Workspace.ProofLemmas.Thm192Claim6Basics

/-! The final use of 17.1 in claim (7) of 19.2. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapCatch

open Workspace.Types.Core.SPGT Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching.SPGT Workspace.Types.Classes.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (claim (7)): "`x₀,x₁,x₂` all have unique neighbours in it ... and
these three vertices do not form a triangle ... contrary to 17.1."
Three distinct unique neighbours of a caught triangle must be pairwise adjacent. -/
theorem unique_neighbours_adjacent {G : SimpleGraph V} (hG : InF7 G)
    {a b c d e f : V} {F : Set V} (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c)
    (hF : ConnectedSet G F) (hdisj : Disjoint F ({a, b, c} : Set V))
    (hd : d ∈ F) (he : e ∈ F) (hf : f ∈ F)
    (had : G.Adj a d) (hbe : G.Adj b e) (hcf : G.Adj c f)
    (hda : ∀ v ∈ F, G.Adj a v → v = d)
    (heb : ∀ v ∈ F, G.Adj b v → v = e)
    (hfc : ∀ v ∈ F, G.Adj c v → v = f)
    (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) : G.Adj d f := by
  have hT : IsTriangle G ({a, b, c} : Set V) := by
    refine ⟨?_, ?_⟩
    · rw [Set.ncard_insert_of_notMem (by simp [hab.ne, hac.ne]), Set.ncard_pair hbc.ne]
    · intro u hu v hv huv
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
      rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
      all_goals first | exact (huv rfl).elim | assumption | exact hab.symm | exact hac.symm | exact hbc.symm
  have hcatch : Catches G F ({a, b, c} : Set V) := by
    refine ⟨hT, hF, hdisj, ?_⟩
    intro v hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨d, hd, had⟩
    · exact ⟨e, he, hbe⟩
    · exact ⟨f, hf, hcf⟩
  rcases Workspace.Statements.S17.SPGT.thm_17_1 G hG _ hT F
    (fun v hv hvT => Set.disjoint_left.mp hdisj hv hvT) hcatch with
    ⟨a₁, a₂, a₃, b₁, b₂, b₃, hTeq, hBF, hR⟩ | ⟨v, hv, htwo⟩
  · have hmate : ∀ t ∈ ({a, b, c} : Set V), ∃ s ∈ ({b₁, b₂, b₃} : Set V), G.Adj t s := by
      intro t ht
      rw [hTeq] at ht
      rcases ht with rfl | rfl | rfl
      · exact ⟨b₁, by simp, (hR.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨b₂, by simp, (hR.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
      · exact ⟨b₃, by simp, (hR.2.2.2 _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩
    obtain ⟨d', hd', had'⟩ := hmate a (by simp)
    obtain ⟨f', hf', hcf'⟩ := hmate c (by simp)
    have hdd := hda d' (hBF hd') had'
    have hff := hfc f' (hBF hf') hcf'
    exact hR.2.1.2 d (hdd ▸ hd') f (hff ▸ hf') hdf
  · obtain ⟨u, hu, w, hw, huw⟩ := (Set.one_lt_ncard (Set.toFinite _)).mp htwo
    have huT : u = a ∨ u = b ∨ u = c := hu.2
    have hwT : w = a ∨ w = b ∨ w = c := hw.2
    have huv : G.Adj u v := hu.1.symm
    have hwv : G.Adj w v := hw.1.symm
    rcases huT with rfl | rfl | rfl <;> rcases hwT with rfl | rfl | rfl
    all_goals first
      | exact (huw rfl).elim
      | exact (hde ((hda v hv huv).symm.trans (heb v hv hwv))).elim
      | exact (hde ((hda v hv hwv).symm.trans (heb v hv huv))).elim
      | exact (hdf ((hda v hv huv).symm.trans (hfc v hv hwv))).elim
      | exact (hdf ((hda v hv hwv).symm.trans (hfc v hv huv))).elim
      | exact (hef ((heb v hv huv).symm.trans (hfc v hv hwv))).elim
      | exact (hef ((heb v hv hwv).symm.trans (hfc v hv huv))).elim

end Workspace.ProofLemmas.Thm192Claim7GapCatch
