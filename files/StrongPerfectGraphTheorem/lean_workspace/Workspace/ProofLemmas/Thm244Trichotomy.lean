import Workspace.Types.Core
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.MinimalThreeTerminalWitnesses
import Workspace.ProofLemmas.DeletedWitnessIsUnique
import Workspace.ProofLemmas.NearestPathAttachment
import Workspace.ProofLemmas.AttachmentIndicesAreLocal
import Workspace.ProofLemmas.ThroughPathWhenThirdWitnessOnPath
import Workspace.ProofLemmas.ShapeFromUniqueAttachment
import Workspace.ProofLemmas.TriangleLegsFromDoubleAttachment
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false

namespace Workspace.Types.Thm244Trichotomy

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm244Shapes

private theorem getElem_congr_idx {α : Type*} {l : List α} {i j : ℕ}
    (hi : i < l.length) (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h
  rfl

theorem minimalConnectedThreeTerminal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Set V) (N : Fin 3 → Set V)
    (hFconn : ConnectedSet G F)
    (hmeet : ∀ i : Fin 3, ∃ f ∈ F, f ∈ N i)
    (hsep : ∀ w ∈ F, ∀ i j : Fin 3, i ≠ j → ¬ (w ∈ N i ∧ w ∈ N j))
    (hmin : ∀ S : Set V, S ⊆ F → ConnectedSet G S →
      (∀ i : Fin 3, ∃ f ∈ S, f ∈ N i) → F.ncard ≤ S.ncard) :
    (∃ v : Fin 3 → V, ∃ u : V, ∃ P : Fin 3 → List V, Spider G F N v u P) ∨
    (∃ v u : Fin 3 → V, ∃ P : Fin 3 → List V, TriangleLegs G F N v u P) ∨
    (∃ i j k : Fin 3, ∃ P : List V, ∃ a b : V, ThroughPath G F N i j k P a b) := by
  classical
  obtain ⟨v, hv, hpair, hfixed⟩ :=
    Workspace.Types.MinimalThreeTerminalWitnesses.minimalThreeTerminalWitnesses
      G F N hmeet hsep hmin
  obtain ⟨Q, hQ, hQF⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
      hFconn (hv 0).1 (hv 1).1
  by_cases hv2Q : v 2 ∈ Q
  · right
    right
    exact ⟨0, 1, 2, Q, v 0, v 1,
      Workspace.Types.ThroughPathWhenThirdWitnessOnPath.throughPathWhenThirdWitnessOnPath
        G F N v hv hpair hmin hfixed Q hQ hQF hv2Q⟩
  · obtain ⟨R, z, hR, hRF, hzQ, hRlen, hinter, hclean⟩ :=
      Workspace.Types.NearestPathAttachment.nearestPathAttachment
        G F Q (v 2) hFconn hQ.1 hQF (hv 2).1 hv2Q
    have hQconn : ConnectedSet G {w : V | w ∈ Q} :=
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hQ.1
    have hRconn : ConnectedSet G {w : V | w ∈ R} :=
      Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1
    have hzR : z ∈ R :=
      (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR).2
    have hUconn : ConnectedSet G ({w : V | w ∈ Q} ∪ {w : V | w ∈ R}) :=
      Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union
        hQconn hRconn (Or.inl ⟨z, hzQ, hzR⟩)
    have hUsub : {w : V | w ∈ Q} ∪ {w : V | w ∈ R} ⊆ F := by
      rintro w (hwQ | hwR)
      · exact hQF w hwQ
      · exact hRF w hwR
    have hcover : F = {w : V | w ∈ Q} ∪ {w : V | w ∈ R} := by
      symm
      apply hfixed _ hUsub hUconn
      intro i
      fin_cases i
      · exact Or.inl (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ).1
      · exact Or.inl (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ).2
      · exact Or.inr (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR).1
    obtain ⟨s, hs, hatt⟩ :=
      Workspace.Types.AttachmentIndicesAreLocal.attachmentIndicesAreLocal
        G F N v hv hmin Q R z hQ hR hv2Q hzQ hRlen hinter hcover
    have hRlast : R[R.length - 1]'(by omega) = z :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hR.2.2 (by omega)
    have hyz : G.Adj (R[R.length - 2]'(by omega)) z := by
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hR.1
        (show (R.length - 2) + 1 < R.length by omega)
      have hidx : R[(R.length - 2) + 1]'(by omega) = z := by
        rw [← hRlast]
        congr 1
        omega
      simpa [hidx] using hadj
    obtain ⟨d, hd, hdz⟩ := List.getElem_of_mem hzQ
    have hyd : G.Adj (R[R.length - 2]'(by omega)) (Q[d]'hd) := by
      simpa [hdz] using hyz
    rcases hatt with ⟨hsingle, _⟩ | ⟨hdouble, _⟩
    · have hds : d = s := (hsingle d hd).mp hyd
      have hzs : z = Q[s]'hs :=
        hdz.symm.trans (getElem_congr_idx hd hs hds)
      rcases Workspace.Types.ShapeFromUniqueAttachment.shapeFromUniqueAttachment
          G F N v hv hpair hmin hfixed Q R z s hQ hQF hR hRF hv2Q hzQ hRlen
          hinter hcover hclean hs hzs hsingle with hspider | hthrough
      · left
        exact ⟨v, hspider⟩
      · right
        right
        exact hthrough
    · obtain ⟨hsucc, hdouble⟩ := hdouble
      have hdzs : d = s ∨ d = s + 1 := (hdouble d hd).mp hyd
      have hzlocal : z = Q[s]'(by omega) ∨ z = Q[s + 1]'hsucc := by
        rcases hdzs with hds | hds
        · exact Or.inl (hdz.symm.trans (getElem_congr_idx hd (by omega) hds))
        · exact Or.inr (hdz.symm.trans (getElem_congr_idx hd hsucc hds))
      right
      left
      exact ⟨v,
        Workspace.Types.TriangleLegsFromDoubleAttachment.triangleLegsFromDoubleAttachment
          G F N v hv hpair hmin hfixed Q R z s hQ hQF hR hRF hv2Q hzQ hRlen
          hinter hcover hclean hsucc hzlocal hdouble⟩

end Workspace.Types.Thm244Trichotomy
