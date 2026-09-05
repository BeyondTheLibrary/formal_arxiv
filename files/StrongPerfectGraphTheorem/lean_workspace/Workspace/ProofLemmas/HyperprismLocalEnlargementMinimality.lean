import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.PathGlue

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

/-- Name the first and last internal vertices of the attachment path. -/
theorem interiorPathData
    {V : Type*} {G : SimpleGraph V} {f : List V} {xA xB : V}
    (hfne : f ≠ [])
    (hfull : IsPathFrom G (xA :: (f ++ [xB])) xA xB)
    (hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v)
    (hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) :
    ∃ f₁ fn : V, IsPathFrom G f f₁ fn ∧ G.Adj xA f₁ ∧ G.Adj xB fn := by
  have h3 : 3 ≤ (xA :: (f ++ [xB])).length := by
    have := List.length_pos_of_ne_nil hfne
    simp
    omega
  have hint := PathGlue.isPathFrom_interior hfull.1 h3
  have hinterior : interior (xA :: (f ++ [xB])) = f := by
    simp [Workspace.Types.Core.SPGT.interior]
  rw [hinterior] at hint
  let f₁ := (xA :: (f ++ [xB]))[1]'(by omega)
  let fn := (xA :: (f ++ [xB]))[(xA :: (f ++ [xB])).length - 2]'(by omega)
  have hfpath : IsPathFrom G f f₁ fn := hint
  have hf₁mem : f₁ ∈ f := PathBasics.head_mem hfpath.2.1
  have hfnmem : fn ∈ f := PathBasics.getLast_mem hfpath.2.2
  refine ⟨f₁, fn, hfpath, (hleft f₁ hf₁mem).mpr hfpath.2.1, ?_⟩
  exact (hright fn hfnmem).mpr hfpath.2.2

private theorem local_mono
    {V : Type*} {A B C : Fin 3 → Set V} {X Y : Set V}
    (hXY : X ⊆ Y) (hY : LocalForHyperprism A B C Y) : LocalForHyperprism A B C X := by
  rcases hY with h | h | h | h | h
  · exact Or.inl (hXY.trans h)
  · exact Or.inr (Or.inl (hXY.trans h))
  · exact Or.inr (Or.inr (Or.inl (hXY.trans h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hXY.trans h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hXY.trans h))))

/-- Removing the first vertex from the path gives a proper connected subset of a minimal
bad set, so its attachment set is local. -/
theorem localAfterFirst
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C : Fin 3 → Set V} {F : Set V}
    (hF : MinimalBad G A B C F) {f : List V} {f₁ fn : V}
    (hf : IsPathFrom G f f₁ fn) (h2 : 2 ≤ f.length)
    (hFeq : F = {z : V | z ∈ f}) :
    LocalForHyperprism A B C (attachments G (F \ {f₁}) (hyperVerts A B C)) := by
  have hfirst : f₁ ∈ F := by rw [hFeq]; exact PathBasics.head_mem hf.2.1
  have hproper : F \ {f₁} ≠ F := by
    intro heq
    have : f₁ ∈ F \ {f₁} := heq.symm ▸ hfirst
    exact this.2 (by simp)
  have hconn : ConnectedSet G (F \ {f₁}) := by
    have htail := Workspace.ProofLemmas.HyperprismRungStructure.isPathList_tail hf.1 h2
    have hc := InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htail
    have heq : F \ {f₁} = {z : V | z ∈ f.tail} := by
      ext z
      rw [hFeq]
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact (Workspace.ProofLemmas.HyperprismRungStructure.mem_tail_iff_of_pathFrom hf).symm
    rwa [heq]
  exact hF.local_of_ssubset (fun _ hz => hz.1) hproper hconn

/-- The symmetric local attachment statement after removing the last path vertex. -/
theorem localBeforeLast
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C : Fin 3 → Set V} {F : Set V}
    (hF : MinimalBad G A B C F) {f : List V} {f₁ fn : V}
    (hf : IsPathFrom G f f₁ fn) (h2 : 2 ≤ f.length)
    (hFeq : F = {z : V | z ∈ f}) :
    LocalForHyperprism A B C (attachments G (F \ {fn}) (hyperVerts A B C)) := by
  have hlast : fn ∈ F := by rw [hFeq]; exact PathBasics.getLast_mem hf.2.2
  have hproper : F \ {fn} ≠ F := by
    intro heq
    have : fn ∈ F \ {fn} := heq.symm ▸ hlast
    exact this.2 (by simp)
  have hconn : ConnectedSet G (F \ {fn}) := by
    have hdrop := Workspace.ProofLemmas.HyperprismRungStructure.isPathList_dropLast hf.1 h2
    have hc := InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hdrop
    have heq : F \ {fn} = {z : V | z ∈ f.dropLast} := by
      ext z
      rw [hFeq]
      simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
      exact (Workspace.ProofLemmas.HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hf).symm
    rwa [heq]
  exact hF.local_of_ssubset (fun _ hz => hz.1) hproper hconn

/-- If the last path vertex sees `B j`, then no vertex other than the first can see
`A k` for `k ≠ j`.  Otherwise the local attachment set after deleting the first vertex
would contain the non-local pair formed by these two attachments. -/
theorem onlyFirstSeesA
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C : Fin 3 → Set V} {F : Set V}
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    {f : List V} {f₁ fn b : V} (hf : IsPathFrom G f f₁ fn) (h2 : 2 ≤ f.length)
    (hFeq : F = {z : V | z ∈ f}) {j k : Fin 3} (hkj : k ≠ j)
    (hb : b ∈ B j) (hfnb : G.Adj fn b) :
    ∀ z ∈ f, ∀ a ∈ A k, G.Adj z a → z = f₁ := by
  have hlocal := localAfterFirst hF hf h2 hFeq
  have hfnF : fn ∈ F := by rw [hFeq]; exact PathBasics.getLast_mem hf.2.2
  have hne : fn ≠ f₁ := (PathBasics.isPathFrom_ends_ne hf (by
    simp only [pathLength]
    omega)).symm
  intro z hzf a ha hadj
  by_contra hz
  apply HyperprismTwoAttachments.not_local_pair hH hkj ha hb
  refine local_mono ?_ hlocal
  intro v hv
  rcases hv with rfl | hv
  · exact ⟨mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inl ha)⟩, z,
      ⟨by rw [hFeq]; exact hzf, by simpa using hz⟩, hadj.symm⟩
  · have hvb : v = b := hv
    subst v
    exact ⟨mem_hyperVerts_iff.mpr ⟨j, Or.inl (Or.inr hb)⟩, fn,
      ⟨hfnF, by simpa using hne⟩, hfnb.symm⟩

/-- The mirror of `onlyFirstSeesA`. -/
theorem onlyLastSeesB
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A B C : Fin 3 → Set V} {F : Set V}
    (hH : IsHyperprism G A B C) (hF : MinimalBad G A B C F)
    {f : List V} {f₁ fn a : V} (hf : IsPathFrom G f f₁ fn) (h2 : 2 ≤ f.length)
    (hFeq : F = {z : V | z ∈ f}) {i k : Fin 3} (hik : i ≠ k)
    (ha : a ∈ A i) (hf₁a : G.Adj f₁ a) :
    ∀ z ∈ f, ∀ b ∈ B k, G.Adj z b → z = fn := by
  have hlocal := localBeforeLast hF hf h2 hFeq
  have hf₁F : f₁ ∈ F := by rw [hFeq]; exact PathBasics.head_mem hf.2.1
  have hne : f₁ ≠ fn := PathBasics.isPathFrom_ends_ne hf (by
    simp only [pathLength]
    omega)
  intro z hzf b hb hadj
  by_contra hz
  apply HyperprismTwoAttachments.not_local_pair hH hik ha hb
  refine local_mono ?_ hlocal
  intro v hv
  rcases hv with rfl | hv
  · exact ⟨mem_hyperVerts_iff.mpr ⟨i, Or.inl (Or.inl ha)⟩, f₁,
      ⟨hf₁F, by simpa using hne⟩, hf₁a.symm⟩
  · have hvb : v = b := hv
    subst v
    exact ⟨mem_hyperVerts_iff.mpr ⟨k, Or.inl (Or.inr hb)⟩, z,
      ⟨by rw [hFeq]; exact hzf, by simpa using hz⟩, hadj.symm⟩

/-- No internal strip vertex can see the outside path when the attachment set avoids every
`C`-set. -/
theorem noPathEdgeToC
    {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V} {F : Set V}
    {f : List V} (hfF : ∀ z ∈ f, z ∈ F)
    (hNoC : ∀ (m : Fin 3) (c : V),
      c ∈ attachments G F (hyperVerts A B C) → c ∉ C m) :
    ∀ z ∈ f, ∀ (m : Fin 3) (c : V), c ∈ C m → ¬ G.Adj z c := by
  intro z hzf m c hc hadj
  exact hNoC m c ⟨mem_hyperVerts_iff.mpr ⟨m, Or.inr hc⟩, z, hfF z hzf, hadj.symm⟩ hc

end Workspace.ProofLemmas.HyperprismLocalEnlargementMinimality
