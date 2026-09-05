import Workspace.ProofLemmas.Thm93KnotHost
import Workspace.ProofLemmas.TrackSlice

/-!
# Chains: the tracks `List.ofFn f` of the canonical host graph

The two long branches of the host graph of 9.3 are the two chains `Fin (m+1)` and `Fin (n+1)`,
written as `List.ofFn`.  This file records what such a list is as a track.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm93KnotChains

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

variable {α : Type*} {k : ℕ}

theorem ofFn_head? (f : Fin (k + 1) → α) : (List.ofFn f).head? = some (f 0) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp), List.getElem_ofFn]
  rfl

theorem ofFn_getLast? (f : Fin (k + 1) → α) :
    (List.ofFn f).getLast? = some (f (Fin.last k)) := by
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem
    (by simp only [List.length_ofFn]; omega), List.getElem_ofFn]
  congr 2
  simp [Fin.last]

theorem ofFn_isTrackList {G : SimpleGraph α} (f : Fin (k + 1) → α)
    (hinj : Function.Injective f)
    (hadj : ∀ i : Fin k, G.Adj (f i.castSucc) (f i.succ)) :
    IsTrackList G (List.ofFn f) := by
  refine ⟨by simp, List.nodup_ofFn_ofInjective hinj, ?_⟩
  intro i hi
  simp only [List.length_ofFn] at hi
  rw [List.getElem_ofFn, List.getElem_ofFn]
  exact hadj ⟨i, by omega⟩

theorem mem_trackEdges_ofFn {f : Fin (k + 1) → α} {e : Sym2 α} :
    e ∈ trackEdges (List.ofFn f) ↔ ∃ i : Fin k, e = s(f i.castSucc, f i.succ) := by
  constructor
  · rintro ⟨i, hi, rfl⟩
    simp only [List.length_ofFn] at hi
    refine ⟨⟨i, by omega⟩, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rfl
  · rintro ⟨i, rfl⟩
    refine ⟨i.val, by simp only [List.length_ofFn]; omega, ?_⟩
    rw [List.getElem_ofFn, List.getElem_ofFn]
    rfl

theorem mem_trackInterior_ofFn {f : Fin (k + 1) → α} {w : α} :
    w ∈ trackInterior (List.ofFn f) ↔
      ∃ i : Fin (k + 1), 0 < i.val ∧ i.val < k ∧ w = f i := by
  rw [Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j + 2 < k + 1 := by simpa using hj
    refine ⟨⟨j + 1, by omega⟩, ?_, ?_, ?_⟩
    · simp
    · simpa using by omega
    · rw [List.getElem_ofFn]
  · rintro ⟨i, hi0, hik, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, i.val = v + 1 := ⟨i.val - 1, by omega⟩
    refine ⟨v, by simp only [List.length_ofFn]; omega, ?_⟩
    rw [List.getElem_ofFn]
    congr 1
    exact Fin.ext hv.symm

theorem mem_ofFn {f : Fin (k + 1) → α} {w : α} :
    w ∈ List.ofFn f ↔ ∃ i, f i = w := by
  simp only [List.mem_ofFn, Set.mem_range]

end Workspace.ProofLemmas.Thm93KnotChains
