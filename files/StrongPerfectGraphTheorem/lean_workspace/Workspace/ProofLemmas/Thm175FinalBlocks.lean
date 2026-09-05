import Workspace.ProofLemmas.Thm175Claims
import Workspace.ProofLemmas.InducedPathExtraction

/-! The antipath blocks used in the last paragraph of 17.5. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175FinalBlocks

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas
open Workspace.ProofLemmas.Thm175Optimal Workspace.ProofLemmas.Thm175Claims

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Read a vertex of a suffix at its original index. -/
theorem mem_drop_iff (p : List V) (k : ℕ) (v : V) :
    v ∈ p.drop k ↔ ∃ i, ∃ hi : i < p.length, k ≤ i ∧ p[i]'hi = v := by
  constructor
  · intro hv
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hv
    have hki : k + i < p.length := by simp only [List.length_drop] at hi; omega
    exact ⟨k + i, hki, by omega, (List.getElem_drop ..).symm.trans he⟩
  · rintro ⟨i, hi, hki, rfl⟩
    have hsub : i - k < (p.drop k).length := by simp; omega
    have he : (p.drop k)[i-k]'hsub = p[i]'hi := by
      simp only [List.getElem_drop]
      congr 1
      omega
    exact he ▸ List.getElem_mem hsub

/-- The first block has the first two vertices named in the paper. -/
theorem two_first {G : SimpleGraph V} {X Y : Set V} (b : AntipathBlocks G X Y) :
    ∃ x₂ r, b.qX = b.x₁ :: x₂ :: r := by
  have hlen := b.hXlong
  cases hx : b.qX with
  | nil => simp [hx] at hlen
  | cons x q =>
    have he : x = b.x₁ := by simpa [hx] using b.hxhead
    cases q with
    | nil => simp [hx] at hlen
    | cons x₂ r => exact ⟨x₂, r, by simpa [he] using hx⟩

/-- Disjointness of the two blocks follows from the antipath having no repeated vertex. -/
theorem blocks_disjoint {G : SimpleGraph V} {X Y : Set V}
    (b : AntipathBlocks G X Y) : Disjoint X Y := by
  apply Set.disjoint_left.mpr
  intro v hvX hvY
  exact (List.nodup_append.mp b.hanti.1.2.1).2.2 v
    ((b.hXverts v).mpr hvX) v ((b.hYverts v).mpr hvY) rfl

/-- Removing the first vertex leaves exactly the tail of the whole antipath. -/
theorem tail_set {G : SimpleGraph V} {X Y : Set V}
    (b : AntipathBlocks G X Y) :
    (X \ {b.x₁}) ∪ Y = {v | v ∈ (b.qX ++ b.qY).drop 1} := by
  obtain ⟨x₂, r, hx⟩ := two_first b
  have hnd := b.hanti.1.2.1
  rw [hx] at hnd
  have hn : b.x₁ ∉ x₂ :: (r ++ b.qY) := (List.nodup_cons.mp hnd).1
  ext v
  simp only [Set.mem_union, Set.mem_diff, Set.mem_singleton_iff, Set.mem_setOf_eq]
  rw [← b.hXverts, ← b.hYverts, hx]
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero, List.mem_cons,
    List.mem_append] at hn ⊢
  constructor
  · rintro (⟨hv | hv | hv, hne⟩ | hv)
    · exact (hne hv).elim
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr hv)
  · intro hv
    have hne : v ≠ b.x₁ := by intro he; subst v; exact hn hv
    rcases hv with hv | hv | hv
    · exact Or.inl ⟨Or.inr (Or.inl hv), hne⟩
    · exact Or.inl ⟨Or.inr (Or.inr hv), hne⟩
    · exact Or.inr hv

/-- The paper's set `W` is an initial segment of the antipath with `x₁` deleted. -/
theorem W_set {G : SimpleGraph V} {X Y : Set V} {p₁ : V}
    (b : AntipathBlocks G X Y) (t : FirstMissContext p₁ b) :
    W b t = {v | v ∈ ((b.qX ++ b.qY).drop 1).take (b.qX.length - 1 + t.t₀)} := by
  obtain ⟨x₂, r, hx⟩ := two_first b
  have hnd := b.hanti.1.2.1
  rw [hx] at hnd
  have hn : b.x₁ ∉ x₂ :: (r ++ b.qY) := (List.nodup_cons.mp hnd).1
  have htail : X \ {b.x₁} = {v | v ∈ x₂ :: r} := by
    ext v
    rw [Set.mem_diff, Set.mem_singleton_iff, ← b.hXverts, hx]
    simp only [Set.mem_setOf_eq, List.mem_cons]
    constructor
    · rintro ⟨hv | hv, hne⟩
      · exact (hne hv).elim
      · exact hv
    · intro hv
      refine ⟨Or.inr hv, ?_⟩
      intro he
      subst v
      apply hn
      exact List.mem_append_left b.qY (List.mem_cons.mpr hv)
  rw [W, htail, hx]
  simp only [List.cons_append, List.drop_succ_cons, List.drop_zero,
    List.length_cons, Nat.add_sub_cancel]
  have he : x₂ :: (r ++ b.qY) = (x₂ :: r) ++ b.qY := rfl
  rw [he, List.take_append]
  simp only [List.length_cons, Nat.add_sub_cancel_left]
  rw [List.take_of_length_le (l := x₂ :: r) (by simp only [List.length_cons]; omega)]
  ext v
  simp [or_assoc]

/-- Both sets used in the smaller counterexample are anticonnected. -/
theorem W_anticonnected {G : SimpleGraph V} {X Y : Set V} {p₁ : V}
    (b : AntipathBlocks G X Y) (t : FirstMissContext p₁ b) :
    AnticonnectedSet G (W b t) ∧ AnticonnectedSet G (W b t ∪ Y) := by
  have hchain := InducedPathExtraction.isChain_of_isPathList b.hanti.1
  have hunion : W b t ∪ Y = (X \ {b.x₁}) ∪ Y := by
    ext v
    constructor
    · rintro ((hv | hv) | hv)
      · exact Or.inl hv
      · exact Or.inr ((b.hYverts v).mp (List.take_subset _ _ hv))
      · exact Or.inr hv
    · rintro (hv | hv)
      · exact Or.inl (Or.inl hv)
      · exact Or.inr hv
  constructor
  · rw [W_set]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      ((hchain.drop 1).take _)
  · rw [hunion, tail_set]
    exact InducedPathExtraction.connectedSet_setOf_mem_of_isChain (hchain.drop 1)

end Workspace.ProofLemmas.Thm175FinalBlocks
