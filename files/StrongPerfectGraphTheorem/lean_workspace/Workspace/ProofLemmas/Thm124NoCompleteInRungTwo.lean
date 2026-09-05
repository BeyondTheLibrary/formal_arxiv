import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S02.Thm_2_8

/-!
# 12.4(2), first step: *"Hence there is no `Q`-complete vertex in `R₂`."*

PAPER (printed p. 74, inside claim (2) of the proof of 12.4):

*"Choose a step `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `a₁` is `Q`-complete and `a₂` is not.
Since `s`, `t` are different it follows that `t` is nonadjacent to both `a₀`, `a₂`; and so by
2.8, `Q` cannot be linked onto the triangle `{a₀, a₁, a₂}`.  Hence there is no `Q`-complete
vertex in `R₂`."*

The three paths that would link `Q` onto the triangle `{a₀, a₁, a₂}` are

* `a₀`-`S`-`s`, the initial stretch `R₀[0 .. iS]` of the banister (its unique `Q`-complete
  vertex is its far end `s`, by minimality of `iS`);
* the one-vertex path `a₁` (which is `Q`-complete);
* the initial stretch `R₂[0 .. j]` of the rung `R₂`, where `j` is the first position of a
  `Q`-complete vertex on `R₂` — this is what the hypothesis for contradiction supplies.

2.8 then forces either two of the three paths to have length `0` (impossible: `a₀` and `a₂` are
not `Q`-complete) or every `Q`-complete vertex to be adjacent to one of two of `a₀, a₁, a₂` —
and each of the three printed pairs contains `a₀` or `a₂`, while `t` is `Q`-complete and
nonadjacent to `a₀`, `a₁` and `a₂`.

Everything is phrased in terms of the two paths `R₀`, `R₂` and the vertex `a₁`; the caller
supplies the cross-edge descriptions, which for a staircase come from the prism formed by
`R₀, R₁, R₂` (`StaircaseStepBanisterOddPrism`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm124NoCompleteInRungTwo

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"by 2.8, `Q` cannot be linked onto the triangle `{a₀, a₁, a₂}`.  Hence there is no
`Q`-complete vertex in `R₂`."* -/
theorem no_complete_in_R₂
    (G : SimpleGraph V) (hG : Berge G) (Q : Set V) (hQanti : AnticonnectedSet G Q)
    (a₀ a₁ a₂ b₀ b₂ : V) (R₀ R₂ : List V)
    (hR₀ : IsPathFrom G R₀ a₀ b₀) (hR₂ : IsPathFrom G R₂ a₂ b₂)
    (hc02 : ∀ u ∈ R₀, ∀ v ∈ R₂, (G.Adj u v ↔ (u = a₀ ∧ v = a₂) ∨ (u = b₀ ∧ v = b₂)))
    (ha₁R₀ : ∀ (k : ℕ) (hk : k < R₀.length), (G.Adj a₁ (R₀[k]'hk) ↔ k = 0))
    (ha₁R₂ : ∀ v ∈ R₂, (G.Adj a₁ v ↔ v = a₂))
    (ha₁R₀mem : a₁ ∉ R₀) (ha₁R₂mem : a₁ ∉ R₂) (hdisj : ∀ x ∈ R₀, x ∉ R₂)
    (hR₀Q : ∀ w ∈ R₀, w ∉ Q) (hR₂Q : ∀ w ∈ R₂, w ∉ Q) (ha₁Q0 : a₁ ∉ Q)
    (iS iT : ℕ) (hiS : iS < R₀.length) (hiT : iT < R₀.length)
    (hiS0 : 0 < iS) (hiSlast : iS < R₀.length - 1) (h2iT : 2 ≤ iT)
    (hminS : ∀ (k : ℕ) (hk : k < R₀.length), k < iS → ¬ VertexComplete G (R₀[k]'hk) Q)
    (hsQ : VertexComplete G (R₀[iS]'hiS) Q)
    (htQ : VertexComplete G (R₀[iT]'hiT) Q)
    (hta₁ : ¬ G.Adj (R₀[iT]'hiT) a₁) (hta₂ : ¬ G.Adj (R₀[iT]'hiT) a₂)
    (ha₁Q : VertexComplete G a₁ Q) (ha₂Q : ¬ VertexComplete G a₂ Q) :
    ∀ w ∈ R₂, ¬ VertexComplete G w Q := by
  classical
  intro w hwR₂ hwQ
  have hlen0 : 0 < R₀.length := PathBasics.path_length_pos hR₀.1
  have hlen2 : 0 < R₂.length := PathBasics.path_length_pos hR₂.1
  have h00 : R₀[0]'hlen0 = a₀ := PathBasics.getElem_zero_of_head? hR₀.2.1 hlen0
  have h0last : R₀[R₀.length - 1]'(by omega) = b₀ :=
    PathBasics.getElem_last_of_getLast? hR₀.2.2 hlen0
  have h20 : R₂[0]'hlen2 = a₂ := PathBasics.getElem_zero_of_head? hR₂.2.1 hlen2
  have hget0 : ∀ (k l : ℕ) (hk : k < R₀.length) (hl : l < R₀.length),
      k = l → (R₀[k]'hk) = (R₀[l]'hl) := by rintro k l hk hl rfl; rfl
  have hget2 : ∀ (k l : ℕ) (hk : k < R₂.length) (hl : l < R₂.length),
      k = l → (R₂[k]'hk) = (R₂[l]'hl) := by rintro k l hk hl rfl; rfl
  -- the first `Q`-complete position on `R₂`
  have hex : ∃ j : ℕ, ∃ hj : j < R₂.length, VertexComplete G (R₂[j]'hj) Q := by
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hwR₂
    exact ⟨k, hk, by rw [hkw]; exact hwQ⟩
  set j : ℕ := Nat.find hex with hjdef
  obtain ⟨hj, hjQ⟩ := Nat.find_spec hex
  have hjmin : ∀ (k : ℕ) (hk : k < R₂.length), k < j →
      ¬ VertexComplete G (R₂[k]'hk) Q := fun k hk hkj hc => Nat.find_min hex hkj ⟨hk, hc⟩
  have hj0 : 0 < j := by
    by_contra hcon
    refine ha₂Q ?_
    rw [← h20, ← hget2 j 0 hj hlen2 (by omega)]
    exact hjQ
  -- the three paths
  set P₁ : List V := (R₀.drop 0).take (iS - 0 + 1) with hP₁def
  set P₂ : List V := [a₁] with hP₂def
  set P₃ : List V := (R₂.drop 0).take (j - 0 + 1) with hP₃def
  have hP₁len : P₁.length = iS - 0 + 1 := PathBasics.length_slice R₀ (by omega) hiS
  have hP₃len : P₃.length = j - 0 + 1 := PathBasics.length_slice R₂ (by omega) hj
  have hP₁from : IsPathFrom G P₁ a₀ (R₀[iS]'hiS) := by
    have := PathBasics.isPathFrom_slice hR₀.1 hiS0 hiS
    rwa [h00] at this
  have hP₃from : IsPathFrom G P₃ a₂ (R₂[j]'hj) := by
    have := PathBasics.isPathFrom_slice hR₂.1 hj0 hj
    rwa [h20] at this
  have hP₂from : IsPathFrom G P₂ a₁ a₁ := ⟨PathBasics.isPathList_singleton G a₁, rfl, rfl⟩
  -- membership decoders
  have hP₁mem : ∀ x ∈ P₁, ∃ (k : ℕ) (hk : k < R₀.length), k ≤ iS ∧ (R₀[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, -, hki, hkx⟩ := (PathBasics.mem_slice_iff R₀ (by omega) hiS).mp hx
    exact ⟨k, hk, hki, hkx⟩
  have hP₃mem : ∀ x ∈ P₃, ∃ (k : ℕ) (hk : k < R₂.length), k ≤ j ∧ (R₂[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, -, hki, hkx⟩ := (PathBasics.mem_slice_iff R₂ (by omega) hj).mp hx
    exact ⟨k, hk, hki, hkx⟩
  have hP₁sub : ∀ x ∈ P₁, x ∈ R₀ := by
    intro x hx; obtain ⟨k, hk, -, rfl⟩ := hP₁mem x hx; exact List.getElem_mem hk
  have hP₃sub : ∀ x ∈ P₃, x ∈ R₂ := by
    intro x hx; obtain ⟨k, hk, -, rfl⟩ := hP₃mem x hx; exact List.getElem_mem hk
  -- no vertex of `P₁` is `b₀`
  have hP₁neb₀ : ∀ x ∈ P₁, x ≠ b₀ := by
    intro x hx
    obtain ⟨k, hk, hki, rfl⟩ := hP₁mem x hx
    rw [← h0last]
    exact PathBasics.path_ne_of_ne_index hR₀.1 hk (by omega) (by omega)
  -- `Q`-complete vertices of the three paths
  have hu₁ : ∀ x ∈ P₁, (VertexComplete G x Q ↔ x = (R₀[iS]'hiS)) := by
    intro x hx
    obtain ⟨k, hk, hki, rfl⟩ := hP₁mem x hx
    constructor
    · intro hc
      rcases lt_or_eq_of_le hki with hlt | rfl
      · exact absurd hc (hminS k hk hlt)
      · rfl
    · intro he
      have : k = iS := by
        by_contra hne
        exact PathBasics.path_ne_of_ne_index hR₀.1 hk hiS hne he
      subst this; exact hsQ
  have hu₂ : ∀ x ∈ P₂, (VertexComplete G x Q ↔ x = a₁) := by
    intro x hx
    have : x = a₁ := by simpa [hP₂def] using hx
    subst this
    exact ⟨fun _ => rfl, fun _ => ha₁Q⟩
  have hu₃ : ∀ x ∈ P₃, (VertexComplete G x Q ↔ x = (R₂[j]'hj)) := by
    intro x hx
    obtain ⟨k, hk, hki, rfl⟩ := hP₃mem x hx
    constructor
    · intro hc
      rcases lt_or_eq_of_le hki with hlt | rfl
      · exact absurd hc (hjmin k hk hlt)
      · rfl
    · intro he
      have : k = j := by
        by_contra hne
        exact PathBasics.path_ne_of_ne_index hR₂.1 hk hj hne he
      subst this; exact hjQ
  -- the linkage
  have hlink : SetLinkedOntoTriangle G Q a₀ a₁ a₂ P₁ P₂ P₃ := by
    refine ⟨⟨hP₁from.1, hP₂from.1, hP₃from.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨Or.inl hP₁from.2.1, Or.inl hP₂from.2.1, Or.inl hP₃from.2.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨⟨R₀[iS]'hiS, (PathBasics.isPathFrom_ends_mem hP₁from).2, hsQ⟩,
        ⟨a₁, by simp [hP₂def], ha₁Q⟩,
        ⟨R₂[j]'hj, (PathBasics.isPathFrom_ends_mem hP₃from).2, hjQ⟩⟩⟩
    · intro x hx hxP₂
      have : x = a₁ := by simpa [hP₂def] using hxP₂
      exact ha₁R₀mem (this ▸ hP₁sub x hx)
    · intro x hx hxP₃
      exact hdisj x (hP₁sub x hx) (hP₃sub x hxP₃)
    · intro x hx hxP₃
      have : x = a₁ := by simpa [hP₂def] using hx
      exact ha₁R₂mem (this ▸ hP₃sub x hxP₃)
    · -- edges between `P₁` and `P₂`
      intro x hx y hy
      have hya : y = a₁ := by simpa [hP₂def] using hy
      subst hya
      obtain ⟨k, hk, hki, rfl⟩ := hP₁mem x hx
      constructor
      · intro hadj
        have hk0 : k = 0 := (ha₁R₀ k hk).mp hadj.symm
        subst hk0
        exact ⟨h00, rfl⟩
      · rintro ⟨hxa, -⟩
        have hk0 : k = 0 := by
          by_contra hne
          exact PathBasics.path_ne_of_ne_index hR₀.1 hk hlen0 hne (hxa.trans h00.symm)
        subst hk0
        exact ((ha₁R₀ 0 hlen0).mpr rfl).symm
    · -- edges between `P₁` and `P₃`
      intro x hx y hy
      have hxR₀ : x ∈ R₀ := hP₁sub x hx
      have hyR₂ : y ∈ R₂ := hP₃sub y hy
      rw [hc02 x hxR₀ y hyR₂]
      constructor
      · rintro (h | h)
        · exact h
        · exact absurd h.1 (hP₁neb₀ x hx)
      · exact Or.inl
    · -- edges between `P₂` and `P₃`
      intro x hx y hy
      have hxa : x = a₁ := by simpa [hP₂def] using hx
      subst hxa
      rw [ha₁R₂ y (hP₃sub y hy)]
      exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  -- 2.8
  have h28 :=
    Workspace.Statements.S02.SPGT.thm_2_8 G hG Q hQanti a₀ a₁ a₂ (R₀[iS]'hiS) a₁ (R₂[j]'hj)
      P₁ P₂ P₃ hlink hP₁from hP₂from hP₃from hu₁ hu₂ hu₃
  have hP₁length : pathLength P₁ = iS := by
    rw [PathBasics.pathLength_eq, hP₁len]; omega
  have hP₃length : pathLength P₃ = j := by
    rw [PathBasics.pathLength_eq, hP₃len]; omega
  -- `t` is nonadjacent to all three of `a₀, a₁, a₂`
  have hta₀ : ¬ G.Adj (R₀[iT]'hiT) a₀ := by
    rw [← h00]
    intro hadj
    have := (PathBasics.path_adj_iff hR₀.1 hiT hlen0).mp hadj
    omega
  rcases h28 with hfam1 | hfam2
  · rcases hfam1 with ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h3⟩
    · rw [hP₁length] at h1; omega
    · rw [hP₁length] at h1; omega
    · rw [hP₃length] at h3; omega
  · rcases hfam2 with ⟨-, -, -, hall⟩ | ⟨-, -, -, hall⟩ | ⟨-, -, -, hall⟩ <;>
      rcases hall (R₀[iT]'hiT) htQ with hc | hc
    · exact hta₀ hc
    · exact hta₁ hc
    · exact hta₀ hc
    · exact hta₂ hc
    · exact hta₁ hc
    · exact hta₂ hc

end Workspace.ProofLemmas.Thm124NoCompleteInRungTwo
