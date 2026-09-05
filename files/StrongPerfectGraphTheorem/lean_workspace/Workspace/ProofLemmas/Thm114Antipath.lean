/-  Carve-out for statement 11.4 (`Workspace.Statements.S11.SPGT.thm_11_4`).

    PAPER (printed p. 67, third sentence of the proof of 11.4):

      *"Since some vertex in `B` has a nonneighbour in `Q`, there is an antipath `q₁-⋯-qₙ` in
      `Q` such that `q₁` is not adjacent to `b₀` and `qₙ` is not adjacent to some vertex in
      `B`.  Choose such an antipath with `n` minimum."*

    (The printed text reads *"a nonneighbour in `F`"*; that is a slip — `F` is anticomplete to
    `A ∪ B ∪ C`, so every vertex of `B` trivially has a nonneighbour in `F` and the sentence
    would be vacuous.  The clause being invoked is the second bullet of 11.4, *"some vertex in
    `B` has a nonneighbour in `Q`"*, and that is what `hfin` below records.)

    This module produces the antipath together with the two consequences of the minimality
    that the rest of the printed proof uses without further comment:

    * `b₀` is adjacent to `q₂, …, qₙ` — otherwise the suffix `qᵢ-⋯-qₙ` would be a shorter
      admissible antipath;
    * `q₁, …, q_{n-1}` are each complete to `B` — otherwise the prefix `q₁-⋯-qᵢ` would be a
      shorter admissible antipath.

    The first is used for *"`b₁ ∈ B₁` is complete to `{b₀, q₁, …, qₙ}` from the minimality of
    `n`"* in step (2) and for the two antiholes of the endgame; the second for
    *"`b₁` is complete to `{q₁, …, qₙ}`"* and *"`b₂` is adjacent to `q₁, …, q_{n-1}`"*.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm114Antipath

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The minimal antipath of the proof of 11.4.**

`Q` is anticonnected, some vertex of `Q` is a nonneighbour of `b₀`, and some vertex of `Q` is
a nonneighbour of some vertex of `B`.  Then there is an antipath `q₁-⋯-qₙ` with all its
vertices in `Q`, with `q₁` a nonneighbour of `b₀` and `qₙ` a nonneighbour of some vertex of
`B`, chosen with `n` minimum; minimality is delivered in the two usable forms

* `hb₀tail` : every `qᵢ` with `i ≥ 2` is adjacent to `b₀`;
* `hBdrop`  : every `qᵢ` with `i ≤ n - 1` is complete to `B`. -/
theorem exists_minimal_antipath {G : SimpleGraph V} (Q B : Set V) (b₀ : V)
    (hQanti : AnticonnectedSet G Q)
    (hstart : ∃ q ∈ Q, ¬ G.Adj b₀ q)
    (hfin : ∃ b ∈ B, ∃ q ∈ Q, ¬ G.Adj b q) :
    ∃ (qs : List V) (q₁ qn : V),
      IsAntipathFrom G qs q₁ qn ∧ (∀ x ∈ qs, x ∈ Q) ∧
        ¬ G.Adj b₀ q₁ ∧ (∃ b ∈ B, ¬ G.Adj b qn) ∧
        (∀ x ∈ qs.tail, G.Adj b₀ x) ∧
        (∀ x ∈ qs.dropLast, ∀ b ∈ B, G.Adj x b) := by
  classical
  let Good : ℕ → Prop := fun n =>
    ∃ (qs : List V) (q₁ qn : V),
      IsAntipathFrom G qs q₁ qn ∧ (∀ x ∈ qs, x ∈ Q) ∧
        ¬ G.Adj b₀ q₁ ∧ (∃ b ∈ B, ¬ G.Adj b qn) ∧ qs.length = n
  have hex : ∃ n, Good n := by
    obtain ⟨q₁, hq₁Q, hb₀q₁⟩ := hstart
    obtain ⟨b, hbB, qn, hqnQ, hbqn⟩ := hfin
    obtain ⟨qs, hqs, hqsQ⟩ :=
      InducedPathExtraction.exists_isAntipathFrom_of_anticonnected hQanti hq₁Q hqnQ
    exact ⟨qs.length, qs, q₁, qn, hqs, hqsQ, hb₀q₁, ⟨b, hbB, hbqn⟩, rfl⟩
  obtain ⟨qs, q₁, qn, hqs, hqsQ, hb₀q₁, hBqn, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (p : List V) (a c : V),
      IsAntipathFrom G p a c → (∀ x ∈ p, x ∈ Q) →
      ¬ G.Adj b₀ a → (∃ b ∈ B, ¬ G.Adj b c) → qs.length ≤ p.length := by
    intro p a c hp hpQ hba hBc
    rw [hlen]
    exact Nat.find_min' hex ⟨p, a, c, hp, hpQ, hba, hBc, rfl⟩
  have hpos : 0 < qs.length := PathBasics.path_length_pos hqs.1
  have hsuffix : ∀ (i : ℕ) (hi : i < qs.length),
      IsAntipathFrom G (qs.drop i) (qs[i]'hi) qn := by
    intro i hi
    refine ⟨PathBasics.isPathList_drop hqs.1 hi, ?_, ?_⟩
    · rw [List.head?_drop, List.getElem?_eq_getElem hi]
    · rw [List.getLast?_drop, if_neg (by omega)]
      exact hqs.2.2
  have hprefix : ∀ (i : ℕ) (hi : i < qs.length),
      IsAntipathFrom G (qs.take (i + 1)) q₁ (qs[i]'hi) := by
    intro i hi
    refine ⟨PathBasics.isPathList_take hqs.1 (Nat.succ_pos i), ?_, ?_⟩
    · simpa [List.head?_take] using hqs.2.1
    · have hlast := PathBasics.getLast?_slice qs (i := 0) (j := i) (by omega) hi
      simpa using hlast
  have hb₀tail : ∀ x ∈ qs.tail, G.Adj b₀ x := by
    intro x hx
    by_contra hbadj
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    have hi : j + 1 < qs.length := by
      rw [List.length_tail] at hj
      omega
    have hix : qs[j + 1]'hi = x := by
      rw [← hjx]
      simp only [List.getElem_tail]
    have hp := hsuffix (j + 1) hi
    rw [hix] at hp
    have hpQ : ∀ z ∈ qs.drop (j + 1), z ∈ Q := by
      intro z hz
      exact hqsQ z (List.mem_of_mem_drop hz)
    have hle := hmin (qs.drop (j + 1)) x qn hp hpQ hbadj hBqn
    rw [List.length_drop] at hle
    omega
  have hBdrop : ∀ x ∈ qs.dropLast, ∀ b ∈ B, G.Adj x b := by
    intro x hx b hbB
    by_contra hbadj
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have hipre : i + 1 < qs.length := by
      have hdropLen : qs.dropLast.length = qs.length - 1 := List.length_dropLast
      omega
    have hiqs : i < qs.length := by
      omega
    have hix' : qs[i]'hiqs = x := by
      rw [← hix]
      simp only [List.getElem_dropLast]
    have hp := hprefix i hiqs
    rw [hix'] at hp
    have hpQ : ∀ z ∈ qs.take (i + 1), z ∈ Q := by
      intro z hz
      exact hqsQ z (List.mem_of_mem_take hz)
    have hle := hmin (qs.take (i + 1)) q₁ x hp hpQ hb₀q₁
      ⟨b, hbB, fun h => hbadj h.symm⟩
    have htakeLen : (qs.take (i + 1)).length = i + 1 := by
      rw [List.length_take]
      omega
    rw [htakeLen] at hle
    omega
  exact ⟨qs, q₁, qn, hqs, hqsQ, hb₀q₁, hBqn, hb₀tail, hBdrop⟩

end Workspace.ProofLemmas.Thm114Antipath
