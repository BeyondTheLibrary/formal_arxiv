import Workspace.ProofLemmas.Thm175Claim2Antipath

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim2Marks

open Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim2Basics
open Workspace.ProofLemmas.Thm175Claim2Antipath

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "So `W₁ ∩ W₂ = {p₁}`." Away from index zero, a vertex
cannot complete both deleted sets, since their union is `X`. -/
theorem marks_disjoint (G : SimpleGraph V) {z : V} (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁))
    (x₁ x₂ : V) (hne : x₁ ≠ x₂) (i : ℕ)
    (hA : Marked G (c.X \ {x₁}) c.core.p i)
    (hB : Marked G (c.X \ {x₂}) c.core.p i) : i = 0 := by
  obtain ⟨hi, hiA⟩ := hA
  obtain ⟨_, hiB⟩ := hB
  have hiX : VertexComplete G (c.core.p[i]'hi) c.X := by
    intro x hx
    by_cases he : x = x₁
    · exact hiB x ⟨hx, fun he₂ => hne (he.symm.trans he₂)⟩
    · exact hiA x ⟨hx, he⟩
  have he := (hfirst _ (List.getElem_mem hi)).mp hiX
  have hpos := PathBasics.path_length_pos c.core.hp.1
  have h0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1 hpos
  exact c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans h0.symm)

/-- PAPER: "We claim that `Q` is odd. ... If some line has length 1,
... `z-pᵢ-x₁-Q-x₂-pᵢ₊₁-z` is an odd antihole, a contradiction."
In fact every pair of differently marked vertices after `p₁` is nonadjacent.
The two odd edge counts supply nonadjacent differently marked vertices first,
which fixes the parity of the antipath in `X`. -/
theorem cross_nonadjacent (G : SimpleGraph V) (hG : Berge G) (z : V)
    (c : Counterexample G z)
    (hfirst : ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁))
    (x₁ x₂ : V) (hx₁ : x₁ ∈ c.X) (hx₂ : x₂ ∈ c.X) (hne : x₁ ≠ x₂)
    (hodd₁ : Odd {e : Sym2 V | ∃ u ∈ c.core.p, ∃ v ∈ c.core.p,
      e = s(u, v) ∧ EdgeComplete G (c.X \ {x₁}) u v}.ncard)
    (hodd₂ : Odd {e : Sym2 V | ∃ u ∈ c.core.p, ∃ v ∈ c.core.p,
      e = s(u, v) ∧ EdgeComplete G (c.X \ {x₂}) u v}.ncard) :
    ∀ a b, 0 < a → 0 < b →
      ∀ (ha : a < c.core.p.length) (hb : b < c.core.p.length),
      Marked G (c.X \ {x₁}) c.core.p a →
      Marked G (c.X \ {x₂}) c.core.p b →
      ¬ G.Adj (c.core.p[a]'ha) (c.core.p[b]'hb) := by
  obtain ⟨Q, hQ, hQX⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected c.hXa hx₁ hx₂
  have hsep := marks_disjoint G c hfirst x₁ x₂ hne
  have hpos := PathBasics.path_length_pos c.core.hp.1
  have h0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1 hpos
  have hnotX (i : ℕ) (hi : i < c.core.p.length) (hip : 0 < i) :
      ¬ VertexComplete G (c.core.p[i]'hi) c.X := by
    intro hc
    have he := (hfirst _ (List.getElem_mem hi)).mp hc
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans h0.symm)
    omega
  have pair (a b : ℕ) (hap : 0 < a) (hbp : 0 < b)
      (ha : a < c.core.p.length) (hb : b < c.core.p.length)
      (haA : Marked G (c.X \ {x₁}) c.core.p a)
      (hbB : Marked G (c.X \ {x₂}) c.core.p b) :
      (¬ G.Adj (c.core.p[a]'ha) (c.core.p[b]'hb) → Odd (pathLength Q)) ∧
      (G.Adj (c.core.p[a]'ha) (c.core.p[b]'hb) → Even (pathLength Q)) := by
    have hab : a ≠ b := by
      rintro rfl
      have := hsep a haA hbB
      omega
    exact cross_pair_parity G hG c.X x₁ x₂ hne Q hQ hQX
      (c.core.p[a]'ha) (c.core.p[b]'hb) z
      (c.core.houtX _ (List.getElem_mem ha)) (c.core.houtX _ (List.getElem_mem hb))
      (fun he => hab (c.core.hp.1.2.1.getElem_inj_iff.mp he))
      haA.2 hbB.2
      (misses_deleted G c.X _ x₁ haA.2 (hnotX a ha hap))
      (misses_deleted G c.X _ x₂ hbB.2 (hnotX b hb hbp))
      (fun x hx => c.hzXY x (Or.inl hx))
      (c.core.hzanti _ (List.getElem_mem ha)) (c.core.hzanti _ (List.getElem_mem hb))
      (fun he => c.core.hzP (Eq.mpr (congrArg (fun w : V => w ∈ c.core.p) he)
        (List.getElem_mem ha)))
      (fun he => c.core.hzP (Eq.mpr (congrArg (fun w : V => w ∈ c.core.p) he)
        (List.getElem_mem hb)))
  obtain ⟨i, hiA, hiA'⟩ := exists_edge_index G (c.X \ {x₁}) c.core.p c.core.hp.1 hodd₁
  obtain ⟨j, hjB, hjB'⟩ := exists_edge_index G (c.X \ {x₂}) c.core.p c.core.hp.1 hodd₂
  have hnij : ¬ G.Adj (c.core.p[i + 1]'hiA'.1) (c.core.p[j + 1]'hjB'.1) := by
    intro hadj
    rcases (PathBasics.path_adj_iff c.core.hp.1 hiA'.1 hjB'.1).mp hadj with he | he
    · have hji : j = i + 1 := by omega
      have := hsep (i + 1) hiA' (hji ▸ hjB)
      omega
    · have hij : i = j + 1 := by omega
      have := hsep (j + 1) (hij ▸ hiA) hjB'
      omega
  have hQodd := (pair (i + 1) (j + 1) (by omega) (by omega) hiA'.1 hjB'.1 hiA' hjB').1 hnij
  intro a b hap hbp ha hb haA hbB hadj
  have hQeven := (pair a b hap hbp ha hb haA hbB).2 hadj
  exact (Nat.not_odd_iff_even.mpr hQeven) hQodd

end Workspace.ProofLemmas.Thm175Claim2Marks
