import Workspace.ProofLemmas.Thm175Claim2Marks
import Workspace.ProofLemmas.Thm175Claim2Slices
import Workspace.ProofLemmas.Thm175Claim2Order

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim2Main

open Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim2Basics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "So we may assume that `(X \ {xᵢ}) ∪ Y` is anticonnected
for `i = 1,2`. ... This proves (2)."
Both deleted sides have odd complete-edge counts. The antihole argument
excludes one-edge lines, and optimality excludes longer odd lines. The
complete-interval and suffix parity rules then give the index contradiction. -/
theorem line_argument_absurd (G : SimpleGraph V) (hG : InF7 G) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (hfirst : ∀ w ∈ c.core.p, (VertexComplete G w c.X ↔ w = c.core.p₁))
    (x₁ x₂ : V) (hx₁ : x₁ ∈ c.X) (hx₂ : x₂ ∈ c.X) (hne : x₁ ≠ x₂)
    (hdel₁ : AnticonnectedSet G (c.X \ {x₁}))
    (hdel₂ : AnticonnectedSet G (c.X \ {x₂}))
    (hunion₁ : AnticonnectedSet G ((c.X \ {x₁}) ∪ c.Y))
    (hunion₂ : AnticonnectedSet G ((c.X \ {x₂}) ∪ c.Y))
    (hodd₁ : Odd {e : Sym2 V | ∃ u ∈ c.core.p, ∃ v ∈ c.core.p,
      e = s(u, v) ∧ EdgeComplete G (c.X \ {x₁}) u v}.ncard)
    (hodd₂ : Odd {e : Sym2 V | ∃ u ∈ c.core.p, ∃ v ∈ c.core.p,
      e = s(u, v) ∧ EdgeComplete G (c.X \ {x₂}) u v}.ncard) : False := by
  let A := c.X \ {x₁}
  let B := c.X \ {x₂}
  let W₁ := Marked G A c.core.p
  let W₂ := Marked G B c.core.p
  have hBerge : Berge G := hG.1.1.1.1
  have hpos := PathBasics.path_length_pos c.core.hp.1
  have h0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1 hpos
  have hW₁0 : W₁ 0 := by
    refine ⟨hpos, ?_⟩
    rw [h0]
    exact fun w hw => c.core.hp₁X w hw.1
  have hW₂0 : W₂ 0 := by
    refine ⟨hpos, ?_⟩
    rw [h0]
    exact fun w hw => c.core.hp₁X w hw.1
  have hsep : ∀ i, W₁ i → W₂ i → i = 0 :=
    Thm175Claim2Marks.marks_disjoint G c hfirst x₁ x₂ hne
  have hnonadj := Thm175Claim2Marks.cross_nonadjacent G hBerge z c hfirst
    x₁ x₂ hx₁ hx₂ hne hodd₁ hodd₂
  have hABeq : A ∪ B = c.X := by
    apply Set.Subset.antisymm
    · rintro w (h | h) <;> exact h.1
    · intro w hw
      by_cases he : w = x₁
      · exact Or.inr ⟨hw, fun he₂ => hne (he.symm.trans he₂)⟩
      · exact Or.inl ⟨hw, he⟩
  have hAB : AnticonnectedSet G (A ∪ B) := by rw [hABeq]; exact c.hXa
  have hBA : AnticonnectedSet G (B ∪ A) := by simpa [Set.union_comm] using hAB
  have hAsub : A ⊆ c.X ∪ c.Y := fun _ hw => Or.inl hw.1
  have hBsub : B ⊆ c.X ∪ c.Y := fun _ hw => Or.inl hw.1
  have hlines : ∀ a b, Line W₁ W₂ a b → Even (b - a) := by
    intro a b hl
    have ha := hl.1
    have hab := hl.2.1
    rcases hl.2.2.1 with h | h
    · exact Thm175Claim2Slices.oriented_line_even G z c hopt A B hdel₁ hdel₂
        hAB hAsub hBsub hsep a b hl h.1 h.2
        (hnonadj a b ha (by omega) h.1.1 h.2.1 h.1 h.2)
    · exact Thm175Claim2Slices.oriented_line_even G z c hopt B A hdel₂ hdel₁
        hBA hBsub hAsub (fun i hiB hiA => hsep i hiA hiB) a b
        (Thm175Claim2Order.line_swap hl) h.1 h.2
        (fun hadj => hnonadj b a (by omega) ha h.2.1 h.1.1 h.2 h.1 hadj.symm)
  obtain ⟨i, _, hi⟩ := exists_edge_index G A c.core.p c.core.hp.1 hodd₁
  obtain ⟨j, _, hj⟩ := exists_edge_index G B c.core.p c.core.hp.1 hodd₂
  apply Thm175Claim2Order.even_lines_absurd W₁ W₂ (pathLength c.core.p)
    c.core.hodd hW₁0 hW₂0
    (fun k hk => by
      have hkl : k < c.core.p.length := hk.elim (fun h => h.1) (fun h => h.1)
      simp only [pathLength]
      omega)
    hsep ⟨i + 1, by omega, hi⟩ ⟨j + 1, by omega, hj⟩
  · intro a b hab ha hb hclean
    exact clean_interval_even G hBerge A hdel₁ c.core.p c.core.hp.1
      (fun w hw hA => c.core.houtX w hw hA.1) z
      (fun w hw => c.hzXY w (Or.inl hw.1)) c.core.hzanti
      a b hab hb.1 ha hb hclean
  · intro a b hab ha hb hclean
    exact clean_interval_even G hBerge B hdel₂ c.core.p c.core.hp.1
      (fun w hw hB => c.core.houtX w hw hB.1) z
      (fun w hw => c.hzXY w (Or.inl hw.1)) c.core.hzanti
      a b hab hb.1 ha hb hclean
  · exact Thm175Claim2Slices.tail_even G z c hopt A hdel₁ hunion₁ (fun _ h => h.1)
  · exact Thm175Claim2Slices.tail_even G z c hopt B hdel₂ hunion₂ (fun _ h => h.1)
  · exact hlines

end Workspace.ProofLemmas.Thm175Claim2Main
