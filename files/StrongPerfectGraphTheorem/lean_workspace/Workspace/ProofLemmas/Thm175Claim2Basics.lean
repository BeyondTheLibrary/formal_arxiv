import Workspace.ProofLemmas.Thm175Optimal
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathAttach

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim2Basics

open Workspace.Types.Core.SPGT Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Minimal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The indexed set of complete vertices used as `Wᵢ` in claim (2). -/
def Marked (G : SimpleGraph V) (X : Set V) (p : List V) (i : ℕ) : Prop :=
  ∃ hi : i < p.length, VertexComplete G (p[i]'hi) X

/-- PAPER: "Let us say a line is a minimal subpath of `P \ p₁` meeting
both `W₁` and `W₂`." Indices are zero-based. -/
def Line (A B : ℕ → Prop) (a b : ℕ) : Prop :=
  0 < a ∧ a < b ∧ ((A a ∧ B b) ∨ (B a ∧ A b)) ∧
    ∀ i, a < i → i < b → ¬ A i ∧ ¬ B i

/-- A path with just one complete vertex has no complete edge. -/
theorem edges_empty_of_unique (G : SimpleGraph V) (X : Set V) (p : List V)
    (a : V) (h : ∀ w ∈ p, VertexComplete G w X → w = a) :
    {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p, e = s(u, v) ∧ EdgeComplete G X u v} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro e ⟨u, hu, v, hv, _, hadj, huc, hvc⟩
  rw [h u hu huc, h v hv hvc] at hadj
  exact G.irrefl hadj

/-- PAPER: "The triple `L, X \ {x₁}, X \ {x₂}` is another
counterexample ... contrary to the optimality of `P,X,Y`."
The same construction applies to the final suffix in the proof. -/
theorem shorter_unique_not_odd (G : SimpleGraph V) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (A B : Set V) (hA : AnticonnectedSet G A) (hB : AnticonnectedSet G B)
    (hAB : AnticonnectedSet G (A ∪ B))
    (p : List V) (a b : V) (hp : IsPathFrom G p a b)
    (hlen : 1 < pathLength p) (hshort : p.length < c.core.p.length)
    (houtA : ∀ w ∈ p, w ∉ A) (houtB : ∀ w ∈ p, w ∉ B)
    (ha : VertexComplete G a A)
    (huniqA : ∀ w ∈ p, VertexComplete G w A → w = a)
    (huniqB : ∀ w ∈ p, VertexComplete G w B ↔ w = b)
    (hz : z ∉ A ∪ B) (hzcomp : VertexComplete G z (A ∪ B))
    (hzp : z ∉ p) (hzanti : VertexAnticomplete G z {w | w ∈ p}) :
    ¬ Odd (pathLength p) := by
  intro hodd
  apply hopt.1
    { X := A, Y := B, hXa := hA, hYa := hB, hXYa := hAB, hz := hz, hzXY := hzcomp
      core := { p := p, p₁ := a, pₙ := b, hp := hp, hodd := hodd, hlong := hlen
                houtX := houtA, houtY := houtB, hp₁X := ha, hYuniq := huniqB
                hzP := hzp, hzanti := hzanti
                heven := by rw [edges_empty_of_unique G A p a huniqA]; simp } }
  exact hshort

/-- PAPER: "But this path has length at least 2, and `z` has no
neighbour in it, so by 2.2 it is even." This form applies to every interval
with complete ends and no complete internal vertex. -/
theorem clean_interval_even (G : SimpleGraph V) (hG : Berge G) (X : Set V)
    (hX : AnticonnectedSet G X) (p : List V) (hp : IsPathList G p)
    (hout : ∀ w ∈ p, w ∉ X) (z : V) (hzX : VertexComplete G z X)
    (hzanti : VertexAnticomplete G z {w | w ∈ p})
    (i j : ℕ) (hij : i + 1 < j) (hj : j < p.length)
    (hiX : Marked G X p i) (hjX : Marked G X p j)
    (hclean : ∀ k, i < k → k < j → ¬ Marked G X p k) :
    Even (j - i) := by
  have hi : i < p.length := by omega
  let q := (p.drop i).take (j - i + 1)
  have hq := PathBasics.isPathFrom_slice hp (show i < j by omega) hj
  have hlen : pathLength q = j - i := by
    rw [pathLength, PathBasics.length_slice p (by omega) hj]
    omega
  have hmem : ∀ w ∈ q, ∃ k, ∃ hk : k < p.length, i ≤ k ∧ k ≤ j ∧ p[k]'hk = w := by
    intro w hw
    exact (PathBasics.mem_slice_iff p (by omega) hj).mp hw
  have hends : ∀ w ∈ q, VertexComplete G w X → w = p[i]'hi ∨ w = p[j]'hj := by
    intro w hw hc
    obtain ⟨k, hk, hki, hkj, rfl⟩ := hmem w hw
    have he : k = i ∨ k = j := by
      by_contra hn
      push Not at hn
      exact hclean k (by omega) (by omega) ⟨hk, hc⟩
    rcases he with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hnoedge : ¬ ∃ u ∈ q, ∃ v ∈ q, EdgeComplete G X u v := by
    rintro ⟨u, hu, v, hv, hadj, huc, hvc⟩
    rcases hends u hu huc with rfl | rfl <;>
      rcases hends v hv hvc with rfl | rfl
    · exact G.irrefl hadj
    · have := (PathBasics.path_adj_iff hp hi hj).mp hadj
      omega
    · have := (PathBasics.path_adj_iff hp hj hi).mp hadj
      omega
    · exact G.irrefl hadj
  apply Nat.not_odd_iff_even.mp
  intro hodd
  obtain ⟨w, hw, hzw⟩ := Workspace.Statements.S02.SPGT.thm_2_2 G hG X hX q
    (p[i]'hi) (p[j]'hj) hq
    (fun w hw => hout w (List.drop_subset _ _ (List.take_subset _ _ hw)))
    (by rwa [hlen]) hiX.2 hjX.2 hnoedge z hzX
  exact hzanti w (List.drop_subset _ _ (List.take_subset _ _ (PathBasics.interior_subset hw))) hzw

/-- A positive complete-edge count supplies an indexed complete edge. -/
theorem exists_edge_index (G : SimpleGraph V) (X : Set V) (p : List V)
    (hp : IsPathList G p)
    (hodd : Odd {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
      e = s(u, v) ∧ EdgeComplete G X u v}.ncard) :
    ∃ i, Marked G X p i ∧ Marked G X p (i + 1) := by
  have hpos : 0 < {e : Sym2 V | ∃ u ∈ p, ∃ v ∈ p,
      e = s(u, v) ∧ EdgeComplete G X u v}.ncard := by
    rw [Nat.odd_iff] at hodd
    omega
  obtain ⟨e, u, hu, v, hv, _, hadj, huc, hvc⟩ :=
    (Set.ncard_pos (Set.toFinite _)).mp hpos
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
  rcases (PathBasics.path_adj_iff hp hi hj).mp hadj with he | he
  · subst j
    exact ⟨i, ⟨hi, huc⟩, ⟨hj, hvc⟩⟩
  · subst i
    exact ⟨j, ⟨hj, hvc⟩, ⟨hi, huc⟩⟩

end Workspace.ProofLemmas.Thm175Claim2Basics
