import Workspace.ProofLemmas.Thm75Claim1
import Workspace.ProofLemmas.Thm75DominanceTriangles
import Workspace.Statements.S07.Thm_7_4

/-!
# Dominance under the replacements in 7.5 claim (2)

PAPER (printed p. 37): *"these two prisms are related as in 7.4"*, and *"The same argument in
the reverse direction shows that Y remains a maximal anticonnected set"*.

The prism data is kept separate from its consequence for dominance. This also handles a
clique of size three: after removing its rung end, only two vertices remain.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm75Claim2Five82Dominance

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-- PAPER: *"There also correspond three tracks in H', yielding a prism in L(H'). ... these
two prisms are related as in 7.4."* The changed triangle vertex is `t`, replaced by `t'`. -/
def SwapPrisms {V : Type*} (G : SimpleGraph V) (N M : Set V) (t t' anchor : V) : Prop :=
  ∀ x ∈ N \ {t}, ∀ z ∈ N \ {t}, x ≠ z → (t = anchor ∨ x = anchor ∨ z = anchor) →
    ∃ (b : Fin 3 → V) (P₁ P₂ P₃ P₁' : List V),
      b 0 ∈ M ∧ b 1 ∈ M ∧ b 2 ∈ M ∧ b 0 ≠ b 1 ∧ b 0 ≠ b 2 ∧ b 1 ≠ b 2 ∧
      FormPrism G ![t, x, z] b P₁ P₂ P₃ ∧
      Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃) ∧
      2 ≤ pathLength P₁ ∧ 2 ≤ pathLength P₂ ∧ 2 ≤ pathLength P₃ ∧
      IsPathFrom G P₁' t' (b 0) ∧ FormPrism G ![t', x, z] b P₁' P₂ P₃

/-- One changed endpoint clique, with prism witnesses in both directions. -/
def SingleCliqueSwap {V : Type*} (G : SimpleGraph V) (N M N' : Set V) : Prop :=
  ∃ t t' a a', t ∈ N ∧ t' ∈ N' ∧ a ∈ N ∧ a' ∈ N' ∧
    N' = (N \ {t}) ∪ {t'} ∧ N = (N' \ {t'}) ∪ {t} ∧
    SwapPrisms G N M t t' a ∧ SwapPrisms G N' M t' t a'

/-- The replacement changes at most one of the two distinguished cliques. The last
alternative reverses the names of the distinguished ends. -/
def OneCliqueReplacement {V : Type*} (G : SimpleGraph V) (N₁ N₂ N₁' N₂' : Set V) : Prop :=
  (N₁' = N₁ ∧ N₂' = N₂) ∨
    (N₂' = N₂ ∧ SingleCliqueSwap G N₁ N₂ N₁') ∨
    (N₁' = N₁ ∧ SingleCliqueSwap G N₂ N₁ N₂')

/-- Apply 7.4 to exclude two missing neighbours in the new clique. -/
theorem subsingleton_after_swap {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (N M : Set V) (t t' y : V)
    (hN : 3 ≤ N.ncard) (hM : 3 ≤ M.ncard) (ht : t ∈ N)
    (anchor : V) (hanchor : anchor ∈ N)
    (hprisms : SwapPrisms G N M t t' anchor) (hy : IsDominantFor G N M y) :
    (((N \ {t}) ∪ {t'}) \ G.neighborSet y).Subsingleton := by
  classical
  have htriN := (Thm75DominanceTriangles.subsingleton_diff_iff_triangles hN).mp hy.1
  have htriM := (Thm75DominanceTriangles.subsingleton_diff_iff_triangles hM).mp hy.2
  have key : ∀ x ∈ N \ {t}, ¬ G.Adj y x → G.Adj y t' := by
    intro x hx hnx
    obtain ⟨z, hzN, hz⟩ : (N \ ({t, x} : Set V)).Nonempty := by
      rw [Set.diff_nonempty]
      intro hsub
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      have hpair := Set.ncard_pair (Ne.symm hx.2)
      omega
    have hzt : z ≠ t := fun h => hz (Or.inl h)
    have hzx : z ≠ x := fun h => hz (Or.inr h)
    obtain ⟨w, hwN, hwt, hwx, ha⟩ : ∃ w ∈ N, w ≠ t ∧ w ≠ x ∧
        (t = anchor ∨ x = anchor ∨ w = anchor) := by
      by_cases hat : anchor = t
      · exact ⟨z, hzN, hzt, hzx, Or.inl hat.symm⟩
      by_cases hax : anchor = x
      · exact ⟨z, hzN, hzt, hzx, Or.inr (Or.inl hax.symm)⟩
      · exact ⟨anchor, hanchor, hat, hax, Or.inr (Or.inr rfl)⟩
    have hwrem : w ∈ N \ {t} := ⟨hwN, hwt⟩
    obtain ⟨b, P₁, P₂, P₃, P₁', hb0, hb1, hb2, hb01, hb02, hb12, hpr,
      he1, he2, he3, hl1, hl2, hl3, hP₁', hpr'⟩ := hprisms x hx w hwrem hwx.symm ha
    have hmajor : MajorForPrism G ![t, x, w] b y := by
      constructor
      · simpa using htriN t ht x hx.1 w hwN (Ne.symm hx.2) hwt.symm hwx.symm
      · simpa using htriM (b 0) hb0 (b 1) hb1 (b 2) hb2 hb01 hb02 hb12
    have htwo := Workspace.Statements.S07.SPGT.thm_7_4 G hG ![t, x, w] b
      P₁ P₂ P₃ hpr he1 he2 he3 hl1 hl2 hl3 t' P₁' hP₁' (by simpa using hpr') y hmajor
    by_contra hnt
    have hsub : ({t', x, w} : Set V) ∩ G.neighborSet y ⊆ {w} := by
      rintro v ⟨hv, hyv⟩
      rcases hv with rfl | rfl | rfl
      · exact (hnt hyv).elim
      · exact (hnx hyv).elim
      · rfl
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    simp only [Set.ncard_singleton] at hle
    have htwo' : 2 ≤ (({t', x, w} : Set V) ∩ G.neighborSet y).ncard := by
      simpa using htwo
    omega
  rintro x ⟨hx, hnx⟩ z ⟨hz, hnz⟩
  rcases hx with hx | rfl <;> rcases hz with hz | rfl
  · exact hy.1 ⟨hx.1, hnx⟩ ⟨hz.1, hnz⟩
  · exact (hnz (key x hx hnx)).elim
  · exact (hnx (key z hz hnz)).elim
  · rfl

/-- PAPER: *"The same argument in the reverse direction"*. -/
theorem dominant_iff_of_one_clique_replacement {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (N₁ N₂ N₁' N₂' : Set V)
    (h₁ : 3 ≤ N₁.ncard) (h₂ : 3 ≤ N₂.ncard)
    (h₁' : 3 ≤ N₁'.ncard) (h₂' : 3 ≤ N₂'.ncard)
    (hrep : OneCliqueReplacement G N₁ N₂ N₁' N₂') (y : V) :
    IsDominantFor G N₁ N₂ y ↔ IsDominantFor G N₁' N₂' y := by
  rcases hrep with ⟨he1, he2⟩ | ⟨he2, t, t', a, a', ht, ht', ha, ha', heq, heq', hf, hr⟩ |
      ⟨he1, t, t', a, a', ht, ht', ha, ha', heq, heq', hf, hr⟩
  · rw [he1, he2]
  · subst N₂'
    constructor
    · intro hy
      refine ⟨?_, hy.2⟩
      rw [heq]
      exact subsingleton_after_swap G hG N₁ N₂ t t' y h₁ h₂ ht a ha hf hy
    · intro hy
      refine ⟨?_, hy.2⟩
      rw [heq']
      exact subsingleton_after_swap G hG N₁' N₂ t' t y h₁' h₂ ht' a' ha' hr hy
  · subst N₁'
    constructor
    · intro hy
      refine ⟨hy.1, ?_⟩
      rw [heq]
      exact subsingleton_after_swap G hG N₂ N₁ t t' y h₂ h₁ ht a ha hf ⟨hy.2, hy.1⟩
    · intro hy
      refine ⟨hy.1, ?_⟩
      rw [heq']
      exact subsingleton_after_swap G hG N₂' N₁ t' t y h₂' h₁ ht' a' ha' hr ⟨hy.2, hy.1⟩

/-- All vertices of a clique except its named rung end are common neighbours of `Y`. -/
theorem dominant_of_complete_remainders {V : Type*} (G : SimpleGraph V)
    (N₁ N₂ Y : Set V) (r₁ r₂ : V)
    (h₁ : ∀ x ∈ N₁ \ {r₁}, VertexComplete G x Y)
    (h₂ : ∀ x ∈ N₂ \ {r₂}, VertexComplete G x Y) :
    ∀ y ∈ Y, IsDominantFor G N₁ N₂ y := by
  have side (N : Set V) (r : V) (h : ∀ x ∈ N \ {r}, VertexComplete G x Y)
      (y : V) (hy : y ∈ Y) : (N \ G.neighborSet y).Subsingleton := by
    have heq : ∀ x ∈ N \ G.neighborSet y, x = r := by
      rintro x ⟨hx, hnx⟩
      by_contra hxr
      exact hnx (h x ⟨hx, hxr⟩ y hy).symm
    intro x hx z hz
    exact (heq x hx).trans (heq z hz).symm
  exact fun y hy => ⟨side N₁ r₁ h₁ y hy, side N₂ r₂ h₂ y hy⟩

/-- PAPER (printed p. 38): *"Since r'₁, r'₂ are not in X, they are certainly not
Y'-complete ... every vertex of N'c₁ \\ {r'₁} and N'c₂ \\ {r'₂} are Y'-complete."*
This uses claim (1) for the new appearance. -/
theorem complete_remainder_of_missing_end {V : Type*} (G : SimpleGraph V)
    (N Y Y' : Set V) (r : V) (hYY' : Y ⊆ Y') (hrN : r ∈ N)
    (hr : ¬ VertexComplete G r Y)
    (hsmall : (N \ {x | VertexComplete G x Y'}).Subsingleton) :
    ∀ x ∈ N \ {r}, VertexComplete G x Y' := by
  intro x hx
  by_contra hxc
  have hrc : ¬ VertexComplete G r Y' := fun h => hr (fun y hy => h y (hYY' hy))
  exact hx.2 (hsmall ⟨hx.1, hxc⟩ ⟨hrN, hrc⟩)

end Workspace.ProofLemmas.Thm75Claim2Five82Dominance
