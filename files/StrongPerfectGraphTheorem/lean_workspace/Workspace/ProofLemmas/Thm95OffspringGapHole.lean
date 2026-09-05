import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm114Aux
import Workspace.ProofLemmas.Thm95OffspringDefs

/-!
# The odd hole `d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁`

PAPER (9.5(1), printed p. 52): *"Suppose there is such a nonedge; and choose `Tⱼ`-antirungs
`xⱼ-Qⱼ-yⱼ`, `x'ⱼ-Q'ⱼ-y'ⱼ` where `xⱼ ∈ U` is nonadjacent to `x'ⱼ ∈ V`, say.  Now `xⱼ, x'ⱼ` have
a common neighbour `d₁ ∈ A₁ ∪ B₁`, and then `d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁` is an odd hole."*

The cycle has `k + 3` vertices, and `k` is even because `f₁-⋯-f_k` has odd length, so it is odd.
Only five facts are used: `p` sees `f₁` and not `f_k`, `q` sees `f_k` and not `f₁`, neither sees
the interior of the path, `pq` is a nonedge, and the common neighbour `d` sees no vertex of the
path (it lies on a strip of the striation, and `F` is anticomplete to every strip).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringGapHole

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(1), p. 52):** the odd hole `d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁`.  Here `p` is `xⱼ`, `q` is
`x'ⱼ` and `d` is `d₁`. -/
theorem no_nonedge_with_common_neighbour {G : SimpleGraph V} (hG : Berge G)
    {R : List V} {r s : V} (hR : IsPathFrom G R r s) (hodd : Odd (pathLength R))
    {p q d : V}
    (hrp : G.Adj r p) (hsp : ¬ G.Adj s p)
    (hsq : G.Adj s q) (hrq : ¬ G.Adj r q)
    (hpq : ¬ G.Adj p q)
    (hdp : G.Adj d p) (hdq : G.Adj d q)
    (hpR : p ∉ R) (hqR : q ∉ R) (hdR : d ∉ R)
    (hpint : ∀ w ∈ SPGT.interior R, ¬ G.Adj p w)
    (hqint : ∀ w ∈ SPGT.interior R, ¬ G.Adj q w)
    (hdnone : ∀ w ∈ R, ¬ G.Adj d w) : False := by
  classical
  have hsplit : ∀ w ∈ R, w = r ∨ w = s ∨ w ∈ SPGT.interior R := by
    intro w hw
    by_cases h1 : w = r
    · exact Or.inl h1
    by_cases h2 : w = s
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hw, h1, h2⟩))
  have hpqne : p ≠ q := by rintro rfl; exact hrq hrp
  have hdpne : d ≠ p := fun h => G.irrefl (h ▸ hdp)
  have hdqne : d ≠ q := fun h => G.irrefl (h ▸ hdq)
  have hpathq : IsPathFrom G [q, d, p] q p := by
    refine ⟨Thm114Aux.isPathList_three ?_ hdq.symm hdp (fun h => hpq h.symm), rfl, rfl⟩
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil,
      or_false, not_or, and_true]
    exact ⟨⟨Ne.symm hdqne, Ne.symm hpqne⟩, hdpne, not_false⟩
  have hdisj : ∀ w ∈ R, w ∉ [q, d, p] := by
    intro w hw hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hqR hw
    · exact hdR hw
    · exact hpR hw
  have hcross : ∀ w ∈ R, ∀ z ∈ [q, d, p],
      (G.Adj w z ↔ (w = s ∧ z = q) ∨ (w = r ∧ z = p)) := by
    intro w hw z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl
    · constructor
      · intro hadj
        rcases hsplit w hw with rfl | rfl | h
        · exact absurd hadj hrq
        · exact Or.inl ⟨rfl, rfl⟩
        · exact absurd hadj.symm (hqint w h)
      · rintro (⟨rfl, -⟩ | ⟨-, h⟩)
        · exact hsq
        · exact absurd h.symm hpqne
    · constructor
      · intro hadj; exact absurd hadj.symm (hdnone w hw)
      · rintro (⟨-, h⟩ | ⟨-, h⟩)
        · exact absurd h hdqne
        · exact absurd h hdpne
    · constructor
      · intro hadj
        rcases hsplit w hw with rfl | rfl | h
        · exact Or.inr ⟨rfl, rfl⟩
        · exact absurd hadj hsp
        · exact absurd hadj.symm (hpint w h)
      · rintro (⟨-, h⟩ | ⟨rfl, -⟩)
        · exact absurd h hpqne
        · exact hrp
  have hlen : 4 ≤ R.length + [q, d, p].length := by
    have := PathBasics.path_length_pos hR.1
    simp only [List.length_cons, List.length_nil]
    omega
  have hhole : IsHoleList G (R ++ [q, d, p]) :=
    PathGlue.glue_hole hR hpathq hdisj hcross hlen
  have heven := hG.1 _ hhole
  rw [holeLength, List.length_append] at heven
  simp only [List.length_cons, List.length_nil] at heven
  have hRlen : R.length = pathLength R + 1 := PathBasics.length_eq_pathLength_add_one hR.1
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff] at hodd
  omega

end Workspace.ProofLemmas.Thm95OffspringGapHole
