import Workspace.ProofLemmas.PathBasics

/-!
# The minimum-path inclusion in 23.2(5)

The path leading to the rim cannot be bypassed when only its last vertex can
meet the rim. This records the consequence of the minimum-length choice of
`T` made immediately before claim (4).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232Claim5PathPrefix

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} {G : SimpleGraph V}

/-- PAPER (23.2(5), printed p. 141): "Since none of `y,v₁,...,v_{n-1}`
have neighbours in `A₀` it follows that
`{y,v₁,...,v_n} ⊆ {y,p₁,...,p_{k-1}}`."

Here `F` is the initial path, including `z` but omitting its rim endpoint.
Its vertices lie outside `A`, and only its last vertex can have a neighbour
in `A`. Any path from its first vertex to `A` inside `F ∪ A` starts with `F`. -/
theorem initial_indices {F P : List V} {A : Set V} {z pn : V}
    (hF : IsPathList G F) (hhead : F.head? = some z)
    (hP : IsPathFrom G P z pn) (hpn : pn ∈ A)
    (hdisj : ∀ v ∈ F, v ∉ A)
    (hallowed : ∀ v ∈ P, v ∈ F ∨ v ∈ A)
    (hattach : ∀ (i : ℕ) (hi : i + 1 < F.length),
      VertexAnticomplete G (F[i]'(by omega)) A) :
    ∀ (i : ℕ) (hi : i < F.length),
      ∃ hiP : i < P.length, P[i]'hiP = F[i]'hi := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi
      have hPpos := path_length_pos hP.1
      by_cases hi0 : i = 0
      · subst i
        exact ⟨hPpos, (getElem_zero_of_head? hP.2.1 hPpos).trans
          (getElem_zero_of_head? hhead hi).symm⟩
      have hp : i - 1 < F.length := by omega
      obtain ⟨hpP, he⟩ := ih (i - 1) (by omega) hp
      have hiP : i < P.length := by
        by_contra hnot
        have hidx : i - 1 = P.length - 1 := by omega
        have hlast : P[i - 1]'hpP = pn := by
          calc
            P[i - 1]'hpP = P[P.length - 1]'(by omega) :=
              hP.1.2.1.getElem_inj_iff.mpr hidx
            _ = pn := getElem_last_of_getLast? hP.2.2 hPpos
        exact hdisj _ (List.getElem_mem hp) (he ▸ hlast ▸ hpn)
      refine ⟨hiP, ?_⟩
      have hadj : G.Adj (F[i - 1]'hp) (P[i]'hiP) := by
        have ha := path_adj_succ hP.1 (i := i - 1) (by omega)
        have hsucc : P[i - 1 + 1]'(by omega) = P[i]'hiP :=
          hP.1.2.1.getElem_inj_iff.mpr (by omega)
        rwa [he, hsucc] at ha
      rcases hallowed _ (List.getElem_mem hiP) with hvF | hvA
      · obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hvF
        have hjadj := (path_adj_iff hF hp hj).mp (by rwa [hjv])
        rcases hjadj with hjnext | hjprev
        · have hji : j = i := by omega
          exact hjv.symm.trans (hF.2.1.getElem_inj_iff.mpr hji)
        · have hji : j < i := by omega
          obtain ⟨hjP, hjPval⟩ := ih j hji hj
          have hdup : P[j]'hjP = P[i]'hiP := hjPval.trans hjv
          have := hP.1.2.1.getElem_inj_iff.mp hdup
          omega
      · exact (hattach (i - 1) (by omega) _ hvA hadj).elim

/-- The vertex inclusion from the same sentence, without introducing indices
at its call sites. -/
theorem initial_subset {F P : List V} {A : Set V} {z pn : V}
    (hF : IsPathList G F) (hhead : F.head? = some z)
    (hP : IsPathFrom G P z pn) (hpn : pn ∈ A)
    (hdisj : ∀ v ∈ F, v ∉ A)
    (hallowed : ∀ v ∈ P, v ∈ F ∨ v ∈ A)
    (hattach : ∀ (i : ℕ) (hi : i + 1 < F.length),
      VertexAnticomplete G (F[i]'(by omega)) A) :
    ∀ v ∈ F, v ∈ P := by
  intro v hv
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
  obtain ⟨hiP, he⟩ := initial_indices hF hhead hP hpn hdisj hallowed hattach i hi
  exact he.trans hiv ▸ List.getElem_mem hiP

end Workspace.ProofLemmas.Thm232Claim5PathPrefix
