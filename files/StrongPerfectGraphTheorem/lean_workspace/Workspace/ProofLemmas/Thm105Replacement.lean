import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Statements.S07.Thm_7_2
import Workspace.Statements.S07.Thm_7_4
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.Thm105Setup

/-!
# Rung replacement for the proof of 10.5

This is the contradiction at the end of claim (1).  The path supplied by
10.3, followed by the old first rung, gives a new first rung.  Theorem 7.4
keeps every member of `Y` major, but the new triangle replaces the
`Y`-complete vertex `a 0` by the non-complete vertex `f₁`.  This contradicts
the opening minimal choice.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm105Replacement

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.Thm105Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The oriented rung-replacement contradiction.  Exchanging the two triangles
turns the second alternative of 10.3 into this one. -/
theorem replacement_contradiction_left (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (Y K : Set V)
    (hprism : IsEvenPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {x : V | x ∈ R 0} ∪ {x : V | x ∈ R 1} ∪ {x : V | x ∈ R 2})
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G a b y)
    (hmin : ∀ (a' b' : Fin 3 → V) (R' : Fin 3 → List V) (Y' : Set V),
      GoodChoice G a' b' R' Y' →
        triangleCompleteCount G a b Y ≤ triangleCompleteCount G a' b' Y')
    (ha₀complete : VertexComplete G (a 0) Y)
    (f : List V) (f₁ fₙ : V) (hf : IsPathFrom G f f₁ fₙ)
    (hfK : ∀ x ∈ f, x ∉ K) (hf₁not : ¬ VertexComplete G f₁ Y)
    (hf₁a₁ : G.Adj f₁ (a 1)) (hf₁a₂ : G.Adj f₁ (a 2))
    (hy : ∃ y ∈ R 0, y ≠ a 0 ∧ G.Adj fₙ y)
    (hother : ∀ x ∈ f, ∀ k ∈ K, k ≠ a 0 → G.Adj x k →
      (x = f₁ ∧ (k = a 1 ∨ k = a 2)) ∨ (x = fₙ ∧ k ∈ R 0)) : False := by
  classical
  have hform := hprism.1
  have hpath : ∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i) := fun i ↦
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hform i
  have hRmemK : ∀ i : Fin 3, ∀ x ∈ R i, x ∈ K := by
    intro i x hx
    rw [hK]
    fin_cases i
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hf₁mem : f₁ ∈ f := Workspace.ProofLemmas.PathBasics.head_mem hf.2.1
  have hfₙmem : fₙ ∈ f := Workspace.ProofLemmas.PathBasics.getLast_mem hf.2.2
  have htail : ∀ x : V, x ∈ (R 0).tail ↔ x ∈ R 0 ∧ x ≠ a 0 := by
    intro x
    exact Workspace.ProofLemmas.HyperprismRungStructure.mem_tail_iff_of_pathFrom (hpath 0)
  obtain ⟨y, hyR, hya₀, hfₙy⟩ := hy
  have hyTail : y ∈ (R 0).tail := htail y |>.2 ⟨hyR, hya₀⟩
  have hb₀Tail : b 0 ∈ (R 0).tail := htail (b 0) |>.2
    ⟨Workspace.ProofLemmas.PathBasics.getLast_mem (hpath 0).2.2,
      (hform.2.2.1 0 0).symm⟩
  have hfconn : ConnectedSet G {x : V | x ∈ f} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hf.1
  have htailPath : IsPathList G (R 0).tail :=
    Workspace.ProofLemmas.HyperprismRungStructure.isPathList_tail (hpath 0).1
      (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hform 0)
  have htailconn : ConnectedSet G {x : V | x ∈ (R 0).tail} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htailPath
  have hunionconn : ConnectedSet G ({x : V | x ∈ f} ∪ {x : V | x ∈ (R 0).tail}) := by
    apply Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hfconn htailconn
    exact Or.inr ⟨fₙ, hfₙmem, y, hyTail, hfₙy⟩
  obtain ⟨R', hR', hR'sub⟩ :=
    Workspace.ProofLemmas.InducedPathExtraction.exists_isPathFrom_of_connected
      hunionconn (Or.inl hf₁mem) (Or.inr hb₀Tail)
  have hcrossNew : ∀ (j : Fin 3), j ≠ 0 → G.Adj f₁ (a j) →
      ∀ u ∈ R', ∀ v ∈ R j,
        (G.Adj u v ↔ (u = f₁ ∧ v = a j) ∨ (u = b 0 ∧ v = b j)) := by
    intro j hj0 hf₁aj u hu v hv
    have hvK : v ∈ K := hRmemK j v hv
    have hva₀ : v ≠ a 0 := by
      intro hva
      exact Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform hj0.symm
        v (hva ▸ Workspace.ProofLemmas.PathBasics.head_mem (hpath 0).2.1) hv
    rcases hR'sub u hu with huF | huTail
    · constructor
      · intro huv
        rcases hother u huF v hvK hva₀ huv with ⟨huf, hva⟩ | ⟨hufn, hvR₀⟩
        · have hvaj : v = a j := by
            rcases hva with hva₁ | hva₂
            · fin_cases j
              · exact False.elim (hj0 rfl)
              · exact hva₁
              · exact False.elim
                  (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
                    (i := 1) (j := 2) (by decide) v (hva₁ ▸
                      Workspace.ProofLemmas.PathBasics.head_mem (hpath 1).2.1) hv)
            · fin_cases j
              · exact False.elim (hj0 rfl)
              · exact False.elim
                  (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform
                    (i := 2) (j := 1) (by decide) v (hva₂ ▸
                      Workspace.ProofLemmas.PathBasics.head_mem (hpath 2).2.1) hv)
              · exact hva₂
          exact Or.inl ⟨huf, hvaj⟩
        · exact False.elim
            (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hform hj0.symm
              v hvR₀ hv)
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · exact hf₁aj
        · exact hform.2.1 0 j hj0.symm
    · have huR₀ := (htail u).1 huTail
      constructor
      · intro huv
        rcases (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform hj0.symm
          u huR₀.1 v hv).mp huv with h | h
        · exact False.elim (huR₀.2 h.1)
        · exact Or.inr h
      · rintro (⟨huf, hvaj⟩ | ⟨hub, hvbj⟩)
        · exact False.elim (hfK f₁ hf₁mem (huf.symm ▸ hRmemK 0 u huR₀.1))
        · exact (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hform hj0.symm
            u huR₀.1 v hv).mpr (Or.inr ⟨hub, hvbj⟩)
  have hf₁neB : ∀ j : Fin 3, f₁ ≠ b j := by
    intro j h
    exact hfK f₁ hf₁mem (h ▸ hRmemK j (b j)
      (Workspace.ProofLemmas.PathBasics.getLast_mem (hpath j).2.2))
  have hnewForm : FormPrism G ![f₁, a 1, a 2] b R' (R 1) (R 2) := by
    have hbVec : ![b 0, b 1, b 2] = b := by
      funext i
      fin_cases i <;> rfl
    rw [← hbVec]
    apply Workspace.ProofLemmas.PrismBasics.formPrism_of_data
    · exact hf₁a₁
    · exact hf₁a₂
    · exact hform.1 1 2 (by decide)
    · exact hform.2.1 0 1 (by decide)
    · exact hform.2.1 0 2 (by decide)
    · exact hform.2.1 1 2 (by decide)
    · exact hf₁neB 0
    · exact hf₁neB 1
    · exact hf₁neB 2
    · exact hform.2.2.1 1 0
    · exact hform.2.2.1 1 1
    · exact hform.2.2.1 1 2
    · exact hform.2.2.1 2 0
    · exact hform.2.2.1 2 1
    · exact hform.2.2.1 2 2
    · exact hR'
    · exact hpath 1
    · exact hpath 2
    · exact hcrossNew 1 (by decide) hf₁a₁
    · exact hcrossNew 2 (by decide) hf₁a₂
    · exact hform.2.2.2.2.2.2.2.2
  have hnewEven₀ : Even (pathLength R') :=
    (Workspace.Statements.S07.SPGT.thm_7_2 G hG ![f₁, a 1, a 2] b R' (R 1) (R 2)
      hnewForm).1.mpr hprism.2.2.1
  have hnewPrism : IsEvenPrism G ![f₁, a 1, a 2] b R' (R 1) (R 2) :=
    ⟨hnewForm, hnewEven₀, hprism.2.2.1, hprism.2.2.2⟩
  have hlen : ∀ i : Fin 3, 2 ≤ pathLength (R i) := by
    intro i
    have hlist := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hform i
    have hpos : 1 ≤ pathLength (R i) := by simp only [pathLength]; omega
    have hev : Even (pathLength (R i)) := by
      fin_cases i
      exacts [hprism.2.1, hprism.2.2.1, hprism.2.2.2]
    obtain ⟨m, hm⟩ := hev
    omega
  have hnewMajor : ∀ y ∈ Y, MajorForPrism G ![f₁, a 1, a 2] b y := by
    intro z hz
    have hfirst := Workspace.Statements.S07.SPGT.thm_7_4 G hG a b (R 0) (R 1) (R 2)
      hform hprism.2.1 hprism.2.2.1 hprism.2.2.2 (hlen 0) (hlen 1) (hlen 2)
      f₁ R' hR' hnewForm z (hYmajor z hz)
    exact ⟨hfirst, (hYmajor z hz).2⟩
  have hnewGood : GoodChoice G ![f₁, a 1, a 2] b ![R', R 1, R 2] Y := by
    exact ⟨hnewPrism, hYne, hYanti, hnewMajor⟩
  have hle := hmin ![f₁, a 1, a 2] b ![R', R 1, R 2] Y hnewGood
  have haVec : ![a 0, a 1, a 2] = a := by
    funext i
    fin_cases i <;> rfl
  have hdrop := triangleCompleteCount_replace_left G (a 0) (a 1) (a 2) f₁ b Y
    ha₀complete hf₁not (hform.1 0 1 (by decide)).ne (hform.1 0 2 (by decide)).ne
  rw [haVec] at hdrop
  omega

end Workspace.ProofLemmas.Thm105Replacement
