import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue

/-!
# The minimum-length choice of `T` in 23.2

PAPER (23.2, printed p. 140), immediately before claim (4):

> *"Let `T` have vertices `z-y-v₁-⋯-v_{n+1}`, where `v_{n+1} ∈ A₀`.  From (3), `n ≥ 1`.  By
> choosing `T` of minimum length we may assume that none of `y, v₁, …, v_{n−1}` have
> neighbours in `A₀`."*

`exists_min_clean_path` makes that choice.  A path from `z` to `A` whose interior avoids the
two forbidden vertices and the hub can always be shortened at the first vertex with a
neighbour in `A`: truncating it there and appending that neighbour gives a shorter path with
the same properties, because by the choice of that first vertex no earlier vertex of the path
sees `A`, so the truncation stays induced.

The conclusion says that every vertex of the chosen path except the last two is anticomplete
to `A`; the last two are the paper's `v_n` (which is adjacent to `v_{n+1}`) and `v_{n+1}`
itself.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm232MinPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **PAPER (23.2, printed p. 140):** *"By choosing `T` of minimum length we may assume that
none of `y, v₁, …, v_{n−1}` have neighbours in `A₀`."* -/
theorem exists_min_clean_path (Y A F : Set V) (z : V) (hzA : z ∉ A) (hAF : ∀ a ∈ A, a ∉ F)
    (T : List V) (w : V) (hT2 : 2 ≤ T.length)
    (hpath : IsPathFrom G T z w) (hwA : w ∈ A)
    (havoid : ∀ v ∈ T, v ∉ F)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y) :
    ∃ (S : List V) (v : V),
      2 ≤ S.length ∧ IsPathFrom G S z v ∧ v ∈ A ∧
      (∀ u ∈ S, u ∉ F) ∧
      (∀ u ∈ SPGT.interior S, u ∉ Y ∧ ¬ VertexComplete G u Y) ∧
      (∀ (i : ℕ) (hi : i + 2 < S.length),
        VertexAnticomplete G (S[i]'(by omega)) A) := by
  classical
  let Good : List V → Prop := fun S =>
    (∃ v, IsPathFrom G S z v ∧ v ∈ A) ∧ 2 ≤ S.length ∧ (∀ u ∈ S, u ∉ F) ∧
      (∀ u ∈ SPGT.interior S, u ∉ Y ∧ ¬ VertexComplete G u Y)
  have hex : ∃ n : ℕ, ∃ S : List V, Good S ∧ S.length = n :=
    ⟨T.length, T, ⟨⟨w, hpath, hwA⟩, hT2, havoid, hint⟩, rfl⟩
  obtain ⟨S, hS, hSlen⟩ := Nat.find_spec hex
  have hmin : ∀ S' : List V, Good S' → S.length ≤ S'.length := by
    intro S' hS'
    rw [hSlen]
    exact Nat.find_min' hex ⟨S', hS', rfl⟩
  obtain ⟨⟨v, hSpath, hvA⟩, hS2, hSF, hSint⟩ := hS
  refine ⟨S, v, hS2, hSpath, hvA, hSF, hSint, ?_⟩
  have hS0 : S[0]'(by omega) = z := getElem_zero_of_head? hSpath.2.1 (by omega)
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
      intro hi a haA hadj
      have hi1 : i + 1 < S.length := by omega
      -- the truncation `z-S-S[i]` of `S`
      have htake : IsPathFrom G (S.take (i + 1)) z (S[i]'(by omega)) := by
        refine ⟨isPathList_take hSpath.1 (by omega), ?_, ?_⟩
        · rw [List.head?_take, if_neg (by omega)]
          exact hSpath.2.1
        · rw [List.getLast?_take, if_neg (by omega)]
          simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem (show i < S.length by omega),
            Option.some_or]
      have htakelen : (S.take (i + 1)).length = i + 1 := by
        simp only [List.length_take]; omega
      have hmemtake : ∀ u ∈ S.take (i + 1), ∃ j, ∃ hj : j < S.length, j ≤ i ∧ S[j]'hj = u := by
        intro u hu
        obtain ⟨j, hj, hju⟩ := List.getElem_of_mem hu
        rw [htakelen] at hj
        exact ⟨j, by omega, by omega, by rw [← hju, List.getElem_take]⟩
      have hnoearlier : ∀ (j : ℕ) (hj : j < S.length), j < i → ¬ G.Adj (S[j]'hj) a := by
        intro j hj hji
        exact ih j hji (by omega) a haA
      have haNotTake : a ∉ S.take (i + 1) := by
        intro hmem
        obtain ⟨j, hj, hji, hju⟩ := hmemtake a hmem
        rcases Nat.eq_zero_or_pos j with rfl | hjpos
        · exact hzA (by rw [← hju, hS0] at haA; exact haA)
        · have hadj' := path_adj_succ hSpath.1 (i := j - 1) (by omega)
          have he : S[j - 1 + 1]'(by omega) = a :=
            (hSpath.1.2.1.getElem_inj_iff.mpr (show j - 1 + 1 = j by omega)).trans hju
          rw [he] at hadj'
          exact hnoearlier (j - 1) (by omega) (by omega) hadj'
      have hglue : IsPathFrom G (S.take (i + 1) ++ [a]) z a := by
        refine PathGlue.glue_path htake ⟨isPathList_singleton G a, rfl, rfl⟩ ?_ ?_
        · intro u hu hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          exact haNotTake (hmem ▸ hu)
        · intro u hu b hb
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
          obtain ⟨j, hj, hji, hju⟩ := hmemtake u hu
          rcases Nat.lt_or_ge j i with hlt | hge
          · constructor
            · intro hcon
              exact absurd (hb ▸ hcon) (hju ▸ hnoearlier j hj hlt)
            · rintro ⟨hcon, -⟩
              exfalso
              have := hSpath.1.2.1.getElem_inj_iff.mp (hju.trans hcon)
              omega
          · have hje : j = i := by omega
            have : u = S[i]'(by omega) := by
              rw [← hju]
              exact hSpath.1.2.1.getElem_inj_iff.mpr hje
            rw [this, hb]
            exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => hadj⟩
      have hlen'' : (S.take (i + 1) ++ [a]).length = i + 2 := by
        simp only [List.length_append, List.length_cons, List.length_nil, htakelen]
      have hgood : Good (S.take (i + 1) ++ [a]) := by
        refine ⟨⟨a, hglue, haA⟩, by omega, ?_, ?_⟩
        · intro u hu
          rcases List.mem_append.mp hu with hu' | hu'
          · exact hSF u (List.take_subset _ _ hu')
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hu'
            exact hu' ▸ hAF a haA
        · intro u hu
          rw [mem_interior_iff_of_pathFrom hglue] at hu
          obtain ⟨huS, huz, hua⟩ := hu
          have huT : u ∈ S.take (i + 1) := by
            rcases List.mem_append.mp huS with h' | h'
            · exact h'
            · simp only [List.mem_cons, List.not_mem_nil, or_false] at h'
              exact absurd h' hua
          obtain ⟨j, hj, hji, hju⟩ := hmemtake u huT
          refine hSint u ((mem_interior_iff_of_pathFrom hSpath).mpr ⟨hju ▸ List.getElem_mem hj,
            huz, ?_⟩)
          intro he
          have hlast : S[S.length - 1]'(by omega) = v :=
            getElem_last_of_getLast? hSpath.2.2 (by omega)
          have := hSpath.1.2.1.getElem_inj_iff.mp (hju.trans (he.trans hlast.symm))
          omega
      have := hmin _ hgood
      omega

end Workspace.ProofLemmas.Thm232MinPath
