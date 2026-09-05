/-  Carve-out for statement 11.4 (`Workspace.Statements.S11.SPGT.thm_11_4`): the endgame, i.e.
    everything from *"Now the path `a₀-a₂-R₂-b₂-b₁` is odd"* to the end of the printed proof.

    PAPER (printed p. 67, last paragraph):

      *"Now the path `a₀-a₂-R₂-b₂-b₁` is odd, and its ends are complete to `{q₁,…,qₙ}`; so by
      (2) and 2.1, there are two adjacent vertices `u, v` in this path, both complete to
      `{q₁,…,qₙ}`.  Since `b₂` is not adjacent to `qₙ`, it follows that
      `u, v ∈ {a₀} ∪ V(R₂ \ b₂)`.  Suppose that the hole `a₀-R₀-b₀-b₂-R₂-a₂-a₀` has length
      ≥ 6.  Then one of `u, v` is nonadjacent to both `b₀, b₂`, say `v`, and hence `n` is odd,
      since `v-b₀-q₁-⋯-qₙ-b₂-v` is an antihole; but `b₁` is adjacent to `b₀` and `b₂`, and has
      no other neighbours in this hole, and is complete to `{q₁,…,qₙ}`, contrary to 3.3.  So
      the hole has length 4, and in particular `a₂` is adjacent to `b₂` and is complete to
      `{q₁,…,qₙ}`, and `a₀` is adjacent to `b₀`.  Hence `n` is odd, because
      `b₁-a₂-b₀-q₁-⋯-qₙ-b₂-a₀-b₁` is an antihole, and so `a₂-b₀-q₁-⋯-qₙ-b₂` is an odd antipath,
      contrary to (2).  This proves 11.4."*

    STRUCTURE OF THE ARGUMENT, and where each hypothesis below is used.

    * `P := a₀ :: (R₂ ++ [b₁])` is the printed path `a₀-a₂-R₂-b₂-b₁`.  It is induced because
      `a₀` is a left-star (its only neighbour on `R₂` is `a₂`) and `b₁` lies on the other rung
      of the step (its only neighbour on `R₂` is `b₂`, and `a₀b₁` is not an edge since `a₀` is
      anticomplete to `B`).  Its length is `pathLength R₂ + 2`, odd by `hR₂odd`, and its two
      ends are complete to `X := {q₁,…,qₙ}` by `ha₀qs` and `hb₁qs`.
    * 2.1 applied to `P` and the anticonnected set `X` gives one of three outcomes.  The
      *leap* outcome is excluded by `hbal` (`Thm114Balanced.not_leap_of_balanced_path`), and
      the *length-3 odd antipath* outcome is excluded by the second clause of `hbal`, since
      the two interior vertices of `P` then lie on `R₂ ⊆ A ∪ B ∪ C` and are adjacent.  What
      survives is an `X`-complete edge `uv` of `P`.
    * `b₂` is not `X`-complete (`hb₂qn`), and the only neighbour of `b₁` on `P` is `b₂`, so
      neither `u` nor `v` is `b₁` or `b₂`: both lie in `{a₀} ∪ (V(R₂) \ {b₂})`.
    * `H := R₀ ++ R₂.reverse` is the printed hole `a₀-R₀-b₀-b₂-R₂-a₂-a₀`; it is a hole because
      the only edges between a banister and a rung are `a₀a₂` and `b₀b₂`.  Its length is
      `R₀.length + R₂.length`, which is even since `hR₀odd` and `hR₂odd` make both summands
      even; so it is `4` or `≥ 6`.
    * Length `≥ 6`: one of `u, v` — call it `v` — is nonadjacent to both `b₀` and `b₂`, since
      `u` and `v` are consecutive on `H` while the neighbours of `b₀, b₂` on `H` other than
      each other are two vertices at distance three apart.  Then
      `v-b₀-q₁-⋯-qₙ-b₂-v` is an antihole on `n + 3` vertices, so `n` is odd; and 3.3, applied
      to `H` rotated to begin `b₀ :: b₂ :: …`, to the antipath `b₀ :: (qs ++ [b₂])` (even of
      length `n + 1 ≥ 4`) and to `z := b₁`, says any vertex of `H` other than `b₀, b₂` that is
      complete to `qs.dropLast` is a hole-neighbour of `b₀` or of `b₂` — which `v` is not.
    * Length `4`: then `R₀ = [a₀, b₀]` and `R₂ = [a₂, b₂]`, so `{a₀} ∪ (V(R₂) \ {b₂}) =
      {a₀, a₂}` and hence `a₂` is `X`-complete.  Now `b₁-a₂-b₀-q₁-⋯-qₙ-b₂-a₀-b₁` is an antihole
      on `n + 5` vertices, so `n` is odd, and `a₂-b₀-q₁-⋯-qₙ-b₂` is an antipath of length
      `n + 2` — odd — between the adjacent vertices `a₂, b₂` of `A ∪ B ∪ C` with interior
      inside `{b₀} ∪ {q₁,…,qₙ}`, contradicting the second clause of `hbal`.

    NOTE ON 3.3.  The proof below cites the sibling formalization of 3.3 exactly as the paper
    does.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.Thm114Aux
import Workspace.ProofLemmas.Thm114Balanced
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.Statements.S02.Thm_2_1
import Workspace.Statements.S03.Thm_3_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm114Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The endgame of the printed proof of 11.4.**

A banister `a₀-R₀-b₀` and a step `a₁-R₁-b₁, a₂-R₂-b₂` of a strip `(A, C, B)`, both rungs odd
(11.3), together with the minimal antipath `q₁-⋯-qₙ` of the proof — `n ≥ 2` by step (1), `b₁`
complete to it, `b₀` adjacent to all of it but `q₁`, `b₂` adjacent to all of it but `qₙ`, `a₀`
complete to it — and the balancedness of step (2), are contradictory. -/
theorem thm114_endgame {G : SimpleGraph V} (hG : Berge G)
    (A C B : Set V)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (hR₀odd : Odd (pathLength R₀))
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V) (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hR₂odd : Odd (pathLength R₂))
    (qs : List V) (q₁ qn : V) (hqs : IsAntipathFrom G qs q₁ qn)
    (hlen2 : 2 ≤ qs.length)
    (hqsS : ∀ x ∈ qs, x ∉ A ∪ B ∪ C)
    (hqsR₀ : ∀ x ∈ qs, x ∉ R₀)
    (ha₀qs : ∀ x ∈ qs, G.Adj a₀ x)
    (hb₁qs : ∀ x ∈ qs, G.Adj b₁ x)
    (hb₀q₁ : ¬ G.Adj b₀ q₁)
    (hb₀tail : ∀ x ∈ qs.tail, G.Adj b₀ x)
    (hb₂qn : ¬ G.Adj b₂ qn)
    (hb₂drop : ∀ x ∈ qs.dropLast, G.Adj b₂ x)
    (hbal : SPGT.Balanced G (A ∪ B ∪ C) (insert b₀ {x : V | x ∈ qs})) :
    False := by
  classical
  let X : Set V := {x : V | x ∈ qs}
  have hXanti : AnticonnectedSet G X :=
    InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList hqs.1
  have hq₁X : q₁ ∈ X := PathBasics.head_mem hqs.2.1
  have hqnX : qn ∈ X := PathBasics.getLast_mem hqs.2.2
  obtain ⟨hR₁, hR₂, hRdisj, hRcross⟩ := hstep
  have hR₂S : ∀ x ∈ R₂, x ∈ A ∪ B ∪ C :=
    fun x hx => Thm114Aux.rung_mem_strip hR₂ x hx
  have ha₂R₂ : a₂ ∈ R₂ := PathBasics.isPathFrom_ends_mem hR₂.1 |>.1
  have hb₂R₂ : b₂ ∈ R₂ := PathBasics.isPathFrom_ends_mem hR₂.1 |>.2
  have hb₁R₁ : b₁ ∈ R₁ := PathBasics.isPathFrom_ends_mem hR₁.1 |>.2
  have ha₂A : a₂ ∈ A := hR₂.2.1
  have hb₁B : b₁ ∈ B := hR₁.2.2.1
  have hb₂B : b₂ ∈ B := hR₂.2.2.1
  have ha₀a₂ : G.Adj a₀ a₂ := hban.2.2.1.2.1 a₂ ha₂A
  have hb₁b₂ : G.Adj b₁ b₂ :=
    (hRcross b₁ hb₁R₁ b₂ hb₂R₂).2 (Or.inr ⟨rfl, rfl⟩)
  have ha₀b₁ : ¬ G.Adj a₀ b₁ := hban.2.2.1.2.2 b₁ (Or.inl hb₁B)
  have ha₀b₁ne : a₀ ≠ b₁ := fun he => hban.2.2.1.1
    (he ▸ Or.inl (Or.inr hb₁B))
  have ha₀R₂ : a₀ ∉ R₂ := fun hm => hban.2.2.1.1 (hR₂S a₀ hm)
  have hb₁R₂ : b₁ ∉ R₂ := hRdisj b₁ hb₁R₁
  have ha₀other : ∀ x ∈ R₂, x ≠ a₂ → ¬ G.Adj a₀ x := by
    intro x hx hxa hadj
    rcases hR₂S x hx with (hxA | hxB) | hxC
    · exact hxa (hR₂.2.2.2.1 x hx hxA)
    · exact hban.2.2.1.2.2 x (Or.inl hxB) hadj
    · exact hban.2.2.1.2.2 x (Or.inr hxC) hadj
  have hb₁other : ∀ x ∈ R₂, x ≠ b₂ → ¬ G.Adj b₁ x := by
    intro x hx hxb hadj
    rcases (hRcross b₁ hb₁R₁ x hx).1 hadj with ⟨he, -⟩ | ⟨-, he⟩
    · exact hban.2.2.1.2.2 b₁ (Or.inl hb₁B)
        (he ▸ hban.2.2.1.2.1 a₁ hR₁.2.1)
    · exact hxb he
  let P : List V := a₀ :: (R₂ ++ [b₁])
  have hP : IsPathFrom G P a₀ b₁ := by
    dsimp [P]
    exact PathAttach.isPathFrom_cons_concat hR₂.1 ha₀a₂ hb₁b₂ ha₀b₁
      ha₀b₁ne ha₀R₂ hb₁R₂ ha₀other (fun x hx hne => hb₁other x hx hne)
  have hPmem : ∀ x : V, x ∈ P ↔ x = a₀ ∨ x ∈ R₂ ∨ x = b₁ := by
    intro x
    simp [P]
  have hPintS : ∀ x ∈ interior P, x ∈ A ∪ B ∪ C := by
    intro x hx
    have hi := (PathBasics.mem_interior_iff_of_pathFrom hP).1 hx
    rcases (hPmem x).1 hi.1 with h | h | h
    · exact absurd h hi.2.1
    · exact hR₂S x h
    · exact absurd h hi.2.2
  have hb₀ne : b₀ ≠ a₀ := by
    intro he
    exact hban.2.2.1.2.2 b₁ (Or.inl hb₁B)
      (he ▸ hban.2.2.2.1.2.1 b₁ hb₁B)
  have hb₀P : b₀ ∉ P := by
    intro hm
    rcases (hPmem b₀).1 hm with h | h | h
    · exact hb₀ne h
    · exact hban.2.2.2.1.1 (hR₂S b₀ h)
    · exact hban.2.2.2.1.1 (h ▸ Or.inl (Or.inr hb₁B))
  have hPX : ∀ x ∈ P, x ∉ X := by
    intro x hx hxX
    have hxq : x ∈ qs := hxX
    rcases (hPmem x).1 hx with h | h | h
    · exact hqsR₀ x hxq (h ▸ PathBasics.isPathFrom_ends_mem hban.1 |>.1)
    · exact hqsS x hxq (hR₂S x h)
    · exact hqsS x hxq (h ▸ Or.inl (Or.inr hb₁B))
  have hPbigAvoid : ∀ x ∈ P, x ∉ insert b₀ X := by
    intro x hx hxin
    rcases hxin with rfl | hxX
    · exact hb₀P hx
    · exact hPX x hx hxX
  have hPodd : Odd (pathLength P) := by
    obtain ⟨k, hk⟩ := hR₂odd
    have hpos := PathBasics.path_length_pos hR₂.1.1
    simp only [pathLength] at hk
    have hRlen : R₂.length = 2 * k + 2 := by omega
    refine ⟨k + 1, ?_⟩
    simp [P, pathLength, hRlen]
    omega
  have ha₀X : VertexComplete G a₀ X := fun x hx => ha₀qs x hx
  have hb₁X : VertexComplete G b₁ X := fun x hx => hb₁qs x hx
  have hcompleteEdge : ∃ u ∈ P, ∃ v ∈ P, EdgeComplete G X u v := by
    rcases Workspace.Statements.S02.SPGT.thm_2_1 G hG X hXanti P a₀ b₁ hP hPX
      hPodd ha₀X hb₁X with hedge | hleap | hanti
    · exact hedge
    · obtain ⟨-, a, haX, b, hbX, hlp⟩ := hleap
      exact (Thm114Balanced.not_leap_of_balanced_path hbal hPintS hPbigAvoid hPodd
        (Or.inr haX) (Or.inr hbX) hlp).elim
    · obtain ⟨hP3, c, d, hInt, Q, hQ, hQodd, hQint⟩ := hanti
      have hPlen4 : 4 ≤ P.length := by
        rw [pathLength] at hP3
        omega
      have hcInt : c ∈ interior P := by rw [hInt]; simp
      have hdInt : d ∈ interior P := by rw [hInt]; simp
      have hcd : G.Adj c d := by
        have hi := PathGlue.isPathFrom_interior hP.1 (by omega)
        rw [hInt] at hi
        have hadj := PathBasics.path_adj_succ hi.1 (i := 0) (by norm_num)
        simpa using hadj
      exact (hbal.2 c d Q (hPintS c hcInt) (hPintS d hdInt) hcd hQ
        (fun x hx => Or.inr (hQint x hx)) hQodd).elim
  obtain ⟨u, huP, v, hvP, huv, huX, hvX⟩ := hcompleteEdge
  have hb₂notX : ¬ VertexComplete G b₂ X := fun hc => hb₂qn (hc qn hqnX)
  have hub₂ : u ≠ b₂ := fun he => hb₂notX (he ▸ huX)
  have hvb₂ : v ≠ b₂ := fun he => hb₂notX (he ▸ hvX)
  have hub₁ : u ≠ b₁ := by
    intro he
    rcases (hPmem v).1 hvP with hv0 | hvR | hv1
    · exact ha₀b₁ (he ▸ hv0 ▸ huv.symm)
    · exact hb₁other v hvR hvb₂ (he ▸ huv)
    · exact huv.ne (he.trans hv1.symm)
  have hvb₁ : v ≠ b₁ := by
    intro he
    rcases (hPmem u).1 huP with hu0 | huR | hu1
    · exact ha₀b₁ (hu0 ▸ he ▸ huv)
    · exact hb₁other u huR hub₂ (he ▸ huv.symm)
    · exact huv.ne (hu1.trans he.symm)
  have huCand : u = a₀ ∨ (u ∈ R₂ ∧ u ≠ b₂) := by
    rcases (hPmem u).1 huP with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hub₂⟩
    · exact absurd h hub₁
  have hvCand : v = a₀ ∨ (v ∈ R₂ ∧ v ≠ b₂) := by
    rcases (hPmem v).1 hvP with h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨h, hvb₂⟩
    · exact absurd h hvb₁
  have hform := PrismFromBanisterAndStep.formPrism_of_banister_and_step hban
    ⟨hR₁, hR₂, hRdisj, hRcross⟩
  have hcross₂₀ : ∀ y ∈ R₂, ∀ x ∈ R₀,
      (G.Adj y x ↔ (y = a₂ ∧ x = a₀) ∨ (y = b₂ ∧ x = b₀)) := by
    simpa using hform.2.2.2.2.2.2.2.2
  have hcross₀₂ : ∀ x ∈ R₀, ∀ y ∈ R₂,
      (G.Adj x y ↔ (x = a₀ ∧ y = a₂) ∨ (x = b₀ ∧ y = b₂)) := by
    intro x hx y hy
    rw [SimpleGraph.adj_comm, hcross₂₀ y hy x hx]
    tauto
  have hR₀R₂ : ∀ x ∈ R₀, x ∉ R₂ := by
    intro x hx hxR₂
    exact hban.2.1 x hx (hR₂S x hxR₂)
  have hR₂rev : IsPathFrom G R₂.reverse b₂ a₂ := PathBasics.isPathFrom_reverse hR₂.1
  have hdisjRev : ∀ x ∈ R₀, x ∉ R₂.reverse :=
    fun x hx hm => hR₀R₂ x hx (List.mem_reverse.1 hm)
  have hcrossRev : ∀ x ∈ R₀, ∀ y ∈ R₂.reverse,
      (G.Adj x y ↔ (x = b₀ ∧ y = b₂) ∨ (x = a₀ ∧ y = a₂)) := by
    intro x hx y hy
    rw [hcross₀₂ x hx y (List.mem_reverse.1 hy)]
    tauto
  let H : List V := R₀ ++ R₂.reverse
  have hH : IsHoleList G H := by
    dsimp [H]
    exact PathGlue.glue_hole hban.1 hR₂rev hdisjRev hcrossRev (by
      have h0 := PathBasics.path_length_pos hban.1.1
      have h2 := PathBasics.path_length_pos hR₂.1.1
      obtain ⟨k0, hk0⟩ := hR₀odd
      obtain ⟨k2, hk2⟩ := hR₂odd
      simp only [pathLength] at hk0 hk2
      simp
      omega)
  have hHeven : Even (holeLength H) := hG.1 H hH
  have hR₀memA : a₀ ∈ R₀ := PathBasics.isPathFrom_ends_mem hban.1 |>.1
  have hR₀memB : b₀ ∈ R₀ := PathBasics.isPathFrom_ends_mem hban.1 |>.2
  have ha₂b₂ : a₂ ≠ b₂ := by
    intro he
    exact hban.2.2.1.2.2 b₂ (Or.inl hb₂B)
      (he ▸ hban.2.2.1.2.1 a₂ ha₂A)
  have end_adj_forces_two : ∀ {p : List V} {s t : V}, IsPathFrom G p s t →
      G.Adj s t → p.length = 2 := by
    intro p s t hp hadj
    have hpos := PathBasics.path_length_pos hp.1
    have h0 : p[0]'hpos = s := PathBasics.getElem_zero_of_head? hp.2.1 hpos
    have hl : p[p.length - 1]'(by omega) = t :=
      PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    have hadj' : G.Adj (p[0]'hpos) (p[p.length - 1]'(by omega)) := by
      simpa [h0, hl] using hadj
    rcases (PathBasics.path_adj_iff hp.1 hpos (by omega)).1 hadj' with h | h
    · omega
    · omega
  have last_neighbour_unique : ∀ {x y : V}, x ∈ R₂ → y ∈ R₂ → x ≠ b₂ → y ≠ b₂ →
      G.Adj x b₂ → G.Adj y b₂ → x = y := by
    intro x y hx hy hxb hyb hxbAdj hybAdj
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hx
    obtain ⟨j, hj, hjy⟩ := List.getElem_of_mem hy
    have hpos := PathBasics.path_length_pos hR₂.1.1
    have hl : R₂[R₂.length - 1]'(by omega) = b₂ :=
      PathBasics.getElem_last_of_getLast? hR₂.1.2.2 hpos
    have hiadj : G.Adj (R₂[i]'hi) (R₂[R₂.length - 1]'(by omega)) := by
      simpa [hix, hl] using hxbAdj
    have hjadj : G.Adj (R₂[j]'hj) (R₂[R₂.length - 1]'(by omega)) := by
      simpa [hjy, hl] using hybAdj
    have hine : i ≠ R₂.length - 1 := by
      intro he
      apply hxb
      rw [← hix, ← hl]
      exact hR₂.1.1.2.1.getElem_inj_iff.2 he
    have hjne : j ≠ R₂.length - 1 := by
      intro he
      apply hyb
      rw [← hjy, ← hl]
      exact hR₂.1.1.2.1.getElem_inj_iff.2 he
    have hi1 := (PathBasics.path_adj_iff hR₂.1.1 hi (by omega)).1 hiadj
    have hj1 := (PathBasics.path_adj_iff hR₂.1.1 hj (by omega)).1 hjadj
    have hij : i = j := by omega
    rw [← hix, ← hjy]
    exact hR₂.1.1.2.1.getElem_inj_iff.2 hij
  have bad_class : ∀ z : V, (z = a₀ ∨ (z ∈ R₂ ∧ z ≠ b₂)) →
      (G.Adj z b₀ ∨ G.Adj z b₂) →
      (z = a₀ ∧ G.Adj a₀ b₀) ∨ (z ∈ R₂ ∧ z ≠ b₂ ∧ G.Adj z b₂) := by
    intro z hz hbad
    rcases hz with hz0 | ⟨hzR, hzb₂⟩
    · subst z
      have hna₂ : ¬ G.Adj a₀ b₂ := by
        intro hadj
        rcases (hcross₀₂ a₀ hR₀memA b₂ hb₂R₂).1 hadj with ⟨-, he⟩ | ⟨he, -⟩
        · exact ha₂b₂ he.symm
        · exact hb₀ne he.symm
      exact Or.inl ⟨rfl, hbad.resolve_right hna₂⟩
    · have hnb₀ : ¬ G.Adj z b₀ := by
        intro hadj
        rcases (hcross₀₂ b₀ hR₀memB z hzR).1 hadj.symm with ⟨he, -⟩ | ⟨-, he⟩
        · exact hb₀ne he
        · exact hzb₂ he
      exact Or.inr ⟨hzR, hzb₂, hbad.resolve_left hnb₀⟩
  have hgoodLong : 6 ≤ holeLength H →
      ∃ w : V, (w = u ∨ w = v) ∧ ¬ G.Adj w b₀ ∧ ¬ G.Adj w b₂ := by
    intro hH6
    by_cases hgu : ¬ G.Adj u b₀ ∧ ¬ G.Adj u b₂
    · exact ⟨u, Or.inl rfl, hgu⟩
    by_cases hgv : ¬ G.Adj v b₀ ∧ ¬ G.Adj v b₂
    · exact ⟨v, Or.inr rfl, hgv⟩
    have hgu' : G.Adj u b₀ ∨ G.Adj u b₂ := by
      by_cases h : G.Adj u b₀
      · exact Or.inl h
      · exact Or.inr (by by_contra h'; exact hgu ⟨h, h'⟩)
    have hgv' : G.Adj v b₀ ∨ G.Adj v b₂ := by
      by_cases h : G.Adj v b₀
      · exact Or.inl h
      · exact Or.inr (by by_contra h'; exact hgv ⟨h, h'⟩)
    rcases bad_class u huCand hgu' with hu0 | hu2
    · rcases bad_class v hvCand hgv' with hv0 | hv2
      · exact absurd (hu0.1.trans hv0.1.symm) huv.ne
      · have hva₂ : v = a₂ := by
          rcases (hcross₀₂ a₀ hR₀memA v hv2.1).1 (hu0.1 ▸ huv) with h | h
          · exact h.2
          · exact absurd h.1 hb₀ne.symm
        have hR₀two := end_adj_forces_two hban.1 hu0.2
        have hR₂two := end_adj_forces_two hR₂.1 (hva₂ ▸ hv2.2.2)
        have : holeLength H = R₀.length + R₂.length := by simp [H, holeLength]
        omega
    · rcases bad_class v hvCand hgv' with hv0 | hv2
      · have hua₂ : u = a₂ := by
          rcases (hcross₀₂ a₀ hR₀memA u hu2.1).1 (hv0.1 ▸ huv.symm) with h | h
          · exact h.2
          · exact absurd h.1 hb₀ne.symm
        have hR₀two := end_adj_forces_two hban.1 hv0.2
        have hR₂two := end_adj_forces_two hR₂.1 (hua₂ ▸ hu2.2.2)
        have : holeLength H = R₀.length + R₂.length := by simp [H, holeLength]
        omega
      · exact absurd (last_neighbour_unique hu2.1 hv2.1 hu2.2.1 hv2.2.1
          hu2.2.2 hv2.2.2) huv.ne
  have hqsne : qs ≠ [] := hqs.1.1
  have hq₁notTail : ∀ x ∈ qs.tail, x ≠ q₁ := by
    intro x hx he
    have hnd := hqs.1.2.1
    cases qs with
    | nil => exact absurd rfl hqsne
    | cons y ys =>
      have hy : y = q₁ := by simpa using hqs.2.1
      subst y
      exact (List.nodup_cons.1 hnd).1 (he ▸ hx)
  have hmemTail : ∀ x : V, x ∈ qs.tail ↔ x ∈ qs ∧ x ≠ q₁ := by
    intro x
    constructor
    · intro hx
      exact ⟨List.mem_of_mem_tail hx, hq₁notTail x hx⟩
    · rintro ⟨hx, hxne⟩
      cases qs with
      | nil => exact absurd rfl hqsne
      | cons y ys =>
        have hy : y = q₁ := by simpa using hqs.2.1
        subst y
        simp only [List.tail_cons, List.mem_cons] at ⊢ hx
        exact hx.resolve_left hxne
  have hlast : qs.getLast hqsne = qn := by
    have h := hqs.2.2
    rw [List.getLast?_eq_some_getLast hqsne] at h
    exact Option.some_injective _ h
  have hmemDrop : ∀ x : V, x ∈ qs.dropLast ↔ x ∈ qs ∧ x ≠ qn := by
    intro x
    rw [PathBasics.mem_dropLast_iff hqs.1.2.1 hqsne, hlast]
  have hb₀qs : b₀ ∉ qs := fun h => hqsR₀ b₀ h hR₀memB
  have hb₂qs : b₂ ∉ qs := fun h => hqsS b₂ h (Or.inl (Or.inr hb₂B))
  have hb₀b₂ : G.Adj b₀ b₂ := hban.2.2.2.1.2.1 b₂ hb₂B
  have hb₀q₁c : Gᶜ.Adj b₀ q₁ := (G.compl_adj b₀ q₁).2
    ⟨fun he => hb₀qs (he ▸ hq₁X), hb₀q₁⟩
  have hb₂qnc : Gᶜ.Adj b₂ qn := (G.compl_adj b₂ qn).2
    ⟨fun he => hb₂qs (he ▸ hqnX), hb₂qn⟩
  have hb₀b₂c : ¬ Gᶜ.Adj b₀ b₂ := fun h => h.2 hb₀b₂
  have hb₀other : ∀ x ∈ qs, x ≠ q₁ → ¬ Gᶜ.Adj b₀ x := by
    intro x hx hne hc
    exact hc.2 (hb₀tail x ((hmemTail x).2 ⟨hx, hne⟩))
  have hb₂other : ∀ x ∈ qs, x ≠ qn → ¬ Gᶜ.Adj b₂ x := by
    intro x hx hne hc
    exact hc.2 (hb₂drop x ((hmemDrop x).2 ⟨hx, hne⟩))
  let Q₀ : List V := b₀ :: (qs ++ [b₂])
  have hQ₀ : IsPathFrom Gᶜ Q₀ b₀ b₂ := by
    dsimp [Q₀]
    exact PathAttach.isPathFrom_cons_concat hqs hb₀q₁c hb₂qnc hb₀b₂c hb₀b₂.ne
      hb₀qs hb₂qs hb₀other hb₂other
  have hQ₀len : Q₀.length = qs.length + 2 := by simp [Q₀]
  by_cases hH4 : holeLength H = 4
  · have hsum : R₀.length + R₂.length = 4 := by
      simpa [H, holeLength] using hH4
    obtain ⟨k₀, hk₀⟩ := hR₀odd
    obtain ⟨k₂, hk₂⟩ := hR₂odd
    have hR₀pos := PathBasics.path_length_pos hban.1.1
    have hR₂pos := PathBasics.path_length_pos hR₂.1.1
    simp only [pathLength] at hk₀ hk₂
    have hR₀two : R₀.length = 2 := by omega
    have hR₂two : R₂.length = 2 := by omega
    obtain ⟨r₀, r₁, hR₀shape'⟩ := PathGlue.length_eq_two hR₀two
    have hr₀ : r₀ = a₀ := by simpa [hR₀shape'] using hban.1.2.1
    have hr₁ : r₁ = b₀ := by simpa [hR₀shape'] using hban.1.2.2
    have hR₀shape : R₀ = [a₀, b₀] := by simpa [hr₀, hr₁] using hR₀shape'
    obtain ⟨s₀, s₁, hR₂shape'⟩ := PathGlue.length_eq_two hR₂two
    have hs₀ : s₀ = a₂ := by simpa [hR₂shape'] using hR₂.1.2.1
    have hs₁ : s₁ = b₂ := by simpa [hR₂shape'] using hR₂.1.2.2
    have hR₂shape : R₂ = [a₂, b₂] := by simpa [hs₀, hs₁] using hR₂shape'
    have ha₀b₀ : G.Adj a₀ b₀ := by
      have h := PathBasics.path_adj_succ hban.1.1 (i := 0) (by rw [hR₀shape]; simp)
      simpa [hR₀shape] using h
    have ha₂b₂adj : G.Adj a₂ b₂ := by
      have h := PathBasics.path_adj_succ hR₂.1.1 (i := 0) (by rw [hR₂shape]; simp)
      simpa [hR₂shape] using h
    have huShort : u = a₀ ∨ u = a₂ := by
      rcases huCand with h | ⟨huR, hub⟩
      · exact Or.inl h
      · simp [hR₂shape] at huR
        exact Or.inr (huR.resolve_right hub)
    have hvShort : v = a₀ ∨ v = a₂ := by
      rcases hvCand with h | ⟨hvR, hvb⟩
      · exact Or.inl h
      · simp [hR₂shape] at hvR
        exact Or.inr (hvR.resolve_right hvb)
    have ha₂X : VertexComplete G a₂ X := by
      rcases huShort with hu₀ | hu₂
      · have hv₂ : v = a₂ := hvShort.resolve_left (fun hv₀ =>
          huv.ne (hu₀.trans hv₀.symm))
        simpa [hv₂] using hvX
      · simpa [hu₂] using huX
    have ha₂b₀ne : a₂ ≠ b₀ := by
      intro he
      exact hban.2.2.2.1.1 (he ▸ Or.inl (Or.inl ha₂A))
    have ha₂b₀n : ¬ G.Adj a₂ b₀ := by
      intro hadj
      exact hban.2.2.2.1.2.2 a₂ (Or.inl ha₂A) hadj.symm
    have ha₂b₀c : Gᶜ.Adj a₂ b₀ := (G.compl_adj a₂ b₀).2 ⟨ha₂b₀ne, ha₂b₀n⟩
    have ha₂Q₀ : a₂ ∉ Q₀ := by
      simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      rintro (h | h | h)
      · exact ha₂b₀ne h
      · exact hqsS a₂ h (Or.inl (Or.inl ha₂A))
      · exact ha₂b₂ h
    have ha₂other : ∀ x ∈ Q₀, x ≠ b₀ → ¬ Gᶜ.Adj a₂ x := by
      intro x hx hxne hc
      simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact hxne rfl
      · exact hc.2 (ha₂X x hx)
      · exact hc.2 ha₂b₂adj
    let Pₛ : List V := a₂ :: Q₀
    have hPₛ : IsAntipathFrom G Pₛ a₂ b₂ := by
      dsimp [Pₛ]
      exact PathAttach.isPathFrom_cons hQ₀ ha₂b₀c ha₂Q₀ ha₂other
    have hb₁a₂ne : b₁ ≠ a₂ := fun he => hb₁R₂ (he.symm ▸ ha₂R₂)
    have hb₁a₂n : ¬ G.Adj b₁ a₂ := hb₁other a₂ ha₂R₂ ha₂b₂
    have hb₁a₂c : Gᶜ.Adj b₁ a₂ := (G.compl_adj b₁ a₂).2 ⟨hb₁a₂ne, hb₁a₂n⟩
    have hb₁b₀ : G.Adj b₁ b₀ := (hban.2.2.2.1.2.1 b₁ hb₁B).symm
    have hb₁Q₀ : VertexComplete G b₁ {x : V | x ∈ Q₀} := by
      intro x hx
      simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact hb₁b₀
      · exact hb₁qs x hx
      · exact hb₁b₂
    have hb₁b₀ne : b₁ ≠ b₀ := by
      intro he
      exact hban.2.2.2.1.1 (he ▸ Or.inl (Or.inr hb₁B))
    have hb₁Pₛ : b₁ ∉ Pₛ := by
      simp only [Pₛ, Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      rintro (h | h | h | h)
      · exact hb₁a₂ne h
      · exact hb₁b₀ne h
      · exact hqsS b₁ h (Or.inl (Or.inr hb₁B))
      · exact hb₁b₂.ne h
    have hb₁otherPₛ : ∀ x ∈ Pₛ, x ≠ a₂ → ¬ Gᶜ.Adj b₁ x := by
      intro x hx hxne hc
      simp only [Pₛ, List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hxne rfl
      · exact hc.2 (hb₁Q₀ x hx)
    let P₁ : List V := b₁ :: Pₛ
    have hP₁ : IsAntipathFrom G P₁ b₁ b₂ := by
      dsimp [P₁]
      exact PathAttach.isPathFrom_cons hPₛ hb₁a₂c hb₁Pₛ hb₁otherPₛ
    have ha₀b₂n : ¬ G.Adj a₀ b₂ := hban.2.2.1.2.2 b₂ (Or.inl hb₂B)
    have ha₀b₂ne : a₀ ≠ b₂ := by
      intro he
      exact hban.2.2.1.1 (he ▸ Or.inl (Or.inr hb₂B))
    have ha₀b₁c : Gᶜ.Adj a₀ b₁ := (G.compl_adj a₀ b₁).2 ⟨ha₀b₁ne, ha₀b₁⟩
    have ha₀b₂c : Gᶜ.Adj a₀ b₂ := (G.compl_adj a₀ b₂).2 ⟨ha₀b₂ne, ha₀b₂n⟩
    have ha₀P₁ : a₀ ∉ P₁ := by
      simp only [P₁, Pₛ, Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      rintro (h | h | h | h | h)
      · exact ha₀b₁ne h
      · exact ha₀a₂.ne h
      · exact hb₀ne h.symm
      · exact hqsR₀ a₀ h hR₀memA
      · exact ha₀b₂ne h
    have ha₀int : ∀ x ∈ interior P₁, ¬ Gᶜ.Adj a₀ x := by
      intro x hx hc
      have hi := (PathBasics.mem_interior_iff_of_pathFrom hP₁).1 hx
      have hm : x = b₁ ∨ x = a₂ ∨ x = b₀ ∨ x ∈ qs ∨ x = b₂ := by
        simpa only [P₁, Pₛ, Q₀, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] using hi.1
      rcases hm with h | h | h | h | h
      · exact hi.2.1 h
      · exact hc.2 (h ▸ ha₀a₂)
      · exact hc.2 (h ▸ ha₀b₀)
      · exact hc.2 (ha₀qs x h)
      · exact hi.2.2 h
    have hAntiShort : IsHoleList Gᶜ (a₀ :: P₁) :=
      PrismBasics.isHoleList_of_path_add_vertex hP₁ (by
        rw [pathLength]
        simp [P₁, Pₛ, hQ₀len]) ha₀b₁c ha₀b₂c ha₀P₁ ha₀int
    have hqsOdd : Odd qs.length := by
      have he := hG.2 _ hAntiShort
      obtain ⟨k, hk⟩ := he
      simp only [holeLength, List.length_cons, P₁, Pₛ, hQ₀len] at hk
      exact ⟨k - 3, by omega⟩
    have hPₛodd : Odd (pathLength Pₛ) := by
      obtain ⟨k, hk⟩ := hqsOdd
      refine ⟨k + 1, ?_⟩
      rw [pathLength]
      simp only [Pₛ, List.length_cons, hQ₀len]
      omega
    have hPₛint : ∀ x ∈ interior Pₛ, x ∈ insert b₀ X := by
      intro x hx
      have hi := (PathBasics.mem_interior_iff_of_pathFrom hPₛ).1 hx
      have hm : x = a₂ ∨ x = b₀ ∨ x ∈ qs ∨ x = b₂ := by
        simpa only [Pₛ, Q₀, List.mem_cons, List.mem_append,
          List.not_mem_nil, or_false] using hi.1
      rcases hm with h | h | h | h
      · exact absurd h hi.2.1
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hi.2.2
    exact hbal.2 a₂ b₂ Pₛ (Or.inl (Or.inl ha₂A)) (Or.inl (Or.inr hb₂B))
      ha₂b₂adj hPₛ hPₛint hPₛodd
  · have hH6 : 6 ≤ holeLength H := by
      obtain ⟨k, hk⟩ := hHeven
      have h4 := hH.1
      simp only [holeLength] at hH4 hk ⊢
      omega
    obtain ⟨w, hwuv, hwb₀, hwb₂⟩ := hgoodLong hH6
    have hwP : w ∈ P := hwuv.elim (fun h => h ▸ huP) (fun h => h ▸ hvP)
    have hwX : VertexComplete G w X :=
      hwuv.elim (fun h => h ▸ huX) (fun h => h ▸ hvX)
    have hwCand : w = a₀ ∨ (w ∈ R₂ ∧ w ≠ b₂) :=
      hwuv.elim (fun h => h ▸ huCand) (fun h => h ▸ hvCand)
    have hwb₀ne : w ≠ b₀ := by
      rcases hwCand with h | ⟨hwR, -⟩
      · exact fun he => hb₀ne (he.symm.trans h)
      · exact fun he => hban.2.2.2.1.1 (hR₂S b₀ (he ▸ hwR))
    have hwb₂ne : w ≠ b₂ := by
      rcases hwuv with h | h
      · exact h ▸ hub₂
      · exact h ▸ hvb₂
    have hwqs : w ∉ qs := fun hm => hPX w hwP hm
    have hwQ₀ : w ∉ Q₀ := by
      simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false]
      rintro (h | h | h)
      · exact hwb₀ne h
      · exact hwqs h
      · exact hwb₂ne h
    have hwQ₀int : ∀ x ∈ interior Q₀, ¬ Gᶜ.Adj w x := by
      intro x hx hc
      have hxmem := PathBasics.interior_subset hx
      have hxne0 := (PathBasics.mem_interior_iff_of_pathFrom hQ₀).1 hx |>.2.1
      have hxne2 := (PathBasics.mem_interior_iff_of_pathFrom hQ₀).1 hx |>.2.2
      have hxqs : x ∈ qs := by
        simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hxmem
        rcases hxmem with h | h | h
        · exact absurd h hxne0
        · exact h
        · exact absurd h hxne2
      exact hc.2 (hwX x hxqs)
    have hwc₀ : Gᶜ.Adj w b₀ := (G.compl_adj w b₀).2 ⟨hwb₀ne, hwb₀⟩
    have hwc₂ : Gᶜ.Adj w b₂ := (G.compl_adj w b₂).2 ⟨hwb₂ne, hwb₂⟩
    have hAnti : IsHoleList Gᶜ (w :: Q₀) :=
      PrismBasics.isHoleList_of_path_add_vertex hQ₀ (by
        rw [pathLength, hQ₀len]
        omega) hwc₀ hwc₂ hwQ₀ hwQ₀int
    have hqsOdd : Odd qs.length := by
      have he := hG.2 _ hAnti
      obtain ⟨k, hk⟩ := he
      simp only [holeLength, List.length_cons, hQ₀len] at hk
      exact ⟨k - 2, by omega⟩
    have hR₀pos := PathBasics.path_length_pos hban.1.1
    have hR₂pos := PathBasics.path_length_pos hR₂.1.1
    have hHlen : H.length = R₀.length + R₂.length := by simp [H]
    let r : ℕ := R₀.length - 1
    let D : List V := H.rotate r
    have hD : IsHoleList G D := HoleBasics.isHoleList_rotate hH r
    have hDlen : D.length = H.length := by simp [D]
    have hrH : r < H.length := by simp [r, hHlen]; omega
    have hD0 : D[0]'(by omega) = b₀ := by
      dsimp [D]
      rw [Workspace.ProofLemmas.WheelParity.getElem_rotate_eq (C := H) (by omega)]
      have hm : (0 + r) % H.length = r := by simpa using Nat.mod_eq_of_lt hrH
      have hrR : r < R₀.length := by simp [r]; omega
      have hl : R₀[R₀.length - 1]'(by omega) = b₀ :=
        PathBasics.getElem_last_of_getLast? hban.1.2.2 hR₀pos
      calc
        H[(0 + r) % H.length]'_ = H[r]'hrH :=
          Workspace.ProofLemmas.HoleArithmetic.getElem_congr_idx H _ hrH hm
        _ = R₀[r]'hrR := by
          dsimp [H]
          exact List.getElem_append_left hrR
        _ = b₀ := by simpa [r] using hl
    have hD1 : D[1]'(by omega) = b₂ := by
      dsimp [D]
      rw [Workspace.ProofLemmas.WheelParity.getElem_rotate_eq (C := H) (by omega)]
      have hm : (1 + r) % H.length = R₀.length := by
        rw [Nat.mod_eq_of_lt (show 1 + r < H.length by simp [r, hHlen]; omega)]
        simp [r]
        omega
      have hglobal : R₀.length < H.length := by rw [hHlen]; omega
      have hrev0 : 0 < R₂.reverse.length := by simp; omega
      have hrev : R₂.reverse[0]'hrev0 = R₂[R₂.length - 1]'(by omega) := by
        simp only [List.getElem_reverse, List.length_reverse]
        congr 1 <;> omega
      calc
        H[(1 + r) % H.length]'_ = H[R₀.length]'hglobal :=
          Workspace.ProofLemmas.HoleArithmetic.getElem_congr_idx H _ hglobal hm
        _ = R₂.reverse[0]'hrev0 := by
          simp only [H, List.getElem_append_right (le_refl R₀.length), Nat.sub_self]
        _ = R₂[R₂.length - 1]'(by omega) := hrev
        _ = b₂ := PathBasics.getElem_last_of_getLast? hR₂.1.2.2 hR₂pos
    have hH6len : 6 ≤ H.length := by simpa [holeLength] using hH6
    have hD3 : 3 ≤ D.length := by rw [hDlen]; omega
    obtain ⟨d₀, d₁, d₂, rest, hDshape⟩ :
        ∃ d₀ d₁ d₂ rest, D = d₀ :: d₁ :: d₂ :: rest := by
      have hDne : D ≠ [] := by intro he; rw [he] at hD3; simp at hD3
      obtain ⟨d₀, t, hDt⟩ := List.exists_cons_of_ne_nil hDne
      have ht2 : 2 ≤ t.length := by rw [hDt] at hD3; simp at hD3; omega
      have htne : t ≠ [] := by intro he; rw [he] at ht2; simp at ht2
      obtain ⟨d₁, t', htt⟩ := List.exists_cons_of_ne_nil htne
      have ht'ne : t' ≠ [] := by
        intro he
        rw [htt, he] at ht2
        simp at ht2
      obtain ⟨d₂, rest, ht'rest⟩ := List.exists_cons_of_ne_nil ht'ne
      exact ⟨d₀, d₁, d₂, rest, by rw [hDt, htt, ht'rest]⟩
    have hd₀ : d₀ = b₀ := by simpa [hDshape] using hD0
    have hd₁ : d₁ = b₂ := by simpa [hDshape] using hD1
    subst d₀
    subst d₁
    have hDne : D ≠ [] := by intro he; rw [he] at hD3; simp at hD3
    let pm : V := D.getLast hDne
    have hpm : D.getLast? = some pm := List.getLast?_eq_some_getLast hDne
    have hb₁b₀ : G.Adj b₁ b₀ := (hban.2.2.2.1.2.1 b₁ hb₁B).symm
    have hb₁Q₀ : VertexComplete G b₁ {x : V | x ∈ Q₀} := by
      intro x hx
      simp only [Q₀, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | hx | rfl
      · exact hb₁b₀
      · exact hb₁qs x hx
      · exact hb₁b₂
    have hb₁a₁ : b₁ ≠ a₁ := by
      intro he
      exact hban.2.2.1.2.2 b₁ (Or.inl hb₁B)
        (he ▸ hban.2.2.1.2.1 a₁ hR₁.2.1)
    have hcross₁₀ : ∀ y ∈ R₁, ∀ x ∈ R₀,
        (G.Adj y x ↔ (y = a₁ ∧ x = a₀) ∨ (y = b₁ ∧ x = b₀)) := by
      simpa using hform.2.2.2.2.2.2.2.1
    have hnodD : (b₀ :: b₂ :: d₂ :: rest).Nodup := by
      rw [← hDshape]
      exact hD.2.1
    have hb₀drop : b₀ ∉ D.drop 2 := by
      rw [hDshape]
      change b₀ ∉ d₂ :: rest
      intro hm
      exact (List.nodup_cons.1 hnodD).1 (List.mem_cons_of_mem b₂ hm)
    have hb₂dropD : b₂ ∉ D.drop 2 := by
      rw [hDshape]
      change b₂ ∉ d₂ :: rest
      exact (List.nodup_cons.1 (List.nodup_cons.1 hnodD).2).1
    have hb₁D : VertexAnticomplete G b₁ {x : V | x ∈ D.drop 2} := by
      intro x hx hadj
      have hxD : x ∈ D := List.mem_of_mem_drop hx
      have hxH : x ∈ H := by
        have : x ∈ H.rotate r := by simpa [D] using hxD
        exact List.mem_rotate.1 this
      have hxb₀ : x ≠ b₀ := fun he => hb₀drop (he ▸ hx)
      have hxb₂ : x ≠ b₂ := fun he => hb₂dropD (he ▸ hx)
      have hxparts : x ∈ R₀ ∨ x ∈ R₂ := by
        simpa [H] using hxH
      rcases hxparts with hxR₀ | hxR₂
      · rcases (hcross₁₀ b₁ hb₁R₁ x hxR₀).1 hadj with ⟨he, -⟩ | ⟨-, he⟩
        · exact hb₁a₁ he
        · exact hxb₀ he
      · rcases (hRcross b₁ hb₁R₁ x hxR₂).1 hadj with ⟨he, -⟩ | ⟨-, he⟩
        · exact hb₁a₁ he
        · exact hxb₂ he
    have hQ₀even : Even (pathLength Q₀) := by
      obtain ⟨k, hk⟩ := hqsOdd
      rw [pathLength, hQ₀len]
      exact ⟨k + 1, by omega⟩
    have hQ₀long : 4 ≤ pathLength Q₀ := by
      rw [pathLength, hQ₀len]
      obtain ⟨k, hk⟩ := hqsOdd
      omega
    have hwH : w ∈ H := by
      rcases hwCand with h | ⟨hwR, -⟩
      · subst w
        dsimp [H]
        exact List.mem_append_left _ hR₀memA
      · dsimp [H]
        exact List.mem_append_right _ (List.mem_reverse.2 hwR)
    have hwD : w ∈ D := by
      dsimp [D]
      exact List.mem_rotate.2 hwH
    have hwDrop : w ∈ D.drop 2 := by
      rw [hDshape] at hwD ⊢
      change w ∈ d₂ :: rest
      simp only [List.mem_cons] at hwD ⊢
      rcases hwD with h | h | h
      · exact absurd h hwb₀ne
      · exact absurd h hwb₂ne
      · exact h
    have hwSmallComplete : VertexComplete G w {x : V | x ∈ qs.dropLast} := by
      intro x hx
      exact hwX x (List.mem_of_mem_dropLast hx)
    have hD6 : 6 ≤ D.length := by rw [hDlen]; exact hH6len
    have hboundary := (Workspace.Statements.S03.SPGT.thm_3_3 G hG D b₀ b₂ d₂ pm rest
      hD (by simpa [holeLength] using hD6) hDshape hpm qs Q₀ rfl hQ₀ hQ₀long hQ₀even
      b₁ hb₁Q₀ hb₁D).2 w hwDrop (Or.inl hwSmallComplete)
    rcases hboundary with hwd₂ | hwpm
    · have hb₂d₂ : G.Adj b₂ d₂ := by
        have h := HoleBasics.hole_adj_succ hD (i := 1) (by rw [hDshape]; simp)
        simpa [hDshape] using h
      exact hwb₂ (hwd₂ ▸ hb₂d₂.symm)
    · have hpmb₀ : G.Adj pm b₀ := by
        have h := HoleBasics.hole_adj_wrap hD
        have hlast : D[D.length - 1]'(by omega) = pm :=
          PathBasics.getElem_last_of_getLast? hpm (by omega)
        have hzero : D[0]'(by omega) = b₀ := by simpa [hDshape]
        simpa [hlast, hzero] using h
      exact hwb₀ (hwpm ▸ hpmb₀)

end Workspace.ProofLemmas.Thm114Endgame
