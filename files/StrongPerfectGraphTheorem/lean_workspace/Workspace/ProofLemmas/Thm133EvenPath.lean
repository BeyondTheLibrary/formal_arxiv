/-  **13.3, the even-path half of the balancedness check** (printed p. 83).

    PAPER: *"Now let `u, v ∈ Y ∪ B` be nonadjacent.  If they are both adjacent to `b₀`, then
    any path joining them with interior in `A ∪ C` (and there is one) is even, since it can be
    completed to a hole via `v`-`b₀`-`u`.  So we may assume that `u` is nonadjacent to `b₀`,
    and hence `u ∉ B`, so `u ∈ Y`.  If they are both in `Y`, then they are joined by an even
    path `u`-`a₁`-`v` for any `a₁ ∈ A`.  So we may assume that `v ∈ B`.  Since `u` is
    nonadjacent to `b₀` and to `v`, it is neither left- nor right-diagonal, and it is not
    central since there is no 2-breaker; so from 12.1 it is a left-star.  Let `a₁`-`R₁`-`v` be
    an `S`-rung; then `u`-`a₁`-`R₁`-`v` is the desired even path between `u` and `v`."*

    In every one of the printed cases the even path produced has its interior inside `A ∪ C`,
    which is what is recorded here.  Since `A ∪ C` is disjoint from `X ∪ Y ∪ B` this is
    stronger than the *"interior in `A₁ ∪ A₂`"* that the application of 4.6 needs, and it is
    what the printed argument actually delivers.  -/
import Mathlib
import Workspace.ProofLemmas.Thm133Setup
import Workspace.ProofLemmas.PathInteriorIn
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S11.Thm_11_3

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm133EvenPath

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.LongOddPrism Workspace.Types.LongOddPrism.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm133Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **13.3, even path.**  PAPER: *"any two nonadjacent vertices in `Y ∪ B` are joined by an
even path with interior in `A₁ ∪ A₂`"* — the printed case analysis in fact always produces a
path whose interior lies in `A ∪ C`. -/
theorem thm133_even_path {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ : V} {R₀ : List V}
    {x : List V} (c : Ctx G A C B a₀ b₀ R₀ x)
    {u v : V} (hu : u ∈ Ys G A C B x ∪ B) (hv : v ∈ Ys G A C B x ∪ B)
    (huv : ¬ G.Adj u v) (hne : u ≠ v) :
    ∃ p : List V, IsPathFrom G p u v ∧ (∀ z ∈ SPGT.interior p, z ∈ A ∪ C) ∧
      Even (pathLength p) := by
  classical
  have hAcomp : ∀ w ∈ Ys G A C B x, VertexComplete G w A := by
    intro w hw z hz
    exact hw.2 z (Or.inl hz)
  have houtAC : ∀ w ∈ Ys G A C B x ∪ B, w ∉ A ∪ C := by
    intro w hw hwAC
    rcases hw with hwY | hwB
    · exact hwY.1 (hwAC.elim (fun h => Or.inl (Or.inl h)) Or.inr)
    · rcases hwAC with hwA | hwC
      · exact (Set.disjoint_left.mp c.stepConn.1.1 hwA) hwB
      · exact (Set.disjoint_left.mp c.stepConn.1.2.2 hwB) hwC
  have hneighAC : ∀ w ∈ Ys G A C B x ∪ B, ∃ z ∈ A ∪ C, G.Adj w z := by
    intro w hw
    rcases hw with hwY | hwB
    · obtain ⟨a, ha⟩ := c.Ane
      exact ⟨a, Or.inl ha, hAcomp w hwY a ha⟩
    · exact bVertex_has_neighbour_in_AC c.maxStaircase w hwB
  have heven_if_both (s t : V) (hs : s ∈ Ys G A C B x ∪ B)
      (ht : t ∈ Ys G A C B x ∪ B) (hst : ¬ G.Adj s t) (hsne : s ≠ t)
      (hsb : G.Adj s b₀) (htb : G.Adj t b₀) :
      ∃ p : List V, IsPathFrom G p s t ∧
        (∀ z ∈ SPGT.interior p, z ∈ A ∪ C) ∧ Even (pathLength p) := by
    obtain ⟨p, hp, hpint⟩ :=
      PathInteriorIn.exists_path_interior_in c.AC_connected (houtAC s hs) (houtAC t ht)
        (hneighAC s hs) (hneighAC t ht)
    have hplen2 : 2 ≤ pathLength p := by
      have hpos := PathBasics.path_length_pos hp.1
      have h0 := PathBasics.getElem_zero_of_head? hp.2.1 hpos
      have hl := PathBasics.getElem_last_of_getLast? hp.2.2 hpos
      rcases (show p.length = 1 ∨ p.length = 2 ∨ 3 ≤ p.length by omega) with h | h | h
      · exfalso
        apply hsne
        rw [← h0, ← hl]
        congr 1
        omega
      · exfalso
        apply hst
        rw [← h0, ← hl]
        exact (PathBasics.path_adj_iff hp.1 hpos (by omega)).mpr (by omega)
      · rw [pathLength]
        omega
    have heven : Even (pathLength p) := by
      by_cases h2 : pathLength p = 2
      · exact ⟨1, by omega⟩
      · have h4 : 4 ≤ p.length := by
          have := PathBasics.length_eq_pathLength_add_one hp.1
          omega
        have hb₀p : b₀ ∉ p := by
          intro hbmem
          have hbneS : b₀ ≠ s := fun h => G.irrefl (h ▸ hsb.symm)
          have hbneT : b₀ ≠ t := fun h => G.irrefl (h ▸ htb.symm)
          have hbint : b₀ ∈ SPGT.interior p :=
            (PathBasics.mem_interior_iff_of_pathFrom hp).mpr ⟨hbmem, hbneS, hbneT⟩
          exact c.rightStar_b₀.1
            (hpint b₀ hbint |>.elim (fun h => Or.inl (Or.inl h)) Or.inr)
        have hbanti : ∀ z ∈ SPGT.interior p, ¬ G.Adj b₀ z := by
          intro z hz
          exact c.rightStar_b₀.2.2 z (hpint z hz)
        have hclosed := PrismBasics.even_of_path_closed_by_vertex c.berge hp h4 hb₀p
          hsb.symm htb.symm hbanti
        obtain ⟨k, hk⟩ := hclosed
        have hlenEq := PathBasics.length_eq_pathLength_add_one hp.1
        refine ⟨k - 1, ?_⟩
        omega
    exact ⟨p, hp, hpint, heven⟩
  have hleft_of_Y (s t : V) (hsY : s ∈ Ys G A C B x) (htB : t ∈ B)
      (hsb : ¬ G.Adj s b₀) (hst : ¬ G.Adj s t) : IsLeftStar G A C B s := by
    have hsA : VertexComplete G s A := hAcomp s hsY
    by_cases hsR : s ∈ R₀
    · by_cases hsa : s = a₀
      · simpa [hsa] using c.leftStar_a₀
      · by_cases hsb₀eq : s = b₀
        · obtain ⟨a, ha⟩ := c.Ane
          exact False.elim
            (c.rightStar_b₀.2.2 a (Or.inl ha) (hsb₀eq ▸ hsA a ha))
        · have hsint : s ∈ SPGT.interior R₀ :=
            (PathBasics.mem_interior_iff_of_pathFrom c.banister.1).mpr ⟨hsR, hsa, hsb₀eq⟩
          obtain ⟨a, ha⟩ := c.Ane
          exact False.elim
            (c.banister.2.2.2.2 s hsint a (Or.inl (Or.inl ha)) (hsA a ha))
    · have hsK : s ∉ staircaseVertices A C B R₀ := by
        rintro (hsR' | hsS)
        · exact hsR hsR'
        · exact hsY.1 hsS
      obtain ⟨i, hi, -⟩ :=
        _root_.Workspace.Statements.S12.SPGT.thm_12_1 G c.berge c.noK4 c.noPrism c.no1br
          A C B a₀ b₀ R₀ c.maxStaircase s hsK
      fin_cases i
      · simp only [Matrix.cons_val_zero] at hi
        exact hi.2.1.resolve_right (fun hn => hn hsA)
      · simp only [Matrix.cons_val_one, Matrix.head_cons] at hi
        rcases hi.2 with hld | hrd | hcent
        · exact False.elim (hsb (hld.2 b₀ (Or.inr rfl)))
        · exact False.elim (hst (hrd.2 t (Or.inl htB)))
        · exact False.elim (hst (hcent.2.1 t (Or.inr htB)))
      · simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hi
        rcases hi with hls | hrs
        · exact hls.1
        · exact False.elim (hst (hrs.1.2.1 t htB))
  have hcore (s t : V) (hs : s ∈ Ys G A C B x ∪ B)
      (ht : t ∈ Ys G A C B x ∪ B) (hst : ¬ G.Adj s t) (hsne : s ≠ t)
      (hsb : ¬ G.Adj s b₀) :
      ∃ p : List V, IsPathFrom G p s t ∧
        (∀ z ∈ SPGT.interior p, z ∈ A ∪ C) ∧ Even (pathLength p) := by
    have hsY : s ∈ Ys G A C B x := by
      rcases hs with hsY | hsB
      · exact hsY
      · exact False.elim (hsb (c.rightStar_b₀.2.1 s hsB).symm)
    rcases ht with htY | htB
    · obtain ⟨a, ha⟩ := c.Ane
      have hat : G.Adj a t := (hAcomp t htY a ha).symm
      have hsnot : s ∉ [a, t] := by
        simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false]
        rintro (hsa | hst')
        · exact hsY.1 (hsa ▸ Or.inl (Or.inl ha))
        · exact hsne hst'
      have hp : IsPathFrom G [s, a, t] s t := by
        apply isPathFrom_cons (S := [a, t])
        · exact ⟨PathBasics.isPathList_pair hat, rfl, rfl⟩
        · exact hsnot
        · intro z hz
          simp only [List.mem_cons, List.mem_singleton, List.mem_nil_iff, or_false] at hz
          rcases hz with hza | hzt
          · subst z
            exact ⟨fun _ => rfl, fun _ => hAcomp s hsY a ha⟩
          · subst z
            refine ⟨fun hadj => False.elim (hst hadj), ?_⟩
            intro hta
            have htA : t ∈ A := hta.symm ▸ ha
            exact False.elim (htY.1 (Or.inl (Or.inl htA)))
      refine ⟨[s, a, t], hp, ?_, ⟨1, by rfl⟩⟩
      intro z hz
      have : SPGT.interior ([s, a, t] : List V) = [a] := rfl
      rw [this] at hz
      have hza : z = a := by simpa using hz
      exact Or.inl (hza ▸ ha)
    · have hleft : IsLeftStar G A C B s := hleft_of_Y s t hsY htB hsb hst
      obtain ⟨a, R, hR⟩ := rung_of_mem_B c.stepConn htB
      have hsnotR : s ∉ R := by
        intro hsR
        by_cases hsa : s = a
        · exact hsY.1 (Or.inl (Or.inl (hsa ▸ hR.2.1)))
        by_cases hst' : s = t
        · exact hsne hst'
        have hsint : s ∈ SPGT.interior R :=
          (PathBasics.mem_interior_iff_of_pathFrom hR.1).mpr ⟨hsR, hsa, hst'⟩
        exact hsY.1 (Or.inr (hR.2.2.2.2.2 s hsint))
      have hadj : ∀ z ∈ R, (G.Adj s z ↔ z = a) := by
        intro z hz
        constructor
        · intro hsz
          by_cases hza : z = a
          · exact hza
          by_cases hzt : z = t
          · exact False.elim (hst (hzt ▸ hsz))
          · have hzint : z ∈ SPGT.interior R :=
              (PathBasics.mem_interior_iff_of_pathFrom hR.1).mpr ⟨hz, hza, hzt⟩
            exact False.elim (hleft.2.2 z (Or.inr (hR.2.2.2.2.2 z hzint)) hsz)
        · intro hza
          exact hza ▸ hleft.2.1 a hR.2.1
      have hp : IsPathFrom G (s :: R) s t := isPathFrom_cons hR.1 hsnotR hadj
      have hpint : ∀ z ∈ SPGT.interior (s :: R), z ∈ A ∪ C := by
        intro z hz
        rw [PathBasics.mem_interior_iff_of_pathFrom hp] at hz
        obtain ⟨hzmem, hzs, hzt⟩ := hz
        have hzR : z ∈ R := by
          rcases List.mem_cons.mp hzmem with h | h
          · exact False.elim (hzs h)
          · exact h
        by_cases hza : z = a
        · exact Or.inl (hza ▸ hR.2.1)
        · exact Or.inr (hR.2.2.2.2.2 z
            ((PathBasics.mem_interior_iff_of_pathFrom hR.1).mpr ⟨hzR, hza, hzt⟩))
      have hRodd :=
        (_root_.Workspace.Statements.S11.SPGT.thm_11_3 G c.berge c.noPrism A C B
          c.stepConn a₀ b₀ R₀ c.banister).1 a R t hR
      obtain ⟨k, hk⟩ := hRodd
      have hRlen := PathBasics.length_eq_pathLength_add_one hR.1.1
      have hplen : pathLength (s :: R) = R.length := PathBasics.pathLength_cons s R
      refine ⟨s :: R, hp, hpint, ⟨k + 1, ?_⟩⟩
      omega
  by_cases hub : G.Adj u b₀
  · by_cases hvb : G.Adj v b₀
    · exact heven_if_both u v hu hv huv hne hub hvb
    · obtain ⟨p, hp, hpint, heven⟩ :=
        hcore v u hv hu (fun h => huv h.symm) hne.symm hvb
      refine ⟨p.reverse, PathBasics.isPathFrom_reverse hp, ?_, ?_⟩
      · intro z hz
        exact hpint z ((PathBasics.mem_interior_reverse).mp hz)
      · simpa only [PathBasics.pathLength_reverse] using heven
  · exact hcore u v hu hv huv hne hub

end Workspace.ProofLemmas.Thm133EvenPath
