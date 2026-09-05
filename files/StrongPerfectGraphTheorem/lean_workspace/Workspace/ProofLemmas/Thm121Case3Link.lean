import Mathlib
import Workspace.Types.Core
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Statements.S11.Thm_11_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.Thm121C3PathCons

/-!
# The application of 11.2 inside case (3) of the proof of 12.1
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm121Case3Link

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- Two `getElem`s at provably equal indices agree.  Stated as a lemma to avoid the
"motive is not type correct" failure of rewriting an index in place. -/
private theorem getElem_eq_of_eq {V : Type*} {l : List V} {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i]'hi = l[j]'hj := by
  subst h; rfl

/-- The paper's *"take the neighbour of `v` closest to `b₀` along `R₀`"*: among the positions
`k ≥ 1` of `l` at which `v` has a neighbour, there is a largest one. -/
private theorem exists_max_adj {V : Type*} (G : SimpleGraph V) (v : V) (l : List V)
    (k0 : ℕ) (hk0 : k0 < l.length) (hk01 : 1 ≤ k0) (hk0adj : G.Adj v (l[k0]'hk0)) :
    ∃ (i : ℕ) (hilt : i < l.length), 1 ≤ i ∧ G.Adj v (l[i]'hilt) ∧
      ∀ (m : ℕ) (hm : m < l.length), i < m → ¬ G.Adj v (l[m]'hm) := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ, T = (Finset.range l.length).filter
      (fun k => 1 ≤ k ∧ ∃ h : k < l.length, G.Adj v (l[k]'h)) := ⟨_, rfl⟩
  have hmemT : ∀ k : ℕ,
      k ∈ T ↔ (k < l.length ∧ 1 ≤ k ∧ ∃ h : k < l.length, G.Adj v (l[k]'h)) := by
    intro k
    rw [hT, Finset.mem_filter, Finset.mem_range]
  have hne : T.Nonempty := ⟨k0, (hmemT k0).mpr ⟨hk0, hk01, hk0, hk0adj⟩⟩
  obtain ⟨hlt, h1, _, hadj⟩ := (hmemT _).mp (Finset.max'_mem T hne)
  refine ⟨T.max' hne, hlt, h1, hadj, ?_⟩
  intro m hm hgt hadjm
  have hle : m ≤ T.max' hne := Finset.le_max' T m ((hmemT m).mpr ⟨hm, by omega, hm, hadjm⟩)
  omega

/-- **"If `v` has a neighbour in `R₀*`, then by 11.2 it is either `B`-complete … or a
left-star."** -/
theorem thm121Case3Link {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hS : StepConnected G A C B) (hban : IsBanister G A C B a₀ R₀ b₀)
    (hlen : 3 ≤ SPGT.pathLength R₀)
    (v : V) (hv : v ∉ staircaseVertices A C B R₀)
    (hvS : ∃ x ∈ A ∪ B ∪ C, G.Adj v x)
    (ha : G.Adj v a₀) (hb : ¬ G.Adj v b₀)
    (hint : ∃ x ∈ SPGT.interior R₀, G.Adj v x) :
    SPGT.VertexComplete G v B ∨ IsLeftStar G A C B v := by
  classical
  obtain ⟨hR0, hR0S, hlstar, hrstar, hantiint⟩ := id hban
  have hlp : SPGT.pathLength R₀ = R₀.length - 1 := rfl
  rw [hlp] at hlen
  have hlen4 : 4 ≤ R₀.length := by omega
  have hjlt : R₀.length - 1 < R₀.length := by omega
  have ha0 : R₀[0]'(show 0 < R₀.length by omega) = a₀ :=
    PathBasics.getElem_zero_of_head? hR0.2.1 (by omega)
  have hb0 : R₀[R₀.length - 1]'hjlt = b₀ :=
    PathBasics.getElem_last_of_getLast? hR0.2.2 (by omega)
  have ha0mem : a₀ ∈ R₀ := PathBasics.head_mem hR0.2.1
  have hb0mem : b₀ ∈ R₀ := PathBasics.getLast_mem hR0.2.2
  have hvABC : v ∉ A ∪ B ∪ C := fun h => hv (Set.mem_union_right _ h)
  have hvR0 : v ∉ R₀ := fun h => hv (Set.mem_union_left _ h)
  have ha0b0 : a₀ ≠ b₀ := by
    rw [← ha0, ← hb0]
    exact PathBasics.path_ne_of_ne_index hR0.1 (by omega) hjlt (by omega)
  -- the neighbour of `v` on `R₀` closest to `b₀`
  obtain ⟨x, hxint, hvx⟩ := hint
  obtain ⟨k0, hk0, hk01, hk02, hk0x⟩ :=
    PathBasics.exists_getElem_of_mem_interior hR0.1 hxint
  have hk0adj : G.Adj v (R₀[k0]'hk0) := by rw [hk0x]; exact hvx
  obtain ⟨i, hilt, hi1, hiadj, hmax⟩ := exists_max_adj G v R₀ k0 hk0 hk01 hk0adj
  have hi2 : i + 2 ≤ R₀.length := by
    by_contra hcon
    refine hb ?_
    have hii : (R₀[i]'hilt) = b₀ := by
      rw [getElem_eq_of_eq hilt hjlt (show i = R₀.length - 1 by omega)]
      exact hb0
    rw [← hii]; exact hiadj
  have hij : i < R₀.length - 1 := by omega
  -- the stretch of `R₀` from that neighbour to `b₀`
  have hvQ0 : v ∉ (R₀.drop i).take (R₀.length - 1 - i + 1) := fun hh =>
    hvR0 (List.mem_of_mem_drop (List.mem_of_mem_take hh))
  have hadjQ0 : ∀ y ∈ (R₀.drop i).take (R₀.length - 1 - i + 1),
      (G.Adj v y ↔ y = R₀[i]'hilt) := by
    intro y hy
    obtain ⟨k, hk, hk1, hk2, hky⟩ :=
      (PathBasics.mem_slice_iff R₀ (le_of_lt hij) hjlt).mp hy
    constructor
    · intro hadj
      have hkeq : k = i := by
        by_contra hnee
        exact hmax k hk (by omega) (by rw [hky]; exact hadj)
      rw [← hky, getElem_eq_of_eq hk hilt hkeq]
    · intro hyi
      rw [hyi]; exact hiadj
  have hQ : IsPathFrom G (v :: (R₀.drop i).take (R₀.length - 1 - i + 1)) v b₀ := by
    have hslice := PathBasics.isPathFrom_slice hR0.1 hij hjlt
    have hcons := Thm121C3PathCons.isPathFrom_cons hslice hvQ0 hadjQ0
    rw [hb0] at hcons
    exact hcons
  have hP : IsPathFrom G [v, a₀] v a₀ :=
    ⟨PathBasics.isPathList_pair ha, by simp, by simp⟩
  have hPavoid : ∀ w ∈ [v, a₀], w ∉ (A ∪ B ∪ C) ∪ ({b₀} : Set V) := by
    intro w hw hcon
    have hw' : w = v ∨ w = a₀ := by simpa using hw
    rcases hw' with rfl | rfl
    · rcases hcon with h | h
      · exact hvABC h
      · exact hvR0 (by rw [(h : w = b₀)]; exact hb0mem)
    · rcases hcon with h | h
      · exact hR0S w ha0mem h
      · exact ha0b0 h
  have hQavoid : ∀ w ∈ v :: (R₀.drop i).take (R₀.length - 1 - i + 1),
      w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V) := by
    intro w hw hcon
    rcases List.mem_cons.mp hw with rfl | hwQ
    · rcases hcon with h | h
      · exact hvABC h
      · exact hvR0 (by rw [(h : w = a₀)]; exact ha0mem)
    · have hwR : w ∈ R₀ := List.mem_of_mem_drop (List.mem_of_mem_take hwQ)
      rcases hcon with h | h
      · exact hR0S w hwR h
      · obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
          (PathBasics.mem_slice_iff R₀ (le_of_lt hij) hjlt).mp hwQ
        have hne0 : (R₀[k]'hk) ≠ (R₀[0]'(show 0 < R₀.length by omega)) :=
          PathBasics.path_ne_of_ne_index hR0.1 hk (by omega) (by omega)
        exact hne0 (by rw [hkw, (h : w = a₀), ← ha0])
  have hPQint : SPGT.Anticomplete G
      ({w : V | w ∈ SPGT.interior [v, a₀]} ∪
        {w : V | w ∈ SPGT.interior (v :: (R₀.drop i).take (R₀.length - 1 - i + 1))})
      (A ∪ B ∪ C) := by
    rintro w (hw | hw)
    · exact absurd hw (by simp [SPGT.interior])
    · obtain ⟨hwmem, hwv, hwb⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw
      have hwQ : w ∈ (R₀.drop i).take (R₀.length - 1 - i + 1) := by
        rcases List.mem_cons.mp hwmem with h | h
        · exact absurd h hwv
        · exact h
      obtain ⟨k, hk, hk1, hk2, hkw⟩ :=
        (PathBasics.mem_slice_iff R₀ (le_of_lt hij) hjlt).mp hwQ
      have hkne : k ≠ R₀.length - 1 := by
        intro hcon
        exact hwb (by rw [← hkw, getElem_eq_of_eq hk hjlt hcon]; exact hb0)
      have hwint : w ∈ SPGT.interior R₀ := by
        rw [← hkw]
        exact PathBasics.getElem_mem_interior hR0.1 hk (by omega) (by omega)
      exact hantiint w hwint
  exact _root_.Workspace.Statements.S11.SPGT.thm_11_2 G hG hK4 A C B hS a₀ b₀ R₀ hban v
    hvABC hvS hb [v, a₀] (v :: (R₀.drop i).take (R₀.length - 1 - i + 1)) hP hPavoid hQ
    hQavoid hPQint

end Workspace.ProofLemmas.Thm121Case3Link
