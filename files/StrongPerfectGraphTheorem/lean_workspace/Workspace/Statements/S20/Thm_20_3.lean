import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.Types.TriangleCatching
import Workspace.Statements.S17.Thm_17_1
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S15.Thm_15_7
import Workspace.Statements.S18.Thm_18_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ReflectionAntihole
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.WheelConverse
import Workspace.ProofLemmas.OptimalWheelChoice
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.YDiamondTruncation
import Workspace.ProofLemmas.Thm203Prelim
import Workspace.ProofLemmas.Thm203AntipathTools
import Workspace.ProofLemmas.Thm203Step1
import Workspace.ProofLemmas.Thm203Step3Aux
import Workspace.ProofLemmas.Thm203Step3CaseB
import Workspace.ProofLemmas.Thm203Endgame

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Scratch203

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.Types.TriangleCatching Workspace.Types.TriangleCatching.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's `A_{t−3} ∪ V(R \ q)`, where `R = r₁-⋯-r_n` has `r₁ = q`. -/
def SRset (A3 : Set V) (R : List V) : Set V := A3 ∪ {v : V | v ∈ R.tail}

theorem mem_SRset {A3 : Set V} {R : List V} {v : V} :
    v ∈ SRset A3 R ↔ v ∈ A3 ∨ v ∈ R.tail := Iff.rfl

/-- Connectivity of `A₃ ∪ V(R \ q)`. -/
theorem connectedSet_SRset {G : SimpleGraph V} {A3 : Set V} (hA3 : ConnectedSet G A3)
    {R : List V} {q rn : V} (hR : IsPathFrom G R q rn) (hrn : rn ∈ A3) (hqrn : q ≠ rn) :
    ConnectedSet G (SRset A3 R) := by
  classical
  have hlen : 2 ≤ R.length := by
    by_contra hcon
    have h1 : R.length = 1 := by
      have := PathBasics.path_length_pos hR.1
      omega
    have hhead : R.head? = some q := hR.2.1
    have hlast : R.getLast? = some rn := hR.2.2
    match R, h1 with
    | [a], _ =>
      simp at hhead hlast
      exact hqrn (hhead.symm.trans hlast)
  have htail : IsPathList G R.tail := by
    have := PathBasics.isPathList_drop hR.1 (k := 1) (by omega)
    simpa using this
  have hrnmem : rn ∈ R.tail := by
    have hlast : R.getLast? = some rn := hR.2.2
    have hmem : rn ∈ R := PathBasics.getLast_mem hlast
    match R, hlen with
    | a :: rest, _ =>
      have hhead : a = q := by
        have := hR.2.1
        simpa using this
      rcases List.mem_cons.mp hmem with h | h
      · exact absurd (h.trans hhead) (Ne.symm hqrn)
      · simpa using h
  refine ConnectedSetUnionAttach.connectedSet_union hA3
    (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList htail) ?_
  exact Or.inl ⟨rn, hrn, hrnmem⟩

/-- `q` has a neighbour in `V(R \ q)` when `R` is a path from `q` to some `rn ≠ q`. -/
theorem exists_adj_tail {G : SimpleGraph V} {R : List V} {q rn : V}
    (hR : IsPathFrom G R q rn) (hqrn : q ≠ rn) : ∃ s ∈ R.tail, G.Adj q s := by
  obtain ⟨hp, hh, hl⟩ := hR
  match R with
  | [] => exact absurd rfl hp.1
  | [a] =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      exact absurd (hh.symm.trans hl) hqrn
  | a :: b :: rest =>
      have ha : a = q := by simpa using hh
      refine ⟨b, by simp, ?_⟩
      have h2 : G.Adj ((a :: b :: rest)[0]) ((a :: b :: rest)[1]) :=
        PathBasics.path_adj_succ hp (i := 0) (by simp)
      simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h2
      exact ha ▸ h2

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
theorem gidx {W : Type*} (q : List W) {i j : ℕ} (h : i = j)
    (hi : i < q.length) (hj : j < q.length) : q[i]'hi = q[j]'hj := by
  subst h; rfl

/-- For a `Nodup` list, the rotation with a prescribed head is unique.  This is what turns
`IsLeapForHole`'s existential rotation into the concrete cut of the cycle. -/
theorem rotate_eq_of_head {α : Type*} {L : List α} (hnd : L.Nodup)
    {i j : ℕ} (hj : j < L.length) {v : α}
    (hi : (L.rotate i).head? = some v) (hjv : L[j]'hj = v) :
    L.rotate i = L.rotate j := by
  have hpos : 0 < L.length := by omega
  have hlenr : (L.rotate i).length = L.length := List.length_rotate ..
  have hposr : 0 < (L.rotate i).length := by omega
  have hmod : (0 + i) % L.length < L.length := Nat.mod_lt _ hpos
  have hg : ((L.rotate i)[0]'hposr) = L[(0 + i) % L.length]'hmod := by
    simp only [List.getElem_rotate, List.length_rotate]
  have hhead : ((L.rotate i)[0]'hposr) = v := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hposr] at hi
    exact Option.some_injective _ hi
  have heq : L[(0 + i) % L.length]'hmod = L[j]'hj := by rw [← hg, hhead, hjv]
  have hidx : (0 + i) % L.length = j := (List.Nodup.getElem_inj_iff hnd).mp heq
  have hij : i % L.length = j := by simpa using hidx
  rw [← List.rotate_mod L i, hij]

/-- `18.2` names the second- and third-to-last vertices of a path through `dropLast`;
these two lemmas convert that to indices. -/
theorem getLast?_dropLast_getElem {α : Type*} (l : List α) (hl : 2 ≤ l.length) :
    l.dropLast.getLast? = some (l[l.length - 2]'(by omega)) := by
  have hd : l.dropLast.length = l.length - 1 := List.length_dropLast
  rw [List.getLast?_eq_getElem?,
    List.getElem?_eq_getElem (show l.dropLast.length - 1 < l.dropLast.length by omega)]
  congr 1
  rw [List.getElem_dropLast]
  exact gidx l (by omega) (by omega) (by omega)

theorem getLast?_dropLast_dropLast_getElem {α : Type*} (l : List α) (hl : 3 ≤ l.length) :
    l.dropLast.dropLast.getLast? = some (l[l.length - 3]'(by omega)) := by
  have hd : l.dropLast.length = l.length - 1 := List.length_dropLast
  rw [getLast?_dropLast_getElem l.dropLast (by omega)]
  congr 1
  rw [List.getElem_dropLast]
  exact gidx l (by omega) (by omega) (by omega)

theorem ncard_le_one_of_subset_singleton {S : Set V} {w : V} (h : S ⊆ {w}) : S.ncard ≤ 1 := by
  have := Set.ncard_le_ncard h (Set.finite_singleton w)
  simpa using this

/-- The three named vertices of a triangle written `{b₁,b₂,b₃}` are pairwise distinct. -/
theorem triangle_ne {G : SimpleGraph V} {b₁ b₂ b₃ : V}
    (h : IsTriangle G ({b₁, b₂, b₃} : Set V)) : b₁ ≠ b₂ ∧ b₁ ≠ b₃ ∧ b₂ ≠ b₃ := by
  have hcard : ({b₁, b₂, b₃} : Set V).ncard = 3 := h.1
  have hpair : ∀ a b : V, ({a, b} : Set V).ncard ≤ 2 := by
    intro a b
    have := Set.ncard_insert_le a ({b} : Set V)
    simpa using this
  refine ⟨?_, ?_, ?_⟩ <;> intro he
  · have hset : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
      ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, he]; tauto
    rw [hset] at hcard
    have := hpair b₂ b₃; omega
  · have hset : ({b₁, b₂, b₃} : Set V) = ({b₂, b₃} : Set V) := by
      ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, he]; tauto
    rw [hset] at hcard
    have := hpair b₂ b₃; omega
  · have hset : ({b₁, b₂, b₃} : Set V) = ({b₁, b₃} : Set V) := by
      ext v; simp only [Set.mem_insert_iff, Set.mem_singleton_iff, he]; tauto
    rw [hset] at hcard
    have := hpair b₁ b₃; omega

/-- From a reflection of the triangle `{a₁,a₂,a₃}`: two distinct vertices `u ≠ v` of the
triangle have *adjacent* partners `bu`, `bv` in the reflecting triangle. -/
theorem reflection_pair {G : SimpleGraph V} {a₁ a₂ a₃ b₁ b₂ b₃ : V}
    (h : IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃)
    {u v : V} (hu : u ∈ ({a₁, a₂, a₃} : Set V)) (hv : v ∈ ({a₁, a₂, a₃} : Set V))
    (huv : u ≠ v) :
    ∃ bu ∈ ({b₁, b₂, b₃} : Set V), ∃ bv ∈ ({b₁, b₂, b₃} : Set V),
      G.Adj u bu ∧ G.Adj v bv ∧ G.Adj bu bv := by
  obtain ⟨hA, hB, hdisj, hiff⟩ := h
  obtain ⟨hb12, hb13, hb23⟩ := triangle_ne hB
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl huv
  · exact ⟨b₁, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb12⟩
  · exact ⟨b₁, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb13⟩
  · exact ⟨b₂, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) (Ne.symm hb12)⟩
  · exact absurd rfl huv
  · exact ⟨b₂, by simp, b₃, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) hb23⟩
  · exact ⟨b₃, by simp, b₁, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩),
      hB.2 _ (by simp) _ (by simp) (Ne.symm hb13)⟩
  · exact ⟨b₃, by simp, b₂, by simp,
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩)),
      (hiff _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩)),
      hB.2 _ (by simp) _ (by simp) (Ne.symm hb23)⟩
  · exact absurd rfl huv

/-- **The conclusion of 20.3's step (2)**, as a relation between the chosen `q` and the
chosen path `R = r₁-⋯-r_n` (with `r₁ = q` and `r_n = rn ∈ A_{t−3}`):

PAPER (printed p. 125): *"There is a vertex `q` in `A_{t−2}` adjacent to both `x_t` and
`x_{t−1}`, and a path `R` in `A_{t−2}` from `q` to `A_{t−3}` such that not both `x_t` and
`x_{t−1}` have neighbours in `A_{t−3} ∪ V(R \ q)`."* -/
def Cond2 (G : SimpleGraph V) (z : V) (A₀ : Set V) (x : ℕ → V) (t : ℕ)
    (q : V) (R : List V) (rn : V) : Prop :=
  q ∈ wheelSystemA G z A₀ x (t - 2) ∧ G.Adj q (x t) ∧ G.Adj q (x (t - 1)) ∧
  IsPathFrom G R q rn ∧ (∀ v ∈ R, v ∈ wheelSystemA G z A₀ x (t - 2)) ∧
  rn ∈ wheelSystemA G z A₀ x (t - 3) ∧
  ¬ ((∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj (x t) s) ∧
     (∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj (x (t - 1)) s))

/-- A vertex of a path other than its first vertex lies in the tail. -/
theorem mem_tail_of_ne_head {G : SimpleGraph V} {L : List V} {u v : V}
    (hL : IsPathFrom G L u v) {w : V} (hw : w ∈ L) (hne : w ≠ u) : w ∈ L.tail := by
  obtain ⟨hp, hh, hl⟩ := hL
  cases L with
  | nil => exact absurd rfl hp.1
  | cons c rest =>
      have hc : c = u := by simpa using hh
      simp only [List.tail_cons]
      rcases List.mem_cons.mp hw with hq | hq
      · exact absurd (hq.trans hc) hne
      · exact hq

/-- Each vertex of a reflected triangle is adjacent to its partner. -/
theorem reflection_partner {G : SimpleGraph V} {a₁ a₂ a₃ b₁ b₂ b₃ : V}
    (h : IsReflectionOfTriangle G a₁ a₂ a₃ b₁ b₂ b₃)
    {u : V} (hu : u ∈ ({a₁, a₂, a₃} : Set V)) :
    ∃ bu ∈ ({b₁, b₂, b₃} : Set V), G.Adj u bu := by
  obtain ⟨hA, hB, hdisj, hcross⟩ := h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · exact ⟨b₁, by simp, (hcross _ (by simp) _ (by simp)).mpr (Or.inl ⟨rfl, rfl⟩)⟩
  · exact ⟨b₂, by simp, (hcross _ (by simp) _ (by simp)).mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))⟩
  · exact ⟨b₃, by simp, (hcross _ (by simp) _ (by simp)).mpr (Or.inr (Or.inr ⟨rfl, rfl⟩))⟩

/-- The first vertex of a path does not lie in its tail. -/
theorem head_notMem_tail {G : SimpleGraph V} {R : List V} {u v : V}
    (hR : IsPathFrom G R u v) : u ∉ R.tail := by
  obtain ⟨hp, hh, hl⟩ := hR
  cases R with
  | nil => simp
  | cons a rest =>
      have ha : a = u := by simpa using hh
      simp only [List.tail_cons]
      rw [← ha]
      exact (List.nodup_cons.mp (PathBasics.path_nodup hp)).1

/-- **20.3, step (2), the leap branch of 2.10.**

PAPER (printed p. 125): *"Suppose it contains a leap; then there are nonadjacent `x_i, x_j ∈
X_{t−2}` such that `x_i-p₁-⋯-p_n-x_{t−1}-x_j` is an odd path.  Since `x_i, x_j` are
`Y ∪ {x_t}`-complete, it follows from 13.6 that this path contains another `Y ∪ {x_t}`-complete
vertex, which must be `p₁` since no others are adjacent to `x_t`.  Its ends are also
`Y ∪ {x_t, z}`-complete, and no internal vertex is `Y ∪ {x_t,z}`-complete, so by 13.6,
`Y ∪ {x_t, z}` is not anticonnected, that is, `z` is `Y`-complete.  But then let `C₁` be the
hole `z-x_i-p₁-⋯-p_n-x_{t−1}-z`; then `(C₁, Y)` is a wheel, a contradiction."* -/
theorem step2_leap_case {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {F : Set V} (hFconn : ConnectedSet G F)
    (hFsub : F ⊆ wheelSystemA G z A₀ x (t - 2))
    (P : List V) (hP : IsPathFrom G P (x t) (x (t - 1)))
    (hPint : ∀ v ∈ SPGT.interior P, v ∈ F) (hPeven : Even (pathLength P))
    (hPlen : 4 ≤ pathLength P) (hCh : IsHoleList G (z :: P))
    (a : V) (haX : a ∈ wheelSystemX x (t - 2))
    (b : V) (hbX : b ∈ wheelSystemX x (t - 2))
    (hleap : IsLeapForHole G (z :: P) z (x t) a b ∨
      IsLeapForHole G (z :: P) (x t) z a b) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hCnd : (z :: P).Nodup := HoleBasics.hole_nodup hCh
  have hPl : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  have hCl : (z :: P).length = P.length + 1 := by simp
  have hP0 : P[0]'(by omega) = x t := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hC0 : (z :: P)[0]'(by omega) = z := rfl
  have hC1 : (z :: P)[1]'(by omega) = x t := by
    simp only [List.getElem_cons_succ]; exact hP0
  have haxt : G.Adj a (x t) := (hXc a haX).symm
  have hbxt : G.Adj b (x t) := (hXc b hbX).symm
  have hbnez : b ≠ z := by
    obtain ⟨jb, hjb, hbje⟩ := hbX
    rw [hbje]; exact (hws.2.2.1 jb (by omega)).2
  have hbnext : b ≠ x t := fun h => G.irrefl (h ▸ hbxt)
  have hanez : a ≠ z := by
    obtain ⟨ja, hja, haje⟩ := haX
    rw [haje]; exact (hws.2.2.1 ja (by omega)).2
  have hanext : a ≠ x t := fun h => G.irrefl (h ▸ haxt)
  have hnd : P.Nodup := PathBasics.path_nodup hP.1
  have hPlast : P[P.length - 1]'(by omega) = x (t - 1) :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hxjF : ∀ j ≤ t, x j ∉ F := fun j hj hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj (hFsub hm)
  have hzFnadj : ∀ v ∈ F, ¬ G.Adj z v := fun v hv =>
    WheelSystemBasics.wheelSystemA_no_nbr (hFsub hv)
  have hYF : ∀ y ∈ Y, y ∉ F := fun y hy hm =>
    Thm203Prelim.Y_notMem_wheelSystemA hVC (show t - 2 < t by omega) hy (hFsub hm)
  have hPmem : ∀ w ∈ P, w = x t ∨ w = x (t - 1) ∨ w ∈ F := by
    intro w hw
    by_cases h1 : w = x t
    · exact Or.inl h1
    by_cases h2 : w = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hw, h1, h2⟩)))
  have hzF : z ∉ F := fun hm =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) (hFsub hm)
  have hzP : z ∉ P := by
    intro hm
    rcases hPmem z hm with h | h | h
    · exact (hws.2.2.1 t le_rfl).2 h.symm
    · exact (hws.2.2.1 (t - 1) (by omega)).2 h.symm
    · exact hzF h
  rcases hleap with hl | hl
  · -- PAPER: the printed orientation `x_i-p₁-⋯-p_n-x_{t−1}-x_j`
    obtain ⟨-, i, hhead, hlast, hlp⟩ := hl
    have hrot1 : (z :: P).rotate 1 = P ++ [z] := by simp [List.rotate_cons_succ]
    have hrot : (z :: P).rotate i = P ++ [z] := by
      rw [rotate_eq_of_head hCnd (j := 1) (by omega) hhead hC1, hrot1]
    rw [hrot] at hlp
    obtain ⟨hLp, hLlen, hab, hnab, hA, hB⟩ := hlp
    have hLen : (P ++ [z]).length = P.length + 1 := by simp
    have hdel : ∀ (w u : V), w ≠ z → w ≠ x t →
        ((G.deleteEdges {s(z, x t)}).Adj w u ↔ G.Adj w u) := by
      intro w u hwz hwx
      rw [SimpleGraph.deleteEdges_adj]
      refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
      exact ⟨fun hh => absurd hh hwz, fun hh => absurd hh hwx⟩
    have hAP : ∀ (k : ℕ) (hk : k < P.length), G.Adj a (P[k]'hk) ↔ (k = 0 ∨ k = 1) := by
      intro k hk
      have hk' : k < (P ++ [z]).length := by omega
      have hgel : (P ++ [z])[k]'hk' = P[k]'hk := List.getElem_append_left hk
      have h := hA k hk'
      rw [hgel, hdel a _ hanez hanext] at h
      rw [h]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr h1
        · exact absurd h1 (by omega)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl h1)
    have hBP : ∀ (k : ℕ) (hk : k < P.length),
        G.Adj b (P[k]'hk) ↔ (k = 0 ∨ k = P.length - 1) := by
      intro k hk
      have hk' : k < (P ++ [z]).length := by omega
      have hgel : (P ++ [z])[k]'hk' = P[k]'hk := List.getElem_append_left hk
      have h := hB k hk'
      rw [hgel, hdel b _ hbnez hbnext] at h
      rw [h]
      constructor
      · rintro (h1 | h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (by omega)
        · exact absurd h1 (by omega)
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (Or.inl (by omega))
    have hnabG : ¬ G.Adj a b := fun h => hnab ((hdel a b hanez hanext).mpr h)
    -- name the first two vertices of `P`: `P = x_t-p₁-⋯`
    obtain ⟨c0, c1, Prest, rfl⟩ : ∃ c0 c1 Prest, P = c0 :: c1 :: Prest := by
      match P, (show 2 ≤ P.length by omega) with
      | c0 :: c1 :: rest, _ => exact ⟨c0, c1, rest, rfl⟩
    have hc0 : c0 = x t := hP0
    have hPrest3 : 3 ≤ Prest.length := by
      have h1 : (c0 :: c1 :: Prest).length = Prest.length + 2 := by simp
      omega
    have hPrpath : IsPathList G (c1 :: Prest) := by
      have h := PathBasics.isPathList_drop hP.1 (k := 1) (by simp only [List.length_cons]; omega)
      simpa using h
    have hPr : IsPathFrom G (c1 :: Prest) c1 (x (t - 1)) :=
      ⟨hPrpath, rfl, by simpa using hP.2.2⟩
    have hac1 : G.Adj a c1 := by
      have h := (hAP 1 (by simp only [List.length_cons]; omega)).mpr (Or.inr rfl); simpa using h
    have hbx1 : G.Adj b (x (t - 1)) := by
      have h := (hBP ((c0 :: c1 :: Prest).length - 1) (by simp only [List.length_cons]; omega)).mpr (Or.inr rfl)
      rwa [hPlast] at h
    have hidx1 : ∀ v ∈ (c1 :: Prest), ∃ (k : ℕ) (hk : k < (c0 :: c1 :: Prest).length),
        1 ≤ k ∧ (c0 :: c1 :: Prest)[k]'hk = v := by
      intro v hv
      obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      exact ⟨k + 1, by simp only [List.length_cons] at hk ⊢; omega, by omega,
        by simpa using hkv⟩
    have hidx2 : ∀ v ∈ Prest, ∃ (k : ℕ) (hk : k < (c0 :: c1 :: Prest).length),
        2 ≤ k ∧ (c0 :: c1 :: Prest)[k]'hk = v := by
      intro v hv
      obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      exact ⟨k + 2, by simp only [List.length_cons] at hk ⊢; omega, by omega,
        by simpa using hkv⟩
    have hanadj : ∀ v ∈ Prest, ¬ G.Adj a v := by
      intro v hv hadj
      obtain ⟨k, hk, hk2, hkv⟩ := hidx2 v hv
      rw [← hkv] at hadj
      rcases (hAP k hk).mp hadj with h | h <;> omega
    have hbnadj : ∀ v ∈ (c1 :: Prest), v ≠ x (t - 1) → ¬ G.Adj b v := by
      intro v hv hvne hadj
      obtain ⟨k, hk, hk1, hkv⟩ := hidx1 v hv
      rw [← hkv] at hadj
      rcases (hBP k hk).mp hadj with h | h
      · omega
      · exact hvne (by rw [← hkv]; exact (gidx _ h hk (by omega)).trans hPlast)
    obtain ⟨ja, hja, haje⟩ := id haX
    obtain ⟨jb, hjb, hbje⟩ := id hbX
    have haP : a ∉ (c0 :: c1 :: Prest) := by
      intro hm
      rcases hPmem a hm with h | h | h
      · exact hanext h
      · have := hinj ja (by omega) (t - 1) (by omega) (haje.symm.trans h); omega
      · exact hxjF ja (by omega) (by rw [← haje]; exact h)
    have hbP : b ∉ (c0 :: c1 :: Prest) := by
      intro hm
      rcases hPmem b hm with h | h | h
      · exact hbnext h
      · have := hinj jb (by omega) (t - 1) (by omega) (hbje.symm.trans h); omega
      · exact hxjF jb (by omega) (by rw [← hbje]; exact h)
    have haP' : a ∉ (c1 :: Prest) := fun hm => haP (List.mem_cons_of_mem _ hm)
    have hbP' : b ∉ (c1 :: Prest) := fun hm => hbP (List.mem_cons_of_mem _ hm)
    have hsother : ∀ v ∈ (c1 :: Prest), v ≠ c1 → ¬ G.Adj a v := by
      intro v hv hvne
      rcases List.mem_cons.mp hv with h | h
      · exact absurd h hvne
      · exact hanadj v h
    -- PAPER: "`x_i-p₁-⋯-p_n-x_{t−1}-x_j` is an odd path"
    have hW : IsPathFrom G (a :: ((c1 :: Prest) ++ [b])) a b :=
      PathAttach.isPathFrom_cons_concat hPr hac1 hbx1 hnabG hab haP' hbP' hsother hbnadj
    have hWlen : (a :: ((c1 :: Prest) ++ [b])).length = (c0 :: c1 :: Prest).length + 1 := by
      simp
    have hWodd : Odd (pathLength (a :: ((c1 :: Prest) ++ [b]))) := by
      have h1 := PathBasics.pathLength_eq (a :: ((c1 :: Prest) ++ [b]))
      obtain ⟨k, hk⟩ := hPeven
      exact ⟨k, by omega⟩
    have hWmem : ∀ v ∈ (a :: ((c1 :: Prest) ++ [b])), v = a ∨ v ∈ (c1 :: Prest) ∨ v = b := by
      intro v hv
      rcases List.mem_cons.mp hv with h | h
      · exact Or.inl h
      · rcases List.mem_append.mp h with h' | h'
        · exact Or.inr (Or.inl h')
        · exact Or.inr (Or.inr (by simpa using h'))
    have hWlen5 : 5 ≤ pathLength (a :: ((c1 :: Prest) ++ [b])) := by
      have h1 := PathBasics.pathLength_eq (a :: ((c1 :: Prest) ++ [b]))
      omega
    -- PAPER: "Since `x_i, x_j` are `Y ∪ {x_t}`-complete, it follows from 13.6 that this path
    -- contains another `Y ∪ {x_t}`-complete vertex, which must be `p₁`"
    have hXanti : AnticonnectedSet G (Y ∪ {x t}) :=
      YDiamondTruncation.anticonnected_union_singleton hYanti (hxY t le_rfl) hnVC
    have hxtW : x t ∉ (a :: ((c1 :: Prest) ++ [b])) := by
      intro hm
      rcases hWmem _ hm with h | h | h
      · exact hanext h.symm
      · exact (List.nodup_cons.mp hnd).1 (by rw [hc0]; exact h)
      · exact hbnext h.symm
    have hYW : ∀ y ∈ Y, y ∉ (a :: ((c1 :: Prest) ++ [b])) := by
      intro y hy hm
      rcases hWmem _ hm with h | h | h
      · exact hxY ja (by omega) (by rw [← haje, ← h]; exact hy)
      · rcases hPmem y (List.mem_cons_of_mem _ h) with h' | h' | h'
        · exact hxY t le_rfl (by rw [← h']; exact hy)
        · exact hxY (t - 1) (by omega) (by rw [← h']; exact hy)
        · exact hYF y hy h'
      · exact hxY jb (by omega) (by rw [← hbje, ← h]; exact hy)
    have hXP : (Y ∪ {x t}) ⊆ {v : V | v ∈ (a :: ((c1 :: Prest) ++ [b]))}ᶜ := by
      rintro v (hv | hv) hm
      · exact hYW v hv hm
      · rw [Set.mem_singleton_iff] at hv; exact hxtW (by rw [← hv]; exact hm)
    have haC : VertexComplete G a (Y ∪ {x t}) := by
      rintro w (hw | hw)
      · rw [haje]; exact hVC ja (by omega) w hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact haxt
    have hbC : VertexComplete G b (Y ∪ {x t}) := by
      rintro w (hw | hw)
      · rw [hbje]; exact hVC jb (by omega) w hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hbxt
    have hcomplW : ∀ w ∈ (a :: ((c1 :: Prest) ++ [b])),
        VertexComplete G w (Y ∪ {x t}) → w = a ∨ w = b ∨ w = c1 := by
      intro w hw hwc
      have hwxt : G.Adj w (x t) := hwc (x t) (Or.inr rfl)
      rcases hWmem w hw with h | h | h
      · exact Or.inl h
      · rcases List.mem_cons.mp h with h' | h'
        · exact Or.inr (Or.inr h')
        · exfalso
          obtain ⟨k, hk, hk2, hkv⟩ := hidx2 w h'
          refine PathBasics.path_not_adj_of_gap hP.1 (i := 0) (j := k) (by omega) hk
            (by omega) (by omega) ?_
          rw [hkv]
          show G.Adj c0 w
          rw [hc0]; exact hwxt.symm
      · exact Or.inr (Or.inl h)
    have hc1c : VertexComplete G c1 (Y ∪ {x t}) := by
      rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5
        (a :: ((c1 :: Prest) ++ [b])) a b hW hWodd (Y ∪ {x t}) hXP hXanti haC hbC
        with hedge | hlen3
      · obtain ⟨u, hu, v, hv, huv, huc, hvc⟩ := hedge
        by_cases hu1 : u = c1
        · rw [hu1] at huc; exact huc
        by_cases hv1 : v = c1
        · rw [hv1] at hvc; exact hvc
        exfalso
        rcases hcomplW u hu huc with hu' | hu' | hu'
        · rcases hcomplW v hv hvc with hv' | hv' | hv'
          · rw [hu', hv'] at huv; exact G.irrefl huv
          · rw [hu', hv'] at huv; exact hnabG huv
          · exact hv1 hv'
        · rcases hcomplW v hv hvc with hv' | hv' | hv'
          · rw [hu', hv'] at huv; exact hnabG huv.symm
          · rw [hu', hv'] at huv; exact G.irrefl huv
          · exact hv1 hv'
        · exact hu1 hu'
      · exact absurd hlen3.1 (by omega)
    -- PAPER: "so by 13.6, `Y ∪ {x_t, z}` is not anticonnected, that is, `z` is `Y`-complete"
    have hc1F : c1 ∈ F := by
      have h : ((c0 :: c1 :: Prest)[1]'(by simp only [List.length_cons]; omega))
          ∈ SPGT.interior (c0 :: c1 :: Prest) :=
        PathBasics.getElem_mem_interior hP.1 (by simp only [List.length_cons]; omega)
          (by omega) (by simp only [List.length_cons]; omega)
      exact hPint _ h
    have hzc1n : ¬ G.Adj z c1 := hzFnadj c1 hc1F
    have hzYC : VertexComplete G z Y := by
      by_contra hznc
      have hzne : z ∉ (Y ∪ {x t}) := by
        rintro (h | h)
        · exact hzY h
        · rw [Set.mem_singleton_iff] at h; exact (hws.2.2.1 t le_rfl).2 h.symm
      have hznc' : ¬ VertexComplete G z (Y ∪ {x t}) := fun hcon =>
        hznc (fun y hy => hcon y (Or.inl hy))
      have hX'anti : AnticonnectedSet G (Y ∪ {x t, z}) := by
        have h2 := YDiamondTruncation.anticonnected_union_singleton hXanti hzne hznc'
        have hset : (Y ∪ {x t}) ∪ {z} = Y ∪ {x t, z} := by
          ext v; simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
        rwa [hset] at h2
      have hX'P : (Y ∪ {x t, z}) ⊆ {v : V | v ∈ (a :: ((c1 :: Prest) ++ [b]))}ᶜ := by
        rintro v (hv | hv) hm
        · exact hYW v hv hm
        · rcases hv with hv | hv
          · exact hxtW (by rw [← hv]; exact hm)
          · rw [Set.mem_singleton_iff] at hv
            rcases hWmem _ hm with h | h | h
            · exact hanez (by rw [← hv, ← h])
            · exact hzP (List.mem_cons_of_mem _ (by rw [← hv]; exact h))
            · exact hbnez (by rw [← hv, ← h])
      have haC' : VertexComplete G a (Y ∪ {x t, z}) := by
        rintro w (hw | hw)
        · rw [haje]; exact hVC ja (by omega) w hw
        · rcases hw with hw | hw
          · rw [hw]; exact haxt
          · rw [Set.mem_singleton_iff] at hw; rw [hw, haje]
            exact (hzadj ja (by omega)).symm
      have hbC' : VertexComplete G b (Y ∪ {x t, z}) := by
        rintro w (hw | hw)
        · rw [hbje]; exact hVC jb (by omega) w hw
        · rcases hw with hw | hw
          · rw [hw]; exact hbxt
          · rw [Set.mem_singleton_iff] at hw; rw [hw, hbje]
            exact (hzadj jb (by omega)).symm
      rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5
        (a :: ((c1 :: Prest) ++ [b])) a b hW hWodd (Y ∪ {x t, z}) hX'P hX'anti haC' hbC'
        with hedge | hlen3
      · obtain ⟨u, hu, v, hv, huv, huc, hvc⟩ := hedge
        have hmono : ∀ w, VertexComplete G w (Y ∪ {x t, z}) →
            VertexComplete G w (Y ∪ {x t}) := by
          rintro w hwc s (hs | hs)
          · exact hwc s (Or.inl hs)
          · rw [Set.mem_singleton_iff] at hs; exact hwc s (Or.inr (Or.inl hs))
        have hnc1 : ∀ w, w = c1 → ¬ VertexComplete G w (Y ∪ {x t, z}) := by
          rintro w rfl hcon
          exact hzc1n (hcon z (Or.inr (Or.inr rfl))).symm
        rcases hcomplW u hu (hmono u huc) with hu' | hu' | hu'
        · rcases hcomplW v hv (hmono v hvc) with hv' | hv' | hv'
          · rw [hu', hv'] at huv; exact G.irrefl huv
          · rw [hu', hv'] at huv; exact hnabG huv
          · exact hnc1 v hv' hvc
        · rcases hcomplW v hv (hmono v hvc) with hv' | hv' | hv'
          · rw [hu', hv'] at huv; exact hnabG huv.symm
          · rw [hu', hv'] at huv; exact G.irrefl huv
          · exact hnc1 v hv' hvc
        · exact hnc1 u hu' huc
      · exact absurd hlen3.1 (by omega)
    -- PAPER: "let `C₁` be the hole `z-x_i-p₁-⋯-p_n-x_{t−1}-z`; then `(C₁, Y)` is a wheel"
    have hac1path : IsPathFrom G (a :: (c1 :: Prest)) a (x (t - 1)) :=
      PathAttach.isPathFrom_cons hPr hac1 haP' hsother
    have hza : G.Adj z a := by rw [haje]; exact hzadj ja (by omega)
    have hzW' : z ∉ (a :: (c1 :: Prest)) := by
      intro hm
      rcases List.mem_cons.mp hm with h | h
      · exact hanez h.symm
      · exact hzP (List.mem_cons_of_mem _ h)
    have hzint : ∀ v ∈ SPGT.interior (a :: (c1 :: Prest)), ¬ G.Adj z v := by
      intro v hv
      obtain ⟨hvm, hva, hvx1⟩ := (PathBasics.mem_interior_iff_of_pathFrom hac1path).mp hv
      have hvin : v ∈ (c1 :: Prest) := by
        rcases List.mem_cons.mp hvm with h | h
        · exact absurd h hva
        · exact h
      have hvxt : v ≠ x t := by
        intro h
        exact (List.nodup_cons.mp hnd).1 (by rw [hc0, ← h]; exact hvin)
      exact hzFnadj v (hPint v ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
        ⟨List.mem_cons_of_mem _ hvin, hvxt, hvx1⟩))
    have hC1hole : IsHoleList G (z :: (a :: (c1 :: Prest))) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hac1path ?_ hza
        (hzadj (t - 1) (by omega)) hzW' hzint
      have h1 := PathBasics.pathLength_eq (a :: (c1 :: Prest))
      simp only [List.length_cons] at h1 ⊢
      omega
    have haY : VertexComplete G a Y := by rw [haje]; exact hVC ja (by omega)
    have hc1Y : VertexComplete G c1 Y := fun y hy => hc1c y (Or.inl hy)
    have hx1Y : VertexComplete G (x (t - 1)) Y := hVC (t - 1) (by omega)
    have hC1Y : ∀ w ∈ (z :: (a :: (c1 :: Prest))), w ∉ Y := by
      intro w hw hwY
      rcases List.mem_cons.mp hw with h | h
      · exact hzY (by rw [← h]; exact hwY)
      · rcases List.mem_cons.mp h with h' | h'
        · exact hxY ja (by omega) (by rw [← haje, ← h']; exact hwY)
        · rcases hPmem w (List.mem_cons_of_mem _ h') with h'' | h'' | h''
          · exact hxY t le_rfl (by rw [← h'']; exact hwY)
          · exact hxY (t - 1) (by omega) (by rw [← h'']; exact hwY)
          · exact hYF w hwY h''
    have hC1len : 6 ≤ holeLength (z :: (a :: (c1 :: Prest))) := by
      simp only [holeLength, List.length_cons]
      omega
    have hax1 : a ≠ x (t - 1) := by
      intro h; have := hinj ja (by omega) (t - 1) (by omega) (haje.symm.trans h); omega
    have hzc1ne : z ≠ c1 := by intro h; exact hzP (by rw [h]; simp)
    have h3 : 3 ≤ OptimalWheelChoice.yEdgeCount G Y (z :: (a :: (c1 :: Prest))) := by
      rw [OptimalWheelChoice.yEdgeCount_def]
      have hsub : ({s(z, a), s(a, c1), s(x (t - 1), z)} : Set (Sym2 V)) ⊆
          {e : Sym2 V | ∃ u ∈ (z :: (a :: (c1 :: Prest))), ∃ v ∈ (z :: (a :: (c1 :: Prest))),
            e = s(u, v) ∧ EdgeComplete G Y u v} := by
        rintro e (rfl | rfl | rfl)
        · exact ⟨z, by simp, a, by simp, rfl, hza, hzYC, haY⟩
        · exact ⟨a, by simp, c1, by simp, rfl, hac1, haY, hc1Y⟩
        · exact ⟨x (t - 1), List.mem_cons_of_mem _
            (PathBasics.isPathFrom_ends_mem hac1path).2, z, by simp, rfl,
            (hzadj (t - 1) (by omega)).symm, hx1Y, hzYC⟩
      have hcard : ({s(z, a), s(a, c1), s(x (t - 1), z)} : Set (Sym2 V)).ncard = 3 := by
        refine Set.ncard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
        · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun h => absurd h (Ne.symm hanez), fun h => absurd h hzc1ne⟩
        · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun _ => hanez, fun _ => hax1⟩
        · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
          exact ⟨fun h => absurd h hax1, fun h => absurd h hanez⟩
      have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
      omega
    exact ⟨hzYC, z :: (a :: (c1 :: Prest)),
      WheelConverse.isWheel_of_three_yEdges hC1hole hC1len hYne hYanti hC1Y h3⟩
  · -- impossible: `b ∈ X_{t−2}` is adjacent to `x_t`, which sits at position `1` of `z :: P`
    exfalso
    obtain ⟨-, i, hhead, hlast, hlp⟩ := hl
    have hrot : (z :: P).rotate i = z :: P := by
      have h := rotate_eq_of_head hCnd (j := 0) (by omega) hhead hC0
      simpa using h
    rw [hrot] at hlp
    obtain ⟨hLp, hLlen, hab, hnab, hA, hB⟩ := hlp
    have h1 : (1 : ℕ) < (z :: P).length := by omega
    have hbadj : (G.deleteEdges {s(x t, z)}).Adj b ((z :: P)[1]'h1) := by
      rw [hC1, SimpleGraph.deleteEdges_adj]
      refine ⟨hbxt, ?_⟩
      simp only [Set.mem_singleton_iff, Sym2.eq_iff, not_or, not_and]
      exact ⟨fun h => absurd h hbnext, fun h => absurd h hbnez⟩
    have := (hB 1 h1).mp hbadj
    omega

/-- **20.3, step (2), hat branch, the endgame.**

PAPER (printed p. 126), the closing sentences of the hat paragraph, once 17.1 has produced a
vertex `f` of the interior of `S` adjacent to `x_t`: *"… and so there is a path `P'` between
`x_t, x_{t−1}` with `P' \ x_t` a subpath of `S \ x_i`.  As before `P'` has length ≥ 4, and so
`S` has length ≥ 4, and `P', S` both have even length since they can be completed to holes
through `z`.  Since the `X_{t−2}`-complete vertex `z` has no neighbours in the interior of
`P'`, from 18.2 (applied to `P'` with anticonnected sets `Y` and `X_{t−2}`) it follows that
there is a `Y`-complete edge in `P'`, and since `x_t` is not `Y`-complete, there is therefore
one in `S`.  But since the edges `zx_{t−1}, zx_i` are also `Y`-complete, we deduce that there
are at least three `Y`-complete edges in the hole `z-x_i-S-x_{t−1}-z`, and such that hole is
the rim of a wheel with hub `Y`."*

`P'` is `x_t :: S.drop i` for `i` the **largest** index with `x_t` adjacent to `S[i]`; the hole
it sits in is `Thm192Infra.holeFromCut` (whose `huadj` is exactly that maximality). -/
theorem step2_hat_endgame {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {F : Set V} (hFsub : F ⊆ wheelSystemA G z A₀ x (t - 2))
    (h : V) (hhX : h ∈ wheelSystemX x (t - 2)) (hzh : G.Adj z h)
    (S : List V) (hS : IsPathFrom G S h (x (t - 1)))
    (hSint : ∀ v ∈ SPGT.interior S, v ∈ F)
    (f : V) (hfint : f ∈ SPGT.interior S) (hfxt : G.Adj f (x t))
    (hnocommon : ¬ ∃ g ∈ F, G.Adj (x t) g ∧ G.Adj (x (t - 1)) g)
    (hzYC : VertexComplete G z Y) :
    ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  obtain ⟨jh, hjh, hhje⟩ := id hhX
  have hxjF : ∀ j ≤ t, x j ∉ F := fun j hj hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj (hFsub hm)
  have hzFnadj : ∀ v ∈ F, ¬ G.Adj z v := fun v hv =>
    WheelSystemBasics.wheelSystemA_no_nbr (hFsub hv)
  have hzF : z ∉ F := fun hm =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) (hFsub hm)
  have hYF : ∀ y ∈ Y, y ∉ F := fun y hy hm =>
    Thm203Prelim.Y_notMem_wheelSystemA hVC (show t - 2 < t by omega) hy (hFsub hm)
  have hhnez : h ≠ z := by rw [hhje]; exact (hws.2.2.1 jh (by omega)).2
  have hhnex1 : h ≠ x (t - 1) := by
    rw [hhje]; intro hq; have := hinj jh (by omega) (t - 1) (by omega) hq; omega
  have hhnext : h ≠ x t := by
    rw [hhje]; intro hq; have := hinj jh (by omega) t le_rfl hq; omega
  have hhF : h ∉ F := by rw [hhje]; exact hxjF jh (by omega)
  have hxtnex1 : x t ≠ x (t - 1) := by
    intro hq; have := hinj t le_rfl (t - 1) (by omega) hq; omega
  have hxtx1nadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  have hSmem : ∀ v ∈ S, v = h ∨ v = x (t - 1) ∨ v ∈ F := by
    intro v hv
    by_cases h1 : v = h
    · exact Or.inl h1
    by_cases h2 : v = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hSint v ((PathBasics.mem_interior_iff_of_pathFrom hS).mpr
      ⟨hv, h1, h2⟩)))
  have hzS : z ∉ S := by
    intro hm
    rcases hSmem z hm with hq | hq | hq
    · exact hhnez hq.symm
    · exact (hws.2.2.1 (t - 1) (by omega)).2 hq.symm
    · exact hzF hq
  have hxtS : x t ∉ S := by
    intro hm
    rcases hSmem (x t) hm with hq | hq | hq
    · exact hhnext hq.symm
    · exact hxtnex1 hq
    · exact hxjF t le_rfl hq
  have hSpos : 0 < S.length := PathBasics.path_length_pos hS.1
  have hSl : S.length = pathLength S + 1 := PathBasics.length_eq_pathLength_add_one hS.1
  have hSlast : S[S.length - 1]'(by omega) = x (t - 1) :=
    PathBasics.getElem_last_of_getLast? hS.2.2 (by omega)
  have hS0 : S[0]'(by omega) = h := PathBasics.getElem_zero_of_head? hS.2.1 (by omega)
  obtain ⟨kf, hkf, hkf1, hkf2, hkfe⟩ := PathBasics.exists_getElem_of_mem_interior hS.1 hfint
  have hzSint : ∀ v ∈ SPGT.interior S, ¬ G.Adj z v := fun v hv => hzFnadj v (hSint v hv)
  -- the hole `z-x_i-S-x_{t−1}-z`
  have hCS : IsHoleList G (z :: S) :=
    PrismBasics.isHoleList_of_path_add_vertex hS (by omega) hzh
      (hzadj (t - 1) (by omega)) hzS hzSint
  -- PAPER: "there is a path `P'` between `x_t, x_{t−1}` with `P' \ x_t` a subpath of
  -- `S \ x_i`" — take the *last* neighbour of `x_t` on `S`
  have hQkf : ∃ hk : kf < S.length, G.Adj (x t) (S[kf]'hk) :=
    ⟨hkf, by rw [hkfe]; exact hfxt.symm⟩
  have hQi := Nat.findGreatest_spec (P := fun k => ∃ hk : k < S.length, G.Adj (x t) (S[k]'hk))
    (m := kf) (n := S.length - 1) (by omega) hQkf
  have hile : Nat.findGreatest (fun k => ∃ hk : k < S.length, G.Adj (x t) (S[k]'hk))
      (S.length - 1) ≤ S.length - 1 := Nat.findGreatest_le _
  have hkfi : kf ≤ Nat.findGreatest (fun k => ∃ hk : k < S.length, G.Adj (x t) (S[k]'hk))
      (S.length - 1) := Nat.le_findGreatest (by omega) hQkf
  obtain ⟨hilt, hiadj⟩ := hQi
  set i : ℕ := Nat.findGreatest (fun k => ∃ hk : k < S.length, G.Adj (x t) (S[k]'hk))
    (S.length - 1) with hidef
  have hinex1 : i ≠ S.length - 1 := by
    intro he
    have heq : S[i]'hilt = x (t - 1) := by
      rw [gidx S he hilt (by omega)]; exact hSlast
    rw [heq] at hiadj
    exact hxtx1nadj hiadj
  have hi2 : i + 2 ≤ S.length := by omega
  have hi1 : 0 < i := by omega
  have huadj : ∀ (k : ℕ) (hk : k < S.length), i ≤ k →
      (G.Adj (x t) (S[k]'hk) ↔ k = i) := by
    intro k hk hik
    constructor
    · intro hadj
      by_contra hne
      exact Nat.findGreatest_is_greatest (P := fun k => ∃ hk : k < S.length,
        G.Adj (x t) (S[k]'hk)) (k := k) (n := S.length - 1) (by omega) (by omega)
        ⟨hk, hadj⟩
    · intro he
      rw [gidx S he hk hilt]; exact hiadj
  have hzAF : VertexAnticomplete G z F := fun v hv => hzFnadj v hv
  have hPP : IsHoleList G (z :: x t :: S.drop i) :=
    Thm192Infra.holeFromCut hS hSint hzAF hzh (hzadj (t - 1) (by omega))
      (hzadj t le_rfl) hzS hxtS hi1 hi2 huadj
  -- `P' = x_t :: S.drop i` as a path
  have hslice : (S.drop i).take (S.length - 1 - i + 1) = S.drop i := by
    refine List.take_of_length_le ?_
    simp only [List.length_drop]; omega
  have hdp : IsPathFrom G (S.drop i) (S[i]'hilt) (x (t - 1)) := by
    have hq := PathBasics.isPathFrom_slice hS.1 (i := i) (j := S.length - 1)
      (by omega) (by omega)
    rw [hslice, hSlast] at hq
    exact hq
  have hdropmem : ∀ w ∈ S.drop i, ∃ (k : ℕ) (hk : k < S.length), i ≤ k ∧ S[k]'hk = w := by
    intro w hw
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    simp only [List.length_drop] at hk
    refine ⟨i + k, by omega, by omega, ?_⟩
    rw [← hkw]
    simp [List.getElem_drop]
  have hxtdrop : x t ∉ S.drop i := fun hm => hxtS (List.mem_of_mem_drop hm)
  have hP' : IsPathFrom G (x t :: S.drop i) (x t) (x (t - 1)) := by
    refine PathAttach.isPathFrom_cons hdp hiadj hxtdrop ?_
    intro w hw hne hadj
    obtain ⟨k, hk, hik, hkw⟩ := hdropmem w hw
    rw [← hkw] at hadj hne
    exact hne (gidx S ((huadj k hk hik).mp hadj) hk hilt)
  have hP'len : (x t :: S.drop i).length = S.length - i + 1 := by
    simp only [List.length_cons, List.length_drop]
  have hP'pl : pathLength (x t :: S.drop i) = S.length - i := by
    have hq := PathBasics.pathLength_eq (x t :: S.drop i); omega
  -- the interior of `P'` lies in `F`
  have hP'int : ∀ w ∈ SPGT.interior (x t :: S.drop i), w ∈ F := by
    intro w hw
    obtain ⟨hwm, hwxt, hwx1⟩ := (PathBasics.mem_interior_iff_of_pathFrom hP').mp hw
    have hwd : w ∈ S.drop i := by
      rcases List.mem_cons.mp hwm with hq | hq
      · exact absurd hq hwxt
      · exact hq
    rcases hSmem w (List.mem_of_mem_drop hwd) with hq | hq | hq
    · exfalso
      obtain ⟨k, hk, hik, hkw⟩ := hdropmem w hwd
      have h0 : S[k]'hk = S[0]'(by omega) := by rw [hkw, hq, ← hS0]
      have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hS.1)).mp h0
      omega
    · exact absurd hq hwx1
    · exact hq
  -- PAPER: "As before `P'` has length ≥ 4, and so `S` has length ≥ 4, and `P', S` both have
  -- even length since they can be completed to holes through `z`"
  have hP'even : Even (pathLength (x t :: S.drop i)) := by
    have hq := hBerge.1 _ hPP
    have hlen : holeLength (z :: x t :: S.drop i) = S.length - i + 2 := by
      simp only [holeLength, List.length_cons, List.length_drop]
    rw [hlen] at hq
    obtain ⟨k, hk⟩ := hq
    exact ⟨k - 1, by omega⟩
  have hP'ne1 : pathLength (x t :: S.drop i) ≠ 1 := by
    intro hq
    exact hxtx1nadj (PathBasics.isPathFrom_ends_adj_of_length_one hP' hq)
  have hP'ne2 : pathLength (x t :: S.drop i) ≠ 2 := by
    intro hq
    have hidx : i + 1 = S.length - 1 := by omega
    refine hnocommon ⟨S[i]'hilt, ?_, hiadj, ?_⟩
    · exact hSint _ (PathBasics.getElem_mem_interior hS.1 hilt (by omega) (by omega))
    · have hadj : G.Adj (S[i]'hilt) (S[i + 1]'(by omega)) :=
        PathBasics.path_adj_succ hS.1 (by omega)
      have he : S[i + 1]'(by omega) = x (t - 1) := by
        rw [gidx S hidx (by omega) (by omega)]; exact hSlast
      rw [he] at hadj; exact hadj.symm
  have hP'4 : 4 ≤ pathLength (x t :: S.drop i) := by
    obtain ⟨k, hk⟩ := hP'even
    omega
  have hSeven : Even (pathLength S) := by
    have hq := hBerge.1 _ hCS
    have hlen : holeLength (z :: S) = S.length + 1 := by
      simp only [holeLength, List.length_cons]
    rw [hlen] at hq
    obtain ⟨k, hk⟩ := hq
    exact ⟨k - 1, by omega⟩
  have hS4 : 4 ≤ pathLength S := by omega
  -- PAPER: "from 18.2 (applied to `P'` with anticonnected sets `Y` and `X_{t−2}`) it follows
  -- that there is a `Y`-complete edge in `P'`"
  have hp : IsPathFrom G ((x t :: S.drop i).reverse) (x (t - 1)) (x t) :=
    PathBasics.isPathFrom_reverse hP'
  have hplen : ((x t :: S.drop i).reverse).length = S.length - i + 1 := by
    rw [List.length_reverse]; exact hP'len
  have hppl : pathLength ((x t :: S.drop i).reverse) = S.length - i := by
    rw [PathBasics.pathLength_reverse]; exact hP'pl
  have hpeven : Even (pathLength ((x t :: S.drop i).reverse)) := by
    rw [PathBasics.pathLength_reverse]; exact hP'even
  have hpmem : ∀ w ∈ ((x t :: S.drop i).reverse), w = x t ∨ w ∈ S.drop i := by
    intro w hw
    rw [List.mem_reverse] at hw
    exact List.mem_cons.mp hw
  have hpintF : ∀ w ∈ SPGT.interior ((x t :: S.drop i).reverse), w ∈ F :=
    fun w hw => hP'int w (PathBasics.mem_interior_reverse.mp hw)
  have hpn1 := getLast?_dropLast_getElem ((x t :: S.drop i).reverse) (by omega)
  have hpn2 := getLast?_dropLast_dropLast_getElem ((x t :: S.drop i).reverse) (by omega)
  have hpn1int :
      (((x t :: S.drop i).reverse)[((x t :: S.drop i).reverse).length - 2]'(by omega))
        ∈ SPGT.interior ((x t :: S.drop i).reverse) :=
    PathBasics.getElem_mem_interior hp.1 (by omega) (by omega) (by omega)
  have hpn2int :
      (((x t :: S.drop i).reverse)[((x t :: S.drop i).reverse).length - 3]'(by omega))
        ∈ SPGT.interior ((x t :: S.drop i).reverse) :=
    PathBasics.getElem_mem_interior hp.1 (by omega) (by omega) (by omega)
  have hXanti : AnticonnectedSet G (wheelSystemX x (t - 2)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)
  have hXne : (wheelSystemX x (t - 2)).Nonempty := ⟨x 0, ⟨0, by omega, rfl⟩⟩
  have hdisj : Disjoint Y (wheelSystemX x (t - 2)) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨j, hj, rfl⟩
    exact hxY j (by omega) hy
  have hcompl : Complete G Y (wheelSystemX x (t - 2)) := by
    rintro y hy w ⟨j, hj, rfl⟩
    exact (hVC j (by omega) y hy).symm
  have hYuniq : ∀ w ∈ ((x t :: S.drop i).reverse),
      (VertexComplete G w (wheelSystemX x (t - 2)) ↔ w = x t) := by
    intro w hw
    constructor
    · intro hwc
      rcases hpmem w hw with hq | hq
      · exact hq
      · exfalso
        rcases hSmem w (List.mem_of_mem_drop hq) with hq' | hq' | hq'
        · obtain ⟨k, hk, hik, hkw⟩ := hdropmem w hq
          have h0 : S[k]'hk = S[0]'(by omega) := by rw [hkw, hq', ← hS0]
          have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hS.1)).mp h0
          omega
        · refine hws.2.2.2.2.2.1 (t - 1) (by omega) (by omega) ?_
          have he : t - 1 - 1 = t - 2 := by omega
          rw [he, ← hq']; exact hwc
        · exact WheelSystemBasics.wheelSystemA_no_complete (hFsub hq') hwc
    · intro hq; rw [hq]; exact hXc
  have hvy : ∃ v : V, VertexComplete G v (wheelSystemX x (t - 2)) ∧
      ¬ G.Adj v
        (((x t :: S.drop i).reverse)[((x t :: S.drop i).reverse).length - 2]'(by omega)) ∧
      ¬ G.Adj v
        (((x t :: S.drop i).reverse)[((x t :: S.drop i).reverse).length - 3]'(by omega)) := by
    refine ⟨z, ?_, ?_, ?_⟩
    · rintro w ⟨j, hj, rfl⟩; exact hzadj j (by omega)
    · exact hzFnadj _ (hpintF _ hpn1int)
    · exact hzFnadj _ (hpintF _ hpn2int)
  obtain ⟨u, hu, v, hv, hedge⟩ :
      ∃ u ∈ ((x t :: S.drop i).reverse), ∃ v ∈ ((x t :: S.drop i).reverse),
        EdgeComplete G Y u v := by
    rcases _root_.Workspace.Statements.S18.SPGT.thm_18_2 G hG Y (wheelSystemX x (t - 2))
        hdisj hYne hXne hYanti hXanti hcompl ((x t :: S.drop i).reverse) (x (t - 1)) _ _ (x t)
        hp.1 hpeven (by omega) hp.2.1 hp.2.2 hpn1 hpn2
        (hVC (t - 1) (by omega)) hnVC hYuniq hvy with hodd | hlen3
    · have hne0 : {e : Sym2 V | ∃ a ∈ ((x t :: S.drop i).reverse),
          ∃ b ∈ ((x t :: S.drop i).reverse), e = s(a, b) ∧ EdgeComplete G Y a b}.ncard ≠ 0 := by
        intro h0
        rw [h0] at hodd
        simp at hodd
      obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero hne0
      obtain ⟨a, ha, b, hb, -, hab⟩ := he
      exact ⟨a, ha, b, hb, hab⟩
    · exact absurd hlen3.1 (by omega)
  -- PAPER: "since `x_t` is not `Y`-complete, there is therefore one in `S`"
  have huS : u ∈ S := by
    rcases hpmem u hu with hq | hq
    · exact absurd (by rw [← hq]; exact hedge.2.1) hnVC
    · exact List.mem_of_mem_drop hq
  have hvS : v ∈ S := by
    rcases hpmem v hv with hq | hq
    · exact absurd (by rw [← hq]; exact hedge.2.2) hnVC
    · exact List.mem_of_mem_drop hq
  -- PAPER: "there are at least three `Y`-complete edges in the hole `z-x_i-S-x_{t−1}-z`,
  -- and such that hole is the rim of a wheel with hub `Y`"
  have hhY : VertexComplete G h Y := by rw [hhje]; exact hVC jh (by omega)
  have hx1Y : VertexComplete G (x (t - 1)) Y := hVC (t - 1) (by omega)
  have hhS : h ∈ S := (PathBasics.isPathFrom_ends_mem hS).1
  have hx1S : x (t - 1) ∈ S := (PathBasics.isPathFrom_ends_mem hS).2
  refine ⟨z :: S, WheelConverse.isWheel_of_three_yEdges hCS ?_ hYne hYanti ?_ ?_⟩
  · simp only [holeLength, List.length_cons]; omega
  · intro w hw hwY
    rcases List.mem_cons.mp hw with hq | hq
    · exact hzY (by rw [← hq]; exact hwY)
    · rcases hSmem w hq with hq' | hq' | hq'
      · exact hxY jh (by omega) (by rw [← hhje, ← hq']; exact hwY)
      · exact hxY (t - 1) (by omega) (by rw [← hq']; exact hwY)
      · exact hYF w hwY hq'
  · rw [OptimalWheelChoice.yEdgeCount_def]
    have hsub : ({s(z, h), s(x (t - 1), z), s(u, v)} : Set (Sym2 V)) ⊆
        {e : Sym2 V | ∃ a ∈ (z :: S), ∃ b ∈ (z :: S), e = s(a, b) ∧ EdgeComplete G Y a b} := by
      rintro e (rfl | rfl | rfl)
      · exact ⟨z, by simp, h, List.mem_cons_of_mem _ hhS, rfl, hzh, hzYC, hhY⟩
      · exact ⟨x (t - 1), List.mem_cons_of_mem _ hx1S, z, by simp, rfl,
          (hzadj (t - 1) (by omega)).symm, hx1Y, hzYC⟩
      · exact ⟨u, List.mem_cons_of_mem _ huS, v, List.mem_cons_of_mem _ hvS, rfl, hedge⟩
    have hcard : ({s(z, h), s(x (t - 1), z), s(u, v)} : Set (Sym2 V)).ncard = 3 := by
      refine Set.ncard_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun _ => hhnez, fun _ => hhnex1⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun hq => absurd (show z ∈ S by rw [hq]; exact huS) hzS,
          fun hq => absurd (show z ∈ S by rw [hq]; exact hvS) hzS⟩
      · simp only [ne_eq, Sym2.eq_iff, not_or, not_and]
        exact ⟨fun _ hq => hzS (by rw [hq]; exact hvS),
          fun _ hq => hzS (by rw [hq]; exact huS)⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega

/-- **20.3, step (2), the hat branch: the wheel.**

PAPER (printed pp. 125–126), the second half of the hat paragraph: *"Let `S` be a path between
`x_i` and `x_{t−1}` with interior in `F`.  Then `V(S ∪ P) \ {x_i, x_t}` (`= F'` say) is
connected and catches the triangle `{z, x_i, x_t}`.  The only neighbour of `z` in `F'` is
`x_{t−1}`, which is nonadjacent to both `x_i, x_t`.  If `F'` contains a reflection of the
triangle, there is an antihole of length 6 containing `z, x_{t−1}, x_t`, which is impossible
by 15.7 since these three vertices belong to `C`.  So by 17.1, there is a vertex in `F'`
adjacent to both `x_i, x_t`.  Since `x_i` has no neighbour in `P \ x_t`, it follows that both
`x_t, x_{t−1}` have neighbours in the interior of `S`, and so there is a path `P'` between
`x_t, x_{t−1}` with `P' \ x_t` a subpath of `S \ x_i`.  As before `P'` has length ≥ 4, and so
`S` has length ≥ 4, and `P', S` both have even length since they can be completed to holes
through `z`.  Since the `X_{t−2}`-complete vertex `z` has no neighbours in the interior of
`P'`, from 18.2 (applied to `P'` with anticonnected sets `Y` and `X_{t−2}`) it follows that
there is a `Y`-complete edge in `P'`, and since `x_t` is not `Y`-complete, there is therefore
one in `S`.  But since the edges `zx_{t−1}, zx_i` are also `Y`-complete, we deduce that there
are at least three `Y`-complete edges in the hole `z-x_i-S-x_{t−1}-z`, and such that hole is
the rim of a wheel with hub `Y`."* -/
theorem step2_hat_wheel {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {F : Set V} (hFconn : ConnectedSet G F)
    (hFsub : F ⊆ wheelSystemA G z A₀ x (t - 2))
    (hA3F : wheelSystemA G z A₀ x (t - 3) ⊆ F)
    (P : List V) (hP : IsPathFrom G P (x t) (x (t - 1)))
    (hPint : ∀ v ∈ SPGT.interior P, v ∈ F) (hPeven : Even (pathLength P))
    (hPlen : 4 ≤ pathLength P) (hCh : IsHoleList G (z :: P))
    (h : V) (hhX : h ∈ wheelSystemX x (t - 2))
    (hhat : IsHatForHole G (z :: P) z (x t) h)
    (hnocommon : ¬ ∃ g ∈ F, G.Adj (x t) g ∧ G.Adj (x (t - 1)) g)
    (hzYC : VertexComplete G z Y) :
    ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF6 : InF6 G := hG.1
  have hF5 : InF5 G := hG.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hPl : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  have hxjF : ∀ j ≤ t, x j ∉ F := fun j hj hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj (hFsub hm)
  have hzFnadj : ∀ v ∈ F, ¬ G.Adj z v := fun v hv =>
    WheelSystemBasics.wheelSystemA_no_nbr (hFsub hv)
  have hzF : z ∉ F := fun hm =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) (hFsub hm)
  have hYF : ∀ y ∈ Y, y ∉ F := fun y hy hm =>
    Thm203Prelim.Y_notMem_wheelSystemA hVC (show t - 2 < t by omega) hy (hFsub hm)
  have hPmem : ∀ w ∈ P, w = x t ∨ w = x (t - 1) ∨ w ∈ F := by
    intro w hw
    by_cases h1 : w = x t
    · exact Or.inl h1
    by_cases h2 : w = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hw, h1, h2⟩)))
  have hzP : z ∉ P := by
    intro hm
    rcases hPmem z hm with hq | hq | hq
    · exact (hws.2.2.1 t le_rfl).2 hq.symm
    · exact (hws.2.2.1 (t - 1) (by omega)).2 hq.symm
    · exact hzF hq
  obtain ⟨-, -, -, -, hhz, hhxt, hhother⟩ := hhat
  obtain ⟨jh, hjh, hhje⟩ := id hhX
  have hhnez : h ≠ z := by rw [hhje]; exact (hws.2.2.1 jh (by omega)).2
  have hhnext : h ≠ x t := fun hq => G.irrefl (hq ▸ hhxt)
  have hhP : h ∉ P := by
    intro hm
    rcases hPmem h hm with hq | hq | hq
    · exact hhnext hq
    · have := hinj jh (by omega) (t - 1) (by omega) (hhje.symm.trans hq); omega
    · exact hxjF jh (by omega) (by rw [← hhje]; exact hq)
  have hhother' : ∀ v ∈ P, v ≠ x t → ¬ G.Adj h v := by
    intro v hv hvne
    exact hhother v (List.mem_cons_of_mem _ hv)
      (fun hq => hzP (by rw [← hq]; exact hv)) hvne
  have hhF : h ∉ F := by rw [hhje]; exact hxjF jh (by omega)
  have hx1F : x (t - 1) ∉ F := hxjF (t - 1) (by omega)
  -- `x_i` has a neighbour in `A_{t−3} ⊆ F`
  have hhnbr : ∃ f ∈ F, G.Adj h f := by
    obtain ⟨f, hf, hfadj⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
      (i := jh) (k := t - 3) (by omega) (by omega) (by omega)
    exact ⟨f, hA3F hf, by rw [hhje]; exact hfadj⟩
  -- `x_{t−1}` has a neighbour in `F`: the last interior vertex of `P`
  have hx1nbr : ∃ f ∈ F, G.Adj (x (t - 1)) f := by
    refine ⟨P[P.length - 2]'(by omega), hPint _ ?_, ?_⟩
    · exact PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
    · have hadj : G.Adj (P[P.length - 2]'(by omega)) (P[P.length - 2 + 1]'(by omega)) :=
        PathBasics.path_adj_succ hP.1 (by omega)
      have he : P[P.length - 2 + 1]'(by omega) = x (t - 1) := by
        rw [gidx P (show P.length - 2 + 1 = P.length - 1 by omega) (by omega) (by omega)]
        exact PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
      rw [he] at hadj; exact hadj.symm
  -- PAPER: "Let `S` be a path between `x_i` and `x_{t−1}` with interior in `F`."
  obtain ⟨S, hS, hSint⟩ :=
    MinimalConnectedIsPath.exists_path_interior_in hFconn hhF hx1F hhnbr hx1nbr
  have hhnex1 : h ≠ x (t - 1) := by
    rw [hhje]; intro hq
    have := hinj jh (by omega) (t - 1) (by omega) hq; omega
  have hxtnex1 : x t ≠ x (t - 1) := by
    intro hq; have := hinj t le_rfl (t - 1) (by omega) hq; omega
  have hhx1nadj : ¬ G.Adj h (x (t - 1)) :=
    hhother' (x (t - 1)) (PathBasics.isPathFrom_ends_mem hP).2 (Ne.symm hxtnex1)
  have hS3 : 3 ≤ S.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hS hhnex1 hhx1nadj
  have hSmem : ∀ v ∈ S, v = h ∨ v = x (t - 1) ∨ v ∈ F := by
    intro v hv
    by_cases h1 : v = h
    · exact Or.inl h1
    by_cases h2 : v = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hSint v ((PathBasics.mem_interior_iff_of_pathFrom hS).mpr
      ⟨hv, h1, h2⟩)))
  have hxtS : x t ∉ S := by
    intro hm
    rcases hSmem (x t) hm with hq | hq | hq
    · exact hhnext hq.symm
    · exact hxtnex1 hq
    · exact hxjF t le_rfl hq
  have hzS : z ∉ S := by
    intro hm
    rcases hSmem z hm with hq | hq | hq
    · exact hhnez hq.symm
    · exact (hws.2.2.1 (t - 1) (by omega)).2 hq.symm
    · exact hzF hq
  -- PAPER: "`V(S ∪ P) \ {x_i, x_t}` (`= F'` say) is connected"
  have hSt : IsPathList G S.tail := by
    have hq := PathBasics.isPathList_drop hS.1 (k := 1) (by omega); simpa using hq
  have hPt : IsPathList G P.tail := by
    have hq := PathBasics.isPathList_drop hP.1 (k := 1) (by omega); simpa using hq
  have hx1St : x (t - 1) ∈ S.tail :=
    mem_tail_of_ne_head hS (PathBasics.isPathFrom_ends_mem hS).2 (Ne.symm hhnex1)
  have hx1Pt : x (t - 1) ∈ P.tail :=
    mem_tail_of_ne_head hP (PathBasics.isPathFrom_ends_mem hP).2 (Ne.symm hxtnex1)
  have hF'conn : ConnectedSet G ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}) :=
    ConnectedSetUnionAttach.connectedSet_union
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hSt)
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hPt)
      (Or.inl ⟨x (t - 1), hx1St, hx1Pt⟩)
  have hF'sub : ∀ v ∈ ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}),
      v ∈ F ∨ v = x (t - 1) := by
    rintro v (hv | hv)
    · rcases hSmem v (List.mem_of_mem_tail hv) with hq | hq | hq
      · exact absurd (by rw [← hq]; exact hv) (head_notMem_tail hS)
      · exact Or.inr hq
      · exact Or.inl hq
    · rcases hPmem v (List.mem_of_mem_tail hv) with hq | hq | hq
      · exact absurd (by rw [← hq]; exact hv) (head_notMem_tail hP)
      · exact Or.inr hq
      · exact Or.inl hq
  -- PAPER: "The only neighbour of `z` in `F'` is `x_{t−1}`"
  have hzF'only : ∀ v ∈ ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}),
      G.Adj z v → v = x (t - 1) := by
    intro v hv hadj
    rcases hF'sub v hv with hq | hq
    · exact absurd hadj (hzFnadj v hq)
    · exact hq
  have hzh : G.Adj z h := hhz.symm
  have hzxt : G.Adj z (x t) := hzadj t le_rfl
  have hznext : z ≠ x t := Ne.symm (hws.2.2.1 t le_rfl).2
  have htri : IsTriangle G ({z, h, x t} : Set V) := by
    refine ⟨Set.ncard_eq_three.mpr
      ⟨z, h, x t, Ne.symm hhnez, hznext, hhnext, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first
        | exact absurd rfl huv
        | exact hzh
        | exact hzxt
        | exact hzh.symm
        | exact hzxt.symm
        | exact hhxt
        | exact hhxt.symm
  have hF'notA : ∀ v ∈ ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}),
      v ≠ z ∧ v ≠ h ∧ v ≠ x t := by
    intro v hv
    rcases hF'sub v hv with hq | hq
    · exact ⟨fun he => hzF (by rw [← he]; exact hq),
        fun he => hhF (by rw [← he]; exact hq),
        fun he => hxjF t le_rfl (by rw [← he]; exact hq)⟩
    · exact ⟨fun he => (hws.2.2.1 (t - 1) (by omega)).2 (by rw [← hq, ← he]),
        fun he => hhnex1 (by rw [← he, hq]), fun he => hxtnex1 (by rw [← he, hq])⟩
  have hF'A : ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}) ⊆ ({z, h, x t} : Set V)ᶜ := by
    intro v hv hmem
    obtain ⟨h1, h2, h3⟩ := hF'notA v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with hq | hq | hq
    · exact h1 hq
    · exact h2 hq
    · exact h3 hq
  have hS0 : S[0]'(by omega) = h := PathBasics.getElem_zero_of_head? hS.2.1 (by omega)
  have hP0 : P[0]'(by omega) = x t := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hS1t : S[1]'(by omega) ∈ S.tail := by
    refine mem_tail_of_ne_head hS (List.getElem_mem _) ?_
    rw [← hS0]; exact PathBasics.path_ne_of_ne_index hS.1 (by omega) (by omega) (by omega)
  have hP1t : P[1]'(by omega) ∈ P.tail := by
    refine mem_tail_of_ne_head hP (List.getElem_mem _) ?_
    rw [← hP0]; exact PathBasics.path_ne_of_ne_index hP.1 (by omega) (by omega) (by omega)
  have hcatch : Catches G ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail})
      ({z, h, x t} : Set V) := by
    refine ⟨htri, hF'conn, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro v hv hmem
      exact hF'A hv hmem
    · intro c hc
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
      rcases hc with hcq | hcq | hcq
      · rw [hcq]
        exact ⟨x (t - 1), Or.inr hx1Pt, hzadj (t - 1) (by omega)⟩
      · rw [hcq]
        refine ⟨S[1]'(by omega), Or.inl hS1t, ?_⟩
        have hq : G.Adj (S[0]'(by omega)) (S[1]'(by omega)) :=
          PathBasics.path_adj_succ hS.1 (by omega)
        rwa [hS0] at hq
      · rw [hcq]
        refine ⟨P[1]'(by omega), Or.inr hP1t, ?_⟩
        have hq : G.Adj (P[0]'(by omega)) (P[1]'(by omega)) :=
          PathBasics.path_adj_succ hP.1 (by omega)
        rwa [hP0] at hq
  have hClen6 : 4 < holeLength (z :: P) := by
    simp only [holeLength, List.length_cons]; omega
  -- PAPER: "If `F'` contains a reflection of the triangle, there is an antihole of length 6
  -- containing `z, x_{t−1}, x_t`, which is impossible by 15.7"
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG ({z, h, x t} : Set V) htri
      ({v : V | v ∈ S.tail} ∪ {v : V | v ∈ P.tail}) hF'A hcatch with hrefl | h2
  · exfalso
    obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hAeq, hBF, hRfl⟩ := hrefl
    have hD : IsAntiholeList G [a₁, b₂, a₃, b₁, a₂, b₃] :=
      ReflectionAntihole.isAntiholeList_of_reflection hRfl
    have hmemDa : ∀ w : V, w ∈ ({a₁, a₂, a₃} : Set V) → w ∈ [a₁, b₂, a₃, b₁, a₂, b₃] := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> simp
    have hmemDb : ∀ w : V, w ∈ ({b₁, b₂, b₃} : Set V) → w ∈ [a₁, b₂, a₃, b₁, a₂, b₃] := by
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl <;> simp
    have hzA : z ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hAeq]; simp
    have hxtA : x t ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hAeq]; simp
    obtain ⟨bz, hbz, hzbz⟩ := reflection_partner hRfl hzA
    have hbzeq : bz = x (t - 1) := hzF'only bz (hBF hbz) hzbz
    have hsub : ({z, x t, x (t - 1)} : Set V) ⊆
        ({w : V | w ∈ (z :: P)} ∩ {w : V | w ∈ [a₁, b₂, a₃, b₁, a₂, b₃]}) := by
      rintro v (rfl | rfl | rfl)
      · exact ⟨by simp, hmemDa v hzA⟩
      · exact ⟨List.mem_cons_of_mem _ (PathBasics.isPathFrom_ends_mem hP).1, hmemDa _ hxtA⟩
      · exact ⟨List.mem_cons_of_mem _ (PathBasics.isPathFrom_ends_mem hP).2,
          by rw [← hbzeq]; exact hmemDb bz hbz⟩
    have hcard3 : ({z, x t, x (t - 1)} : Set V).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨z, x t, x (t - 1), hznext,
        fun he => (hws.2.2.1 (t - 1) (by omega)).2 he.symm, hxtnex1, rfl⟩
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h157 := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hF6 (z :: P)
      [a₁, b₂, a₃, b₁, a₂, b₃] hCh hClen6 hD (by
        rw [ReflectionAntihole.holeLength_reflection]; omega)
    omega
  · -- PAPER: "So by 17.1, there is a vertex in `F'` adjacent to both `x_i, x_t`."
    obtain ⟨f, hfF', hfcard⟩ := h2
    have hxtx1nadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
    have hfz : ¬ G.Adj f z := by
      intro hadj
      have hfe : f = x (t - 1) := hzF'only f hfF' hadj.symm
      have hsub : (G.neighborSet f ∩ ({z, h, x t} : Set V)) ⊆ {z} := by
        rintro u ⟨hu1, hu2⟩
        have hadjfu : G.Adj f u := hu1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with hq | hq | hq
        · exact hq
        · exact absurd (show G.Adj h (x (t - 1)) by
            rw [← hfe, ← hq]; exact hadjfu.symm) hhx1nadj
        · exact absurd (show G.Adj (x t) (x (t - 1)) by
            rw [← hfe, ← hq]; exact hadjfu.symm) hxtx1nadj
      have hle := ncard_le_one_of_subset_singleton hsub
      omega
    have hfh : G.Adj f h := by
      by_contra hcon
      have hsub : (G.neighborSet f ∩ ({z, h, x t} : Set V)) ⊆ {x t} := by
        rintro u ⟨hu1, hu2⟩
        have hadjfu : G.Adj f u := hu1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with hq | hq | hq
        · exact absurd (by rw [← hq]; exact hadjfu) hfz
        · exact absurd (by rw [← hq]; exact hadjfu) hcon
        · exact hq
      have hle := ncard_le_one_of_subset_singleton hsub
      omega
    have hfxt : G.Adj f (x t) := by
      by_contra hcon
      have hsub : (G.neighborSet f ∩ ({z, h, x t} : Set V)) ⊆ {h} := by
        rintro u ⟨hu1, hu2⟩
        have hadjfu : G.Adj f u := hu1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with hq | hq | hq
        · exact absurd (by rw [← hq]; exact hadjfu) hfz
        · exact hq
        · exact absurd (by rw [← hq]; exact hadjfu) hcon
      have hle := ncard_le_one_of_subset_singleton hsub
      omega
    -- PAPER: "Since `x_i` has no neighbour in `P \ x_t`, it follows that both `x_t, x_{t−1}`
    -- have neighbours in the interior of `S`"
    have hfSt : f ∈ S.tail := by
      rcases hfF' with hq | hq
      · exact hq
      · exfalso
        have hfP : f ∈ P := List.mem_of_mem_tail hq
        have hfnext : f ≠ x t := by
          intro he
          exact head_notMem_tail hP (by rw [← he]; exact hq)
        exact hhother' f hfP hfnext hfh.symm
    have hfnex1 : f ≠ x (t - 1) := by
      intro he
      exact hhx1nadj (by rw [← he]; exact hfh.symm)
    have hfint : f ∈ SPGT.interior S :=
      (PathBasics.mem_interior_iff_of_pathFrom hS).mpr
        ⟨List.mem_of_mem_tail hfSt, fun he => head_notMem_tail hS (by rw [← he]; exact hfSt),
          hfnex1⟩
    exact step2_hat_endgame hG hframe hd ht hFsub h hhX hzh S hS hSint f hfint hfxt
      hnocommon hzYC

/-- **20.3, step (2), the hat branch of 2.10.**

PAPER (printed pp. 125–126): *"So `X_{t−2}` contains a hat for `C`; that is, there exists
`x_i ∈ X_{t−2}` with no neighbours in `C` except `x_t, z`. …"* — the paragraph running to
*"This proves (2)"*, using 13.6, 15.7, 17.1 and 18.2. -/
theorem step2_hat_case {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {F : Set V} (hFconn : ConnectedSet G F)
    (hFsub : F ⊆ wheelSystemA G z A₀ x (t - 2))
    (hA3F : wheelSystemA G z A₀ x (t - 3) ⊆ F)
    (P : List V) (hP : IsPathFrom G P (x t) (x (t - 1)))
    (hPint : ∀ v ∈ SPGT.interior P, v ∈ F) (hPeven : Even (pathLength P))
    (hPlen : 4 ≤ pathLength P) (hCh : IsHoleList G (z :: P))
    (h : V) (hhX : h ∈ wheelSystemX x (t - 2))
    (hhat : IsHatForHole G (z :: P) z (x t) h)
    (hnocommon : ¬ ∃ g ∈ F, G.Adj (x t) g ∧ G.Adj (x (t - 1)) g)
    -- PAPER: *"Let `S` be a path between `x_i` and `x_{t−1}` with interior in `F` … we deduce
    -- that there are at least three `Y`-complete edges in the hole `z-x_i-S-x_{t−1}-z`, and
    -- such that hole is the rim of a wheel with hub `Y`."*  (17.1, 15.7, 18.2)
    (hwheel : VertexComplete G z Y → ∃ C : List V, IsWheel G C Y) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hPl : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  have hxjF : ∀ j ≤ t, x j ∉ F := fun j hj hm =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj (hFsub hm)
  have hzFnadj : ∀ v ∈ F, ¬ G.Adj z v := fun v hv =>
    WheelSystemBasics.wheelSystemA_no_nbr (hFsub hv)
  have hzF : z ∉ F := fun hm =>
    Thm203Prelim.z_notMem_wheelSystemA hws (show t - 2 ≤ t by omega) (hFsub hm)
  have hYF : ∀ y ∈ Y, y ∉ F := fun y hy hm =>
    Thm203Prelim.Y_notMem_wheelSystemA hVC (show t - 2 < t by omega) hy (hFsub hm)
  have hPmem : ∀ w ∈ P, w = x t ∨ w = x (t - 1) ∨ w ∈ F := by
    intro w hw
    by_cases h1 : w = x t
    · exact Or.inl h1
    by_cases h2 : w = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hw, h1, h2⟩)))
  have hzP : z ∉ P := by
    intro hm
    rcases hPmem z hm with hq | hq | hq
    · exact (hws.2.2.1 t le_rfl).2 hq.symm
    · exact (hws.2.2.1 (t - 1) (by omega)).2 hq.symm
    · exact hzF hq
  -- PAPER: "there exists `x_i ∈ X_{t−2}` with no neighbours in `C` except `x_t, z`"
  obtain ⟨-, -, -, -, hhz, hhxt, hhother⟩ := hhat
  obtain ⟨jh, hjh, hhje⟩ := id hhX
  have hhnez : h ≠ z := by rw [hhje]; exact (hws.2.2.1 jh (by omega)).2
  have hhnext : h ≠ x t := fun hq => G.irrefl (hq ▸ hhxt)
  have hhP : h ∉ P := by
    intro hm
    rcases hPmem h hm with hq | hq | hq
    · exact hhnext hq
    · have := hinj jh (by omega) (t - 1) (by omega) (hhje.symm.trans hq); omega
    · exact hxjF jh (by omega) (by rw [← hhje]; exact hq)
  have hhother' : ∀ v ∈ P, v ≠ x t → ¬ G.Adj h v := by
    intro v hv hvne
    exact hhother v (List.mem_cons_of_mem _ hv)
      (fun hq => hzP (by rw [← hq]; exact hv)) hvne
  -- PAPER: "Hence the path `x_i-x_t-p₁-⋯-p_n-x_{t−1}` is odd and has length ≥ 5"
  have hHp : IsPathFrom G (h :: P) h (x (t - 1)) :=
    PathAttach.isPathFrom_cons hP hhxt hhP hhother'
  have hHlen : (h :: P).length = P.length + 1 := by simp
  have hHodd : Odd (pathLength (h :: P)) := by
    have h1 := PathBasics.pathLength_eq (h :: P)
    obtain ⟨k, hk⟩ := hPeven
    exact ⟨k, by omega⟩
  have hHlen5 : 5 ≤ pathLength (h :: P) := by
    have h1 := PathBasics.pathLength_eq (h :: P); omega
  -- PAPER: "its ends are `Y ∪ {z}`-complete, and no internal vertex is `Y ∪ {z}`-complete,
  -- so by 13.6, `z` is `Y`-complete"
  have hzYC : VertexComplete G z Y := by
    by_contra hznc
    have hXanti : AnticonnectedSet G (Y ∪ {z}) :=
      YDiamondTruncation.anticonnected_union_singleton hYanti hzY hznc
    have hXP : (Y ∪ {z}) ⊆ {v : V | v ∈ (h :: P)}ᶜ := by
      rintro v (hv | hv) hm
      · rcases List.mem_cons.mp hm with hq | hq
        · exact hxY jh (by omega) (by rw [← hhje, ← hq]; exact hv)
        · rcases hPmem v hq with hq' | hq' | hq'
          · exact hxY t le_rfl (by rw [← hq']; exact hv)
          · exact hxY (t - 1) (by omega) (by rw [← hq']; exact hv)
          · exact hYF v hv hq'
      · rw [Set.mem_singleton_iff] at hv
        rcases List.mem_cons.mp hm with hq | hq
        · exact hhnez (by rw [← hq]; exact hv)
        · exact hzP (by rw [← hv]; exact hq)
    have hhC : VertexComplete G h (Y ∪ {z}) := by
      rintro w (hw | hw)
      · rw [hhje]; exact hVC jh (by omega) w hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact hhz
    have hx1C : VertexComplete G (x (t - 1)) (Y ∪ {z}) := by
      rintro w (hw | hw)
      · exact hVC (t - 1) (by omega) w hw
      · rw [Set.mem_singleton_iff] at hw; rw [hw]
        exact (hzadj (t - 1) (by omega)).symm
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hF5 (h :: P) h (x (t - 1))
        hHp hHodd (Y ∪ {z}) hXP hXanti hhC hx1C with hedge | hlen3
    · obtain ⟨u, hu, v, hv, huv, huc, hvc⟩ := hedge
      have hcompl : ∀ w ∈ (h :: P), VertexComplete G w (Y ∪ {z}) →
          w = h ∨ w = x (t - 1) := by
        intro w hw hwc
        have hwz : G.Adj w z := hwc z (Or.inr rfl)
        rcases List.mem_cons.mp hw with hq | hq
        · exact Or.inl hq
        · rcases hPmem w hq with hq' | hq' | hq'
          · exact absurd (show VertexComplete G w Y from fun y hy => hwc y (Or.inl hy))
              (by rw [hq']; exact hnVC)
          · exact Or.inr hq'
          · exact absurd hwz (fun hcon => hzFnadj w hq' hcon.symm)
      have hhx1 : ¬ G.Adj h (x (t - 1)) := by
        refine hhother' (x (t - 1)) (PathBasics.isPathFrom_ends_mem hP).2 ?_
        intro hq
        have := hinj t le_rfl (t - 1) (by omega) hq.symm; omega
      rcases hcompl u hu huc with hu' | hu' <;> rcases hcompl v hv hvc with hv' | hv'
      · rw [hu', hv'] at huv; exact G.irrefl huv
      · rw [hu', hv'] at huv; exact hhx1 huv
      · rw [hu', hv'] at huv; exact hhx1 huv.symm
      · rw [hu', hv'] at huv; exact G.irrefl huv
    · exact absurd hlen3.1 (by omega)
  exact ⟨hzYC, hwheel hzYC⟩

/-- **20.3, step (2), the case where `x_t` and `x_{t−1}` have no common neighbour in the
minimal connected set `F`.**

PAPER (printed p. 125), the paragraph running from *"Let `P` be a path between `x_t` and
`x_{t−1}` with interior in `F`, say `x_t-p₁-⋯-p_n-x_{t−1}`"* to *"This proves (2)"*: it uses
2.10 (`X_{t−2}` contains a leap or a hat for the hole `C = z-x_t-P-x_{t−1}-z`), 13.6 twice,
15.7, 17.1 and 18.2, and every branch ends by exhibiting a wheel with hub `Y` together with
`z` being `Y`-complete — that is, 20.3's own conclusion, which contradicts the standing
assumption of the proof. -/
theorem step2_no_common_nbr {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {F : Set V} (hFconn : ConnectedSet G F)
    (hFsub : F ⊆ wheelSystemA G z A₀ x (t - 2))
    (hA3F : wheelSystemA G z A₀ x (t - 3) ⊆ F)
    (hxtF : ∃ f ∈ F, G.Adj (x t) f) (hx1F : ∃ f ∈ F, G.Adj (x (t - 1)) f)
    (hnocommon : ¬ ∃ f ∈ F, G.Adj (x t) f ∧ G.Adj (x (t - 1)) f)
    (hFmin : ∀ F' : Set V, ConnectedSet G F' → F' ⊆ F →
      wheelSystemA G z A₀ x (t - 3) ⊆ F' →
      (∃ f ∈ F', G.Adj (x t) f) → (∃ f ∈ F', G.Adj (x (t - 1)) f) → F ⊆ F')
    -- PAPER: "Suppose it contains a leap; …"
    (hleapcase : ∀ (P : List V), IsPathFrom G P (x t) (x (t - 1)) →
      (∀ v ∈ SPGT.interior P, v ∈ F) → Even (pathLength P) → 4 ≤ pathLength P →
      IsHoleList G (z :: P) → ∀ a ∈ wheelSystemX x (t - 2), ∀ b ∈ wheelSystemX x (t - 2),
      (IsLeapForHole G (z :: P) z (x t) a b ∨ IsLeapForHole G (z :: P) (x t) z a b) →
      VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y)
    -- PAPER: "So `X_{t−2}` contains a hat for `C`; …"
    (hhatcase : ∀ (P : List V), IsPathFrom G P (x t) (x (t - 1)) →
      (∀ v ∈ SPGT.interior P, v ∈ F) → Even (pathLength P) → 4 ≤ pathLength P →
      IsHoleList G (z :: P) →
      (¬ ∃ g ∈ F, G.Adj (x t) g ∧ G.Adj (x (t - 1)) g) →
      ∀ h ∈ wheelSystemX x (t - 2), IsHatForHole G (z :: P) z (x t) h →
      VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  have hxA2 : ∀ j ≤ t, x j ∉ wheelSystemA G z A₀ x (t - 2) := fun j hj =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj
  have hzA2 : z ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hxF : ∀ j ≤ t, x j ∉ F := fun j hj hmem => hxA2 j hj (hFsub hmem)
  have hzF : z ∉ F := fun hmem => hzA2 (hFsub hmem)
  have hzFnadj : ∀ v ∈ F, ¬ G.Adj z v := fun v hv =>
    WheelSystemBasics.wheelSystemA_no_nbr (hFsub hv)
  have hx1nc : ¬ VertexComplete G (x (t - 1)) (wheelSystemX x (t - 2)) := by
    have h := hws.2.2.2.2.2.1 (t - 1) (by omega) (by omega)
    have he : t - 1 - 1 = t - 2 := by omega
    rwa [he] at h
  have hnetx1 : x t ≠ x (t - 1) := by
    intro h; have := hinj t le_rfl (t - 1) (by omega) h; omega
  -- PAPER: "Let `P` be a path between `x_t` and `x_{t−1}` with interior in `F`."
  obtain ⟨P, hP, hPint⟩ := MinimalConnectedIsPath.exists_path_interior_in hFconn
    (hxF t le_rfl) (hxF (t - 1) (by omega)) hxtF hx1F
  have hP3 : 3 ≤ P.length :=
    MinimalConnectedIsPath.three_le_length_of_not_adj hP hnetx1 hnonadj
  have hPl : P.length = pathLength P + 1 := PathBasics.length_eq_pathLength_add_one hP.1
  -- PAPER: "Hence `P` has length > 2"  (otherwise its middle vertex is a common neighbour)
  have hPne2 : pathLength P ≠ 2 := by
    intro h2
    have h0 : P[0]'(by omega) = x t := PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
    have hl2 : P[2]'(by omega) = x (t - 1) := by
      rw [gidx P (show (2 : ℕ) = P.length - 1 by omega) (by omega) (by omega)]
      exact PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
    refine hnocommon ⟨P[1]'(by omega), hPint _ ?_, ?_, ?_⟩
    · exact PathBasics.getElem_mem_interior hP.1 (by omega) (by omega) (by omega)
    · have hadj : G.Adj (P[0]'(by omega)) (P[1]'(by omega)) :=
        PathBasics.path_adj_succ hP.1 (i := 0) (by omega)
      rw [h0] at hadj; exact hadj
    · have hadj : G.Adj (P[1]'(by omega)) (P[2]'(by omega)) :=
        PathBasics.path_adj_succ hP.1 (i := 1) (by omega)
      rw [hl2] at hadj; exact hadj.symm
  -- PAPER: "and from the hole `z-x_t-P-x_{t−1}-z` (`= C` say) it follows that `P` is even"
  have hzP : z ∉ P := by
    intro hmem
    have h1 : z ≠ x t := Ne.symm (hws.2.2.1 t le_rfl).2
    have h2 : z ≠ x (t - 1) := Ne.symm (hws.2.2.1 (t - 1) (by omega)).2
    exact hzF (hPint z ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hmem, h1, h2⟩))
  have hCh : IsHoleList G (z :: P) :=
    PrismBasics.isHoleList_of_path_add_vertex hP (by omega) (hzadj t le_rfl)
      (hzadj (t - 1) (by omega)) hzP (fun v hv => hzFnadj v (hPint v hv))
  have hClen : holeLength (z :: P) = pathLength P + 2 := by
    simp only [holeLength, List.length_cons]; omega
  have hPeven : Even (pathLength P) := by
    have h := hBerge.1 _ hCh
    rw [hClen] at h
    obtain ⟨k, hk⟩ := h
    exact ⟨k - 1, by omega⟩
  have hPlen : 4 ≤ pathLength P := by
    obtain ⟨k, hk⟩ := hPeven
    omega
  -- PAPER: "The only `X_{t−2}`-complete vertices in `C` are `z` and `x_t`, so by 2.10,
  -- `X_{t−2}` contains a leap or a hat for `C`."
  have hXanti : AnticonnectedSet G (wheelSystemX x (t - 2)) :=
    Thm203Prelim.anticonnected_wheelSystemX hws (t - 2) (by omega)
  have hPmem : ∀ w ∈ P, w = x t ∨ w = x (t - 1) ∨ w ∈ F := by
    intro w hw
    by_cases h1 : w = x t
    · exact Or.inl h1
    by_cases h2 : w = x (t - 1)
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hPint w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
      ⟨hw, h1, h2⟩)))
  have hcX : ∀ w ∈ (z :: P), w ∉ wheelSystemX x (t - 2) := by
    intro w hw hwX
    obtain ⟨j, hj, hje⟩ := hwX
    rcases List.mem_cons.mp hw with h | h
    · exact (hws.2.2.1 j (by omega)).2 (by rw [← hje, h])
    · rcases hPmem w h with h' | h' | h'
      · have := hinj t le_rfl j (by omega) (by rw [← h', hje]); omega
      · have := hinj (t - 1) (by omega) j (by omega) (by rw [← h', hje]); omega
      · exact hxF j (by omega) (by rw [← hje]; exact h')
  have honly : ∀ w ∈ (z :: P), VertexComplete G w (wheelSystemX x (t - 2)) →
      w = z ∨ w = x t := by
    intro w hw hwc
    rcases List.mem_cons.mp hw with h | h
    · exact Or.inl h
    · rcases hPmem w h with h' | h' | h'
      · exact Or.inr h'
      · exact absurd (by rw [← h']; exact hwc) hx1nc
      · exact absurd (hFsub h') (by
          intro hmem
          exact WheelSystemBasics.wheelSystemA_no_complete hmem hwc)
  have hzc : VertexComplete G z (wheelSystemX x (t - 2)) := by
    rintro v ⟨j, hj, rfl⟩
    exact hzadj j (by omega)
  have hClen4 : 4 < holeLength (z :: P) := by rw [hClen]; omega
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_10 G hBerge (wheelSystemX x (t - 2))
      hXanti (z :: P) hCh hcX hClen4 z (x t) (by simp)
      (by simp [(PathBasics.isPathFrom_ends_mem hP).1]) (hzadj t le_rfl)
      hzc hXc honly with hhat | hleap
  · obtain ⟨h, hhX, hhat⟩ := hhat
    exact hhatcase P hP hPint hPeven hPlen hCh hnocommon h hhX hhat
  · obtain ⟨a, haX, b, hbX, hleap⟩ := hleap
    exact hleapcase P hP hPint hPeven hPlen hCh a haX b hbX hleap

/-- **20.3, step (2).** -/
theorem step2 {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hstep1 : ¬ ((∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x t) a) ∧
      (∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)))
    (hcontra : ¬ (VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y)) :
    ∃ (q : V) (R : List V) (rn : V), Cond2 G z A₀ x t q R rn := by
  classical
  have hws : IsWheelSystem G z A₀ x t := hd.1
  have hA2conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 2)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3A2 : wheelSystemA G z A₀ x (t - 3) ⊆ wheelSystemA G z A₀ x (t - 2) :=
    WheelSystemBasics.wheelSystemA_mono (by omega)
  have hxtA2 : ∃ f ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x t) f := hd.2.2.2.2.2.2.2.2
  have hx1A2 : ∃ f ∈ wheelSystemA G z A₀ x (t - 2), G.Adj (x (t - 1)) f :=
    Thm203Prelim.exists_nbr_wheelSystemA hframe hws (i := t - 1) (k := t - 2)
      (by omega) (by omega) (by omega)
  -- PAPER: "let `F` be a minimal connected subgraph of `A_{t−2}` including `A_{t−3}` and
  -- containing neighbours of both `x_t` and `x_{t−1}`"
  have hex : ∃ n : ℕ, ∃ F : Set V,
      (ConnectedSet G F ∧ F ⊆ wheelSystemA G z A₀ x (t - 2) ∧
        wheelSystemA G z A₀ x (t - 3) ⊆ F ∧
        (∃ f ∈ F, G.Adj (x t) f) ∧ (∃ f ∈ F, G.Adj (x (t - 1)) f)) ∧ F.ncard = n :=
    ⟨_, wheelSystemA G z A₀ x (t - 2), ⟨hA2conn, subset_rfl, hA3A2, hxtA2, hx1A2⟩, rfl⟩
  obtain ⟨F, ⟨hFconn, hFsub, hA3F, hxtF, hx1F⟩, hFcard⟩ := Nat.find_spec hex
  have hFmin : ∀ F' : Set V, ConnectedSet G F' → F' ⊆ F →
      wheelSystemA G z A₀ x (t - 3) ⊆ F' →
      (∃ f ∈ F', G.Adj (x t) f) → (∃ f ∈ F', G.Adj (x (t - 1)) f) → F ⊆ F' := by
    intro F' hc hsub h3 h1 h2
    have hle : Nat.find hex ≤ F'.ncard :=
      Nat.find_min' hex ⟨F', ⟨hc, hsub.trans hFsub, h3, h1, h2⟩, rfl⟩
    rw [← hFcard] at hle
    have hEq : F' = F := Set.eq_of_subset_of_ncard_le hsub hle (Set.toFinite _)
    intro v hv
    rw [hEq]
    exact hv
  -- PAPER: "If `x_t`, `x_{t−1}` have a common neighbour in `F`, then the claim is satisfied
  -- (from the minimality of `F`)"
  by_cases hcom : ∃ f ∈ F, G.Adj (x t) f ∧ G.Adj (x (t - 1)) f
  · obtain ⟨q, hqF, hqt, hqt1⟩ := hcom
    have hqA2 : q ∈ wheelSystemA G z A₀ x (t - 2) := hFsub hqF
    by_cases hqA3 : q ∈ wheelSystemA G z A₀ x (t - 3)
    · -- `q` already lies in `A_{t−3}`: take `R = [q]`, so `A_{t−3} ∪ V(R \ q) = A_{t−3}`
      refine ⟨q, [q], q, hqA2, hqt.symm, hqt1.symm,
        ⟨PathBasics.isPathList_singleton G q, rfl, rfl⟩, ?_, hqA3, ?_⟩
      · intro v hv; rw [List.mem_singleton] at hv; rw [hv]; exact hqA2
      · have hsub : SRset (wheelSystemA G z A₀ x (t - 3)) [q] ⊆
            wheelSystemA G z A₀ x (t - 3) := by
          rintro v (hv | hv)
          · exact hv
          · simp only [List.tail_cons, Set.mem_setOf_eq, List.not_mem_nil] at hv
        rintro ⟨⟨s, hs, hsa⟩, ⟨s', hs', hs'a⟩⟩
        exact hstep1 ⟨⟨s, hsub hs, hsa⟩, ⟨s', hsub hs', hs'a⟩⟩
    · -- otherwise take for `R` the initial segment of a path of `F` reaching `A_{t−3}`
      obtain ⟨a0, ha0⟩ := hframe.1
      have ha0A3 : a0 ∈ wheelSystemA G z A₀ x (t - 3) :=
        Thm203Prelim.A₀_subset_wheelSystemA' hframe hws (by omega) ha0
      have ha0F : a0 ∈ F := hA3F ha0A3
      have hqnea0 : q ≠ a0 := fun h => hqA3 (by rw [h]; exact ha0A3)
      obtain ⟨P0, hP0, hP0mem⟩ :=
        InducedPathExtraction.exists_isPathFrom_of_connected hFconn hqF ha0F
      obtain ⟨s0, hs0, hs0adj⟩ := exists_adj_tail hP0 hqnea0
      have hvA : ∃ a ∈ F, G.Adj q a := ⟨s0, hP0mem s0 (List.mem_of_mem_tail hs0), hs0adj⟩
      obtain ⟨p, hpFA3, R, hR, hRpos, hRF, hRA3⟩ :=
        FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G F
          (wheelSystemA G z A₀ x (t - 3)) q hFconn hvA ⟨a0, ha0F, ha0A3⟩ hqA3
      have hqnep : q ≠ p := fun h => hqA3 (by rw [h]; exact hpFA3.2)
      have htailF : ∀ v ∈ R.tail, v ∈ F := by
        intro v hv
        refine hRF v (List.mem_of_mem_tail hv) ?_
        intro hvq
        exact head_notMem_tail hR (by rw [← hvq]; exact hv)
      refine ⟨q, R, p, hqA2, hqt.symm, hqt1.symm, hR, ?_, hpFA3.2, ?_⟩
      · intro v hv
        by_cases h : v = q
        · rw [h]; exact hqA2
        · exact hFsub (hRF v hv h)
      · rintro ⟨hxtn, hx1n⟩
        have hF'conn : ConnectedSet G (SRset (wheelSystemA G z A₀ x (t - 3)) R) :=
          connectedSet_SRset hA3conn hR hpFA3.2 hqnep
        have hF'sub : SRset (wheelSystemA G z A₀ x (t - 3)) R ⊆ F := by
          rintro v (hv | hv)
          · exact hA3F hv
          · exact htailF v hv
        rcases hFmin _ hF'conn hF'sub Set.subset_union_left hxtn hx1n hqF with hv | hv
        · exact hqA3 hv
        · exact head_notMem_tail hR hv
  · refine absurd (step2_no_common_nbr hG hframe hd ht hFconn hFsub hA3F hxtF hx1F hcom hFmin
      (fun P hP hPint hPeven hPlen hCh a haX b hbX hleap =>
        step2_leap_case hG hframe hd ht hFconn hFsub P hP hPint hPeven hPlen hCh a haX b hbX
          hleap)
      (fun P hP hPint hPeven hPlen hCh hnc h hhX hhat =>
        step2_hat_case hG hframe hd ht hFconn hFsub hA3F P hP hPint hPeven hPlen hCh h hhX
          hhat hnc (fun hzYC => step2_hat_wheel hG hframe hd ht hFconn hFsub hA3F P hP hPint
            hPeven hPlen hCh h hhX hhat hnc hzYC))) hcontra

/-- **20.3, step (3), the case `x_{t−1}` has a neighbour in `A_{t−3} ∪ V(R \ q)`.**

`hqmin` is the distilled consequence of *"Choose `q`, `R` as in (2) with `R` minimal"* — see
`AMBIGUITIES.md` A11b. -/
theorem caseA {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    {q : V} (hqA2 : q ∈ wheelSystemA G z A₀ x (t - 2))
    (hqt : G.Adj q (x t)) (hqt1 : G.Adj q (x (t - 1)))
    {R : List V} {rn : V} (hR : IsPathFrom G R q rn)
    (hRsub : ∀ v ∈ R, v ∈ wheelSystemA G z A₀ x (t - 2))
    (hrnA3 : rn ∈ wheelSystemA G z A₀ x (t - 3))
    (hqmin : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q a → R.length ≤ 2)
    (hno1 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a)
    (hx1SR : ∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj (x (t - 1)) s)
    (hxtSR : ∀ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, ¬ G.Adj (x t) s)
    (hnone_sq : ¬ ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y')
    {Q : List V} (hQ : IsAntipathFrom G Q (x (t - 1)) q)
    (hQint : ∀ y ∈ SPGT.interior Q, y ∈ wheelSystemX x (t - 2))
    (hQeven : Even (pathLength Q)) : False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hF5 : InF5 G := hG.1.1
  obtain ⟨hws, hYne, hYanti, ⟨hzY, hxY⟩, hVC, hnVC, ht3, hXc, hAn⟩ := id hd
  have hinj : ∀ j ≤ t, ∀ k ≤ t, x j = x k → j = k := hws.2.1
  have hzadj : ∀ j ≤ t, G.Adj z (x j) := hws.2.2.2.2.2.2
  have hnonadj : ¬ G.Adj (x t) (x (t - 1)) := YDiamondTruncation.ydiamond_top_nonadj hd
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3A2 : wheelSystemA G z A₀ x (t - 3) ⊆ wheelSystemA G z A₀ x (t - 2) :=
    WheelSystemBasics.wheelSystemA_mono (by omega)
  have hxA2 : ∀ j ≤ t, x j ∉ wheelSystemA G z A₀ x (t - 2) := fun j hj =>
    Thm203Prelim.x_notMem_wheelSystemA hws hj
  have hzA2 : z ∉ wheelSystemA G z A₀ x (t - 2) :=
    Thm203Prelim.z_notMem_wheelSystemA hws (by omega)
  have hX2A2 : ∀ v ∈ wheelSystemX x (t - 2), v ∉ wheelSystemA G z A₀ x (t - 2) := by
    rintro v ⟨j, hj, rfl⟩; exact hxA2 j (by omega)
  have hqA3 : q ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hno1 q h hqt1.symm
  -- PAPER: "all neighbours of `x_{t−1}` in `A_{t−3} ∪ V(R \ q)` lie in the interior of `R`,
  -- and in particular `R` has length ≥ 2"
  rcases R with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, rest⟩⟩⟩
  · exact absurd rfl hR.1.1
  · obtain ⟨s, hs, hsadj⟩ := hx1SR
    rcases hs with hs | hs
    · exact hno1 s hs hsadj
    · simp only [List.tail_cons, Set.mem_setOf_eq, List.not_mem_nil] at hs
  · have hc1 : c1 = rn := by simpa using hR.2.2
    obtain ⟨s, hs, hsadj⟩ := hx1SR
    rcases hs with hs | hs
    · exact hno1 s hs hsadj
    · simp only [List.tail_cons, Set.mem_setOf_eq, List.mem_singleton] at hs
      exact hno1 s (by rw [hs, hc1]; exact hrnA3) hsadj
  -- ### the main case: `R = q-r₂-r₃-⋯-r_n`
  have hc0 : c0 = q := by simpa using hR.2.1
  subst hc0
  have hnd : (c0 :: c1 :: c2 :: rest).Nodup := PathBasics.path_nodup hR.1
  have hRlen : (c0 :: c1 :: c2 :: rest).length = rest.length + 3 := by simp
  -- the sub-path `r₂-⋯-r_n`
  have hR1 : IsPathFrom G (c1 :: c2 :: rest) c1 rn := by
    refine ⟨?_, rfl, ?_⟩
    · have := PathBasics.isPathList_drop hR.1 (k := 1) (by simp)
      simpa using this
    · simpa using hR.2.2
  have hrnmem : rn ∈ c2 :: rest := by
    have hlast : (c2 :: rest).getLast? = some rn := by simpa using hR.2.2
    exact PathBasics.getLast_mem hlast
  have hc1nern : c1 ≠ rn := by
    intro h
    have h2 : c1 ∈ c2 :: rest := h ▸ hrnmem
    exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 h2
  -- `S' = A_{t−3} ∪ {r₃,…,r_n}` is `SRset` of the sub-path
  have hS'conn : ConnectedSet G
      (SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest)) :=
    connectedSet_SRset hA3conn hR1 hrnA3 hc1nern
  have hS'sub : SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ⊆
      SRset (wheelSystemA G z A₀ x (t - 3)) (c0 :: c1 :: c2 :: rest) := by
    rintro v (hv | hv)
    · exact Or.inl hv
    · refine Or.inr ?_
      simp only [List.tail_cons, Set.mem_setOf_eq] at hv ⊢
      exact List.mem_cons_of_mem _ hv
  have hS'A2 : SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ⊆
      wheelSystemA G z A₀ x (t - 2) := by
    rintro v (hv | hv)
    · exact hA3A2 hv
    · simp only [List.tail_cons, Set.mem_setOf_eq] at hv
      exact hRsub v (by simp [hv])
  have hzS'nadj : ∀ a ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest),
      ¬ G.Adj z a := fun a ha => WheelSystemBasics.wheelSystemA_no_nbr (hS'A2 ha)
  have hzS' : z ∉ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) :=
    fun h => hzA2 (hS'A2 h)
  -- index bookkeeping along `R`
  have hmemidx : ∀ v ∈ c2 :: rest, ∃ i : ℕ,
      ∃ h : i + 2 < (c0 :: c1 :: c2 :: rest).length, (c0 :: c1 :: c2 :: rest)[i + 2] = v := by
    intro v hv
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_cons] at hi ⊢; omega
    · simpa using hiv
  have hqnadj : ∀ v ∈ c2 :: rest, ¬ G.Adj c0 v := by
    intro v hv hadj
    obtain ⟨i, hi, hiv⟩ := hmemidx v hv
    exact PathBasics.path_not_adj_of_gap hR.1 (i := 0) (j := i + 2) (by simp) hi
      (by omega) (by omega) (by rw [hiv]; exact hadj)
  have hr2nadj : ∀ v ∈ rest, ¬ G.Adj c1 v := by
    intro v hv hadj
    obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hv
    have hj : i + 3 < (c0 :: c1 :: c2 :: rest).length := by
      simp only [List.length_cons] at hi ⊢; omega
    refine PathBasics.path_not_adj_of_gap hR.1 (i := 1) (j := i + 3) (by simp) hj
      (by omega) (by omega) ?_
    have hh : (c0 :: c1 :: c2 :: rest)[i + 3] = v := by simpa using hiv
    rw [hh]; exact hadj
  have hqr2 : G.Adj c0 c1 := by
    have := PathBasics.path_adj_succ hR.1 (i := 0) (by simp)
    simpa using this
  have hr2r3 : G.Adj c1 c2 := by
    have := PathBasics.path_adj_succ hR.1 (i := 1) (by simp)
    simpa using this
  -- AMBIGUITIES A11b: `R` minimal ⟹ `q` has no neighbour in `A_{t−3}`
  have hqnoA3 : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj c0 a := by
    intro a ha hadj
    have := hqmin a ha hadj
    simp only [List.length_cons] at this
    omega
  have hc1A3 : c1 ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hqnoA3 c1 h hqr2
  have hqS' : ∀ a ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest),
      ¬ G.Adj c0 a := by
    rintro a (ha | ha)
    · exact hqnoA3 a ha
    · simp only [List.tail_cons, Set.mem_setOf_eq] at ha
      exact hqnadj a ha
  -- PAPER: "The antipath `x_t-x_{t−1}-Q-q` is odd"
  have hQp : IsPathFrom Gᶜ Q (x (t - 1)) c0 := hQ
  have hQmem : ∀ y ∈ Q, y = x (t - 1) ∨ y = c0 ∨ y ∈ wheelSystemX x (t - 2) := by
    intro y hy
    by_cases h1 : y = x (t - 1)
    · exact Or.inl h1
    by_cases h2 : y = c0
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQint y
      ((PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hy, h1, h2⟩)))
  have hxtQ : IsAntipathFrom G (x t :: Q) (x t) c0 := by
    refine PathAttach.isPathFrom_cons (G := Gᶜ) hQp ?_ ?_ ?_
    · rw [SimpleGraph.compl_adj]
      refine ⟨fun h => ?_, hnonadj⟩
      have := hinj t le_rfl (t - 1) (by omega) h; omega
    · intro hmem
      rcases hQmem _ hmem with h | h | h
      · have := hinj t le_rfl (t - 1) (by omega) h; omega
      · exact hxA2 t le_rfl (by rw [h]; exact hqA2)
      · obtain ⟨j, hj, hje⟩ := h
        have := hinj t le_rfl j (by omega) hje; omega
    · intro y hy hy1
      rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
      rcases hQmem y hy with h | h | h
      · exact hy1 h
      · exact hn (by rw [h]; exact hqt.symm)
      · exact hn (hXc y h)
  have hxtQodd : Odd (pathLength (x t :: Q)) := by
    have h1 : pathLength (x t :: Q) = Q.length := PathBasics.pathLength_cons _ _
    have h2 : Q.length = pathLength Q + 1 := PathBasics.length_eq_pathLength_add_one hQp.1
    obtain ⟨k, hk⟩ := hQeven
    exact ⟨k, by omega⟩
  -- PAPER: "so `x_{t−1}` has no neighbour in `A_{t−3} ∪ {r₃,…,r_n}`"
  have hx1noS' : ∀ a ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest),
      ¬ G.Adj (x (t - 1)) a := by
    intro a ha hadj
    have hQTS' : ∀ w ∈ (x t :: Q),
        w ∉ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) := by
      intro w hw hwS'
      rcases List.mem_cons.mp hw with h | h
      · exact hxA2 t le_rfl (by rw [← h]; exact hS'A2 hwS')
      · rcases hQmem w h with h' | h' | h'
        · exact hxA2 (t - 1) (by omega) (by rw [← h']; exact hS'A2 hwS')
        · rcases hwS' with hv | hv
          · exact hqA3 (by rw [← h']; exact hv)
          · simp only [List.tail_cons, Set.mem_setOf_eq] at hv
            exact (List.nodup_cons.mp hnd).1
              (by rw [← h']; exact List.mem_cons_of_mem _ hv)
        · obtain ⟨j, hj, hje⟩ := h'
          exact hxA2 j (by omega) (by rw [← hje]; exact hS'A2 hwS')
    have hintS' : ∀ w ∈ SPGT.interior (x t :: Q),
        ∃ b ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest), G.Adj w b := by
      intro w hw
      obtain ⟨hwmem, hwxt, hwq⟩ := (PathBasics.mem_interior_iff_of_pathFrom hxtQ).mp hw
      rcases List.mem_cons.mp hwmem with h | h
      · exact absurd h hwxt
      · rcases hQmem w h with h' | h' | h'
        · exact ⟨a, ha, by rw [h']; exact hadj⟩
        · exact absurd h' hwq
        · obtain ⟨j, hj, hje⟩ := h'
          obtain ⟨b, hb, hbadj⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
            (i := j) (k := t - 3) (by omega) (by omega) (by omega)
          exact ⟨b, Or.inl hb, by rw [hje]; exact hbadj⟩
    have hintz : ∀ w ∈ SPGT.interior (x t :: Q), G.Adj z w := by
      intro w hw
      obtain ⟨hwmem, hwxt, hwq⟩ := (PathBasics.mem_interior_iff_of_pathFrom hxtQ).mp hw
      rcases List.mem_cons.mp hwmem with h | h
      · exact absurd h hwxt
      · rcases hQmem w h with h' | h' | h'
        · rw [h']; exact hzadj (t - 1) (by omega)
        · exact absurd h' hwq
        · obtain ⟨j, hj, hje⟩ := h'
          rw [hje]; exact hzadj j (by omega)
    rcases Thm203AntipathTools.exists_end_nbr_of_odd_antipath hBerge hS'conn hzS' hzS'nadj
        hxtQ hxtQodd hqt.symm hQTS' hintS' hintz with ⟨b, hb, hbadj⟩ | ⟨b, hb, hbadj⟩
    · exact hxtSR b (hS'sub hb) hbadj
    · exact hqS' b hb hbadj
  -- PAPER: "Hence `r₂` is its only neighbour in `A_{t−3} ∪ V(R \ q)`."
  have hx1r2 : G.Adj (x (t - 1)) c1 := by
    obtain ⟨s, hs, hsadj⟩ := hx1SR
    rcases hs with hs | hs
    · exact absurd hsadj (hno1 s hs)
    · simp only [List.tail_cons, Set.mem_setOf_eq] at hs
      rcases List.mem_cons.mp hs with h | h
      · rw [← h]; exact hsadj
      · exact absurd hsadj (hx1noS' s (Or.inr h))
  -- PAPER: "So some antipath `Q'` between `x_{t−1}` and `r₂` with interior in `X_{t−2}` is even."
  have hc1A2 : c1 ∈ wheelSystemA G z A₀ x (t - 2) := hRsub c1 (by simp)
  obtain ⟨Q', hQ', hQ'int, hQ'even⟩ :=
    Thm203Step3Aux.exists_even_antipath hG hframe hd ht hno1 hc1A2 hx1r2 hnone_sq
  have hQ'p : IsPathFrom Gᶜ Q' (x (t - 1)) c1 := hQ'
  have hQ'mem : ∀ y ∈ Q', y = x (t - 1) ∨ y = c1 ∨ y ∈ wheelSystemX x (t - 2) := by
    intro y hy
    by_cases h1 : y = x (t - 1)
    · exact Or.inl h1
    by_cases h2 : y = c1
    · exact Or.inr (Or.inl h2)
    exact Or.inr (Or.inr (hQ'int y
      ((PathBasics.mem_interior_iff_of_pathFrom hQ'p).mpr ⟨hy, h1, h2⟩)))
  have hzc1 : ¬ G.Adj z c1 := WheelSystemBasics.wheelSystemA_no_nbr hc1A2
  have hznec1 : z ≠ c1 := by
    intro h
    rw [← h] at hc1A2
    exact hzA2 hc1A2
  -- PAPER: "Hence the antipath `x_{t−1}-Q'-r₂-z` is odd."
  have hQ'z : IsAntipathFrom G (Q' ++ [z]) (x (t - 1)) z := by
    refine PathAttach.isPathFrom_concat (G := Gᶜ) hQ'p ?_ ?_ ?_
    · rw [SimpleGraph.compl_adj]; exact ⟨hznec1, hzc1⟩
    · intro hmem
      rcases hQ'mem _ hmem with h | h | h
      · exact (hws.2.2.1 (t - 1) (by omega)).2 h.symm
      · exact hznec1 h
      · obtain ⟨j, hj, hje⟩ := h
        exact (hws.2.2.1 j (by omega)).2 hje.symm
    · intro y hy hyc1
      rw [SimpleGraph.compl_adj]; rintro ⟨-, hn⟩
      rcases hQ'mem y hy with h | h | h
      · exact hn (by rw [h]; exact hzadj (t - 1) (by omega))
      · exact absurd h hyc1
      · obtain ⟨j, hj, hje⟩ := h
        exact hn (by rw [hje]; exact hzadj j (by omega))
  have hQ'pos : 0 < Q'.length := PathBasics.path_length_pos hQ'p.1
  have hQ'zlen : (Q' ++ [z]).length = Q'.length + 1 := by simp
  have hQ'zodd : Odd (pathLength (Q' ++ [z])) := by
    have h1 := PathBasics.pathLength_eq (Q' ++ [z])
    have h2 := PathBasics.pathLength_eq Q'
    obtain ⟨k, hk⟩ := hQ'even
    exact ⟨k, by omega⟩
  have hQ'zS' : ∀ w ∈ (Q' ++ [z]),
      w ∉ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) := by
    intro w hw hwS'
    rcases List.mem_append.mp hw with h | h
    · rcases hQ'mem w h with h' | h' | h'
      · exact hxA2 (t - 1) (by omega) (by rw [← h']; exact hS'A2 hwS')
      · rcases hwS' with hv | hv
        · exact hc1A3 (by rw [← h']; exact hv)
        · simp only [List.tail_cons, Set.mem_setOf_eq] at hv
          exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by rw [← h']; exact hv)
      · obtain ⟨j, hj, hje⟩ := h'
        exact hxA2 j (by omega) (by rw [← hje]; exact hS'A2 hwS')
    · rw [List.mem_singleton] at h
      rw [h] at hwS'
      exact hzS' hwS'
  have hQ'zint : ∀ w ∈ SPGT.interior (Q' ++ [z]),
      ∃ b ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest), G.Adj w b := by
    intro w hw
    obtain ⟨hwmem, hwx1, hwz⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ'z).mp hw
    rcases List.mem_append.mp hwmem with h | h
    · rcases hQ'mem w h with h' | h' | h'
      · exact absurd h' hwx1
      · exact ⟨c2, Or.inr (by simp), by rw [h']; exact hr2r3⟩
      · obtain ⟨j, hj, hje⟩ := h'
        obtain ⟨b, hb, hbadj⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
          (i := j) (k := t - 3) (by omega) (by omega) (by omega)
        exact ⟨b, Or.inl hb, by rw [hje]; exact hbadj⟩
    · rw [List.mem_singleton] at h
      exact absurd h hwz
  -- PAPER: "so by 13.6 this antipath has length 3, that is, `Q'` has length 2"
  have hlen3 : pathLength (Q' ++ [z]) = 3 :=
    Thm203AntipathTools.antipath_length_three_of_odd hF5 hS'conn hQ'z hQ'zodd
      (hzadj (t - 1) (by omega)).symm hQ'zS' hx1noS' hzS'nadj hQ'zint
  have hQ'l3 : Q'.length = 3 := by
    have h1 := PathBasics.pathLength_eq (Q' ++ [z])
    omega
  -- PAPER: "Let `x_i` be its middle vertex."
  obtain ⟨xi, hxieq⟩ : ∃ v : V, Q'[1]'(by omega) = v := ⟨_, rfl⟩
  have hxiint : xi ∈ SPGT.interior Q' := by
    rw [← hxieq]
    exact PathBasics.getElem_mem_interior hQ'p.1 (by omega) (by omega) (by omega)
  have hxiX2 : xi ∈ wheelSystemX x (t - 2) := hQ'int xi hxiint
  obtain ⟨jx, hjx, hxije⟩ := id hxiX2
  have hQ'0 : Q'[0]'(by omega) = x (t - 1) :=
    PathBasics.getElem_zero_of_head? hQ'p.2.1 (by omega)
  have hQ'2 : Q'[2]'(by omega) = c1 := by
    have hl := PathBasics.getElem_last_of_getLast? hQ'p.2.2 (show 0 < Q'.length by omega)
    simp only [hQ'l3] at hl
    exact hl
  have hx1xi : ¬ G.Adj (x (t - 1)) xi := by
    have hadj01 : Gᶜ.Adj (Q'[0]'(by omega)) (Q'[1]'(by omega)) :=
      PathBasics.path_adj_succ hQ'p.1 (by omega)
    rw [hQ'0, hxieq, SimpleGraph.compl_adj] at hadj01
    exact hadj01.2
  have hxic1 : ¬ G.Adj xi c1 := by
    have hadj12 : Gᶜ.Adj (Q'[1]'(by omega)) (Q'[2]'(by omega)) :=
      PathBasics.path_adj_succ hQ'p.1 (by omega)
    rw [hxieq, hQ'2, SimpleGraph.compl_adj] at hadj12
    exact hadj12.2
  -- PAPER: "Then the connected set `A_{t−3} ∪ V(R \ {r₁,r₂}) ∪ {x_i, x_t, z}` (= `F`)
  -- catches the triangle `{r₁, r₂, x_{t−1}}`"
  have hxiA2 : xi ∉ wheelSystemA G z A₀ x (t - 2) := by
    rw [hxije]; exact hxA2 jx (by omega)
  have hxinex1 : xi ≠ x (t - 1) := by
    rw [hxije]; intro h; have := hinj jx (by omega) (t - 1) (by omega) h; omega
  have hne01 : c0 ≠ c1 := fun h => (List.nodup_cons.mp hnd).1 (by rw [h]; simp)
  have hne0x : c0 ≠ x (t - 1) := by
    intro h; rw [h] at hqA2; exact hxA2 (t - 1) (by omega) hqA2
  have hne1x : c1 ≠ x (t - 1) := by
    intro h; rw [h] at hc1A2; exact hxA2 (t - 1) (by omega) hc1A2
  have htri : IsTriangle G ({c0, c1, x (t - 1)} : Set V) := by
    refine ⟨Set.ncard_eq_three.mpr ⟨c0, c1, x (t - 1), hne01, hne0x, hne1x, rfl⟩, ?_⟩
    intro u hu v hv huv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      first
        | exact absurd rfl huv
        | exact hqr2
        | exact hqt1
        | exact hqr2.symm
        | exact hqt1.symm
        | exact hx1r2.symm
        | exact hx1r2
  have hzxi : G.Adj z xi := by rw [hxije]; exact hzadj jx (by omega)
  have hxinbrS' : ∃ p ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest),
      G.Adj xi p := by
    obtain ⟨b, hb, hbadj⟩ := Thm203Prelim.exists_nbr_wheelSystemA hframe hws
      (i := jx) (k := t - 3) (by omega) (by omega) (by omega)
    exact ⟨b, Or.inl hb, by rw [hxije]; exact hbadj⟩
  have hFconn : ConnectedSet G
      (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪ {z}) ∪ {x t}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton
      (ConnectedSetUnionAttach.connectedSet_union_singleton
        (ConnectedSetUnionAttach.connectedSet_union_singleton hS'conn hxinbrS')
        ⟨xi, Or.inr rfl, hzxi⟩)
      ⟨z, Or.inr rfl, (hzadj t le_rfl).symm⟩
  have hFnotA : ∀ f ∈ (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪
      {z}) ∪ {x t}), f ≠ c0 ∧ f ≠ c1 ∧ f ≠ x (t - 1) := by
    rintro f (((hf | hf) | hf) | hf)
    · refine ⟨?_, ?_, ?_⟩
      · intro h; rw [h] at hf
        rcases hf with hv | hv
        · exact hqA3 hv
        · simp only [List.tail_cons, Set.mem_setOf_eq] at hv
          exact (List.nodup_cons.mp hnd).1 (List.mem_cons_of_mem _ hv)
      · intro h; rw [h] at hf
        rcases hf with hv | hv
        · exact hc1A3 hv
        · simp only [List.tail_cons, Set.mem_setOf_eq] at hv
          exact (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 hv
      · intro h; rw [h] at hf
        exact hxA2 (t - 1) (by omega) (hS'A2 hf)
    · rw [Set.mem_singleton_iff] at hf
      refine ⟨?_, ?_, ?_⟩
      · intro h; rw [hf] at h; rw [← h] at hqA2; exact hxiA2 hqA2
      · intro h; rw [hf] at h; rw [← h] at hc1A2; exact hxiA2 hc1A2
      · intro h; rw [hf] at h; exact hxinex1 h
    · rw [Set.mem_singleton_iff] at hf
      refine ⟨?_, ?_, ?_⟩
      · intro h; rw [hf] at h; rw [← h] at hqA2; exact hzA2 hqA2
      · intro h; rw [hf] at h; rw [← h] at hc1A2; exact hzA2 hc1A2
      · intro h; rw [hf] at h; exact (hws.2.2.1 (t - 1) (by omega)).2 h.symm
    · rw [Set.mem_singleton_iff] at hf
      refine ⟨?_, ?_, ?_⟩
      · intro h; rw [hf] at h; rw [← h] at hqA2; exact hxA2 t le_rfl hqA2
      · intro h; rw [hf] at h; rw [← h] at hc1A2; exact hxA2 t le_rfl hc1A2
      · intro h; rw [hf] at h
        have := hinj t le_rfl (t - 1) (by omega) h; omega
  have hcatch : Catches G
      (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪ {z}) ∪ {x t})
      ({c0, c1, x (t - 1)} : Set V) := by
    refine ⟨htri, hFconn, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro f hf hfA
      obtain ⟨h1, h2, h3⟩ := hFnotA f hf
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfA
      rcases hfA with h | h | h
      · exact h1 h
      · exact h2 h
      · exact h3 h
    · intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl | rfl
      · exact ⟨x t, Or.inr rfl, hqt⟩
      · exact ⟨c2, Or.inl (Or.inl (Or.inl (Or.inr (by simp)))), hr2r3⟩
      · exact ⟨z, Or.inl (Or.inr rfl), (hzadj (t - 1) (by omega)).symm⟩
  have hFsubA : (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪ {z}) ∪
      {x t}) ⊆ ({c0, c1, x (t - 1)} : Set V)ᶜ := by
    intro f hf hfA
    obtain ⟨h1, h2, h3⟩ := hFnotA f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hfA
    rcases hfA with h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
  -- the three neighbour restrictions printed by the paper
  have hNx1 : ∀ f ∈ (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪
      {z}) ∪ {x t}), G.Adj (x (t - 1)) f → f = z := by
    rintro f (((hf | hf) | hf) | hf) hadj
    · exact absurd hadj (hx1noS' f hf)
    · rw [Set.mem_singleton_iff] at hf; rw [hf] at hadj; exact absurd hadj hx1xi
    · rw [Set.mem_singleton_iff] at hf; exact hf
    · rw [Set.mem_singleton_iff] at hf; rw [hf] at hadj; exact absurd hadj.symm hnonadj
  have hNc1 : ∀ f ∈ (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪
      {z}) ∪ {x t}), G.Adj c1 f →
      f ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) := by
    rintro f (((hf | hf) | hf) | hf) hadj
    · exact hf
    · rw [Set.mem_singleton_iff] at hf; rw [hf] at hadj; exact absurd hadj.symm hxic1
    · rw [Set.mem_singleton_iff] at hf; rw [hf] at hadj; exact absurd hadj.symm hzc1
    · rw [Set.mem_singleton_iff] at hf; rw [hf] at hadj
      exact absurd hadj.symm (hxtSR c1 (Or.inr (by simp)))
  -- PAPER: "This contradicts 17.1, since `z` has no neighbour in `A_{t−3} ∪ {r₃}`."
  rcases _root_.Workspace.Statements.S17.SPGT.thm_17_1 G hG ({c0, c1, x (t - 1)} : Set V) htri
      (((SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) ∪ {xi}) ∪ {z}) ∪ {x t})
      hFsubA hcatch with hrefl | h2
  · obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hAeq, hBF, hRfl⟩ := hrefl
    have hu : x (t - 1) ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hAeq]; simp
    have hv : c1 ∈ ({a₁, a₂, a₃} : Set V) := by rw [← hAeq]; simp
    obtain ⟨bu, hbu, bv, hbv, hadju, hadjv, hadjuv⟩ :=
      reflection_pair hRfl hu hv (Ne.symm hne1x)
    have hbuz : bu = z := hNx1 bu (hBF hbu) hadju
    have hbvS' : bv ∈ SRset (wheelSystemA G z A₀ x (t - 3)) (c1 :: c2 :: rest) :=
      hNc1 bv (hBF hbv) hadjv
    exact hzS'nadj bv hbvS' (by rw [← hbuz]; exact hadjuv)
  · obtain ⟨f, hfF, hfcard⟩ := h2
    have hsub : ∃ v0 : V, (G.neighborSet f ∩ ({c0, c1, x (t - 1)} : Set V)) ⊆ {v0} := by
      rcases hfF with ((hf | hf) | hf) | hf
      · refine ⟨c1, ?_⟩
        rintro u ⟨hu1, hu2⟩
        have hadj : G.Adj f u := hu1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with h | h | h
        · exact absurd (show G.Adj c0 f by rw [← h]; exact hadj.symm) (hqS' f hf)
        · exact h
        · exact absurd (show G.Adj (x (t - 1)) f by rw [← h]; exact hadj.symm)
            (hx1noS' f hf)
      · rw [Set.mem_singleton_iff] at hf
        refine ⟨c0, ?_⟩
        rintro u ⟨hu1, hu2⟩
        have hadj : G.Adj f u := hu1
        rw [hf] at hadj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with h | h | h
        · exact h
        · exact absurd (show G.Adj xi c1 by rw [← h]; exact hadj) hxic1
        · exact absurd (show G.Adj (x (t - 1)) xi by rw [← h]; exact hadj.symm) hx1xi
      · rw [Set.mem_singleton_iff] at hf
        refine ⟨x (t - 1), ?_⟩
        rintro u ⟨hu1, hu2⟩
        have hadj : G.Adj f u := hu1
        rw [hf] at hadj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with h | h | h
        · exact absurd (show G.Adj z c0 by rw [← h]; exact hadj)
            (WheelSystemBasics.wheelSystemA_no_nbr hqA2)
        · exact absurd (show G.Adj z c1 by rw [← h]; exact hadj) hzc1
        · exact h
      · rw [Set.mem_singleton_iff] at hf
        refine ⟨c0, ?_⟩
        rintro u ⟨hu1, hu2⟩
        have hadj : G.Adj f u := hu1
        rw [hf] at hadj
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu2
        rcases hu2 with h | h | h
        · exact h
        · exact absurd (show G.Adj (x t) c1 by rw [← h]; exact hadj)
            (hxtSR c1 (Or.inr (by simp)))
        · exact absurd (show G.Adj (x t) (x (t - 1)) by rw [← h]; exact hadj) hnonadj
    obtain ⟨v0, hsub⟩ := hsub
    have hle := ncard_le_one_of_subset_singleton hsub
    omega

theorem assembly {G : SimpleGraph V} (hG : InF7 G) {z : V} {A₀ : Set V}
    (hframe : IsFrame G z A₀) {x : ℕ → V} {t : ℕ} {Y : Set V}
    (hd : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hnone : ¬ ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y'))) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  classical
  have hws : IsWheelSystem G z A₀ x t := hd.1
  have hA2conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 2)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3conn : ConnectedSet G (wheelSystemA G z A₀ x (t - 3)) :=
    WheelSystemBasics.connectedSet_wheelSystemA hframe.1
  have hA3A2 : wheelSystemA G z A₀ x (t - 3) ⊆ wheelSystemA G z A₀ x (t - 2) :=
    WheelSystemBasics.wheelSystemA_mono (by omega)
  -- PAPER: the `Y`-square alternative of `hnone`, isolated
  have hnone_sq : ¬ ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y' := by
    rintro ⟨Y', h1, h2, h3⟩
    exact hnone ⟨Y', h1, h2, Or.inr (Or.inl h3)⟩
  -- PAPER (1): "Not both `x_t` and `x_{t−1}` have neighbours in `A_{t−3}`."
  have step1 : ¬ ((∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x t) a) ∧
      (∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a)) := by
    rintro ⟨h1, h2⟩
    obtain ⟨Y', hY'a, hY'sub, x', hx'⟩ :=
      Thm203Step1.exists_diamond_of_both_nbrs hframe hd ht h1 h2
    exact hnone ⟨Y', hY'a, hY'sub, Or.inl ⟨x', hx'⟩⟩
  -- PAPER: "Assume that either `z` is not `Y`-complete or `G` contains no wheel `(C,Y)`."
  by_contra hcontra
  -- PAPER (2), then "Choose `q`, `R` as in (2) with `R` minimal"
  have hex : ∃ n : ℕ, ∃ (q : V) (R : List V) (rn : V),
      Cond2 G z A₀ x t q R rn ∧ R.length = n := by
    obtain ⟨q, R, rn, hc⟩ := step2 hG hframe hd ht step1 hcontra
    exact ⟨R.length, q, R, rn, hc, rfl⟩
  obtain ⟨q, R, rn, hc, hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (q' : V) (R' : List V) (rn' : V),
      Cond2 G z A₀ x t q' R' rn' → R.length ≤ R'.length := by
    intro q' R' rn' h'
    rw [hlen]
    exact Nat.find_min' hex ⟨q', R', rn', h', rfl⟩
  obtain ⟨hqA2, hqt, hqt1, hR, hRsub, hrnA3, hnotboth⟩ := hc
  have hSRsub : SRset (wheelSystemA G z A₀ x (t - 3)) R ⊆ wheelSystemA G z A₀ x (t - 2) := by
    rintro v (hv | hv)
    · exact hA3A2 hv
    · exact hRsub v (List.mem_of_mem_tail hv)
  have hA3SR : wheelSystemA G z A₀ x (t - 3) ⊆ SRset (wheelSystemA G z A₀ x (t - 3)) R :=
    Set.subset_union_left
  -- AMBIGUITIES A11b: the distilled form of the minimality of `R`
  have hqmin : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q a → R.length ≤ 2 := by
    intro a ha hadj
    have hc2 : Cond2 G z A₀ x t q [q, a] a := by
      refine ⟨hqA2, hqt, hqt1, ⟨PathBasics.isPathList_pair hadj, rfl, by simp⟩, ?_, ha, ?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with h | h
        · exact h ▸ hqA2
        · rw [List.mem_singleton] at h; exact h ▸ hA3A2 ha
      · have hsub : SRset (wheelSystemA G z A₀ x (t - 3)) [q, a] ⊆
            wheelSystemA G z A₀ x (t - 3) := by
          rintro v (hv | hv)
          · exact hv
          · simp only [List.tail_cons, Set.mem_setOf_eq, List.mem_singleton] at hv
            exact hv ▸ ha
        rintro ⟨⟨s, hs, hsa⟩, ⟨s', hs', hs'a⟩⟩
        exact step1 ⟨⟨s, hsub hs, hsa⟩, ⟨s', hsub hs', hs'a⟩⟩
    simpa using hmin q [q, a] a hc2
  -- PAPER (3): "`x_{t−1}` has neighbours in `A_{t−3}`."
  have step3 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a := by
    by_contra hcon
    push Not at hcon
    have hcon' : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x (t - 1)) a := hcon
    -- "it follows that `q ∉ A_{t−3}`, and so `R` has length > 0"
    have hqA3 : q ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hcon' q h hqt1.symm
    have hqrn : q ≠ rn := fun h => hqA3 (h ▸ hrnA3)
    have hSRconn : ConnectedSet G (SRset (wheelSystemA G z A₀ x (t - 3)) R) :=
      connectedSet_SRset hA3conn hR hrnA3 hqrn
    obtain ⟨s0, hs0, hs0adj⟩ := exists_adj_tail hR hqrn
    have hqSR : ∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj q s :=
      ⟨s0, Or.inr hs0, hs0adj⟩
    -- "So we may assume some antipath `Q` between `x_{t−1}` and `q` … is even."
    obtain ⟨Q, hQ, hQint, hQeven⟩ :=
      Thm203Step3Aux.exists_even_antipath hG hframe hd ht hcon' hqA2 hqt1.symm hnone_sq
    by_cases hx1 : ∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj (x (t - 1)) s
    · -- PAPER: "Suppose that `x_{t−1}` has such a neighbour, and so `x_t` does not."
      have hxtSR : ∀ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, ¬ G.Adj (x t) s := by
        intro s hs hadj
        exact hnotboth ⟨⟨s, hs, hadj⟩, hx1⟩
      exact caseA hG hframe hd ht hqA2 hqt hqt1 hR hRsub hrnA3 hqmin hcon' hx1 hxtSR
        hnone_sq hQ hQint hQeven
    · -- PAPER: "So `x_{t−1}` has no neighbours in `A_{t−3} ∪ V(R \ q)`."
      push Not at hx1
      exact hcontra (Thm203Step3CaseB.case_no_nbr hG hframe hd ht hqA2 hqt hqt1
        hSRconn hSRsub hA3SR hqSR hx1 hQ hQint hQeven)
  -- PAPER: "From (3) and the choice of `R` it follows that `x_t` has no neighbours in
  -- `A_{t−3} ∪ V(R \ q)`."
  obtain ⟨a1, ha1A3, ha1adj⟩ := step3
  have hnbr1 : ∃ a ∈ wheelSystemA G z A₀ x (t - 3), G.Adj (x (t - 1)) a := ⟨a1, ha1A3, ha1adj⟩
  have hxtSR : ∀ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, ¬ G.Adj (x t) s := by
    intro s hs hadj
    exact hnotboth ⟨⟨s, hs, hadj⟩, ⟨a1, hA3SR ha1A3, ha1adj⟩⟩
  have hqA3 : q ∉ wheelSystemA G z A₀ x (t - 3) := fun h => hxtSR q (Or.inl h) hqt.symm
  have hqrn : q ≠ rn := fun h => hqA3 (h ▸ hrnA3)
  have hSRconn : ConnectedSet G (SRset (wheelSystemA G z A₀ x (t - 3)) R) :=
    connectedSet_SRset hA3conn hR hrnA3 hqrn
  obtain ⟨s0, hs0, hs0adj⟩ := exists_adj_tail hR hqrn
  have hqSR : ∃ s ∈ SRset (wheelSystemA G z A₀ x (t - 3)) R, G.Adj q s :=
    ⟨s0, Or.inr hs0, hs0adj⟩
  -- "… so by 2.2 applied in `Ḡ`, one of its ends, and hence `q`, has a neighbour in `A_{t−3}`"
  have hqnbr : ∃ b ∈ wheelSystemA G z A₀ x (t - 3), G.Adj q b :=
    Thm203Endgame.q_has_nbr_in_A3 hG hframe hd ht hqA2 hqt hqt1
      hSRconn hSRsub hA3SR hqSR hxtSR hnbr1
  have hno : ∀ a ∈ wheelSystemA G z A₀ x (t - 3), ¬ G.Adj (x t) a :=
    fun a ha => hxtSR a (Or.inl ha)
  -- the final sentence of the printed proof
  obtain ⟨Y', hY'a, hY'sub, hdisj⟩ :=
    Thm203Step1.exists_diamond_endgame hd ht hno hnbr1 ⟨q, hqA2, hqt, hqt1, hqnbr⟩
  rcases hdisj with h | h
  · exact hnone ⟨Y', hY'a, hY'sub, Or.inl h⟩
  · exact hnone ⟨Y', hY'a, hY'sub, Or.inr (Or.inr h)⟩

end Scratch203


namespace Workspace.Statements.S20

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_20_3 (G : SimpleGraph V) (hG : InF7 G)
    (z : V) (A₀ : Set V) (hframe : IsFrame G z A₀)
    (Y : Set V) (hYsub : ∀ y ∈ Y, y ∉ A₀ ∧ y ≠ z)
    (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (x : ℕ → V) (t : ℕ) (hdiam : IsYDiamond G z A₀ x t Y) (ht : 4 ≤ t)
    (hnone : ¬ ∃ Y' : Set V, AnticonnectedSet G Y' ∧ Y ⊆ Y' ∧
      ((∃ x' : ℕ → V, IsYDiamond G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsYSquare G z A₀ x' (t - 1) Y') ∨
       (∃ x' : ℕ → V, IsPolishedYDiamond G z A₀ x' t Y'))) :
    VertexComplete G z Y ∧ ∃ C : List V, IsWheel G C Y := by
  exact Scratch203.assembly hG hframe hdiam ht hnone

end SPGT

end Workspace.Statements.S20
