import Workspace.ProofLemmas.Thm232RimFacts
import Workspace.ProofLemmas.Thm232Claim4Symmetry
import Workspace.ProofLemmas.Thm232MinPath
import Workspace.ProofLemmas.FirstTargetInducedPathInConnectedSet
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.Thm232Claim5PathPrefix
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.Types.WheelSystems
import Workspace.Types.Decompositions

/-!
# The path of claim (5) of 23.2

PAPER (23.2, claim (5), printed p. 140):

> *"For let `P` be a path `y-p₁-⋯-p_k` from `y` to some `Y`-complete vertex `p_k ∈ A₀`, with
> interior in `A₀ ∪ {v₁,…,v_n}`, such that `p_k` is the only `Y`-complete vertex in `P`.
> Since none of `y, v₁, …, v_{n−1}` have neighbours in `A₀` it follows that
> `{y,v₁,…,v_n} ⊆ {y,p₁,…,p_{k−1}}`.  From (4), `k ≥ 3`."*

`exists_claim5_path` builds that path, prefixed by `z`, together with every property the
subsequent appeal to 2.11 needs.  The set `{y,v₁,…,v_n}` is the interior of `T`, and
`A₀ ∪ {y,v₁,…,v_n}` is connected, so the path is produced by
`FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet`, which stops at the
first `Y`-complete vertex.  The inclusion of the printed sentence is
`Thm232Claim5PathPrefix.initial_subset`, fed by the minimum-length choice of `T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm232Claim5Path

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.ProofLemmas.PathBasics
open Workspace.ProofLemmas.KiteTailBasics
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Remaining gap, PAPER (23.2), claim (4), printed p. 140:**
*"(4) If `n = 1` then no neighbour of `v₁` in `A₀` is `Y`-complete."*

Here `n = 1` means that `T` is the four-vertex path `z-y-v₁-v₂` with `v₂ ∈ A₀`, so `v₁` is the
last interior vertex of `T`.  The printed proof of (4) goes through an antipath between `y` and
`v₁` with interior in `Y`, then 16.1 and 22.3, and ends with the odd hole
`x₀-Q-c₃-v₁-y-x₀`. -/
theorem claim4_gap (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y) (hc1Y : VertexComplete G c₁ Y)
    (hc2Y : VertexComplete G c₂ Y) (hc3Y : VertexComplete G c₃ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁) (hnbc : IsRimNeighbours G C c₂ c₁ c₃)
    (hexh : ∀ u v : V, u ∈ C → v ∈ C → EdgeComplete G Y u v →
      ({u, v} : Set V) = {x₀, z} ∨ ({u, v} : Set V) = {z, x₁} ∨
      ({u, v} : Set V) = {c₁, c₂} ∨ ({u, v} : Set V) = {c₂, c₃})
    (T : List V) (y v₁ w : V) (hTeq : T = [z, y, v₁, w])
    (hpath : IsPathFrom G T z w)
    (hwA : w ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (h2 : ¬ (G.Adj y x₀ ∧ G.Adj y x₁))
    (h3 : VertexAnticomplete G y ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (u : V) (hu : u ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (huadj : G.Adj v₁ u) :
    ¬ VertexComplete G u Y :=
  Thm232Claim4Symmetry.claim4 G hG hbsp C Y hopt x₀ z x₁ c₁ c₂ c₃ k d hd2 hdn hpre1 hpre2
    h0Y hzY h1Y hc1Y hc2Y hc3Y hnb hnbc hexh T y v₁ w hTeq hpath hwA havoid hint h3 u hu huadj

/-- **PAPER (23.2, claim (5), printed p. 140):** the path `z-y-p₁-⋯-p_k`, with every property
its use in claim (5) needs.  `hclaim4` is claim (4). -/
theorem exists_claim5_path (G : SimpleGraph V) (C : List V) (Y : Set V)
    (hC : IsHoleList G C) (hn6 : 6 ≤ C.length) (hCY : ∀ v ∈ C, v ∉ Y)
    (x₀ z x₁ c₂ : V) (k : ℕ) (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hnb : IsRimNeighbours G C z x₀ x₁) (hzY : VertexComplete G z Y)
    (hc2A : c₂ ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (hc2Y : VertexComplete G c₂ Y)
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hpath : IsPathFrom G T z w)
    (hwA : w ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (havoid : ∀ v ∈ T, v ≠ x₀ ∧ v ≠ x₁)
    (hint : ∀ v ∈ SPGT.interior T, v ∉ Y ∧ ¬ VertexComplete G v Y)
    (hattach : ∀ (i : ℕ) (hi : i + 2 < T.length),
      VertexAnticomplete G (T[i]'(by omega)) ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (h3 : VertexAnticomplete G y ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)))
    (hclaim4 : T.length = 4 → ∀ v ∈ SPGT.interior T, v ≠ y →
      ∀ u ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)), G.Adj v u → ¬ VertexComplete G u Y) :
    ∃ (P : List V) (pn : V),
      IsPathFrom G P z pn ∧
      P.tail.head? = some y ∧
      (∀ v ∈ P, v ∉ Y ∧ v ∉ ({x₀, x₁} : Set V)) ∧
      4 ≤ pathLength P ∧
      (∀ v ∈ P, VertexComplete G v Y ↔ v = z ∨ v = pn) ∧
      ¬ VertexComplete G pn ({x₀, x₁} : Set V) ∧
      pn ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)) ∧
      (∀ v ∈ SPGT.interior P, v ∈ ({q : V | q ∈ C} \ ({z, x₀, x₁} : Set V)) ∪
        {q : V | q ∈ SPGT.interior T}) ∧
      (∀ v ∈ SPGT.interior T, v ∈ P.tail) := by
  classical
  set A₀ : Set V := {q : V | q ∈ C} \ ({z, x₀, x₁} : Set V) with hA₀def
  -- basic shape of `T`
  have hTlen2 : 2 ≤ T.length := by rw [hTeq]; simp
  have hTz : T[0]'(by omega) = z := getElem_zero_of_head? hpath.2.1 (by omega)
  have hTy : T[1]'(by omega) = y := by
    have h1 : T.tail.head? = some y := by rw [hTeq]; rfl
    have := getElem_zero_of_head? h1 (by rw [List.length_tail]; omega)
    rw [List.getElem_tail] at this
    exact this
  have hzy : G.Adj z y := by
    have h := path_adj_succ hpath.1 (i := 0) (by omega)
    rw [hTz, hTy] at h
    exact h
  have hTlast : T[T.length - 1]'(by omega) = w :=
    getElem_last_of_getLast? hpath.2.2 (by omega)
  have hT3 : 3 ≤ T.length := by
    rcases Nat.lt_or_ge T.length 3 with h | h
    · exfalso
      have h2 : T.length = 2 := by omega
      have : w = y := by
        rw [← hTlast, ← hTy]
        exact hpath.1.2.1.getElem_inj_iff.mpr (by omega)
      rcases hnb.2.2.2.2.2 w hwA.1 (this ▸ hzy) with he | he
      · exact hwA.2 (by simp [he])
      · exact hwA.2 (by simp [he])
    · exact h
  have hT4 : 4 ≤ T.length := by
    rcases Nat.lt_or_ge T.length 4 with h | h
    · exfalso
      have h3' : T.length = 3 := by omega
      have hwy : G.Adj y w := by
        have hadj := path_adj_succ hpath.1 (i := 1) (by omega)
        have he : T[1 + 1]'(by omega) = w := by
          rw [← hTlast]
          exact hpath.1.2.1.getElem_inj_iff.mpr (by omega)
        rw [hTy, he] at hadj
        exact hadj
      exact h3 w hwA hwy
    · exact h
  have hyint : y ∈ SPGT.interior T := by
    rw [← hTy]
    exact getElem_mem_interior hpath.1 (by omega) (by omega) (by omega)
  have hv₁int : (T[2]'(by omega)) ∈ SPGT.interior T :=
    getElem_mem_interior hpath.1 (by omega) (by omega) (by omega)
  have hyv₁ : G.Adj y (T[2]'(by omega)) := by
    have hadj := path_adj_succ hpath.1 (i := 1) (by omega)
    rw [hTy] at hadj
    exact hadj
  -- the connected set `A₀ ∪ {y, v₁, …, v_n}`
  set A : Set V := {q : V | q ∈ SPGT.interior T} ∪ A₀ with hAdef
  have hintPath : IsPathList G (SPGT.interior T) :=
    (PathGlue.isPathFrom_interior hpath.1 (by omega)).1
  have hAconn : ConnectedSet G A := by
    refine ConnectedSetUnionAttach.connectedSet_union
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hintPath)
      (Thm232RimFacts.a0_connected hC hn6 hpre1) (Or.inr ⟨T[T.length - 2]'(by omega), ?_, w,
        hwA, ?_⟩)
    · exact getElem_mem_interior hpath.1 (by omega) (by omega) (by omega)
    · have hadj := path_adj_succ hpath.1 (i := T.length - 2) (by omega)
      have he : T[T.length - 2 + 1]'(by omega) = w := by
        rw [← hTlast]
        exact hpath.1.2.1.getElem_inj_iff.mpr (by omega)
      rw [he] at hadj
      exact hadj
  -- the first `Y`-complete vertex reached from `y` inside that set
  obtain ⟨pn, hpnAB, P₀, hP₀, hP₀pos, hP₀A, hP₀B⟩ :=
    FirstTargetInducedPathInConnectedSet.firstTargetInducedPathInConnectedSet G A
      {q : V | VertexComplete G q Y} y hAconn ⟨T[2]'(by omega), Or.inl hv₁int, hyv₁⟩
      ⟨c₂, Or.inr hc2A, hc2Y⟩ (fun h => (hint y hyint).2 h)
  have hpnY : VertexComplete G pn Y := hpnAB.2
  have hpnA₀ : pn ∈ A₀ := by
    rcases hpnAB.1 with h | h
    · exact absurd hpnY (hint pn h).2
    · exact h
  -- the vertices of `P₀`
  have hP₀mem : ∀ q ∈ P₀, q = y ∨ q ∈ SPGT.interior T ∨ q ∈ A₀ := by
    intro q hq
    by_cases hqy : q = y
    · exact Or.inl hqy
    · rcases hP₀A q hq hqy with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hzP₀ : z ∉ P₀ := by
    intro hz
    rcases hP₀mem z hz with h | h | h
    · exact hzy.ne h
    · exact absurd ((mem_interior_iff_of_pathFrom hpath).mp h).2.1 (fun hh => hh rfl)
    · exact h.2 (by simp)
  have hzother : ∀ q ∈ P₀, q ≠ y → ¬ G.Adj z q := by
    intro q hq hqy
    rcases hP₀mem q hq with h | h | h
    · exact absurd h hqy
    · intro hadj
      obtain ⟨j, hj, hj1, hj2, hjq⟩ := exists_getElem_of_mem_interior hpath.1 h
      have := (path_adj_iff hpath.1 (show 0 < T.length by omega) hj).mp (by
        rw [hTz, hjq]; exact hadj)
      have hj1' : j = 1 := by omega
      exact hqy (hjq.symm.trans ((hpath.1.2.1.getElem_inj_iff.mpr hj1').trans hTy))
    · intro hadj
      rcases hnb.2.2.2.2.2 q h.1 hadj with he | he
      · exact h.2 (by simp [he])
      · exact h.2 (by simp [he])
  have hP : IsPathFrom G (z :: P₀) z pn :=
    PathAttach.isPathFrom_cons hP₀ hzy hzP₀ hzother
  -- claim (4) gives `k ≥ 3`
  have hlong : 4 ≤ pathLength (z :: P₀) := by
    rw [pathLength_cons]
    have h1 : 1 ≤ pathLength P₀ := hP₀pos
    have hlenP2 : 2 ≤ P₀.length := by unfold pathLength at h1; omega
    by_contra hcon
    have hP₀len : P₀.length ≤ 3 := by unfold pathLength at hcon; omega
    have hy0 : P₀[0]'(by omega) = y := getElem_zero_of_head? hP₀.2.1 (by omega)
    have hpnlast : P₀[P₀.length - 1]'(by omega) = pn :=
      getElem_last_of_getLast? hP₀.2.2 (by omega)
    have hcases : P₀.length = 2 ∨ P₀.length = 3 := by omega
    rcases hcases with hlen2 | hlen3
    · have hadj := path_adj_succ hP₀.1 (i := 0) (by omega)
      have he : P₀[0 + 1]'(by omega) = pn := by
        rw [← hpnlast]
        exact hP₀.1.2.1.getElem_inj_iff.mpr (by omega)
      rw [hy0, he] at hadj
      exact h3 pn hpnA₀ hadj
    · set q : V := P₀[1]'(by omega) with hqdef
      have hqmem : q ∈ P₀ := List.getElem_mem _
      have hyq : G.Adj y q := by
        have hadj := path_adj_succ hP₀.1 (i := 0) (by omega)
        rw [hy0] at hadj
        exact hadj
      have hqpn : G.Adj q pn := by
        have hadj := path_adj_succ hP₀.1 (i := 1) (by omega)
        have he : P₀[1 + 1]'(by omega) = pn := by
          rw [← hpnlast]
          exact hP₀.1.2.1.getElem_inj_iff.mpr (by omega)
        rw [he] at hadj
        exact hadj
      have hqy : q ≠ y := by
        intro he
        have := hP₀.1.2.1.getElem_inj_iff.mp (he.trans hy0.symm)
        omega
      rcases hP₀mem q hqmem with h | h | h
      · exact hqy h
      · -- `q` is an interior vertex of `T` with a neighbour in `A₀`
        obtain ⟨j, hj, hj1, hj2, hjq⟩ := exists_getElem_of_mem_interior hpath.1 h
        have hjlast : j + 2 = T.length := by
          by_contra hne
          exact hattach j (by omega) pn hpnA₀ (by rw [hjq]; exact hqpn)
        have hjy : j = 2 := by
          have hadj : G.Adj (T[1]'(by omega)) (T[j]'hj) := by rw [hTy, hjq]; exact hyq
          have := (path_adj_iff hpath.1 (show 1 < T.length by omega) hj).mp hadj
          omega
        exact hclaim4 (by omega) q h hqy pn hpnA₀ hqpn hpnY
      · exact h3 q h hyq
  -- the printed inclusion `{y,v₁,…,v_n} ⊆ {y,p₁,…,p_{k-1}}`
  obtain ⟨hx0C, hzC', hx1C, -⟩ := hole_triple hC ⟨k, hpre1⟩
  have hintdrop : ∀ v ∈ SPGT.interior T, v ∈ T.dropLast := by
    intro v hv
    obtain ⟨j, hj, hj1, hj2, hjv⟩ := exists_getElem_of_mem_interior hpath.1 hv
    have : (T.dropLast)[j]'(by rw [List.length_dropLast]; omega) = v := by
      rw [List.getElem_dropLast]; exact hjv
    exact this ▸ List.getElem_mem _
  have hdropPath : IsPathList G T.dropLast := by
    rw [List.dropLast_eq_take]
    exact isPathList_take hpath.1 (by omega)
  have hdropHead : (T.dropLast).head? = some z := by
    rw [List.dropLast_eq_take, List.head?_take, if_neg (by omega)]
    exact hpath.2.1
  have hdropA : ∀ v ∈ T.dropLast, v ∉ A₀ := by
    intro v hv hvA
    obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
    rw [List.length_dropLast] at hj
    have hjT : T[j]'(by omega) = v := by rw [← hjv, List.getElem_dropLast]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [hTz] at hjT
      exact hvA.2 (by simp [hjT.symm])
    · have hadj := path_adj_succ hpath.1 (i := j - 1) (by omega)
      have he : T[j - 1 + 1]'(by omega) = v :=
        (hpath.1.2.1.getElem_inj_iff.mpr (show j - 1 + 1 = j by omega)).trans hjT
      rw [he] at hadj
      exact hattach (j - 1) (by omega) v hvA hadj
  have hdropAttach : ∀ (i : ℕ) (hi : i + 1 < (T.dropLast).length),
      VertexAnticomplete G ((T.dropLast)[i]'(by omega)) A₀ := by
    intro i hi
    rw [List.length_dropLast] at hi
    have : (T.dropLast)[i]'(by rw [List.length_dropLast]; omega) = T[i]'(by omega) := by
      rw [List.getElem_dropLast]
    rw [this]
    exact hattach i (by omega)
  have hallowed : ∀ v ∈ z :: P₀, v ∈ T.dropLast ∨ v ∈ A₀ := by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · refine Or.inl ?_
      have : (T.dropLast)[0]'(by rw [List.length_dropLast]; omega) = v := by
        rw [List.getElem_dropLast]; exact hTz
      exact this ▸ List.getElem_mem _
    · rcases hP₀mem v hv' with h | h | h
      · exact Or.inl (hintdrop v (h ▸ hyint))
      · exact Or.inl (hintdrop v h)
      · exact Or.inr h
  have hsubset : ∀ v ∈ T.dropLast, v ∈ z :: P₀ :=
    Thm232Claim5PathPrefix.initial_subset hdropPath hdropHead hP hpnA₀ hdropA hallowed
      hdropAttach
  refine ⟨z :: P₀, pn, hP, hP₀.2.1, ?_, hlong, ?_, ?_, hpnA₀, ?_, ?_⟩
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨hCY v hzC', by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hnb.2.2.2.1.ne, hnb.2.2.2.2.1.ne⟩⟩
    · have hvT : v ∉ ({x₀, x₁} : Set V) → v ∉ Y → v ∉ Y ∧ v ∉ ({x₀, x₁} : Set V) :=
        fun h1 h2 => ⟨h2, h1⟩
      rcases hP₀mem v hv' with h | h | h
      · subst h
        refine ⟨(hint v hyint).1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact havoid v (interior_subset hyint)
      · refine ⟨(hint v h).1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact havoid v (interior_subset h)
      · refine ⟨hCY v h.1, ?_⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨fun he => h.2 (by simp [he]), fun he => h.2 (by simp [he])⟩
  · intro v hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact ⟨fun _ => Or.inl rfl, fun _ => hzY⟩
    · constructor
      · intro hvc
        exact Or.inr ((hP₀B v hv').mp hvc)
      · rintro (rfl | rfl)
        · exact absurd hv' hzP₀
        · exact hpnY
  · intro hcon
    exact Thm232RimFacts.not_complete_to_pair hC hn6 hpre1 pn hpnA₀.1
      (fun he => hpnA₀.2 (by simp [he]))
      ⟨hcon x₀ (by simp), hcon x₁ (by simp)⟩
  · intro v hv
    have hvmem := interior_subset hv
    have hvz : v ≠ z := ((mem_interior_iff_of_pathFrom hP).mp hv).2.1
    have hv' : v ∈ P₀ := by
      rcases List.mem_cons.mp hvmem with he | he
      · exact absurd he hvz
      · exact he
    rcases hP₀mem v hv' with h | h | h
    · exact Or.inr (h ▸ hyint)
    · exact Or.inr h
    · exact Or.inl h
  · intro v hv
    have hvz : v ≠ z := ((mem_interior_iff_of_pathFrom hpath).mp hv).2.1
    have := hsubset v (hintdrop v hv)
    rcases List.mem_cons.mp this with he | he
    · exact absurd he hvz
    · simpa using he

end Workspace.ProofLemmas.Thm232Claim5Path
