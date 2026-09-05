import Mathlib
import Workspace.ProofLemmas.Thm181Local
import Workspace.ProofLemmas.Thm185Claim6Bridge
import Workspace.ProofLemmas.Thm185Helpers
import Workspace.ProofLemmas.Thm185TripleRRReduction
import Workspace.ProofLemmas.Thm186Setup
import Workspace.ProofLemmas.Thm183EdgeCount
import Workspace.ProofLemmas.Thm183LineOddCase
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.SubpathIsSlice
import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S13.Thm_13_7
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_9
import Workspace.Statements.S18.Thm_18_4
import Workspace.Statements.S18.Thm_18_2

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Scratch186Singleton

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private abbrev VertexGood (G : SimpleGraph V) (X Y : Set V) (P : List V)
    (p₁ pₙ v : V) : Prop :=
  ∃ q : List V, IsPathList G q ∧ q <:+: P ∧
    (∀ w ∈ P, G.Adj v w → w ∈ q) ∧
    (∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y) ∧
    (VertexComplete G v X → ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q))

private theorem depIndex (q : List V) {a b : ℕ} (hab : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst b
  rfl

private theorem pathLength_one_of_ends_adj {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hadj : G.Adj a b) : pathLength p = 1 := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hkey := (PathBasics.path_adj_iff hp.1 hpos (show p.length - 1 < p.length by omega)).mp
    (by rw [h0, hl]; exact hadj)
  rw [PathBasics.pathLength_eq]
  omega

private theorem eq_pair_of_pathLength_one {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : pathLength p = 1) : p = [a,b] := by
  have hlen2 : p.length = 2 := by rw [PathBasics.pathLength_eq] at hlen; omega
  obtain ⟨x, y, hxy⟩ := PathGlue.length_eq_two hlen2
  rw [hxy] at hp ⊢
  have hx : x = a := Option.some_injective _ hp.2.1
  have hy : y = b := by simpa using Option.some_injective _ hp.2.2
  rw [hx, hy]

private theorem pathFrom_ends_not_adj {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : 2 ≤ pathLength p) : ¬ G.Adj a b := by
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have h0 : p[0]'hpos = a := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hl : p[p.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  rw [← h0, ← hl]
  apply PathBasics.path_ends_not_adj hp.1
  rw [PathBasics.pathLength_eq] at hlen
  omega

private theorem isPathFrom_slice_le {G : SimpleGraph V} {p : List V}
    (h : IsPathList G p) {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) := by
  refine ⟨?_, PathBasics.head?_slice p hij hj, PathBasics.getLast?_slice p hij hj⟩
  rcases eq_or_lt_of_le hij with he | hlt
  · have hlen : ((p.drop i).take (j - i + 1)).length = 1 := by
      rw [PathBasics.length_slice p hij hj]
      omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx]
    exact PathBasics.isPathList_singleton G x
  · exact PathBasics.isPathList_slice h hlt hj

private theorem y_window_size (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j) :
    3 ≤ j - i := by
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  have hcard : 3 ≤ (Thm183EdgeCount.YEdgeIdx G Y P).ncard := by
    rw [← Thm183EdgeCount.yEdges_ncard_eq_index_ncard hP]
    exact h184.1.2
  have hsub : Thm183EdgeCount.YEdgeIdx G Y P ⊆ Set.Ico i j := by
    intro k hk
    obtain ⟨hk1, hkY, hk1Y⟩ := hk
    have hkpos : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      subst k
      exact hP1Y hk1 hk1Y
    have hki := hminmax k (by omega) hkpos hkY
    have hki1 := hminmax (k + 1) hk1 (by omega) hk1Y
    exact ⟨hki.1, by omega⟩
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  simpa using (le_trans hcard hle)

private theorem exists_y_internal (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j) :
    ∃ (s : ℕ) (hs : s < P.length), i < s ∧ s < j ∧ VertexComplete G (P[s]'hs) Y := by
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  have hcard : 3 ≤ (Thm183EdgeCount.YEdgeIdx G Y P).ncard := by
    rw [← Thm183EdgeCount.yEdges_ncard_eq_index_ncard hP]
    exact h184.1.2
  by_contra hno
  push_neg at hno
  have hsub : Thm183EdgeCount.YEdgeIdx G Y P ⊆ ({j - 1} : Set ℕ) := by
    intro k hk
    obtain ⟨hk1, hkY, hk1Y⟩ := hk
    have hkpos : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      subst k
      exact hP1Y hk1 hk1Y
    have hki := hminmax k (by omega) hkpos hkY
    have hki1 := hminmax (k + 1) hk1 (by omega) hk1Y
    have hnot : ¬ (k + 1 < j) := by
      intro hlt
      exact hno (k + 1) hk1 (by omega) hlt hk1Y
    have : k = j - 1 := by omega
    simpa [this]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  simp at hle
  omega

private theorem first_y_even (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (i : ℕ) (hi : i < P.length) (h1i : 1 ≤ i)
    (hYi : VertexComplete G (P[i]'hi) Y)
    (hmin : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t) : Even i := by
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have h0lt : 0 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hi2 : 2 ≤ i := by
    by_contra h
    have hi1 : i = 1 := by omega
    subst i
    exact hP1Y hi hYi
  let q : List V := (P.drop 0).take (i - 0 + 1)
  have hqfrom0 : IsPathFrom G q (P[0]'h0lt) (P[i]'hi) := by
    exact PathBasics.isPathFrom_slice hP (by omega) hi
  have hqfrom : IsPathFrom G q p₁ (P[i]'hi) := by
    rw [← hp0]
    exact hqfrom0
  have hqinf : q <:+: P := Thm185Helpers.slice_infix P 0 (i - 0 + 1)
  have hqint : ∀ w ∈ SPGT.interior q, ¬ VertexComplete G w Y := by
    intro w hw hwY
    obtain ⟨t, ht, ht0, hti, rfl⟩ :=
      (PathBasics.mem_interior_slice_iff hP (show 0 < i by omega) hi).mp hw
    exact (not_lt_of_ge (hmin t ht (by omega) hwY)) hti
  have hqLen : q.length = i + 1 := by
    simp [q]
    omega
  have hmax : ∀ (r : List V), r <:+: P →
      (∀ w ∈ SPGT.interior r, ¬ VertexComplete G w Y) → q <:+: r → r = q := by
    intro r hrP hrint hqr
    obtain ⟨s, hslen, hrEq⟩ := Thm185Helpers.infix_eq_slice r P hrP
    have hrpos : 0 < r.length := by
      have hle : q.length ≤ r.length := List.IsInfix.length_le hqr
      omega
    have hrend : s + r.length - 1 < P.length := by omega
    have hrEq' : r = (P.drop s).take (s + r.length - 1 - s + 1) := by
      have hc : s + r.length - 1 - s + 1 = r.length := by omega
      simpa [hc] using hrEq
    have hqsub : ∀ z ∈ q, z ∈ r := by
      obtain ⟨l, rr, hlr⟩ := hqr
      intro z hz
      rw [← hlr]
      simp [hz]
    have hp0q : P[0]'h0lt ∈ q := by
      dsimp [q]
      exact (PathBasics.mem_slice_iff P (Nat.zero_le i) hi).mpr
        ⟨0, h0lt, le_rfl, Nat.zero_le i, rfl⟩
    have hp0r := hqsub _ hp0q
    have hs0 : s = 0 := by
      rw [hrEq'] at hp0r
      obtain ⟨t, ht, hst, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (by omega : s ≤ s + r.length - 1) hrend).mp hp0r
      have ht0 : t = 0 := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp heq
      omega
    subst s
    have hrend0 : r.length - 1 < P.length := by simpa using hrend
    have hrEq0 : r = (P.drop 0).take (r.length - 1 - 0 + 1) := by
      rw [show r.length - 1 - 0 + 1 = r.length by omega]
      simpa using hrEq
    have hpiq : P[i]'hi ∈ q := by
      dsimp [q]
      exact (PathBasics.mem_slice_iff P (Nat.zero_le i) hi).mpr
        ⟨i, hi, Nat.zero_le i, le_rfl, rfl⟩
    have hpir := hqsub _ hpiq
    have hirlen : i < r.length := by
      rw [hrEq0] at hpir
      obtain ⟨t, ht, -, htr, heq⟩ :=
        (PathBasics.mem_slice_iff P (by omega : 0 ≤ r.length - 1) hrend0).mp hpir
      have hti : t = i := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp heq
      omega
    have hrle : r.length ≤ i + 1 := by
      by_contra h
      have hmemint : P[i]'hi ∈ SPGT.interior r := by
        rw [hrEq0]
        exact (PathBasics.mem_interior_slice_iff hP (show 0 < r.length - 1 by omega) hrend0).mpr
          ⟨i, hi, by omega, by omega, rfl⟩
      exact hrint _ hmemint hYi
    have hrlen : r.length = i + 1 := by omega
    rw [hrEq, hrlen]
    dsimp [q]
  obtain ⟨t, ht, ht1, htY⟩ := hYex
  have hptne : P[t]'ht ≠ p₁ := by
    rw [← hp0]
    exact PathBasics.path_ne_of_ne_index hP ht h0lt (by omega)
  have htwo : 2 ≤ {w : V | w ∈ P ∧ VertexComplete G w Y}.ncard :=
    (Set.one_lt_ncard (Set.toFinite _)).mpr
      ⟨p₁, ⟨PathBasics.head_mem hhead, hp₁Y⟩, P[t]'ht,
        ⟨List.getElem_mem ht, htY⟩, hptne.symm⟩
  have h183 := _root_.Workspace.Statements.S18.SPGT.thm_18_3 G hG X Y hXY hXne hYne
    hXanti hYanti hcompl P p₁ pₙ hP houtU (by omega) hhead hlast hXuniq
  have hpar := (h183.2 htwo).1 q p₁ (P[i]'hi) hqinf hqfrom hqint hmax (by
    rw [PathBasics.pathLength_eq, hqLen]
    omega)
  have hendempty : {w : V | (w = p₁ ∨ w = P[i]'hi) ∧
      (w = p₁ ∨ w = pₙ) ∧ ¬ VertexComplete G w Y} = ∅ := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl | rfl, -, hw⟩
    · exact hw hp₁Y
    · exact hw hYi
  rw [hendempty, Set.ncard_empty, Nat.zero_mod] at hpar
  rw [PathBasics.pathLength_eq, hqLen] at hpar
  exact Nat.even_iff.mpr (by omega)

private theorem crossing_hole_absurd (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvP : v ∉ P) (hvnotY : v ∉ Y) (hvY : ¬ VertexComplete G v Y)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j)
    (hnoMid : ∀ (t : ℕ) (ht : t < P.length), i < t → t < j →
      ¬ G.Adj v (P[t]'ht))
    (hleft : ∃ (t : ℕ) (ht : t < P.length), t ≤ i ∧ G.Adj v (P[t]'ht))
    (hright : ∃ (t : ℕ) (ht : t < P.length), j ≤ t ∧ G.Adj v (P[t]'ht)) : False := by
  classical
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have hgap : 3 ≤ j - i :=
    y_window_size G hG X Y P p₁ pₙ hopt hhead hlast i j hi hj h1i hminmax
  let L : Finset ℕ := (Finset.range (i + 1)).filter
    (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht))
  have hLne : L.Nonempty := by
    obtain ⟨t, ht, hti, hadj⟩ := hleft
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨ht, hadj⟩⟩⟩
  let l := L.max' hLne
  have hlmem : l ∈ L := L.max'_mem hLne
  obtain ⟨hrangeL, hllen⟩ := Finset.mem_filter.mp hlmem
  have hli : l ≤ i := by simpa using Finset.mem_range.mp hrangeL
  let hllt : l < P.length := hllen.choose
  have hladj : G.Adj v (P[l]'hllt) := hllen.choose_spec
  have hleftMax : ∀ (t : ℕ) (ht : t < P.length), t ≤ i → G.Adj v (P[t]'ht) → t ≤ l := by
    intro t ht hti hadj
    exact Finset.le_max' L t
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ⟨ht, hadj⟩⟩)
  let R : Finset ℕ := (Finset.range P.length).filter
    (fun t => j ≤ t ∧ ∃ ht : t < P.length, G.Adj v (P[t]'ht))
  have hRne : R.Nonempty := by
    obtain ⟨t, ht, hjt, hadj⟩ := hright
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hjt, ⟨ht, hadj⟩⟩⟩
  let r := R.min' hRne
  have hrmem : r ∈ R := R.min'_mem hRne
  obtain ⟨hrange, hjr, hrEx⟩ := Finset.mem_filter.mp hrmem
  have hrlt : r < P.length := Finset.mem_range.mp hrange
  have hradj : G.Adj v (P[r]'hrlt) := by simpa only using hrEx.choose_spec
  have hrightMin : ∀ (t : ℕ) (ht : t < P.length), j ≤ t → G.Adj v (P[t]'ht) → r ≤ t := by
    intro t ht hjt hadj
    exact Finset.min'_le R t
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, hjt, ⟨ht, hadj⟩⟩)
  have hlr : l + 2 ≤ r := by omega
  have hbetween : ∀ (t : ℕ) (ht : t < P.length), l < t → t < r →
      ¬ G.Adj v (P[t]'ht) := by
    intro t ht hlt htr hadj
    by_cases hti : t ≤ i
    · exact (not_le_of_gt hlt) (hleftMax t ht hti hadj)
    by_cases htj : t < j
    · exact hnoMid t ht (by omega) htj hadj
    · exact (not_le_of_gt htr) (hrightMin t ht (by omega) hadj)
  let C : List V := v :: (P.drop l).take (r - l + 1)
  have hC : IsHoleList G C := by
    exact Thm185Helpers.hole_from_two_neighbours G P hP v hvP l r hlr hrlt hladj hradj
      hbetween
  have hCY : ∀ w ∈ C, w ∉ Y := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact hvnotY
    · intro hwY
      exact houtU w (List.mem_of_mem_drop (List.mem_of_mem_take hw)) (Or.inr hwY)
  have hyeq : HoleYEdgeParity.yEdges G Y C = HoleYEdgeParity.yEdges G Y P := by
    ext e
    constructor
    · rintro ⟨u, hu, w, hw, rfl, huw, huY, hwY⟩
      have huP : u ∈ P := by
        rcases List.mem_cons.mp hu with rfl | hu
        · exact absurd huY hvY
        · exact List.mem_of_mem_drop (List.mem_of_mem_take hu)
      have hwP : w ∈ P := by
        rcases List.mem_cons.mp hw with rfl | hw
        · exact absurd hwY hvY
        · exact List.mem_of_mem_drop (List.mem_of_mem_take hw)
      exact ⟨u, huP, w, hwP, rfl, huw, huY, hwY⟩
    · rintro ⟨u, hu, w, hw, rfl, huw, huY, hwY⟩
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hw
      have habidx := (PathBasics.path_adj_iff hP ha hb).mp huw
      have ha1 : 1 ≤ a := by
        by_contra h
        have ha0 : a = 0 := by omega
        subst a
        have hb1 : b = 1 := by rcases habidx with h | h <;> omega
        subst b
        exact hP1Y hb hwY
      have hb1 : 1 ≤ b := by
        by_contra h
        have hb0 : b = 0 := by omega
        subst b
        have ha1' : a = 1 := by rcases habidx with h | h <;> omega
        subst a
        exact hP1Y ha huY
      have haij := hminmax a ha ha1 huY
      have hbij := hminmax b hb hb1 hwY
      have haC : P[a]'ha ∈ C := by
        apply List.mem_cons_of_mem
        exact (PathBasics.mem_slice_iff P (by omega : l ≤ r) hrlt).mpr
          ⟨a, ha, by omega, by omega, rfl⟩
      have hbC : P[b]'hb ∈ C := by
        apply List.mem_cons_of_mem
        exact (PathBasics.mem_slice_iff P (by omega : l ≤ r) hrlt).mpr
          ⟨b, hb, by omega, by omega, rfl⟩
      exact ⟨_, haC, _, hbC, rfl, huw, huY, hwY⟩
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  exact HoleYEdgeParity.not_odd_ge_three_yEdges' hBerge hYanti hC hCY
    (by rw [hyeq]; exact h184.1.1) (by rw [hyeq]; exact h184.1.2)

private theorem left_only_xcomplete_absurd (G : SimpleGraph V) (hG : InF7 G)
    (X Y : Set V) (P : List V) (p₁ pₙ v : V)
    (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (hvX : VertexComplete G v X) (hv0 : ¬ G.Adj v p₁)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hij : i ≤ j) (hYi : VertexComplete G (P[i]'hi) Y)
    (hYj : VertexComplete G (P[j]'hj) Y)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j)
    (hnbr : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → t ≤ i)
    (hex : ∃ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht)) : False := by
  classical
  obtain ⟨hP, hlen7, hevenP, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have hgap : 3 ≤ j - i :=
    y_window_size G hG X Y P p₁ pₙ hopt hhead hlast i j hi hj h1i hminmax
  have hiEven : Even i :=
    first_y_even G hG X Y P p₁ pₙ hopt hhead hlast i hi h1i hYi
      (fun t ht ht1 htY => (hminmax t ht ht1 htY).1)
  let N : Finset ℕ := (Finset.range P.length).filter
    (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht))
  have hNne : N.Nonempty := by
    obtain ⟨t, ht, hadj⟩ := hex
    exact ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ⟨ht, hadj⟩⟩⟩
  let k := N.max' hNne
  have hkmem : k ∈ N := N.max'_mem hNne
  obtain ⟨hkrange, hkEx⟩ := Finset.mem_filter.mp hkmem
  have hklt : k < P.length := Finset.mem_range.mp hkrange
  have hkadj : G.Adj v (P[k]'hklt) := by simpa only using hkEx.choose_spec
  have hkmax : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → t ≤ k := by
    intro t ht hadj
    exact Finset.le_max' N t
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, ⟨ht, hadj⟩⟩)
  have hki : k ≤ i := hnbr k hklt hkadj
  have hkpos : 1 ≤ k := by
    by_contra h
    have hk0 : k = 0 := by omega
    apply hv0
    have hp0 : P[0]'(by omega) = p₁ :=
      PathBasics.getElem_zero_of_head? hhead (by omega)
    have hkadj0 : G.Adj v (P[0]'(by omega)) := by
      simpa [hk0] using hkadj
    rw [← hp0]
    exact hkadj0
  have hnlt : P.length - 1 < P.length := by omega
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast (by omega)
  let S : List V := (P.drop k).take (P.length - 1 - k + 1)
  have hSfrom : IsPathFrom G S (P[k]'hklt) pₙ := by
    have h := PathBasics.isPathFrom_slice hP (show k < P.length - 1 by omega) hnlt
    rw [hpn] at h
    exact h
  have hSmem : ∀ w : V, w ∈ S ↔ ∃ (t : ℕ) (ht : t < P.length),
      k ≤ t ∧ t ≤ P.length - 1 ∧ (P[t]'ht) = w := by
    intro w
    exact PathBasics.mem_slice_iff P (by omega) hnlt
  have hvS : v ∉ S := by
    intro hv
    obtain ⟨t, ht, -, -, heq⟩ := (hSmem v).mp hv
    exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hother : ∀ w ∈ S, w ≠ P[k]'hklt → ¬ G.Adj v w := by
    intro w hw hwne hadj
    obtain ⟨t, ht, hkt, -, rfl⟩ := (hSmem w).mp hw
    have htk := hkmax t ht hadj
    have hteq : t = k := by omega
    subst t
    exact hwne rfl
  let Rpath : List V := v :: S
  have hRfrom : IsPathFrom G Rpath v pₙ :=
    PathAttach.isPathFrom_cons hSfrom hkadj hvS hother
  have hSlen : S.length = P.length - k := by
    dsimp [S]
    rw [PathBasics.length_slice P (by omega : k ≤ P.length - 1) hnlt]
    omega
  have hRlen : pathLength Rpath = P.length - k := by
    rw [PathBasics.pathLength_eq]
    simp [Rpath, hSlen]
  have hR4 : 4 ≤ pathLength Rpath := by omega
  have hXR : X ⊆ {w : V | w ∈ Rpath}ᶜ := by
    intro x hxX hxR
    rcases List.mem_cons.mp hxR with rfl | hxS
    · exact hvXY (Or.inl hxX)
    · obtain ⟨t, ht, -, -, rfl⟩ := (hSmem x).mp hxS
      exact houtU _ (List.getElem_mem ht) (Or.inl hxX)
  have hpnX : VertexComplete G pₙ X := by
    exact (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
  have hRX : ∀ w ∈ Rpath, VertexComplete G w X ↔ (w = v ∨ w = pₙ) := by
    intro w hw
    constructor
    · intro hwX
      rcases List.mem_cons.mp hw with rfl | hwS
      · exact Or.inl rfl
      · right
        obtain ⟨t, ht, hkt, -, rfl⟩ := (hSmem w).mp hwS
        rcases (hXuniq _ (List.getElem_mem ht)).mp hwX with ht0 | htn
        · have hp0 : P[0]'(by omega) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
          rw [← hp0] at ht0
          have : t = 0 := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp ht0
          omega
        · exact htn
    · rintro (rfl | rfl)
      · exact hvX
      · exact hpnX
  have hRendsNotAdj : ¬ G.Adj v pₙ := by
    have hna := PathBasics.path_ends_not_adj hRfrom.1 (by
      rw [PathBasics.pathLength_eq] at hR4
      omega)
    have hpos : 0 < Rpath.length := PathBasics.path_length_pos hRfrom.1
    rw [PathBasics.getElem_zero_of_head? hRfrom.2.1 hpos,
      PathBasics.getElem_last_of_getLast? hRfrom.2.2 hpos] at hna
    exact hna
  have hReven : Even (pathLength Rpath) := by
    by_contra hnot
    have hodd : Odd (pathLength Rpath) := Nat.not_even_iff_odd.mp hnot
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 Rpath v pₙ hRfrom hodd
        X hXR hXanti hvX hpnX with hedge | hshort
    · obtain ⟨u, hu, w, hw, huw, huX, hwX⟩ := hedge
      rcases (hRX u hu).mp huX with rfl | rfl <;>
        rcases (hRX w hw).mp hwX with rfl | rfl
      · exact G.irrefl huw
      · exact hRendsNotAdj huw
      · exact hRendsNotAdj huw.symm
      · exact G.irrefl huw
    · omega
  let Tbase : List V := (P.drop k).take (i - k + 1)
  have hTbaseFrom : IsPathFrom G Tbase (P[k]'hklt) (P[i]'hi) :=
    isPathFrom_slice_le hP hki hi
  have hTmem : ∀ w : V, w ∈ Tbase ↔ ∃ (t : ℕ) (ht : t < P.length),
      k ≤ t ∧ t ≤ i ∧ (P[t]'ht) = w := by
    intro w
    exact PathBasics.mem_slice_iff P hki hi
  have hvT : v ∉ Tbase := by
    intro hv
    obtain ⟨t, ht, -, -, heq⟩ := (hTmem v).mp hv
    exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hTother : ∀ w ∈ Tbase, w ≠ P[k]'hklt → ¬ G.Adj v w := by
    intro w hw hwne hadj
    obtain ⟨t, ht, hkt, -, rfl⟩ := (hTmem w).mp hw
    have htk := hkmax t ht hadj
    have hteq : t = k := by omega
    subst t
    exact hwne rfl
  let T : List V := v :: Tbase
  have hTfrom : IsPathFrom G T v (P[i]'hi) :=
    PathAttach.isPathFrom_cons hTbaseFrom hkadj hvT hTother
  have hTbaseLen : Tbase.length = i - k + 1 := by
    dsimp [Tbase]
    rw [PathBasics.length_slice P hki hi]
  have hTlen : pathLength T = i - k + 1 := by
    rw [PathBasics.pathLength_eq]
    simp [T, hTbaseLen]
  have hTeven : Even (pathLength T) := by
    rw [Nat.even_iff] at hevenP hReven hiEven ⊢
    rw [PathBasics.pathLength_eq] at hevenP
    rw [hRlen] at hReven
    rw [hTlen]
    omega
  have hTpos : 0 < pathLength T := by rw [hTlen]; omega
  have hTX : ∀ w ∈ T, VertexComplete G w X ↔ w = v := by
    intro w hw
    constructor
    · intro hwX
      rcases List.mem_cons.mp hw with rfl | hwB
      · rfl
      · obtain ⟨t, ht, hkt, hti, rfl⟩ := (hTmem w).mp hwB
        rcases (hXuniq _ (List.getElem_mem ht)).mp hwX with ht0 | htn
        · have hp0 : P[0]'(by omega) = p₁ := PathBasics.getElem_zero_of_head? hhead (by omega)
          rw [← hp0] at ht0
          have : t = 0 := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp ht0
          omega
        · rw [← hpn] at htn
          have : t = P.length - 1 :=
            (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hP)).mp htn
          omega
    · rintro rfl
      exact hvX
  have hTY : ∀ w ∈ T, VertexComplete G w Y ↔ w = P[i]'hi := by
    intro w hw
    constructor
    · intro hwY
      rcases List.mem_cons.mp hw with rfl | hwB
      · exact absurd hwY hvY
      · obtain ⟨t, ht, hkt, hti, rfl⟩ := (hTmem w).mp hwB
        have hit := (hminmax t ht (by omega) hwY).1
        have hti' : t = i := by omega
        subst t
        rfl
    · rintro rfl
      exact hYi
  obtain ⟨hT2, c, hTshape, AQ, AR, ⟨hAQ, hAQint⟩, ⟨hAR, hARint⟩, hxor⟩ :=
    _root_.Workspace.Statements.S13.SPGT.thm_13_7 G hG.1.1 X Y hXY hXne hYne
      hXanti hYanti hcompl T v (P[i]'hi) hTfrom.1 hTeven hTpos hTfrom.2.1 hTfrom.2.2 hTX hTY
  have hik : i = k + 1 := by rw [hTlen] at hT2; omega
  have hc : c = P[k]'hklt := by
    have hT1 : 1 < T.length := by
      rw [PathBasics.pathLength_eq] at hT2
      omega
    have hshape1 : T[1]'hT1 = c := by simp [hTshape]
    have hbasepos : 0 < Tbase.length := by rw [hTbaseLen]; omega
    have hbase0 : Tbase[0]'hbasepos = P[k]'hklt :=
      PathBasics.getElem_zero_of_head? hTbaseFrom.2.1 hbasepos
    have hT1base : T[1]'hT1 = Tbase[0]'hbasepos := by simp [T]
    rw [← hshape1, hT1base, hbase0]
  have hkiAdj : G.Adj (P[k]'hklt) (P[i]'hi) :=
    (PathBasics.path_adj_iff hP hklt hi).mpr (Or.inl hik.symm)
  have hjv : ¬ G.Adj (P[j]'hj) v := by
    intro hadj
    have := hnbr j hj hadj.symm
    omega
  have hjk : ¬ G.Adj (P[j]'hj) (P[k]'hklt) :=
    PathBasics.path_not_adj_of_gap hP hj hklt (by omega) (by omega)
  have hjneV : P[j]'hj ≠ v := by
    intro heq
    apply hvP
    rw [← heq]
    exact List.getElem_mem hj
  have hjneK : P[j]'hj ≠ P[k]'hklt :=
    PathBasics.path_ne_of_ne_index hP hj hklt (by omega)
  have hpnk : ¬ G.Adj pₙ (P[k]'hklt) := by
    rw [← hpn]
    exact PathBasics.path_not_adj_of_gap hP hnlt hklt (by omega) (by omega)
  have hpni : ¬ G.Adj pₙ (P[i]'hi) := by
    rw [← hpn]
    exact PathBasics.path_not_adj_of_gap hP hnlt hi (by omega) (by omega)
  have hpnneK : pₙ ≠ P[k]'hklt := by
    rw [← hpn]
    exact PathBasics.path_ne_of_ne_index hP hnlt hklt (by omega)
  have hpnneI : pₙ ≠ P[i]'hi := by
    rw [← hpn]
    exact PathBasics.path_ne_of_ne_index hP hnlt hi (by omega)
  have hAReven : Even (pathLength AR) := by
    rw [hc] at hAR
    exact AntiholeCompletion.even_pathLength_of_witness hBerge hkadj hYj hjv hjk
      hjneV hjneK hAR hARint
  have hAQeven : Even (pathLength AQ) := by
    rw [hc] at hAQ
    exact AntiholeCompletion.even_pathLength_of_witness hBerge hkiAdj hpnX hpnk hpni
      hpnneK hpnneI hAQ hAQint
  rcases hxor with ⟨hAQodd, -⟩ | ⟨hARodd, -⟩
  · exact Nat.not_even_iff_odd.mpr hAQodd hAQeven
  · exact Nat.not_even_iff_odd.mpr hARodd hAReven

private theorem claim2_path (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hij : i ≤ j) (hYi : VertexComplete G (P[i]'hi) Y)
    (hYj : VertexComplete G (P[j]'hj) Y)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j) :
    VertexGood G X Y P p₁ pₙ v ∨
      ∃ (Q : List V) (q : V), IsPathFrom G Q v q ∧
        (∀ w ∈ Q, VertexComplete G w Y ↔ w = q) ∧
        (∀ w ∈ Q, w ≠ v → ∃ (t : ℕ) (ht : t < P.length),
          i < t ∧ t < j ∧ (P[t]'ht) = w) := by
  classical
  obtain ⟨hP, hlen7, heven, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨s, hs, his, hsj, hsY⟩ :=
    exists_y_internal G hG X Y P p₁ pₙ hopt hhead hlast i j hi hj h1i hminmax
  by_cases hmid : ∃ (t : ℕ) (ht : t < P.length), i < t ∧ t < j ∧
      G.Adj v (P[t]'ht)
  · obtain ⟨t, ht, hit, htj, hadj⟩ := hmid
    right
    exact Thm185Helpers.claim2_of_neighbour G Y P hP v hvP hvY i j t s ht hs hit htj
      his hsj hadj hsY
  · have hnoMid : ∀ (t : ℕ) (ht : t < P.length), i < t → t < j →
        ¬ G.Adj v (P[t]'ht) := by
      intro t ht hit htj hadj
      exact hmid ⟨t, ht, hit, htj, hadj⟩
    by_cases hleft : ∃ (t : ℕ) (ht : t < P.length), t ≤ i ∧ G.Adj v (P[t]'ht)
    · by_cases hright : ∃ (t : ℕ) (ht : t < P.length), j ≤ t ∧ G.Adj v (P[t]'ht)
      · exact (crossing_hole_absurd G hG X Y P p₁ pₙ v hopt hhead hlast hvP
          (fun hv => hvXY (Or.inr hv)) hvY i j hi hj h1i hminmax hnoMid hleft hright).elim
      · have hnbr : ∀ (t : ℕ) (ht : t < P.length), G.Adj v (P[t]'ht) → t ≤ i := by
          intro t ht hadj
          by_contra hti
          by_cases htj : t < j
          · exact hnoMid t ht (by omega) htj hadj
          · exact hright ⟨t, ht, by omega, hadj⟩
        by_cases hvX : VertexComplete G v X
        · by_cases hv0 : G.Adj v p₁
          · left
            exact Thm185Helpers.claim1 G hG X Y P p₁ pₙ hopt hhead hlast v hvXY hvP hvY
              hv0 hvX
          · exact (left_only_xcomplete_absurd G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP
              hvY hvX hv0 i j hi hj h1i hij hYi hYj hminmax hnbr
              (by obtain ⟨t, ht, -, hadj⟩ := hleft; exact ⟨t, ht, hadj⟩)).elim
        · left
          exact Thm185Helpers.window_le G X Y P hP p₁ pₙ hhead hlast v hvX i hi hnbr
            (by
              intro t ht ht1 hti htY
              exact (not_lt_of_ge (hminmax t ht ht1 htY).1) hti)
    · left
      apply Thm185Helpers.window_after G X Y P hP p₁ pₙ hhead hlast v j hj
      · intro t ht hadj
        by_contra htj
        by_cases hti : t ≤ i
        · exact hleft ⟨t, ht, hti, hadj⟩
        · exact hnoMid t ht (by omega) (by omega) hadj
      · intro t ht hjt htY
        have := (hminmax t ht (by omega) htY).2
        omega

private theorem nonX_nonadj_absurd (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (hvX : ¬ VertexComplete G v X) (hv0 : ¬ G.Adj v p₁)
    (hbad : ¬ VertexGood G X Y P p₁ pₙ v)
    (i j : ℕ) (hi : i < P.length) (hj : j < P.length) (h1i : 1 ≤ i)
    (hij : i ≤ j) (hYi : VertexComplete G (P[i]'hi) Y)
    (hYj : VertexComplete G (P[j]'hj) Y)
    (hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j)
    (Q : List V) (q : V) (hQ : IsPathFrom G Q v q)
    (hQY : ∀ w ∈ Q, VertexComplete G w Y ↔ w = q)
    (hQsub : ∀ w ∈ Q, w ≠ v → ∃ (t : ℕ) (ht : t < P.length),
      i < t ∧ t < j ∧ (P[t]'ht) = w) : False := by
  classical
  obtain ⟨hP, hlen7, hevenP, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1nePn : p₁ ≠ pₙ := by
    rw [← hp0, ← hpn]
    exact PathBasics.path_ne_of_ne_index hP h0lt hnlt (by omega)
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
  have hqQ : q ∈ Q := PathBasics.getLast_mem hQ.2.2
  have hqY : VertexComplete G q Y := (hQY q hqQ).mpr rfl
  have hvq : v ≠ q := by
    intro he
    exact hvY (he ▸ hqY)
  have hQlen1 : 1 ≤ pathLength Q := by
    rw [PathBasics.pathLength_eq]
    by_contra hc
    have hlen : Q.length = 1 := by omega
    have heq : v = q := by
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
      rw [hx] at hQ
      simpa using hQ.2.1.symm.trans hQ.2.2
    exact hvq heq
  have hexNbr : ∃ t, t < P.length ∧ 0 ≤ t ∧
      (∃ ht : t < P.length, G.Adj v (P[t]'ht)) := by
    have hQ1 : 1 < Q.length := by rw [PathBasics.pathLength_eq] at hQlen1; omega
    have hadj := PathBasics.path_adj_succ hQ.1 (i := 0) hQ1
    have hQ0 : Q[0]'(by omega) = v :=
      PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have hmem : Q[1]'hQ1 ∈ Q := List.getElem_mem hQ1
    obtain ⟨t, ht, hit, htj, heq⟩ := hQsub _ hmem (by
      intro he
      have hndQ := PathBasics.path_nodup hQ.1
      have := hndQ.getElem_inj_iff.mp (he.trans hQ0.symm)
      omega)
    refine ⟨t, ht, Nat.zero_le _, ht, ?_⟩
    rw [hQ0, ← heq] at hadj
    exact hadj
  obtain ⟨h, k, hh, hk, -, hhk, hvhEx, hvkEx, hext⟩ :=
    Thm185Helpers.exists_minmax_index P.length 0
      (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht)) hexNbr
  have hvh : G.Adj v (P[h]'hh) := by simpa only using hvhEx.choose_spec
  have hvk : G.Adj v (P[k]'hk) := by simpa only using hvkEx.choose_spec
  have hhpos : 0 < h := by
    by_contra hc
    have hh0 : h = 0 := by omega
    apply hv0
    rw [← hp0]
    simpa [hh0] using hvh
  have hgap : h + 2 ≤ k := by
    by_contra hc
    apply hbad
    exact Thm185Helpers.subpath_window G X Y P hP p₁ pₙ hhead hlast v h k hhk hk
      (fun t ht hadj => hext t ht (Nat.zero_le _) ⟨ht, hadj⟩)
      (by intro t ht hht htk; omega)
      (fun hvc => absurd hvc hvX)
  let L : List V := P.take (h + 1)
  let R : List V := P.drop k
  have hLfrom : IsPathFrom G L p₁ (P[h]'hh) := by
    have hs := PathBasics.isPathFrom_slice hP (show 0 < h by omega) hh
    rw [hp0] at hs
    simpa [L] using hs
  have hRfrom : IsPathFrom G R (P[k]'hk) pₙ := by
    have hs := isPathFrom_slice_le hP (show k ≤ P.length - 1 by omega) hnlt
    rw [hpn] at hs
    have hc : P.length - 1 - k + 1 = P.length - k := by omega
    rw [hc] at hs
    have htake : (P.drop k).take (P.length - k) = P.drop k := by
      rw [← List.length_drop]
      exact List.take_length
    rw [htake] at hs
    simpa [R] using hs
  have hLmem : ∀ x : V, x ∈ L ↔ ∃ (t : ℕ) (ht : t < P.length),
      t ≤ h ∧ P[t]'ht = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, heq⟩ := List.getElem_of_mem hx
      have htP : t < P.length := by
        dsimp [L] at ht
        simp only [List.length_take, lt_min_iff] at ht
        exact ht.2
      exact ⟨t, htP, by
        dsimp [L] at ht
        simp only [List.length_take, lt_min_iff] at ht
        omega, by simpa [L] using heq⟩
    · rintro ⟨t, ht, hth, rfl⟩
      have htL : t < L.length := by simp [L]; omega
      have he : L[t]'htL = P[t]'ht := by simp [L]
      rw [← he]
      exact List.getElem_mem htL
  have hRmem : ∀ x : V, x ∈ R ↔ ∃ (t : ℕ) (ht : t < P.length),
      k ≤ t ∧ P[t]'ht = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨r, hr, heq⟩ := List.getElem_of_mem hx
      have ht : k + r < P.length := by dsimp [R] at hr; simp only [List.length_drop] at hr; omega
      exact ⟨k + r, ht, by omega, by simpa [R] using heq⟩
    · rintro ⟨t, ht, hkt, rfl⟩
      have hr : t - k < R.length := by simp [R]; omega
      have he : R[t - k]'hr = P[t]'ht := by
        simp only [R, List.getElem_drop]
        exact depIndex P (by omega) (by omega) ht
      rw [← he]
      exact List.getElem_mem hr
  have hvL : v ∉ L := by
    intro hv
    obtain ⟨t, ht, -, heq⟩ := (hLmem v).mp hv
    exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hLother : ∀ x ∈ L, x ≠ P[h]'hh → ¬ G.Adj v x := by
    intro x hx hxne hadj
    obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hx
    have hht := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).1
    have hteq : t = h := by omega
    subst t
    exact hxne rfl
  let LV : List V := L ++ [v]
  have hLVfrom : IsPathFrom G LV p₁ v := by
    simpa [LV] using PathAttach.isPathFrom_concat hLfrom hvh hvL hLother
  have hLVmem : ∀ x : V, x ∈ LV ↔ x ∈ L ∨ x = v := by
    intro x
    simp [LV]
  have hLVRdisj : ∀ x ∈ LV, x ∉ R := by
    intro x hxLV hxR
    rcases (hLVmem x).mp hxLV with hxL | rfl
    · obtain ⟨s, hs, hsh, hseq⟩ := (hLmem x).mp hxL
      obtain ⟨t, ht, hkt, hteq⟩ := (hRmem x).mp hxR
      have he : P[s]'hs = P[t]'ht := hseq.trans hteq.symm
      have : s = t := hnd.getElem_inj_iff.mp he
      omega
    · obtain ⟨t, ht, -, heq⟩ := (hRmem _).mp hxR
      exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hLVRCross : ∀ x ∈ LV, ∀ y ∈ R,
      (G.Adj x y ↔ (x = v ∧ y = P[k]'hk)) := by
    intro x hx y hy
    obtain ⟨t, ht, hkt, rfl⟩ := (hRmem y).mp hy
    constructor
    · intro hadj
      rcases (hLVmem x).mp hx with hxL | rfl
      · obtain ⟨s, hs, hsh, rfl⟩ := (hLmem x).mp hxL
        have hidx := (PathBasics.path_adj_iff hP hs ht).mp hadj
        omega
      · have htk := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).2
        have hteq : t = k := by omega
        exact ⟨rfl, depIndex P hteq ht hk⟩
    · rintro ⟨rfl, heq⟩
      have hteq : t = k := hnd.getElem_inj_iff.mp heq
      subst t
      exact hvk
  let P' : List V := LV ++ R
  have hP'from : IsPathFrom G P' p₁ pₙ := by
    simpa [P'] using PathGlue.glue_path hLVfrom hRfrom hLVRdisj hLVRCross
  have hP'mem : ∀ x : V, x ∈ P' ↔ x ∈ L ∨ x = v ∨ x ∈ R := by
    intro x
    simp [P', LV]
  have hP'len : P'.length = h + 2 + (P.length - k) := by
    simp [P', LV, L, R]
    omega
  by_cases houterY : ∃ (t : ℕ) (ht : t < P.length),
      ((1 ≤ t ∧ t ≤ h) ∨ k ≤ t) ∧ VertexComplete G (P[t]'ht) Y
  · obtain ⟨tY, htY, htRange, htYC⟩ := houterY
    have hP'5 : 5 ≤ P'.length := by
      rw [hP'len]
      rcases htRange with ⟨ht1, hth⟩ | hkt
      · have htne1 : tY ≠ 1 := by
          intro he
          subst tY
          exact hP1Y (by omega) htYC
        omega
      · have htneLast : tY ≠ P.length - 1 := by
          intro he
          apply hpₙY
          rw [← hpn]
          simpa [he] using htYC
        omega
    have hP'out : ∀ x ∈ P', x ∉ X ∧ x ∉ Y := by
      intro x hx
      rcases (hP'mem x).mp hx with hxL | rfl | hxR
      · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
      · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
      · obtain ⟨t, ht, -, rfl⟩ := (hRmem x).mp hxR
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    have hP'X : ∀ x ∈ P', VertexComplete G x X ↔ (x = p₁ ∨ x = pₙ) := by
      intro x hx
      rcases (hP'mem x).mp hx with hxL | rfl | hxR
      · obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hxL
        constructor
        · intro hc
          rcases (hXuniq _ (List.getElem_mem ht)).mp hc with hp | hn
          · exact Or.inl hp
          · exfalso
            rw [← hpn] at hn
            have := hnd.getElem_inj_iff.mp hn
            omega
        · rintro (hp | hn)
          · exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inl hp)
          · exfalso
            rw [← hpn] at hn
            have := hnd.getElem_inj_iff.mp hn
            omega
      · constructor
        · exact fun hc => absurd hc hvX
        · rintro (hp | hn)
          · exact absurd (by rw [hp]; exact PathBasics.head_mem hhead) hvP
          · exact absurd (by rw [hn]; exact PathBasics.getLast_mem hlast) hvP
      · obtain ⟨t, ht, hkt, rfl⟩ := (hRmem x).mp hxR
        constructor
        · intro hc
          rcases (hXuniq _ (List.getElem_mem ht)).mp hc with hp | hn
          · exfalso
            rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · exact Or.inr hn
        · rintro (hp | hn)
          · exfalso
            rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inr hn)
    have hP'1lt : 1 < P'.length := by omega
    have hP'1 : P'[1]'hP'1lt = P[1]'(by omega) := by
      have h1L : 1 < L.length := by simp [L]; omega
      have h1LV : 1 < LV.length := by simp [LV]; omega
      change (LV ++ R)[1]'_ = P[1]'_
      rw [List.getElem_append_left h1LV]
      change (L ++ [v])[1]'_ = P[1]'_
      rw [List.getElem_append_left h1L]
      simp [L]
    have hP'tail : P'.tail.head? = some (P[1]'(by omega)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)]
      simp [hP'1]
    have htMem : P[tY]'htY ∈ P' := by
      rcases htRange with ⟨-, hth⟩ | hkt
      · exact (hP'mem _).mpr (Or.inl ((hLmem _).mpr ⟨tY, htY, hth, rfl⟩))
      · exact (hP'mem _).mpr (Or.inr (Or.inr ((hRmem _).mpr ⟨tY, htY, hkt, rfl⟩)))
    have htNe : P[tY]'htY ≠ p₁ := by
      rw [← hp0]
      exact PathBasics.path_ne_of_ne_index hP htY h0lt (by
        rcases htRange with ⟨ht1, -⟩ | hkt <;> omega)
    have hP'pw : IsPseudowheel G X Y P' :=
      PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl hP'from
        hP'tail hP'out hP'5 hP'X hp₁Y ⟨P[tY]'htY, htMem, htNe, htYC⟩
        (hP1Y (by omega)) hpₙY
    have hsubset : {x : V | x ∈ P' ∧ VertexComplete G x Y} ⊆
        {x : V | x ∈ P ∧ VertexComplete G x Y} := by
      rintro x ⟨hx, hxY⟩
      refine ⟨?_, hxY⟩
      rcases (hP'mem x).mp hx with hxL | rfl | hxR
      · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
        exact List.getElem_mem ht
      · exact absurd hxY hvY
      · obtain ⟨t, ht, -, rfl⟩ := (hRmem x).mp hxR
        exact List.getElem_mem ht
    have hnoGapY : ∀ (s : ℕ) (hs : s < P.length), h < s → s < k →
        ¬ VertexComplete G (P[s]'hs) Y := by
      intro s hs hhs hsk hsY
      have hsNot : P[s]'hs ∉ {x : V | x ∈ P' ∧ VertexComplete G x Y} := by
        rintro ⟨hsMem, -⟩
        rcases (hP'mem _).mp hsMem with hsL | hsv | hsR
        · obtain ⟨r, hr, hrh, heq⟩ := (hLmem _).mp hsL
          have : r = s := hnd.getElem_inj_iff.mp heq
          omega
        · exact hvP (by rw [← hsv]; exact List.getElem_mem hs)
        · obtain ⟨r, hr, hkr, heq⟩ := (hRmem _).mp hsR
          have : r = s := hnd.getElem_inj_iff.mp heq
          omega
      apply hopt.2.1
      exact ⟨X, Y, P', hP'pw,
        Set.ncard_lt_ncard
          ((Set.ssubset_iff_of_subset hsubset).mpr
            ⟨P[s]'hs, ⟨List.getElem_mem hs, hsY⟩, hsNot⟩)
          (Set.toFinite _)⟩
    apply hbad
    exact Thm185Helpers.subpath_window G X Y P hP p₁ pₙ hhead hlast v h k hhk hk
      (fun t ht hadj => hext t ht (Nat.zero_le _) ⟨ht, hadj⟩)
      hnoGapY (fun hvc => absurd hvc hvX)
  · push_neg at houterY
    have hhi : h < i := by
      by_contra hc
      exact houterY i hi (Or.inl ⟨h1i, by omega⟩) hYi
    have hjk : j < k := by
      by_contra hc
      exact houterY j hj (Or.inr (by omega)) hYj
    let RQ : List V := Q.reverse ++ R
    have hQRdisj : ∀ x ∈ Q.reverse, x ∉ R := by
      intro x hxQ hxR
      have hxQ' : x ∈ Q := List.mem_reverse.mp hxQ
      rcases eq_or_ne x v with rfl | hxv
      · obtain ⟨t, ht, -, heq⟩ := (hRmem _).mp hxR
        exact hvP (by rw [← heq]; exact List.getElem_mem ht)
      · obtain ⟨s, hs, his, hsj, heqs⟩ := hQsub x hxQ' hxv
        obtain ⟨t, ht, hkt, heqt⟩ := (hRmem x).mp hxR
        have : s = t := hnd.getElem_inj_iff.mp (heqs.trans heqt.symm)
        omega
    have hQRCross : ∀ x ∈ Q.reverse, ∀ y ∈ R,
        (G.Adj x y ↔ (x = v ∧ y = P[k]'hk)) := by
      intro x hxQ y hyR
      have hxQ' : x ∈ Q := List.mem_reverse.mp hxQ
      obtain ⟨t, ht, hkt, rfl⟩ := (hRmem y).mp hyR
      constructor
      · intro hadj
        rcases eq_or_ne x v with rfl | hxv
        · have htk := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).2
          have heq : t = k := by omega
          exact ⟨rfl, depIndex P heq ht hk⟩
        · obtain ⟨s, hs, his, hsj, rfl⟩ := hQsub x hxQ' hxv
          have hidx := (PathBasics.path_adj_iff hP hs ht).mp hadj
          omega
      · rintro ⟨rfl, heq⟩
        have heq' : t = k := hnd.getElem_inj_iff.mp heq
        subst t
        exact hvk
    have hRQfrom : IsPathFrom G RQ q pₙ := by
      simpa [RQ] using PathGlue.glue_path (PathBasics.isPathFrom_reverse hQ) hRfrom
        hQRdisj hQRCross
    have hRQmem : ∀ x : V, x ∈ RQ ↔ x ∈ Q ∨ x ∈ R := by
      intro x
      simp [RQ]
    have hRQlen : pathLength RQ = pathLength Q + (P.length - k) := by
      rw [PathBasics.pathLength_eq]
      simp [RQ, R]
      rw [PathBasics.pathLength_eq]
      omega
    have hRQout : ∀ x ∈ RQ, x ∉ X ∧ x ∉ Y := by
      intro x hx
      rcases (hRQmem x).mp hx with hxQ | hxR
      · rcases eq_or_ne x v with rfl | hxv
        · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
        · obtain ⟨t, ht, -, -, rfl⟩ := hQsub x hxQ hxv
          exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
            fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
      · obtain ⟨t, ht, -, rfl⟩ := (hRmem x).mp hxR
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    have hRQY : ∀ x ∈ RQ, VertexComplete G x Y ↔ x = q := by
      intro x hx
      rcases (hRQmem x).mp hx with hxQ | hxR
      · exact hQY x hxQ
      · obtain ⟨t, ht, hkt, rfl⟩ := (hRmem x).mp hxR
        constructor
        · intro htY
          have htj := (hminmax t ht (by omega) htY).2
          omega
        · intro heq
          exfalso
          have hqR : q ∈ R := by rw [← heq]; exact hxR
          have hqQ : q ∈ Q := PathBasics.getLast_mem hQ.2.2
          have hqne : q ≠ v := hvq.symm
          obtain ⟨s, hs, -, hsj, heqs⟩ := hQsub q hqQ hqne
          obtain ⟨r, hr, hkr, heqr⟩ := (hRmem q).mp hqR
          have : s = r := hnd.getElem_inj_iff.mp (heqs.trans heqr.symm)
          omega
    have hRQX : ∀ x ∈ RQ, VertexComplete G x X ↔ x = pₙ := by
      intro x hx
      rcases (hRQmem x).mp hx with hxQ | hxR
      · constructor
        · intro hxX
          rcases eq_or_ne x v with rfl | hxv
          · exact absurd hxX hvX
          · obtain ⟨t, ht, hit, htj, rfl⟩ := hQsub x hxQ hxv
            rcases (hXuniq _ (List.getElem_mem ht)).mp hxX with hp | hn
            · rw [← hp0] at hp
              have := hnd.getElem_inj_iff.mp hp
              omega
            · exact hn
        · intro heq
          rcases eq_or_ne x v with rfl | hxv
          · exfalso
            apply hvP
            rw [heq]
            exact PathBasics.getLast_mem hlast
          · obtain ⟨t, ht, -, htj, heqt⟩ := hQsub x hxQ hxv
            rw [heq, ← hpn] at heqt
            have := hnd.getElem_inj_iff.mp heqt
            omega
      · obtain ⟨t, ht, hkt, rfl⟩ := (hRmem x).mp hxR
        constructor
        · intro hxX
          rcases (hXuniq _ (List.getElem_mem ht)).mp hxX with hp | hn
          · rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · exact hn
        · intro hn
          exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inr hn)
    have hp1NotRQ : p₁ ∉ RQ := by
      intro hpRQ
      rcases (hRQmem p₁).mp hpRQ with hpQ | hpR
      · rcases eq_or_ne p₁ v with heq | hne
        · exact hvP (by rw [← heq]; exact PathBasics.head_mem hhead)
        · obtain ⟨t, ht, hit, -, heqt⟩ := hQsub p₁ hpQ hne
          rw [← hp0] at heqt
          have := hnd.getElem_inj_iff.mp heqt
          omega
      · obtain ⟨t, ht, hkt, heqt⟩ := (hRmem p₁).mp hpR
        rw [← hp0] at heqt
        have := hnd.getElem_inj_iff.mp heqt
        omega
    have hp1AntiRQ : ∀ x ∈ RQ, ¬ G.Adj p₁ x := by
      intro x hx
      rcases (hRQmem x).mp hx with hxQ | hxR
      · rcases eq_or_ne x v with rfl | hxv
        · exact fun h => hv0 h.symm
        · obtain ⟨t, ht, hit, -, rfl⟩ := hQsub x hxQ hxv
          rw [← hp0]
          exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
      · obtain ⟨t, ht, hkt, rfl⟩ := (hRmem x).mp hxR
        rw [← hp0]
        exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    have hp1X : VertexComplete G p₁ X :=
      (hXuniq p₁ (PathBasics.head_mem hhead)).mpr (Or.inl rfl)
    have hp1Out : p₁ ∉ X ∧ p₁ ∉ Y := by
      exact ⟨fun h => houtU p₁ (PathBasics.head_mem hhead) (Or.inl h),
        fun h => houtU p₁ (PathBasics.head_mem hhead) (Or.inr h)⟩
    have hbalY : SPGT.Balanced G ({x : V | x ∈ RQ} \ {q}) Y := by
      refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
        ({x : V | x ∈ RQ} \ {q}) Y
        (Set.disjoint_left.mpr (fun x hxA hxY => (hRQout x hxA.1).2 hxY)) p₁ ?_ hp₁Y ?_
      · intro hp
        rcases hp with hpA | hpY
        · exact hp1NotRQ hpA.1
        · exact hp1Out.2 hpY
      · intro x hxA
        exact hp1AntiRQ x hxA.1
    have hbalX : SPGT.Balanced G ({x : V | x ∈ RQ} \ {pₙ}) X := by
      refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
        ({x : V | x ∈ RQ} \ {pₙ}) X
        (Set.disjoint_left.mpr (fun x hxA hxX => (hRQout x hxA.1).1 hxX)) p₁ ?_ hp1X ?_
      · intro hp
        rcases hp with hpA | hpX
        · exact hp1NotRQ hpA.1
        · exact hp1Out.1 hpX
      · intro x hxA
        exact hp1AntiRQ x hxA.1
    have hRQodd : Odd (pathLength RQ) := by
      by_contra hnot
      have hEven : Even (pathLength RQ) := Nat.not_odd_iff_even.mp hnot
      have hpos : 0 < pathLength RQ := by
        rw [hRQlen]
        omega
      have h29 := _root_.Workspace.Statements.S02.SPGT.thm_2_9 G hBerge Y X hXY.symm hYne hXne
        hYanti hXanti (fun y hy x hx => (hcompl x hx y hy).symm) RQ q pₙ hRQfrom.1
        (fun x hx hxy => by
          rcases hxy with hxY | hxX
          · exact (hRQout x hx).2 hxY
          · exact (hRQout x hx).1 hxX)
        hEven hpos hRQfrom.2.1 hRQfrom.2.2 hRQY hRQX
      rcases h29.2 with hn | hn
      · exact hn hbalY
      · exact hn hbalX
    let A : List V := L ++ Q
    have hLQdisj : ∀ x ∈ L, x ∉ Q := by
      intro x hxL hxQ
      obtain ⟨s, hs, hsh, heqs⟩ := (hLmem x).mp hxL
      rcases eq_or_ne x v with heq | hxv
      · exact hvP (by rw [← heq, ← heqs]; exact List.getElem_mem hs)
      · obtain ⟨t, ht, hit, -, heqt⟩ := hQsub x hxQ hxv
        have : s = t := hnd.getElem_inj_iff.mp (heqs.trans heqt.symm)
        omega
    have hLQCross : ∀ x ∈ L, ∀ y ∈ Q,
        (G.Adj x y ↔ (x = P[h]'hh ∧ y = v)) := by
      intro x hxL y hyQ
      obtain ⟨s, hs, hsh, rfl⟩ := (hLmem x).mp hxL
      constructor
      · intro hadj
        rcases eq_or_ne y v with rfl | hyv
        · have hhs := (hext s hs (Nat.zero_le _) ⟨hs, hadj.symm⟩).1
          have heq : s = h := by omega
          exact ⟨depIndex P heq hs hh, rfl⟩
        · obtain ⟨t, ht, hit, -, rfl⟩ := hQsub y hyQ hyv
          have hidx := (PathBasics.path_adj_iff hP hs ht).mp hadj
          omega
      · rintro ⟨heq, rfl⟩
        have hsEq : s = h := hnd.getElem_inj_iff.mp heq
        subst s
        exact hvh.symm
    have hAfrom : IsPathFrom G A p₁ q := by
      simpa [A] using PathGlue.glue_path hLfrom hQ hLQdisj hLQCross
    have hAmem : ∀ x : V, x ∈ A ↔ x ∈ L ∨ x ∈ Q := by
      intro x
      simp [A]
    have hAlen : pathLength A = h + 1 + pathLength Q := by
      rw [PathBasics.pathLength_eq, PathBasics.pathLength_eq]
      simp [A, L]
      omega
    have hAout : ∀ x ∈ A, x ∉ X ∧ x ∉ Y := by
      intro x hx
      rcases (hAmem x).mp hx with hxL | hxQ
      · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
      · rcases eq_or_ne x v with rfl | hxv
        · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
        · obtain ⟨t, ht, -, -, rfl⟩ := hQsub x hxQ hxv
          exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
            fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    have hAY : ∀ x ∈ A, VertexComplete G x Y ↔ (x = p₁ ∨ x = q) := by
      intro x hx
      rcases (hAmem x).mp hx with hxL | hxQ
      · obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hxL
        constructor
        · intro htY
          by_cases ht0 : t = 0
          · left
            exact (depIndex P ht0 ht h0lt).trans hp0
          · have hit := (hminmax t ht (by omega) htY).1
            omega
        · rintro (hp | hq)
          · rw [← hp0] at hp
            have ht0 : t = 0 := hnd.getElem_inj_iff.mp hp
            subst t
            simpa [hp0] using hp₁Y
          · exfalso
            have hqQ' : q ∈ Q := PathBasics.getLast_mem hQ.2.2
            have hqv : q ≠ v := hvq.symm
            obtain ⟨r, hr, hir, -, heqr⟩ := hQsub q hqQ' hqv
            have : t = r := hnd.getElem_inj_iff.mp (hq.trans heqr.symm)
            omega
      · constructor
        · intro hxY
          exact Or.inr ((hQY x hxQ).mp hxY)
        · rintro (hp | hq)
          · exfalso
            have hpneV : p₁ ≠ v := by
              intro he
              exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
            obtain ⟨t, ht, hit, -, heqt⟩ := hQsub p₁ (by simpa [hp] using hxQ) hpneV
            rw [← hp0] at heqt
            have := hnd.getElem_inj_iff.mp heqt
            omega
          · exact (hQY x hxQ).mpr hq
    have hBout : ∀ x ∈ P', x ∉ X ∧ x ∉ Y := by
      intro x hx
      rcases (hP'mem x).mp hx with hxL | rfl | hxR
      · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
      · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
      · obtain ⟨t, ht, -, rfl⟩ := (hRmem x).mp hxR
        exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
          fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    have hBX : ∀ x ∈ P', VertexComplete G x X ↔ (x = p₁ ∨ x = pₙ) := by
      intro x hx
      rcases (hP'mem x).mp hx with hxL | rfl | hxR
      · obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hxL
        constructor
        · intro hc
          rcases (hXuniq _ (List.getElem_mem ht)).mp hc with hp | hn
          · exact Or.inl hp
          · rw [← hpn] at hn
            have := hnd.getElem_inj_iff.mp hn
            omega
        · rintro (hp | hn)
          · exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inl hp)
          · rw [← hpn] at hn
            have := hnd.getElem_inj_iff.mp hn
            omega
      · constructor
        · exact fun hc => absurd hc hvX
        · rintro (hp | hn)
          · exact absurd (by rw [hp]; exact PathBasics.head_mem hhead) hvP
          · exact absurd (by rw [hn]; exact PathBasics.getLast_mem hlast) hvP
      · obtain ⟨t, ht, hkt, rfl⟩ := (hRmem x).mp hxR
        constructor
        · intro hc
          rcases (hXuniq _ (List.getElem_mem ht)).mp hc with hp | hn
          · rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · exact Or.inr hn
        · rintro (hp | hn)
          · rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inr hn)
    have hBlen : pathLength P' = h + 1 + (P.length - k) := by
      rw [PathBasics.pathLength_eq, hP'len]
      omega
    have hoddPaths : Odd (pathLength A) ∨ Odd (pathLength P') := by
      by_cases hAo : Odd (pathLength A)
      · exact Or.inl hAo
      · right
        rw [Nat.not_odd_iff_even, Nat.even_iff] at hAo
        rw [Nat.odd_iff] at hRQodd ⊢
        rw [hAlen] at hAo
        rw [hRQlen] at hRQodd
        rw [hBlen]
        omega
    have hp1ne : P[1]'(by omega) ≠ p₁ := by
      rw [← hp0]
      exact PathBasics.path_ne_of_ne_index hP (by omega) h0lt (by omega)
    have hp1nePn : P[1]'(by omega) ≠ pₙ := by
      rw [← hpn]
      exact PathBasics.path_ne_of_ne_index hP (by omega) hnlt (by omega)
    have hp1A : P[1]'(by omega) ∈ A := by
      apply (hAmem _).mpr
      left
      exact (hLmem _).mpr ⟨1, by omega, by omega, rfl⟩
    have hvA : v ∈ A := (hAmem _).mpr (Or.inr (PathBasics.head_mem hQ.2.1))
    have hp1B : P[1]'(by omega) ∈ P' := by
      exact (hP'mem _).mpr (Or.inl ((hLmem _).mpr ⟨1, by omega, by omega, rfl⟩))
    have hvB : v ∈ P' := (hP'mem _).mpr (Or.inr (Or.inl rfl))
    have hp1neQ : P[1]'(by omega) ≠ q := by
      intro he
      have hqQ' : q ∈ Q := PathBasics.getLast_mem hQ.2.2
      have hqv : q ≠ v := hvq.symm
      obtain ⟨t, ht, hit, -, heqt⟩ := hQsub q hqQ' hqv
      rw [← he] at heqt
      have : t = 1 := hnd.getElem_inj_iff.mp heqt
      omega
    have hp1IntA : P[1]'(by omega) ∈ SPGT.interior A :=
      (PathBasics.mem_interior_iff_of_pathFrom hAfrom).mpr ⟨hp1A, hp1ne, hp1neQ⟩
    have hvIntA : v ∈ SPGT.interior A :=
      (PathBasics.mem_interior_iff_of_pathFrom hAfrom).mpr ⟨hvA,
        (fun he => hvP (by simpa [he] using PathBasics.head_mem hhead)), hvq⟩
    have hp1IntB : P[1]'(by omega) ∈ SPGT.interior P' :=
      (PathBasics.mem_interior_iff_of_pathFrom hP'from).mpr ⟨hp1B, hp1ne, hp1nePn⟩
    have hvIntB : v ∈ SPGT.interior P' :=
      (PathBasics.mem_interior_iff_of_pathFrom hP'from).mpr ⟨hvB,
        (fun he => hvP (by simpa [he] using PathBasics.head_mem hhead)),
        (fun he => hvP (by simpa [he] using PathBasics.getLast_mem hlast))⟩
    have hp1v : P[1]'(by omega) ≠ v := by
      intro he
      exact hvP (by rw [← he]; exact List.getElem_mem (by omega))
    have hOddAnti : h = 1 ∧
        ((∃ S : List V, IsAntipathFrom G S v (P[1]'(by omega)) ∧
            Odd (pathLength S) ∧ ∀ x ∈ SPGT.interior S, x ∈ Y) ∨
          (∃ S : List V, IsAntipathFrom G S v (P[1]'(by omega)) ∧
            Odd (pathLength S) ∧ ∀ x ∈ SPGT.interior S, x ∈ X)) := by
      rcases hoddPaths with hAo | hBo
      · have hres := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 A p₁ q
          hAfrom hAo Y (fun y hy hmem => (hAout y hmem).2 hy) hYanti hp₁Y hqY
        rcases hres with hedge | ⟨hlen3, c, d, hInt, S, hS, hSodd, hSint⟩
        · obtain ⟨u, hu, w, hw, huw, huY, hwY⟩ := hedge
          rcases (hAY u hu).mp huY with rfl | rfl <;>
            rcases (hAY w hw).mp hwY with rfl | rfl
          · exact (G.irrefl huw).elim
          · exact (pathFrom_ends_not_adj hAfrom (by rw [hAlen]; omega) huw).elim
          · exact (pathFrom_ends_not_adj hAfrom (by rw [hAlen]; omega) huw.symm).elim
          · exact (G.irrefl huw).elim
        · have hh1 : h = 1 := by rw [hAlen] at hlen3; omega
          have hp1cd : P[1]'(by omega) = c ∨ P[1]'(by omega) = d := by
            rw [hInt] at hp1IntA
            simpa using hp1IntA
          have hvcd : v = c ∨ v = d := by rw [hInt] at hvIntA; simpa using hvIntA
          refine ⟨hh1, Or.inl ?_⟩
          rcases hp1cd with hp1c | hp1d <;> rcases hvcd with hvc | hvd
          · exact absurd (hp1c.trans hvc.symm) hp1v
          · refine ⟨S.reverse, ?_, ?_, ?_⟩
            · simpa [hvd, hp1c] using PathBasics.isAntipathFrom_reverse hS
            · simpa [PathBasics.pathLength_reverse] using hSodd
            · intro x hx
              exact hSint x ((PathBasics.mem_interior_reverse).mp hx)
          · refine ⟨S, ?_, hSodd, hSint⟩
            simpa [hvc, hp1d] using hS
          · exact absurd (hp1d.trans hvd.symm) hp1v
      · have hpₙX : VertexComplete G pₙ X :=
          (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
        have hres := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 P' p₁ pₙ
          hP'from hBo X (fun x hx hmem => (hBout x hmem).1 hx) hXanti hp1X hpₙX
        rcases hres with hedge | ⟨hlen3, c, d, hInt, S, hS, hSodd, hSint⟩
        · obtain ⟨u, hu, w, hw, huw, huX, hwX⟩ := hedge
          rcases (hBX u hu).mp huX with rfl | rfl <;>
            rcases (hBX w hw).mp hwX with rfl | rfl
          · exact (G.irrefl huw).elim
          · exact (pathFrom_ends_not_adj hP'from (by rw [hBlen]; omega) huw).elim
          · exact (pathFrom_ends_not_adj hP'from (by rw [hBlen]; omega) huw.symm).elim
          · exact (G.irrefl huw).elim
        · have hh1 : h = 1 := by rw [hBlen] at hlen3; omega
          have hp1cd : P[1]'(by omega) = c ∨ P[1]'(by omega) = d := by
            rw [hInt] at hp1IntB
            simpa using hp1IntB
          have hvcd : v = c ∨ v = d := by rw [hInt] at hvIntB; simpa using hvIntB
          refine ⟨hh1, Or.inr ?_⟩
          rcases hp1cd with hp1c | hp1d <;> rcases hvcd with hvc | hvd
          · exact absurd (hp1c.trans hvc.symm) hp1v
          · refine ⟨S.reverse, ?_, ?_, ?_⟩
            · simpa [hvd, hp1c] using PathBasics.isAntipathFrom_reverse hS
            · simpa [PathBasics.pathLength_reverse] using hSodd
            · intro x hx
              exact hSint x ((PathBasics.mem_interior_reverse).mp hx)
          · refine ⟨S, ?_, hSodd, hSint⟩
            simpa [hvc, hp1d] using hS
          · exact absurd (hp1d.trans hvd.symm) hp1v
    obtain ⟨hh1, hOddAnti⟩ := hOddAnti
    have hvNotX : v ∉ X := fun h => hvXY (Or.inl h)
    have hvNotY : v ∉ Y := fun h => hvXY (Or.inr h)
    have hp1mem : P[1]'(by omega) ∈ P := List.getElem_mem (by omega)
    have hp1NotX : P[1]'(by omega) ∉ X :=
      fun h => houtU _ hp1mem (Or.inl h)
    have hp1NotY : P[1]'(by omega) ∉ Y :=
      fun h => houtU _ hp1mem (Or.inr h)
    have hp1NotCompleteX : ¬ VertexComplete G (P[1]'(by omega)) X := by
      intro hc
      rcases (hXuniq _ hp1mem).mp hc with he | he
      · exact hp1ne he
      · exact hp1nePn he
    have hp1NotCompleteY : ¬ VertexComplete G (P[1]'(by omega)) Y :=
      hP1Y (by omega)
    have miss_of_not_complete : ∀ {z : V} {S : Set V},
        ¬ VertexComplete G z S → ∃ x ∈ S, ¬ G.Adj z x := by
      intro z S hn
      by_contra hc
      push_neg at hc
      exact hn hc
    have hvp1 : G.Adj v (P[1]'(by omega)) := by
      simpa [hh1] using hvh
    have hBoth :
        (∃ SX : List V, IsAntipathFrom G SX v (P[1]'(by omega)) ∧
          Odd (pathLength SX) ∧ ∀ x ∈ SPGT.interior SX, x ∈ X) ∧
        (∃ SY : List V, IsAntipathFrom G SY v (P[1]'(by omega)) ∧
          Odd (pathLength SY) ∧ ∀ x ∈ SPGT.interior SY, x ∈ Y) := by
      rcases hOddAnti with ⟨SY, hSY, hSYodd, hSYint⟩ | ⟨SX, hSX, hSXodd, hSXint⟩
      · obtain ⟨SX, hSX, hSXint⟩ :=
          InducedPathExtraction.exists_antipath_interior_in hXanti hvNotX hp1NotX
            (miss_of_not_complete hvX) (miss_of_not_complete hp1NotCompleteX)
        have heven := AntiholeCompletion.even_add_pathLength_of_two_antipaths
          hBerge hXY hcompl hvp1 hvNotX hp1NotX hvNotY hp1NotY
          hSY hSYint hSX hSXint
        have hSXodd' : Odd (pathLength SX) := by
          rw [Nat.even_iff] at heven
          rw [Nat.odd_iff] at hSYodd ⊢
          omega
        exact ⟨⟨SX, hSX, hSXodd', hSXint⟩, ⟨SY, hSY, hSYodd, hSYint⟩⟩
      · obtain ⟨SY, hSY, hSYint⟩ :=
          InducedPathExtraction.exists_antipath_interior_in hYanti hvNotY hp1NotY
            (miss_of_not_complete hvY) (miss_of_not_complete hp1NotCompleteY)
        have heven := AntiholeCompletion.even_add_pathLength_of_two_antipaths
          hBerge hXY hcompl hvp1 hvNotX hp1NotX hvNotY hp1NotY
          hSY hSYint hSX hSXint
        have hSYodd' : Odd (pathLength SY) := by
          rw [Nat.even_iff] at heven
          rw [Nat.odd_iff] at hSXodd ⊢
          omega
        exact ⟨⟨SX, hSX, hSXodd, hSXint⟩, ⟨SY, hSY, hSYodd', hSYint⟩⟩
    obtain ⟨⟨SX, hSX, hSXodd, hSXint⟩, ⟨SY, hSY, hSYodd, hSYint⟩⟩ := hBoth
    have hcoverX : ∀ z : V, VertexComplete G z X →
        G.Adj z v ∨ G.Adj z (P[1]'(by omega)) := by
      intro z hzX
      by_contra hnone
      push_neg at hnone
      have hznev : z ≠ v := by
        intro he
        subst z
        exact hvX hzX
      have hznp1 : z ≠ P[1]'(by omega) := by
        intro he
        subst z
        exact hp1NotCompleteX hzX
      have heven := AntiholeCompletion.even_pathLength_of_witness hBerge hvp1
        hzX hnone.1 hnone.2 hznev hznp1 hSX hSXint
      exact (Nat.not_even_iff_odd.mpr hSXodd) heven
    have hcoverY : ∀ z : V, VertexComplete G z Y →
        G.Adj z v ∨ G.Adj z (P[1]'(by omega)) := by
      intro z hzY
      by_contra hnone
      push_neg at hnone
      have hznev : z ≠ v := by
        intro he
        subst z
        exact hvY hzY
      have hznp1 : z ≠ P[1]'(by omega) := by
        intro he
        subst z
        exact hp1NotCompleteY hzY
      have heven := AntiholeCompletion.even_pathLength_of_witness hBerge hvp1
        hzY hnone.1 hnone.2 hznev hznp1 hSY hSYint
      exact (Nat.not_even_iff_odd.mpr hSYodd) heven
    have hpₙX : VertexComplete G pₙ X :=
      (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
    have hpnNotAdjP1 : ¬ G.Adj pₙ (P[1]'(by omega)) := by
      rw [← hpn]
      exact PathBasics.path_not_adj_of_gap hP hnlt (by omega) (by omega) (by omega)
    have hvpn : G.Adj v pₙ := by
      rcases hcoverX pₙ hpₙX with h | h
      · exact h.symm
      · exact (hpnNotAdjP1 h).elim
    have hkLast : k = P.length - 1 := by
      have he := hext (P.length - 1) hnlt (Nat.zero_le _) ⟨hnlt, by
        rw [hpn]
        exact hvpn⟩
      omega
    obtain ⟨tq, htq, hitq, htqj, heqq⟩ := hQsub q hqQ hvq.symm
    have hqNotAdjP1 : ¬ G.Adj q (P[1]'(by omega)) := by
      rw [← heqq]
      exact PathBasics.path_not_adj_of_gap hP htq (by omega) (by omega) (by omega)
    have hqvAdj : G.Adj q v := by
      rcases hcoverY q hqY with h | h
      · exact h
      · exact (hqNotAdjP1 h).elim
    have hQone : pathLength Q = 1 := pathLength_one_of_ends_adj hQ hqvAdj.symm
    rw [Nat.odd_iff, hRQlen, hQone, hkLast] at hRQodd
    omega

private theorem xcomplete_good (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (hvX : VertexComplete G v X) : VertexGood G X Y P p₁ pₙ v := by
  classical
  by_cases hv0 : G.Adj v p₁
  · exact Thm185Helpers.claim1 G hG X Y P p₁ pₙ hopt hhead hlast v hvXY hvP hvY hv0 hvX
  obtain ⟨hP, hlen7, hevenP, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1nePn : p₁ ≠ pₙ := by
    rw [← hp0, ← hpn]
    exact PathBasics.path_ne_of_ne_index hP h0lt hnlt (by omega)
  have hnd : P.Nodup := PathBasics.path_nodup hP
  obtain ⟨i, j, hi, hj, h1i, hij, hYiEx, hYjEx, hminmax0⟩ :=
    Thm185Helpers.exists_minmax_index P.length 1
      (fun t => ∃ ht : t < P.length, VertexComplete G (P[t]'ht) Y)
      (by obtain ⟨t, ht, ht1, htY⟩ := hYex; exact ⟨t, ht, ht1, ht, htY⟩)
  have hYi : VertexComplete G (P[i]'hi) Y := by simpa only using hYiEx.choose_spec
  have hYj : VertexComplete G (P[j]'hj) Y := by simpa only using hYjEx.choose_spec
  have hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j := by
    intro t ht ht1 htY
    exact hminmax0 t ht ht1 ⟨ht, htY⟩
  by_contra hbad
  rcases claim2_path G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY
      i j hi hj h1i hij hYi hYj hminmax with hdone | ⟨Q, q, hQ, hQY, hQsub⟩
  · exact hbad hdone
  have hqQ : q ∈ Q := PathBasics.getLast_mem hQ.2.2
  have hqY : VertexComplete G q Y := (hQY q hqQ).mpr rfl
  have hvq : v ≠ q := by
    intro he
    exact hvY (he ▸ hqY)
  have hQlen1 : 1 ≤ pathLength Q := by
    rw [PathBasics.pathLength_eq]
    have hQpos := PathBasics.path_length_pos hQ.1
    by_contra hc
    have hlen : Q.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx] at hQ
    exact hvq (by simpa using hQ.2.1.symm.trans hQ.2.2)
  have hQ1lt : 1 < Q.length := by rw [PathBasics.pathLength_eq] at hQlen1; omega
  have hQ0 : Q[0]'(by omega) = v :=
    PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hQ1mem : Q[1]'hQ1lt ∈ Q := List.getElem_mem hQ1lt
  have hQ1ne : Q[1]'hQ1lt ≠ v := by
    intro he
    have := (PathBasics.path_nodup hQ.1).getElem_inj_iff.mp (he.trans hQ0.symm)
    omega
  obtain ⟨tQ, htQ, hitQ, htQj, hQ1eq⟩ := hQsub _ hQ1mem hQ1ne
  have hvQ1 : G.Adj v (Q[1]'hQ1lt) := by
    rw [← hQ0]
    exact PathBasics.path_adj_succ hQ.1 hQ1lt
  have hvtQ : G.Adj v (P[tQ]'htQ) := by rw [hQ1eq]; exact hvQ1
  have hexNbr : ∃ t, t < P.length ∧ 0 ≤ t ∧
      (∃ ht : t < P.length, G.Adj v (P[t]'ht)) :=
    ⟨tQ, htQ, Nat.zero_le _, htQ, hvtQ⟩
  obtain ⟨h, k, hh, hk, -, hhk, hvhEx, hvkEx, hext⟩ :=
    Thm185Helpers.exists_minmax_index P.length 0
      (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht)) hexNbr
  have hvh : G.Adj v (P[h]'hh) := by simpa only using hvhEx.choose_spec
  have hhpos : 0 < h := by
    by_contra hc
    have hh0 : h = 0 := by omega
    apply hv0
    rw [← hp0]
    simpa [hh0] using hvh
  have htle : h ≤ tQ := (hext tQ htQ (Nat.zero_le _) ⟨htQ, hvtQ⟩).1
  have hhj : h < j := by omega
  have hjlast : j < P.length - 1 := by
    by_contra hc
    have hjeq : j = P.length - 1 := by omega
    apply hpₙY
    rw [← hpn]
    simpa [hjeq] using hYj
  let L : List V := P.take (h + 1)
  have hLfrom : IsPathFrom G L p₁ (P[h]'hh) := by
    have hs := PathBasics.isPathFrom_slice hP hhpos hh
    rw [hp0] at hs
    simpa [L] using hs
  have hLmem : ∀ x : V, x ∈ L ↔ ∃ (t : ℕ) (ht : t < P.length),
      t ≤ h ∧ P[t]'ht = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨t, ht, heq⟩ := List.getElem_of_mem hx
      have htP : t < P.length := by
        dsimp [L] at ht
        simp only [List.length_take, lt_min_iff] at ht
        exact ht.2
      exact ⟨t, htP, by
        dsimp [L] at ht
        simp only [List.length_take, lt_min_iff] at ht
        omega, by simpa [L] using heq⟩
    · rintro ⟨t, ht, hth, rfl⟩
      have htL : t < L.length := by simp [L]; omega
      have he : L[t]'htL = P[t]'ht := by simp [L]
      rw [← he]
      exact List.getElem_mem htL
  have hvL : v ∉ L := by
    intro hv
    obtain ⟨t, ht, -, heq⟩ := (hLmem v).mp hv
    exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hLother : ∀ x ∈ L, x ≠ P[h]'hh → ¬ G.Adj v x := by
    intro x hx hxne hadj
    obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hx
    have hht := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).1
    have hteq : t = h := by omega
    subst t
    exact hxne rfl
  let LV : List V := L ++ [v]
  have hLVfrom : IsPathFrom G LV p₁ v := by
    simpa [LV] using PathAttach.isPathFrom_concat hLfrom hvh hvL hLother
  have hLVmem : ∀ x : V, x ∈ LV ↔ x ∈ L ∨ x = v := by
    intro x
    simp [LV]
  have hLVlen : pathLength LV = h + 1 := by
    rw [PathBasics.pathLength_eq]
    simp [LV, L]
    omega
  have hLVout : ∀ x ∈ LV, x ∉ X ∧ x ∉ Y := by
    intro x hx
    rcases (hLVmem x).mp hx with hxL | rfl
    · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
      exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
        fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
  have hLVX : ∀ x ∈ LV, VertexComplete G x X ↔ (x = p₁ ∨ x = v) := by
    intro x hx
    rcases (hLVmem x).mp hx with hxL | rfl
    · obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hxL
      constructor
      · intro htX
        rcases (hXuniq _ (List.getElem_mem ht)).mp htX with hp | hn
        · exact Or.inl hp
        · rw [← hpn] at hn
          have := hnd.getElem_inj_iff.mp hn
          omega
      · rintro (hp | hv)
        · exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inl hp)
        · exfalso
          exact hvP (by rw [← hv]; exact List.getElem_mem ht)
    · exact ⟨fun _ => Or.inr rfl, fun _ => hvX⟩
  have hhodd : Odd h := by
    apply Nat.not_even_iff_odd.mp
    intro hheven
    have hLVodd : Odd (pathLength LV) := by
      obtain ⟨m, hm⟩ := hheven
      rw [hLVlen]
      exact ⟨m, by omega⟩
    have hnoedge : ¬ ∃ u ∈ LV, ∃ w ∈ LV, EdgeComplete G X u w := by
      rintro ⟨u, hu, w, hw, huw, huX, hwX⟩
      rcases (hLVX u hu).mp huX with rfl | rfl <;>
        rcases (hLVX w hw).mp hwX with rfl | rfl
      · exact G.irrefl huw
      · exact hv0 huw.symm
      · exact hv0 huw
      · exact G.irrefl huw
    have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 LV p₁ v
      hLVfrom hLVodd X (fun x hx hmem => (hLVout x hmem).1 hx) hXanti
      ((hLVX p₁ (PathBasics.head_mem hLVfrom.2.1)).mpr (Or.inl rfl)) hvX
    rcases h136 with hedge | ⟨hlen3, c, d, hint, S, hS, hSodd, hSint⟩
    · exact hnoedge hedge
    · have hh2 : h = 2 := by rw [hLVlen] at hlen3; omega
      have hpₙX : VertexComplete G pₙ X :=
        (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
      obtain ⟨w, hwint, hpnw⟩ :=
        _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge X hXanti LV p₁ v
          hLVfrom (fun x hx hX => (hLVout x hx).1 hX) hLVodd
          ((hLVX p₁ (PathBasics.head_mem hLVfrom.2.1)).mpr (Or.inl rfl)) hvX
          hnoedge pₙ hpₙX
      have hwLV := (PathBasics.mem_interior_iff_of_pathFrom hLVfrom).mp hwint
      rcases (hLVmem w).mp hwLV.1 with hwL | hwv
      · obtain ⟨t, ht, hth, rfl⟩ := (hLmem w).mp hwL
        rw [← hpn] at hpnw
        exact PathBasics.path_not_adj_of_gap hP hnlt ht (by omega) (by omega) hpnw
      · exact hwLV.2.2 hwv
  have hnoLeftY : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t → t ≤ h →
      ¬ VertexComplete G (P[t]'ht) Y := by
    intro t ht ht1 hth htY
    have htne1 : t ≠ 1 := by
      intro he
      subst t
      exact hP1Y ht htY
    have hh3 : 3 ≤ h := by
      obtain ⟨m, hm⟩ := hhodd
      omega
    have hLV1lt : 1 < LV.length := by
      rw [PathBasics.length_eq_pathLength_add_one hLVfrom.1, hLVlen]
      omega
    have hLV1 : LV[1]'hLV1lt = P[1]'(by omega) := by
      have h1L : 1 < L.length := by simp [L]; omega
      change (L ++ [v])[1]'_ = P[1]'_
      rw [List.getElem_append_left h1L]
      simp [L]
    have hLVtail : LV.tail.head? = some (P[1]'(by omega)) := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by simp; omega)]
      simp [hLV1]
    have htLV : P[t]'ht ∈ LV := by
      apply (hLVmem _).mpr
      left
      exact (hLmem _).mpr ⟨t, ht, hth, rfl⟩
    have htnep₁ : P[t]'ht ≠ p₁ := by
      rw [← hp0]
      exact PathBasics.path_ne_of_ne_index hP ht h0lt (by omega)
    have hpwLV : IsPseudowheel G X Y LV :=
      PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl hLVfrom
        hLVtail hLVout (by rw [PathBasics.length_eq_pathLength_add_one hLVfrom.1, hLVlen]; omega)
        hLVX hp₁Y ⟨P[t]'ht, htLV, htnep₁, htY⟩ (hP1Y (by omega)) hvY
    have hsubset : {x : V | x ∈ LV ∧ VertexComplete G x Y} ⊆
        {x : V | x ∈ P ∧ VertexComplete G x Y} := by
      rintro x ⟨hx, hxY⟩
      refine ⟨?_, hxY⟩
      rcases (hLVmem x).mp hx with hxL | rfl
      · obtain ⟨s, hs, -, rfl⟩ := (hLmem x).mp hxL
        exact List.getElem_mem hs
      · exact absurd hxY hvY
    have hjNot : P[j]'hj ∉ {x : V | x ∈ LV ∧ VertexComplete G x Y} := by
      rintro ⟨hjLV, -⟩
      rcases (hLVmem _).mp hjLV with hjL | hjv
      · obtain ⟨s, hs, hsh, heq⟩ := (hLmem _).mp hjL
        have : s = j := hnd.getElem_inj_iff.mp heq
        omega
      · exact hvP (by rw [← hjv]; exact List.getElem_mem hj)
    exact hopt.2.1 ⟨X, Y, LV, hpwLV,
      Set.ncard_lt_ncard
        ((Set.ssubset_iff_of_subset hsubset).mpr
          ⟨P[j]'hj, ⟨List.getElem_mem hj, hYj⟩, hjNot⟩)
        (Set.toFinite _)⟩
  have hhi : h < i := by
    by_contra hc
    exact hnoLeftY i hi h1i (by omega) hYi
  have hQout : ∀ x ∈ Q, x ∉ X ∧ x ∉ Y := by
    intro x hx
    rcases eq_or_ne x v with rfl | hxv
    · exact ⟨fun h => hvXY (Or.inl h), fun h => hvXY (Or.inr h)⟩
    · obtain ⟨t, ht, -, -, rfl⟩ := hQsub x hx hxv
      exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
        fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
  have hQX : ∀ x ∈ Q, VertexComplete G x X ↔ x = v := by
    intro x hx
    constructor
    · intro hxX
      by_contra hxv
      obtain ⟨t, ht, hit, htj, rfl⟩ := hQsub x hx hxv
      rcases (hXuniq _ (List.getElem_mem ht)).mp hxX with hp | hn
      · rw [← hp0] at hp
        have := hnd.getElem_inj_iff.mp hp
        omega
      · rw [← hpn] at hn
        have := hnd.getElem_inj_iff.mp hn
        omega
    · rintro rfl
      exact hvX
  have hp1NotQ : p₁ ∉ Q := by
    intro hpQ
    rcases eq_or_ne p₁ v with he | hne
    · exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
    · obtain ⟨t, ht, hit, -, heqt⟩ := hQsub p₁ hpQ hne
      rw [← hp0] at heqt
      have := hnd.getElem_inj_iff.mp heqt
      omega
  have hp1AntiQ : ∀ x ∈ Q, ¬ G.Adj p₁ x := by
    intro x hx
    rcases eq_or_ne x v with rfl | hxv
    · exact fun h => hv0 h.symm
    · obtain ⟨t, ht, hit, -, rfl⟩ := hQsub x hx hxv
      rw [← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
  have hp1X : VertexComplete G p₁ X :=
    (hXuniq p₁ (PathBasics.head_mem hhead)).mpr (Or.inl rfl)
  have hp1Out : p₁ ∉ X ∧ p₁ ∉ Y :=
    ⟨fun hx => houtU p₁ (PathBasics.head_mem hhead) (Or.inl hx),
      fun hy => houtU p₁ (PathBasics.head_mem hhead) (Or.inr hy)⟩
  have hbalX : SPGT.Balanced G ({x : V | x ∈ Q} \ {v}) X := by
    refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
      ({x : V | x ∈ Q} \ {v}) X
      (Set.disjoint_left.mpr (fun x hxA hxX => (hQout x hxA.1).1 hxX)) p₁ ?_ hp1X ?_
    · rintro (hpA | hpX)
      · exact hp1NotQ hpA.1
      · exact hp1Out.1 hpX
    · intro x hxA
      exact hp1AntiQ x hxA.1
  have hbalY : SPGT.Balanced G ({x : V | x ∈ Q} \ {q}) Y := by
    refine _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge
      ({x : V | x ∈ Q} \ {q}) Y
      (Set.disjoint_left.mpr (fun x hxA hxY => (hQout x hxA.1).2 hxY)) p₁ ?_ hp₁Y ?_
    · rintro (hpA | hpY)
      · exact hp1NotQ hpA.1
      · exact hp1Out.2 hpY
    · intro x hxA
      exact hp1AntiQ x hxA.1
  have hQodd : Odd (pathLength Q) := by
    by_contra hnot
    have hQeven : Even (pathLength Q) := Nat.not_odd_iff_even.mp hnot
    have h29 := _root_.Workspace.Statements.S02.SPGT.thm_2_9 G hBerge X Y hXY hXne hYne
      hXanti hYanti hcompl Q v q hQ.1
      (fun x hx hxy => by
        rcases hxy with hxX | hxY
        · exact (hQout x hx).1 hxX
        · exact (hQout x hx).2 hxY)
      hQeven (by omega) hQ.2.1 hQ.2.2 hQX hQY
    rcases h29.2 with hn | hn
    · exact hn hbalX
    · exact hn hbalY
  let A : List V := L ++ Q
  have hLQdisj : ∀ x ∈ L, x ∉ Q := by
    intro x hxL hxQ
    obtain ⟨s, hs, hsh, heqs⟩ := (hLmem x).mp hxL
    rcases eq_or_ne x v with heq | hxv
    · exact hvP (by rw [← heq, ← heqs]; exact List.getElem_mem hs)
    · obtain ⟨t, ht, hit, -, heqt⟩ := hQsub x hxQ hxv
      have : s = t := hnd.getElem_inj_iff.mp (heqs.trans heqt.symm)
      omega
  have hLQCross : ∀ x ∈ L, ∀ y ∈ Q,
      (G.Adj x y ↔ (x = P[h]'hh ∧ y = v)) := by
    intro x hxL y hyQ
    obtain ⟨s, hs, hsh, rfl⟩ := (hLmem x).mp hxL
    constructor
    · intro hadj
      rcases eq_or_ne y v with rfl | hyv
      · have hhs := (hext s hs (Nat.zero_le _) ⟨hs, hadj.symm⟩).1
        have heq : s = h := by omega
        exact ⟨depIndex P heq hs hh, rfl⟩
      · obtain ⟨t, ht, hit, -, rfl⟩ := hQsub y hyQ hyv
        have hidx := (PathBasics.path_adj_iff hP hs ht).mp hadj
        omega
    · rintro ⟨heq, rfl⟩
      have hsEq : s = h := hnd.getElem_inj_iff.mp heq
      subst s
      exact hvh.symm
  have hAfrom : IsPathFrom G A p₁ q := by
    simpa [A] using PathGlue.glue_path hLfrom hQ hLQdisj hLQCross
  have hAmem : ∀ x : V, x ∈ A ↔ x ∈ L ∨ x ∈ Q := by
    intro x
    simp [A]
  have hAlen : pathLength A = h + 1 + pathLength Q := by
    rw [PathBasics.pathLength_eq, PathBasics.pathLength_eq]
    simp [A, L]
    omega
  have hAout : ∀ x ∈ A, x ∉ X ∧ x ∉ Y := by
    intro x hx
    rcases (hAmem x).mp hx with hxL | hxQ
    · obtain ⟨t, ht, -, rfl⟩ := (hLmem x).mp hxL
      exact ⟨fun h => houtU _ (List.getElem_mem ht) (Or.inl h),
        fun h => houtU _ (List.getElem_mem ht) (Or.inr h)⟩
    · exact hQout x hxQ
  have hAY : ∀ x ∈ A, VertexComplete G x Y ↔ (x = p₁ ∨ x = q) := by
    intro x hx
    rcases (hAmem x).mp hx with hxL | hxQ
    · obtain ⟨t, ht, hth, rfl⟩ := (hLmem x).mp hxL
      constructor
      · intro htY
        by_cases ht0 : t = 0
        · left
          exact (depIndex P ht0 ht h0lt).trans hp0
        · exact absurd htY (hnoLeftY t ht (by omega) hth)
      · rintro (hp | hq)
        · rw [← hp0] at hp
          have ht0 : t = 0 := hnd.getElem_inj_iff.mp hp
          subst t
          simpa [hp0] using hp₁Y
        · exfalso
          have : P[t]'ht ∈ Q := by rw [hq]; exact hqQ
          exact hLQdisj _ hxL this
    · constructor
      · intro hxY
        exact Or.inr ((hQY x hxQ).mp hxY)
      · rintro (hp | hq)
        · exfalso
          exact hp1NotQ (by rw [← hp]; exact hxQ)
        · exact (hQY x hxQ).mpr hq
  have hAodd : Odd (pathLength A) := by
    obtain ⟨mh, hmh⟩ := hhodd
    obtain ⟨mq, hmq⟩ := hQodd
    rw [hAlen]
    exact ⟨mh + mq + 1, by omega⟩
  have hnoAYedge : ¬ ∃ u ∈ A, ∃ w ∈ A, EdgeComplete G Y u w := by
    rintro ⟨u, hu, w, hw, huw, huY, hwY⟩
    rcases (hAY u hu).mp huY with rfl | rfl <;>
      rcases (hAY w hw).mp hwY with rfl | rfl
    · exact G.irrefl huw
    · exact pathFrom_ends_not_adj hAfrom (by rw [hAlen]; omega) huw
    · exact pathFrom_ends_not_adj hAfrom (by rw [hAlen]; omega) huw.symm
    · exact G.irrefl huw
  have h136A := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 A p₁ q
    hAfrom hAodd Y (fun y hy hmem => (hAout y hmem).2 hy) hYanti hp₁Y hqY
  have hAthree : pathLength A = 3 := by
    rcases h136A with hedge | hthree
    · exact absurd hedge hnoAYedge
    · exact hthree.1
  have hh1 : h = 1 := by
    rw [hAlen] at hAthree
    obtain ⟨mh, hmh⟩ := hhodd
    obtain ⟨mq, hmq⟩ := hQodd
    omega
  have hQone : pathLength Q = 1 := by rw [hAlen, hh1] at hAthree; omega
  have hvqAdj : G.Adj v q := PathBasics.isPathFrom_ends_adj_of_length_one hQ hQone
  have hLeq : L = [p₁, P[1]'(by omega)] := by
    have hLone : pathLength L = 1 := by
      rw [PathBasics.pathLength_eq]
      simp [L, hh1, show 2 ≤ P.length by omega]
    have he := eq_pair_of_pathLength_one hLfrom hLone
    have hidx : P[h]'hh = P[1]'(by omega) := depIndex P hh1 hh (by omega)
    simpa [hidx] using he
  have hQeq : Q = [v,q] := eq_pair_of_pathLength_one hQ hQone
  have hAeq : A = [p₁, P[1]'(by omega), v, q] := by
    simp [A, hLeq, hQeq]
  have hcoverY : ∀ z : V, VertexComplete G z Y →
      G.Adj z v ∨ G.Adj z (P[1]'(by omega)) := by
    intro z hzY
    obtain ⟨w, hw, hzw⟩ :=
      _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y hYanti A p₁ q hAfrom
        (fun y hy hmem => (hAout y hy).2 hmem) hAodd hp₁Y hqY hnoAYedge z hzY
    rw [hAeq] at hw
    simp [SPGT.interior] at hw
    rcases hw with rfl | rfl
    · exact Or.inr hzw
    · exact Or.inl hzw
  have hYadj : ∀ (t : ℕ) (ht : t < P.length), VertexComplete G (P[t]'ht) Y →
      t ≠ 0 → t ≠ 2 → G.Adj v (P[t]'ht) := by
    intro t ht htY ht0 ht2
    rcases hcoverY _ htY with hadj | hadj
    · exact hadj.symm
    · have hidx := (PathBasics.path_adj_iff hP ht (show 1 < P.length by omega)).mp hadj
      omega
  have hgap : 3 ≤ j - i :=
    y_window_size G hG X Y P p₁ pₙ hopt hhead hlast i j hi hj h1i hminmax
  have hiEven : Even i :=
    first_y_even G hG X Y P p₁ pₙ hopt hhead hlast i hi h1i hYi
      (fun t ht ht1 htY => (hminmax t ht ht1 htY).1)
  have hvi : ¬ G.Adj v (P[i]'hi) := by
    intro hvi
    obtain ⟨y0, hy0Y, hvy0⟩ : ∃ y ∈ Y, ¬ G.Adj v y := by
      by_contra hc
      push_neg at hc
      exact hvY hc
    let Yv : Set V := Y ∪ {v}
    have hvNotY : v ∉ Y := fun hv => hvXY (Or.inr hv)
    have hvNotX : v ∉ X := fun hv => hvXY (Or.inl hv)
    have hvney : v ≠ y0 := fun he => hvNotY (he ▸ hy0Y)
    have hYvanti : AnticonnectedSet G Yv := by
      dsimp [Yv]
      exact ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hYanti
        ⟨y0, hy0Y, ⟨hvney, hvy0⟩⟩
    have hXYv : Disjoint X Yv := by
      dsimp [Yv]
      rw [Set.disjoint_union_right]
      exact ⟨hXY, Set.disjoint_singleton_right.mpr hvNotX⟩
    have hcomplYv : Complete G X Yv := by
      intro x hx z hz
      rcases hz with hzY | hzv
      · exact hcompl x hx z hzY
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        exact (hvX x hx).symm
    let B : List V := P.take (i + 1)
    have hBfrom0 : IsPathFrom G B (P[0]'h0lt) (P[i]'hi) := by
      simpa [B] using PathBasics.isPathFrom_slice hP (show 0 < i by omega) hi
    have hBfrom : IsPathFrom G B p₁ (P[i]'hi) := by rw [← hp0]; exact hBfrom0
    have hBlen : pathLength B = i := by
      rw [PathBasics.pathLength_eq]
      simp [B]
      omega
    have hBmem : ∀ x : V, x ∈ B ↔ ∃ (t : ℕ) (ht : t < P.length),
        t ≤ i ∧ P[t]'ht = x := by
      intro x
      constructor
      · intro hx
        obtain ⟨t, ht, heq⟩ := List.getElem_of_mem hx
        have htP : t < P.length := by
          dsimp [B] at ht
          simp only [List.length_take, lt_min_iff] at ht
          exact ht.2
        exact ⟨t, htP, by
          dsimp [B] at ht
          simp only [List.length_take, lt_min_iff] at ht
          omega, by simpa [B] using heq⟩
      · rintro ⟨t, ht, hti, rfl⟩
        have htB : t < B.length := by simp [B]; omega
        have he : B[t]'htB = P[t]'ht := by simp [B]
        rw [← he]
        exact List.getElem_mem htB
    have hBX : ∀ x ∈ B, VertexComplete G x X ↔ x = p₁ := by
      intro x hx
      obtain ⟨t, ht, hti, rfl⟩ := (hBmem x).mp hx
      constructor
      · intro htX
        rcases (hXuniq _ (List.getElem_mem ht)).mp htX with hp | hn
        · exact hp
        · rw [← hpn] at hn
          have := hnd.getElem_inj_iff.mp hn
          omega
      · intro hp
        exact (hXuniq _ (List.getElem_mem ht)).mpr (Or.inl hp)
    have hBYv : ∀ x ∈ B, VertexComplete G x Yv ↔ x = P[i]'hi := by
      intro x hx
      obtain ⟨t, ht, hti, rfl⟩ := (hBmem x).mp hx
      constructor
      · intro htYv
        have htY : VertexComplete G (P[t]'ht) Y := fun y hy => htYv y (Or.inl hy)
        have hit := (hminmax t ht (by
          by_contra hc
          have ht0 : t = 0 := by omega
          subst t
          have h0v : G.Adj (P[0]'ht) v := htYv v (Or.inr rfl)
          rw [hp0] at h0v
          exact hv0 h0v.symm) htY).1
        have htiEq : t = i := by omega
        exact depIndex P htiEq ht hi
      · intro heq
        have htiEq : t = i := hnd.getElem_inj_iff.mp heq
        subst t
        intro z hz
        rcases hz with hzY | hzv
        · exact hYi z hzY
        · rw [Set.mem_singleton_iff] at hzv
          subst z
          exact hvi.symm
    have hYvne : Yv.Nonempty := ⟨v, Or.inr rfl⟩
    have hBeven : Even (pathLength B) := by simpa only [hBlen] using hiEven
    have h137 := _root_.Workspace.Statements.S13.SPGT.thm_13_7 G hG.1.1 X Yv
      hXYv hXne hYvne hXanti hYvanti hcomplYv B p₁ (P[i]'hi)
      hBfrom.1 hBeven (by rw [hBlen]; omega) hBfrom.2.1 hBfrom.2.2 hBX hBYv
    obtain ⟨hBtwo, c, hBshape, QX, RY, ⟨hQXanti, hQXint⟩,
      ⟨hRYanti, hRYint⟩, hxor⟩ := h137
    have hi2 : i = 2 := by rw [hBlen] at hBtwo; omega
    have hc : c = P[1]'(by omega) := by
      have hB1 : B[1]? = some (P[1]'(by omega)) := by simp [B, hi2]
      have hshape1 := congrArg (fun l : List V => l[1]?) hBshape
      simpa [hB1] using hshape1.symm
    have hpₙX : VertexComplete G pₙ X :=
      (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
    have hpₙnotA : pₙ ∉ ({P[1]'(by omega), P[2]'(by omega)} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (he | he) <;> rw [← hpn] at he
      all_goals have := hnd.getElem_inj_iff.mp he; omega
    have hpₙnotX : pₙ ∉ X := fun hx =>
      houtU pₙ (PathBasics.getLast_mem hlast) (Or.inl hx)
    have hpₙanti : VertexAnticomplete G pₙ ({P[1]'(by omega), P[2]'(by omega)} : Set V) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl <;> rw [← hpn]
      all_goals exact PathBasics.path_not_adj_of_gap hP hnlt (by omega) (by omega) (by omega)
    have hbalPX : SPGT.Balanced G ({P[1]'(by omega), P[2]'(by omega)} : Set V) X :=
      _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge _ _
        (Set.disjoint_left.mpr (fun z hz hx =>
          houtU z (by rcases hz with rfl | rfl <;> simp) (Or.inl hx))) pₙ
        (by rintro (hz | hx); exact hpₙnotA hz; exact hpₙnotX hx) hpₙX hpₙanti
    have hjYv : VertexComplete G (P[j]'hj) Yv := by
      intro z hz
      rcases hz with hzY | hzv
      · exact hYj z hzY
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        exact (hYadj j hj hYj (by omega) (by omega)).symm
    have hjnotA : P[j]'hj ∉ ({p₁, P[1]'(by omega)} : Set V) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (he | he)
      · rw [← hp0] at he
        have := hnd.getElem_inj_iff.mp he
        omega
      · have := hnd.getElem_inj_iff.mp he
        omega
    have hjnotYv : P[j]'hj ∉ Yv := by
      rintro (hy | hv)
      · exact houtU _ (List.getElem_mem hj) (Or.inr hy)
      · exact hvP (by simpa using hv.symm ▸ List.getElem_mem hj)
    have hjanti : VertexAnticomplete G (P[j]'hj) ({p₁, P[1]'(by omega)} : Set V) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · rw [← hp0]
        exact PathBasics.path_not_adj_of_gap hP hj h0lt (by omega) (by omega)
      · exact PathBasics.path_not_adj_of_gap hP hj (by omega) (by omega) (by omega)
    have hpairYvDisj : Disjoint ({p₁, P[1]'(by omega)} : Set V) Yv := by
      apply Set.disjoint_left.mpr
      intro z hz hzyv
      rcases hz with rfl | rfl
      · rcases hzyv with hy | hv
        · exact hp1Out.2 hy
        · rw [Set.mem_singleton_iff] at hv
          exact hvP (hv ▸ PathBasics.head_mem hhead)
      · rcases hzyv with hy | hv
        · exact houtU _ (List.getElem_mem (show 1 < P.length by omega)) (Or.inr hy)
        · rw [Set.mem_singleton_iff] at hv
          exact hvP (hv ▸ List.getElem_mem (show 1 < P.length by omega))
    have hbalYv : SPGT.Balanced G ({p₁, P[1]'(by omega)} : Set V) Yv :=
      _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge _ _ hpairYvDisj
        (P[j]'hj)
        (by rintro (hz | hYv); exact hjnotA hz; exact hjnotYv hYv) hjYv hjanti
    have hPi2 : P[i]'hi = P[2]'(by omega) := depIndex P hi2 hi (by omega)
    rw [hc, hPi2] at hQXanti
    rw [hc] at hRYanti
    rcases hxor with ⟨hQodd, -⟩ | ⟨hRodd, -⟩
    · exact hbalPX.2 _ _ QX (by simp) (by simp)
        (PathBasics.path_adj_succ hP (show 2 < P.length by omega)) hQXanti hQXint hQodd
    · exact hbalYv.2 _ _ RY (by simp) (by simp)
        (by rw [← hp0]; exact PathBasics.path_adj_succ hP (show 1 < P.length by omega))
        hRYanti hRYint hRodd
  have hi2 : i = 2 := by
    by_contra hne
    exact hvi (hYadj i hi hYi (by omega) hne)
  have hexRight : ∃ t, t < P.length ∧ i + 1 ≤ t ∧
      (∃ ht : t < P.length, G.Adj v (P[t]'ht)) :=
    ⟨tQ, htQ, by omega, htQ, hvtQ⟩
  obtain ⟨r, rmax, hr, hrmax, hir, -, hvrEx, -, hrext⟩ :=
    Thm185Helpers.exists_minmax_index P.length (i + 1)
      (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht)) hexRight
  have hvr : G.Adj v (P[r]'hr) := by simpa only using hvrEx.choose_spec
  have hrleQ : r ≤ tQ :=
    (hrext tQ htQ (by omega) ⟨htQ, hvtQ⟩).1
  have hrj : r < j := by omega
  have hrmin : ∀ (t : ℕ) (ht : t < P.length), i < t → t < r →
      ¬ G.Adj v (P[t]'ht) := by
    intro t ht hit htr hadj
    have hrt := (hrext t ht (by omega) ⟨ht, hadj⟩).1
    omega
  have hv1 : G.Adj v (P[1]'(by omega)) := by simpa [hh1] using hvh
  have hmid1r : ∀ (m : ℕ) (hm : m < P.length), 1 < m → m < r →
      ¬ G.Adj v (P[m]'hm) := by
    intro m hm hm1 hmr
    by_cases hmi : m = i
    · subst m
      exact hvi
    · exact hrmin m hm (by omega) hmr
  let H : List V := v :: (P.drop 1).take (r - 1 + 1)
  have hH : IsHoleList G H := by
    dsimp [H]
    exact Thm185Helpers.hole_from_two_neighbours G P hP v hvP 1 r
      (by omega) hr hv1 hvr hmid1r
  have hHlen : holeLength H = r + 1 := by
    have hslen : ((P.drop 1).take (r - 1 + 1)).length = r := by
      rw [PathBasics.length_slice P (show 1 ≤ r by omega) hr]
      omega
    simp only [H, holeLength, List.length_cons]
    rw [hslen]
  have hHeven : Even (holeLength H) := hBerge.1 H hH
  have hrOdd : Odd r := by
    rw [hHlen, Nat.even_iff] at hHeven
    rw [Nat.odd_iff]
    omega
  let S : List V := (P.drop 2).take (r - 2 + 1)
  have hSfrom : IsPathFrom G S (P[2]'(by omega)) (P[r]'hr) := by
    simpa [S] using PathBasics.isPathFrom_slice hP (show 2 < r by omega) hr
  have hvS : v ∉ S := by
    intro hmem
    obtain ⟨t, ht, -, -, heq⟩ :=
      (PathBasics.mem_slice_iff P (show 2 ≤ r by omega) hr).mp hmem
    exact hvP (by rw [← heq]; exact List.getElem_mem ht)
  have hSother : ∀ x ∈ S, x ≠ P[r]'hr → ¬ G.Adj v x := by
    intro x hx hxne hadj
    obtain ⟨t, ht, h2t, htr, rfl⟩ :=
      (PathBasics.mem_slice_iff P (show 2 ≤ r by omega) hr).mp hx
    have htr' : t < r := by
      by_contra hc
      have hteq : t = r := by omega
      exact hxne (depIndex P hteq ht hr)
    exact hmid1r t ht (by omega) htr' hadj
  let C : List V := S ++ [v]
  have hCfrom : IsPathFrom G C (P[2]'(by omega)) v := by
    simpa [C] using PathAttach.isPathFrom_concat hSfrom hvr hvS hSother
  have hSlen : S.length = r - 1 := by
    dsimp [S]
    rw [PathBasics.length_slice P (show 2 ≤ r by omega) hr]
    omega
  have hClen : C.length = r := by
    simp only [C, List.length_append, List.length_singleton]
    rw [hSlen]
    omega
  have hCplen : pathLength C = r - 1 := by
    rw [PathBasics.pathLength_eq, hClen]
  have hCeven : Even (pathLength C) := by
    rw [hCplen, Nat.even_iff]
    rw [Nat.odd_iff] at hrOdd
    omega
  have hCpos : 0 < pathLength C := by rw [hCplen]; omega
  have hCmem : ∀ x : V, x ∈ C ↔
      (∃ (t : ℕ) (ht : t < P.length), 2 ≤ t ∧ t ≤ r ∧ P[t]'ht = x) ∨ x = v := by
    intro x
    rw [show C = S ++ [v] by rfl, List.mem_append, List.mem_singleton]
    rw [show S = (P.drop 2).take (r - 2 + 1) by rfl,
      PathBasics.mem_slice_iff P (show 2 ≤ r by omega) hr]
  have hCXuniq : ∀ x ∈ C, VertexComplete G x X ↔ x = v := by
    intro x hx
    constructor
    · intro hxX
      rcases (hCmem x).mp hx with ⟨t, ht, h2t, htr, rfl⟩ | rfl
      · rcases (hXuniq _ (List.getElem_mem ht)).mp hxX with hp | hn
        · rw [← hp0] at hp
          have := hnd.getElem_inj_iff.mp hp
          omega
        · rw [← hpn] at hn
          have := hnd.getElem_inj_iff.mp hn
          omega
      · rfl
    · rintro rfl
      exact hvX
  have hClast1 : C.dropLast.getLast? = some (P[r]'hr) := by
    simp only [C, List.dropLast_concat]
    simpa [S] using PathBasics.getLast?_slice P (show 2 ≤ r by omega) hr
  have hClast2 : C.dropLast.dropLast.getLast? = some (P[r - 1]'(by omega)) := by
    rw [Workspace.ProofLemmas.Thm182DropLastIndex.dropLast_dropLast_getLast?_eq C
      (by rw [hClen]; omega)]
    have hidx : C[C.length - 3]'(by omega) = P[r - 1]'(by omega) := by
      simp only [C, hClen]
      rw [List.getElem_append_left (by rw [hSlen]; omega)]
      exact PathBasics.getElem_slice' P (by rw [hSlen]; omega) (by omega) (by omega)
    rw [hidx]
  have hp1X : VertexComplete G p₁ X :=
    (hXuniq p₁ (PathBasics.head_mem hhead)).mpr (Or.inl rfl)
  have hp1r : ¬ G.Adj p₁ (P[r]'hr) := by
    rw [← hp0]
    exact PathBasics.path_not_adj_of_gap hP h0lt hr (by omega) (by omega)
  have hp1rm1 : ¬ G.Adj p₁ (P[r - 1]'(by omega)) := by
    rw [← hp0]
    exact PathBasics.path_not_adj_of_gap hP h0lt (by omega) (by omega) (by omega)
  have h182 := _root_.Workspace.Statements.S18.SPGT.thm_18_2 G hG Y X
    (Disjoint.symm hXY) hYne hXne hYanti hXanti
    (fun y hy x hx => (hcompl x hx y hy).symm)
    C (P[2]'(by omega)) (P[r - 1]'(by omega)) (P[r]'hr) v hCfrom.1
    hCeven hCpos hCfrom.2.1 hCfrom.2.2 hClast1 hClast2
    (by simpa [hi2] using hYi) hvY hCXuniq
    ⟨p₁, hp1X, hp1r, hp1rm1⟩
  have hCYends : ∀ x ∈ C, VertexComplete G x Y →
      x = P[2]'(by omega) ∨ x = P[r]'hr := by
    intro x hx hxY
    rcases (hCmem x).mp hx with ⟨t, ht, h2t, htr, rfl⟩ | rfl
    · by_cases ht2 : t = 2
      · exact Or.inl (depIndex P ht2 ht (by omega))
      · by_cases htrEq : t = r
        · exact Or.inr (depIndex P htrEq ht hr)
        · have hvt := hYadj t ht hxY (by omega) ht2
          exact absurd hvt (hmid1r t ht (by omega) (by omega))
    · exact absurd hxY hvY
  have hr3Y : r = 3 ∧ VertexComplete G (P[r]'hr) Y := by
    rcases h182 with hEodd | ⟨hCthree, AQ, hAQ, hAQodd, hAQint⟩
    · have hEpos : 0 < {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C,
          e = s(u, w) ∧ EdgeComplete G Y u w}.ncard := by
        obtain ⟨m, hm⟩ := hEodd
        omega
      obtain ⟨e, he⟩ := Set.nonempty_of_ncard_ne_zero (by omega :
        {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C,
          e = s(u, w) ∧ EdgeComplete G Y u w}.ncard ≠ 0)
      change ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧ EdgeComplete G Y u w at he
      obtain ⟨u, hu, w, hw, -, huw, huY, hwY⟩ := he
      have huEnd := hCYends u hu huY
      have hwEnd := hCYends w hw hwY
      have h2rY : G.Adj (P[2]'(by omega)) (P[r]'hr) ∧
          VertexComplete G (P[r]'hr) Y := by
        rcases huEnd with hu2 | hur <;> rcases hwEnd with hw2 | hwr
        · exfalso
          rw [hu2, hw2] at huw
          exact G.irrefl huw
        · exact ⟨by simpa [hu2, hwr] using huw, by simpa [hwr] using hwY⟩
        · exact ⟨by simpa [hur, hw2] using huw.symm, by simpa [hur] using huY⟩
        · exfalso
          rw [hur, hwr] at huw
          exact G.irrefl huw
      have hrEq : r = 3 := by
        have hidx := (PathBasics.path_adj_iff hP (show 2 < P.length by omega) hr).mp h2rY.1
        omega
      exact ⟨hrEq, h2rY.2⟩
    · exfalso
      have hpairY : Disjoint ({P[r]'hr, v} : Set V) Y := by
        apply Set.disjoint_left.mpr
        intro z hz hzY
        rcases hz with rfl | rfl
        · exact houtU _ (List.getElem_mem hr) (Or.inr hzY)
        · exact hvXY (Or.inr hzY)
      have hp1neR : p₁ ≠ P[r]'hr := by
        rw [← hp0]
        exact PathBasics.path_ne_of_ne_index hP h0lt hr (by omega)
      have hp1neV : p₁ ≠ v := by
        intro he
        exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
      have hp1antiPair : VertexAnticomplete G p₁ ({P[r]'hr, v} : Set V) := by
        intro z hz
        rcases hz with rfl | rfl
        · exact hp1r
        · exact fun hadj => hv0 hadj.symm
      have hbalPair : SPGT.Balanced G ({P[r]'hr, v} : Set V) Y :=
        _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hBerge _ _ hpairY p₁
          (by simp [hp1neR, hp1neV, hp1Out.2]) hp₁Y hp1antiPair
      exact hbalPair.2 _ _ AQ (by simp) (by simp) hvr.symm hAQ hAQint hAQodd
  obtain ⟨hr3, hPrY⟩ := hr3Y
  have hp1P1 : p₁ ≠ P[1]'(by omega) := by
    rw [← hp0]
    exact PathBasics.path_ne_of_ne_index hP h0lt (by omega) (by omega)
  have hp1P2 : p₁ ≠ P[2]'(by omega) := by
    rw [← hp0]
    exact PathBasics.path_ne_of_ne_index hP h0lt (by omega) (by omega)
  have hp1P3 : p₁ ≠ P[3]'(by omega) := by
    rw [← hp0]
    exact PathBasics.path_ne_of_ne_index hP h0lt (by omega) (by omega)
  have hP1P2 : P[1]'(by omega) ≠ P[2]'(by omega) :=
    PathBasics.path_ne_of_ne_index hP (by omega) (by omega) (by omega)
  have hP1P3 : P[1]'(by omega) ≠ P[3]'(by omega) :=
    PathBasics.path_ne_of_ne_index hP (by omega) (by omega) (by omega)
  have hP2P3 : P[2]'(by omega) ≠ P[3]'(by omega) :=
    PathBasics.path_ne_of_ne_index hP (by omega) (by omega) (by omega)
  have hp1v : p₁ ≠ v := by
    intro he
    exact hvP (he ▸ PathBasics.head_mem hhead)
  have hP1v : P[1]'(by omega) ≠ v := by
    intro he
    exact hvP (he ▸ List.getElem_mem (show 1 < P.length by omega))
  have hP2v : P[2]'(by omega) ≠ v := by
    intro he
    exact hvP (he ▸ List.getElem_mem (show 2 < P.length by omega))
  have hP3v : P[3]'(by omega) ≠ v := by
    intro he
    exact hvP (he ▸ List.getElem_mem (show 3 < P.length by omega))
  have hTnd : [p₁, P[1]'(by omega), P[2]'(by omega), P[3]'(by omega), v].Nodup := by
    simp [List.nodup_cons, hp1P1, hp1P2, hp1P3, hp1v, hP1P2, hP1P3,
      hP1v, hP2P3, hP2v, hP3v]
  have hp1P1adj : G.Adj p₁ (P[1]'(by omega)) := by
    rw [← hp0]
    exact PathBasics.path_adj_succ hP (show 1 < P.length by omega)
  have hP1P2adj : G.Adj (P[1]'(by omega)) (P[2]'(by omega)) :=
    PathBasics.path_adj_succ hP (show 2 < P.length by omega)
  have hP2P3adj : G.Adj (P[2]'(by omega)) (P[3]'(by omega)) :=
    PathBasics.path_adj_succ hP (show 3 < P.length by omega)
  have hP3vadj : G.Adj (P[3]'(by omega)) v := by simpa [hr3] using hvr.symm
  have htrack : Workspace.Types.Tracks.SPGT.IsTrackList G
      [p₁, P[1]'(by omega), P[2]'(by omega), P[3]'(by omega), v] := by
    refine ⟨by simp, hTnd, ?_⟩
    intro t ht
    have ht4 : t < 4 := by
      exact Nat.lt_of_succ_lt_succ (by simpa [Nat.succ_eq_add_one] using ht)
    have ht3 : t ≤ 3 := by omega
    interval_cases t
    · simpa using hp1P1adj
    · simpa using hP1P2adj
    · simpa using hP2P3adj
    · simpa using hP3vadj
  have hTout : ∀ w ∈ [p₁, P[1]'(by omega), P[2]'(by omega), P[3]'(by omega), v],
      w ∉ X ∪ Y := by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | hw | hw | hw | hw
    · subst w
      exact houtU p₁ (PathBasics.head_mem hhead)
    · subst w
      exact houtU _ (List.getElem_mem (show 1 < P.length by omega))
    · subst w
      exact houtU _ (List.getElem_mem (show 2 < P.length by omega))
    · subst w
      exact houtU _ (List.getElem_mem (show 3 < P.length by omega))
    · subst w
      exact hvXY
  have hP1notX : ¬ VertexComplete G (P[1]'(by omega)) X := by
    intro hX
    rcases (hXuniq _ (List.getElem_mem (show 1 < P.length by omega))).mp hX with hp | hn
    · exact hp1P1 hp.symm
    · rw [← hpn] at hn
      have := hnd.getElem_inj_iff.mp hn
      omega
  have hP2notX : ¬ VertexComplete G (P[2]'(by omega)) X := by
    intro hX
    rcases (hXuniq _ (List.getElem_mem (show 2 < P.length by omega))).mp hX with hp | hn
    · exact hp1P2 hp.symm
    · rw [← hpn] at hn
      have := hnd.getElem_inj_iff.mp hn
      omega
  have hP3notX : ¬ VertexComplete G (P[3]'(by omega)) X := by
    intro hX
    rcases (hXuniq _ (List.getElem_mem (show 3 < P.length by omega))).mp hX with hp | hn
    · exact hp1P3 hp.symm
    · rw [← hpn] at hn
      have := hnd.getElem_inj_iff.mp hn
      omega
  have hp1P2non : ¬ G.Adj p₁ (P[2]'(by omega)) := by
    rw [← hp0]
    exact PathBasics.path_not_adj_of_gap hP h0lt (by omega) (by omega) (by omega)
  have hp1P3non : ¬ G.Adj p₁ (P[3]'(by omega)) := by
    rw [← hp0]
    exact PathBasics.path_not_adj_of_gap hP h0lt (by omega) (by omega) (by omega)
  have hP1P3non : ¬ G.Adj (P[1]'(by omega)) (P[3]'(by omega)) :=
    PathBasics.path_not_adj_of_gap hP (by omega) (by omega) (by omega) (by omega)
  have hP2vnon : ¬ G.Adj (P[2]'(by omega)) v := by
    intro hadj
    exact hvi (by simpa [hi2] using hadj.symm)
  have hP2Y : VertexComplete G (P[2]'(by omega)) Y := by simpa [hi2] using hYi
  have hP3Y : VertexComplete G (P[3]'(by omega)) Y := by simpa [hr3] using hPrY
  have h181 := Scratch181.thm181_local G hG X Y hXY hXne hYne hXanti hYanti hcompl
    p₁ (P[1]'(by omega)) (P[2]'(by omega)) (P[3]'(by omega)) v
    htrack hTout
    ⟨hp1P2non, hp1P3non, (fun hadj => hv0 hadj.symm), hP1P3non, hP2vnon⟩
    ⟨hp1X, hvX⟩ ⟨hP1notX, hP2notX, hP3notX⟩ hp₁Y hP2Y hP3Y
  rcases h181 with hP1Y' | hvY'
  · exact hP1Y (by omega) hP1Y'
  · exact hvY hvY'

private theorem nonx_adj_good (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y)
    (hvX : ¬ VertexComplete G v X) (hv0 : G.Adj v p₁) :
    VertexGood G X Y P p₁ pₙ v := by
  classical
  by_contra hbad
  obtain ⟨hP, hlen7, hevenP, houtU, hXuniq, hp₁Y, hpₙY, hP1Y, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩ := hopt.1.1
  have hBerge : Berge G := hG.1.1.1.1
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ :=
    PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1nePn : p₁ ≠ pₙ := by
    rw [← hp0, ← hpn]
    exact PathBasics.path_ne_of_ne_index hP h0lt hnlt (by omega)
  have hnd : P.Nodup := PathBasics.path_nodup hP
  obtain ⟨i, j, hi, hj, h1i, hij, hYiEx, hYjEx, hminmax0⟩ :=
    Thm185Helpers.exists_minmax_index P.length 1
      (fun t => ∃ ht : t < P.length, VertexComplete G (P[t]'ht) Y)
      (by obtain ⟨t, ht, ht1, htY⟩ := hYex; exact ⟨t, ht, ht1, ht, htY⟩)
  have hYi : VertexComplete G (P[i]'hi) Y := by simpa only using hYiEx.choose_spec
  have hYj : VertexComplete G (P[j]'hj) Y := by simpa only using hYjEx.choose_spec
  have hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j := by
    intro t ht ht1 htY
    exact hminmax0 t ht ht1 ⟨ht, htY⟩
  rcases claim2_path G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY
      i j hi hj h1i hij hYi hYj hminmax with hdone | ⟨Q, q, hQ, hQY, hQsub⟩
  · exact hbad hdone
  have hqQ : q ∈ Q := PathBasics.getLast_mem hQ.2.2
  have hqY : VertexComplete G q Y := (hQY q hqQ).mpr rfl
  have hvq : v ≠ q := by
    intro he
    exact hvY (he ▸ hqY)
  have hQlen1 : 1 ≤ pathLength Q := by
    rw [PathBasics.pathLength_eq]
    have hQpos := PathBasics.path_length_pos hQ.1
    by_contra hc
    have hlen : Q.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
    rw [hx] at hQ
    exact hvq (by simpa using hQ.2.1.symm.trans hQ.2.2)
  have hQ1lt : 1 < Q.length := by rw [PathBasics.pathLength_eq] at hQlen1; omega
  have hQ0 : Q[0]'(by omega) = v :=
    PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hQ1mem : Q[1]'hQ1lt ∈ Q := List.getElem_mem hQ1lt
  have hQ1ne : Q[1]'hQ1lt ≠ v := by
    intro he
    have := (PathBasics.path_nodup hQ.1).getElem_inj_iff.mp (he.trans hQ0.symm)
    omega
  obtain ⟨tQ, htQ, hitQ, htQj, hQ1eq⟩ := hQsub _ hQ1mem hQ1ne
  have hvQ1 : G.Adj v (Q[1]'hQ1lt) := by
    rw [← hQ0]
    exact PathBasics.path_adj_succ hQ.1 hQ1lt
  have hvtQ : G.Adj v (P[tQ]'htQ) := by rw [hQ1eq]; exact hvQ1
  have hexNbr : ∃ t, t < P.length ∧ 0 ≤ t ∧
      (∃ ht : t < P.length, G.Adj v (P[t]'ht)) :=
    ⟨0, h0lt, Nat.zero_le _, h0lt, by simpa [hp0] using hv0⟩
  obtain ⟨h, k, hh, hk, -, hhk, hvhEx, hvkEx, hext⟩ :=
    Thm185Helpers.exists_minmax_index P.length 0
      (fun t => ∃ ht : t < P.length, G.Adj v (P[t]'ht)) hexNbr
  have hvh : G.Adj v (P[h]'hh) := by simpa only using hvhEx.choose_spec
  have hvk : G.Adj v (P[k]'hk) := by simpa only using hvkEx.choose_spec
  have hh0 : h = 0 := by
    have hle := (hext 0 h0lt (Nat.zero_le _) ⟨h0lt, by simpa [hp0] using hv0⟩).1
    omega
  have htk : tQ ≤ k := (hext tQ htQ (Nat.zero_le _) ⟨htQ, hvtQ⟩).2
  have hik : i < k := by omega
  obtain ⟨x0, hx0X, hvx0⟩ : ∃ x ∈ X, ¬ G.Adj v x := by
    by_contra hc
    push_neg at hc
    exact hvX hc
  obtain ⟨y0, hy0Y, hvy0⟩ : ∃ y ∈ Y, ¬ G.Adj v y := by
    by_contra hc
    push_neg at hc
    exact hvY hc
  let Yv : Set V := Y ∪ {v}
  have hvNotX : v ∉ X := fun hx => hvXY (Or.inl hx)
  have hvNotY : v ∉ Y := fun hy => hvXY (Or.inr hy)
  have hYvanti : AnticonnectedSet G Yv := by
    dsimp [Yv]
    exact ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hYanti
      ⟨y0, hy0Y, ⟨(fun he => hvNotY (he ▸ hy0Y)), hvy0⟩⟩
  have hXYvanti : AnticonnectedSet G (X ∪ Yv) := by
    apply ConnectedSetUnionAttach.connectedSet_union (G := Gᶜ) hXanti hYvanti
    right
    refine ⟨x0, hx0X, v, Or.inr rfl, ?_⟩
    rw [SimpleGraph.compl_adj]
    exact ⟨fun he => hvNotX (he ▸ hx0X), fun hadj => hvx0 hadj.symm⟩
  have hp₁X : VertexComplete G p₁ X :=
    (hXuniq p₁ (PathBasics.head_mem hhead)).mpr (Or.inl rfl)
  have hpₙX : VertexComplete G pₙ X :=
    (hXuniq pₙ (PathBasics.getLast_mem hlast)).mpr (Or.inr rfl)
  have hp₁Yv : VertexComplete G p₁ Yv := by
    intro z hz
    rcases hz with hzY | hzv
    · exact hp₁Y z hzY
    · rw [Set.mem_singleton_iff] at hzv
      subst z
      exact hv0.symm
  have hPoutYv : ∀ z ∈ P, z ∉ Yv := by
    intro z hz hzyv
    rcases hzyv with hzY | hzv
    · exact houtU z hz (Or.inr hzY)
    · rw [Set.mem_singleton_iff] at hzv
      exact hvP (hzv ▸ hz)
  have hPoutX : ∀ z ∈ P, z ∉ X := by
    intro z hz hzX
    exact houtU z hz (Or.inl hzX)
  have hclaim5 : ¬ VertexComplete G (P[P.length - 2]'(by omega)) Yv := by
    intro hn1Yv
    let D : List V := P.take (P.length - 1)
    have hDfrom : IsPathFrom G D p₁ (P[P.length - 2]'(by omega)) := by
      have hs := PathBasics.isPathFrom_slice hP (show 0 < P.length - 2 by omega)
        (show P.length - 2 < P.length by omega)
      rw [hp0] at hs
      have htake : P.length - 2 + 1 = P.length - 1 := by omega
      simpa [D, htake] using hs
    have hDlen : pathLength D = P.length - 2 := by
      rw [PathBasics.pathLength_eq]
      simp [D]
      omega
    have hDodd : Odd (pathLength D) := by
      rw [hDlen, Nat.odd_iff]
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      omega
    have hDout : ∀ z ∈ D, z ∉ Yv := by
      intro z hz
      exact hPoutYv z (List.mem_of_mem_take hz)
    have h136 := _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 D p₁
      (P[P.length - 2]'(by omega)) hDfrom hDodd Yv
      (fun y hy hyD => hDout y hyD hy) hYvanti hp₁Yv hn1Yv
    have hedge : ∃ u ∈ D, ∃ w ∈ D, EdgeComplete G Yv u w := by
      rcases h136 with hedge | ⟨hlen3, -⟩
      · exact hedge
      · rw [hDlen] at hlen3
        omega
    obtain ⟨u, huD, w, hwD, huw, huYv, hwYv⟩ := hedge
    have huP : u ∈ P := List.mem_of_mem_take huD
    have hwP : w ∈ P := List.mem_of_mem_take hwD
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem huP
    obtain ⟨b, hb, rfl⟩ := List.getElem_of_mem hwP
    have haBound : a < P.length - 1 := by
      obtain ⟨a', ha', he⟩ := List.getElem_of_mem huD
      have ha'Bound : a' < P.length - 1 := by simpa [D] using ha'
      have he' : P[a]'ha = P[a']'(by omega) := by
        rw [← he]
        simp only [D, List.getElem_take]
      have haa : a = a' := hnd.getElem_inj_iff.mp he'
      omega
    have hbBound : b < P.length - 1 := by
      obtain ⟨b', hb', he⟩ := List.getElem_of_mem hwD
      have hb'Bound : b' < P.length - 1 := by simpa [D] using hb'
      have he' : P[b]'hb = P[b']'(by omega) := by
        rw [← he]
        simp only [D, List.getElem_take]
      have hbb : b = b' := hnd.getElem_inj_iff.mp he'
      omega
    have habAdj := (PathBasics.path_adj_iff hP ha hb).mp huw
    have ha0 : a ≠ 0 := by
      intro hae
      subst a
      have hb1 : b = 1 := by omega
      subst b
      exact hP1Y hb (fun y hy => hwYv y (Or.inl hy))
    have hb0 : b ≠ 0 := by
      intro hbe
      subst b
      have ha1 : a = 1 := by omega
      subst a
      exact hP1Y ha (fun y hy => huYv y (Or.inl hy))
    have hexBefore : ∃ t, t < P.length - 2 ∧ 1 ≤ t ∧
        (∃ ht : t < P.length, VertexComplete G (P[t]'ht) Yv) := by
      by_cases haLast : a = P.length - 2
      · refine ⟨b, by omega, by omega, hb, hwYv⟩
      · refine ⟨a, by omega, by omega, ha, huYv⟩
    obtain ⟨l, jp, hl, hjpSmall, hl1, hljp, hlYvEx, hjpYvEx, hYvext⟩ :=
      Thm185Helpers.exists_minmax_index (P.length - 2) 1
        (fun t => ∃ ht : t < P.length, VertexComplete G (P[t]'ht) Yv) hexBefore
    have hjp : jp < P.length := by omega
    have hjpYv : VertexComplete G (P[jp]'hjp) Yv := by
      simpa only using hjpYvEx.choose_spec
    have hjp2 : 2 ≤ jp := by
      by_contra hc
      have hjp1 : jp = 1 := by omega
      subst jp
      exact hP1Y hjp (fun y hy => hjpYv y (Or.inl hy))
    have hjLast : j = P.length - 2 := by
      have hn1Y : VertexComplete G (P[P.length - 2]'(by omega)) Y := fun y hy => hn1Yv y (Or.inl hy)
      have hle := (hminmax (P.length - 2) (by omega) (by omega) hn1Y).2
      have hjNotLast : j < P.length - 1 := by
        by_contra hc
        have heq : j = P.length - 1 := by omega
        apply hpₙY
        rw [← hpn]
        simpa [heq] using hYj
      omega
    let T : List V := (P.drop jp).take ((P.length - 1) - jp + 1)
    have hTfrom : IsPathFrom G T (P[jp]'hjp) pₙ := by
      have hs := PathBasics.isPathFrom_slice hP (show jp < P.length - 1 by omega) hnlt
      rw [hpn] at hs
      simpa [T] using hs
    have hTlen : pathLength T = (P.length - 1) - jp := by
      rw [PathBasics.pathLength_eq]
      dsimp [T]
      rw [PathBasics.length_slice P (by omega) hnlt]
      omega
    have hTlong : 1 < pathLength T := by rw [hTlen]; omega
    have hToutYv : ∀ z ∈ T, z ∉ Yv := by
      intro z hz
      exact hPoutYv z (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hToutX : ∀ z ∈ T, z ∉ X := by
      intro z hz
      exact hPoutX z (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hTXuniq : ∀ z ∈ T, VertexComplete G z X ↔ z = pₙ := by
      intro z hz
      have hzP := List.drop_subset jp P (List.take_subset _ (P.drop jp) hz)
      constructor
      · intro hzX
        rcases (hXuniq z hzP).mp hzX with hz1 | hzn
        · obtain ⟨t, ht, hjpt, -, heq⟩ :=
            (PathBasics.mem_slice_iff P (show jp ≤ P.length - 1 by omega) hnlt).mp hz
          rw [← hp0] at hz1
          have := hnd.getElem_inj_iff.mp (heq.trans hz1)
          omega
        · exact hzn
      · rintro rfl
        exact hpₙX
    have hp1notT : p₁ ∉ T := by
      intro hz
      obtain ⟨t, ht, hjpt, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (show jp ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0] at heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    have hp1outXYv : p₁ ∉ Yv ∪ X := by
      rintro (hyv | hx)
      · exact hPoutYv p₁ (PathBasics.head_mem hhead) hyv
      · exact hPoutX p₁ (PathBasics.head_mem hhead) hx
    have hp1comp : VertexComplete G p₁ (Yv ∪ X) := by
      intro z hz
      rcases hz with hzYv | hzX
      · exact hp₁Yv z hzYv
      · exact hp₁X z hzX
    have hp1antiT : VertexAnticomplete G p₁ {z : V | z ∈ T} := by
      intro z hz
      obtain ⟨t, ht, hjpt, -, rfl⟩ :=
        (PathBasics.mem_slice_iff P (show jp ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    have hTlast1 : T.dropLast.getLast? =
        some (P[P.length - 2]'(by omega)) := by
      dsimp [T]
      rw [Workspace.ProofLemmas.Thm182DropLastIndex.dropLast_getLast?_eq _ (by
        simp only [List.length_take, List.length_drop]
        omega)]
      congr 1
      simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop]
      congr 1 <;> omega
    have hpₙNotYv : ¬ VertexComplete G pₙ Yv := by
      intro hpₙYv
      exact hpₙY (fun y hy => hpₙYv y (Or.inl hy))
    have hx0OutYv : x0 ∉ Yv := by
      rintro (hx0Y | hx0v)
      · exact Set.disjoint_left.mp hXY hx0X hx0Y
      · rw [Set.mem_singleton_iff] at hx0v
        exact hvNotX (hx0v ▸ hx0X)
    obtain ⟨yn, hynY, hpₙyn⟩ : ∃ y ∈ Y, ¬ G.Adj pₙ y := by
      by_contra hc
      push_neg at hc
      exact hpₙY hc
    have hpₙMissYv : ∃ y ∈ Yv, ¬ G.Adj pₙ y :=
      ⟨yn, Or.inl hynY, hpₙyn⟩
    have hx0MissYv : ∃ y ∈ Yv, ¬ G.Adj x0 y :=
      ⟨v, Or.inr rfl, fun h => hvx0 h.symm⟩
    have hnot :=
      Workspace.ProofLemmas.Thm185TripleRRReduction.penultimate_not_complete
        G hG T (P[jp]'hjp) (P[P.length - 2]'(by omega)) pₙ hTfrom.1 hTlong
        hTfrom.2.1 hTfrom.2.2 hTlast1 Yv X hToutYv hToutX hYvanti hXanti
        (by simpa [Set.union_comm] using hXYvanti) hjpYv hTXuniq
        p₁ hp1outXYv hp1notT hp1comp hp1antiT hpₙNotYv x0 hx0X hx0OutYv
        hpₙMissYv hx0MissYv (hpₙX x0 hx0X)
    exact hnot hn1Yv
  have hjOdd : Odd j := by
    have hlineOdd : Odd (P.length - 1 - j) := by
      by_cases hfar : j + 2 ≤ P.length - 1
      · exact Workspace.ProofLemmas.Thm183LineOddCase.line_odd_of_last_end_not_YComplete
          G hG.1.1 X Y hXY hXne hYne hXanti hYanti hcompl P p₁ pₙ hP houtU
          (by omega : 5 ≤ P.length) hhead hlast hXuniq j (by omega) hfar
          (by
            intro t ht hjt htlast htY
            have := (hminmax t ht (by omega) htY).2
            omega)
          hYj hpₙY ⟨0, h0lt, by omega, by simpa [hp0] using hp₁Y⟩
      · have hjNear : j = P.length - 2 := by
          have hjNotLast : j < P.length - 1 := by
            by_contra hc
            have heq : j = P.length - 1 := by omega
            apply hpₙY
            rw [← hpn]
            simpa [heq] using hYj
          omega
        rw [hjNear]
        exact ⟨0, by omega⟩
    rw [Nat.odd_iff] at hlineOdd ⊢
    rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
    omega
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  have hIdx3 : 3 ≤ (Thm183EdgeCount.YEdgeIdx G Y P).ncard := by
    rw [← Thm183EdgeCount.yEdges_ncard_eq_index_ncard hP]
    exact h184.1.2
  obtain ⟨a, ha, ha2, haOdd, haNe, haY⟩ : ∃ (a : ℕ) (ha : a < P.length),
      2 ≤ a ∧ Odd a ∧ a ≠ P.length - 2 ∧ VertexComplete G (P[a]'ha) Y := by
    by_contra hnone
    push_neg at hnone
    have hsub : Thm183EdgeCount.YEdgeIdx G Y P ⊆
        ({P.length - 3, P.length - 2} : Set ℕ) := by
      intro t ht
      obtain ⟨ht1, htY, ht1Y⟩ := ht
      rcases Nat.even_or_odd t with htEven | htOdd
      · have htpos : 0 < t := by
          by_contra hc
          have ht0 : t = 0 := by omega
          subst t
          exact hP1Y ht1 ht1Y
        have ht1Odd : Odd (t + 1) := by
          rw [Nat.even_iff] at htEven
          rw [Nat.odd_iff]
          omega
        have heq : t + 1 = P.length - 2 := by
          by_contra hne
          exact hnone (t + 1) ht1 (by omega) ht1Odd hne ht1Y
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        exact Or.inl (by omega)
      · have ht2 : 2 ≤ t := by
          by_contra hc
          have ht1eq : t = 1 := by
            rw [Nat.odd_iff] at htOdd
            omega
          subst t
          exact hP1Y (by omega) htY
        have heq : t = P.length - 2 := by
          by_contra hne
          exact hnone t (by omega) ht2 htOdd hne htY
        simp [heq]
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have hpair : ({P.length - 3, P.length - 2} : Set ℕ).ncard ≤ 2 := by
      calc
        ({P.length - 3, P.length - 2} : Set ℕ).ncard ≤
            ({P.length - 2} : Set ℕ).ncard + 1 := Set.ncard_insert_le _ _
        _ = 2 := by simp
    omega
  have hjlast : j < P.length - 1 := by
    by_contra hc
    have hjEq : j = P.length - 1 := by omega
    apply hpₙY
    rw [← hpn]
    simpa only [depIndex P hjEq hj hnlt] using hYj
  have hclaim6 : ¬ G.Adj v pₙ := by
    intro hvpn
    have haj : a ≤ j := (hminmax a ha (by omega) haY).2
    have hjaEven : Even (j - a) := by
      rw [Nat.even_iff]
      rw [Nat.odd_iff] at haOdd hjOdd
      omega
    let R : List V := (P.drop a).take (j - a + 1)
    have hRfrom : IsPathFrom G R (P[a]'ha) (P[j]'hj) := by
      simpa [R] using isPathFrom_slice_le hP haj hj
    have hRinf : R <:+: P := Thm185Helpers.slice_infix P a (j - a + 1)
    have hRlen : pathLength R = j - a := by
      rw [PathBasics.pathLength_eq]
      dsimp [R]
      rw [PathBasics.length_slice P haj hj]
      omega
    have hRedgeEven : Even {e : Sym2 V | ∃ u ∈ R, ∃ w ∈ R,
        e = s(u, w) ∧ EdgeComplete G Y u w}.ncard := by
      have h23 := (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y hYanti P
        (Or.inl hP) (fun z hz hzy => houtU z hz (Or.inr hzy))).1 R
        (P[a]'ha) (P[j]'hj) (Or.inl ⟨hP, hRinf⟩) hRfrom haY hYj
      rcases h23 with hpar | hOnly
      · rw [Nat.even_iff]
        rw [Nat.even_iff] at hjaEven
        calc
          {e : Sym2 V | ∃ u ∈ R, ∃ w ∈ R,
              e = s(u, w) ∧ EdgeComplete G Y u w}.ncard % 2 = pathLength R % 2 := hpar
          _ = (j - a) % 2 := by rw [hRlen]
          _ = 0 := hjaEven
      · exfalso
        have hp0Only := hOnly p₁ (PathBasics.head_mem hhead) hp₁Y
        rcases hp0Only with he | he
        · rw [← hp0] at he
          have := hnd.getElem_inj_iff.mp he
          omega
        · rw [← hp0] at he
          have := hnd.getElem_inj_iff.mp he
          omega
    let T : List V := (P.drop a).take ((P.length - 1) - a + 1)
    have hTfrom : IsPathFrom G T (P[a]'ha) pₙ := by
      have haLast : a < P.length - 1 := lt_of_le_of_lt haj hjlast
      have hs := PathBasics.isPathFrom_slice hP haLast hnlt
      rw [hpn] at hs
      simpa [T] using hs
    have hTlen : pathLength T = (P.length - 1) - a := by
      rw [PathBasics.pathLength_eq]
      dsimp [T]
      rw [PathBasics.length_slice P (by omega) hnlt]
      omega
    have hTodd : Odd (pathLength T) := by
      rw [hTlen, Nat.odd_iff]
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      rw [Nat.odd_iff] at haOdd
      omega
    have hTlong : 1 < pathLength T := by
      have haN3 : a ≤ P.length - 3 := by omega
      rw [hTlen]
      omega
    have hTedgeEq : {e : Sym2 V | ∃ u ∈ T, ∃ w ∈ T,
          e = s(u, w) ∧ EdgeComplete G Y u w} =
        {e : Sym2 V | ∃ u ∈ R, ∃ w ∈ R,
          e = s(u, w) ∧ EdgeComplete G Y u w} := by
      ext e
      constructor
      · rintro ⟨u, hu, w, hw, rfl, huw, huY, hwY⟩
        obtain ⟨tu, htu, hatu, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mp hu
        obtain ⟨tw, htw, hatw, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mp hw
        have htuj : tu ≤ j := (hminmax tu htu (by omega) huY).2
        have htwj : tw ≤ j := (hminmax tw htw (by omega) hwY).2
        exact ⟨_, (PathBasics.mem_slice_iff P haj hj).mpr ⟨tu, htu, hatu, htuj, rfl⟩,
          _, (PathBasics.mem_slice_iff P haj hj).mpr ⟨tw, htw, hatw, htwj, rfl⟩,
          rfl, huw, huY, hwY⟩
      · rintro ⟨u, hu, w, hw, rfl, huw, huY, hwY⟩
        obtain ⟨tu, htu, hatu, htuj, rfl⟩ := (PathBasics.mem_slice_iff P haj hj).mp hu
        obtain ⟨tw, htw, hatw, htwj, rfl⟩ := (PathBasics.mem_slice_iff P haj hj).mp hw
        exact ⟨_, (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mpr
            ⟨tu, htu, hatu, by omega, rfl⟩,
          _, (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mpr
            ⟨tw, htw, hatw, by omega, rfl⟩, rfl, huw, huY, hwY⟩
    have hXvanti : AnticonnectedSet G (X ∪ {v}) :=
      ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hXanti
        ⟨x0, hx0X, ⟨(fun he => hvNotX (he ▸ hx0X)), hvx0⟩⟩
    have hToutY : ∀ z ∈ T, z ∉ Y := by
      intro z hz hzY
      exact houtU z (List.drop_subset _ _ (List.take_subset _ _ hz)) (Or.inr hzY)
    have hToutXv : ∀ z ∈ T, z ∉ X ∪ {v} := by
      intro z hz hzXv
      rcases hzXv with hzX | hzv
      · exact houtU z (List.drop_subset _ _ (List.take_subset _ _ hz)) (Or.inl hzX)
      · rw [Set.mem_singleton_iff] at hzv
        exact hvP (hzv ▸ List.drop_subset _ _ (List.take_subset _ _ hz))
    have hTXuniq : ∀ z ∈ T, VertexComplete G z X ↔ z = pₙ := by
      intro z hz
      have hzP := List.drop_subset a P (List.take_subset _ (P.drop a) hz)
      constructor
      · intro hzX
        rcases (hXuniq z hzP).mp hzX with hz1 | hzn
        · obtain ⟨t, ht, hat, -, heq⟩ :=
            (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mp hz
          rw [← hp0] at hz1
          have := hnd.getElem_inj_iff.mp (heq.trans hz1)
          omega
        · exact hzn
      · rintro rfl
        exact hpₙX
    have hTXvuniq : ∀ z ∈ T, VertexComplete G z (X ∪ {v}) ↔ z = pₙ := by
      intro z hz
      constructor
      · intro hzXv
        have hzX : VertexComplete G z X := fun x hx => hzXv x (Or.inl hx)
        exact (hTXuniq z hz).mp hzX
      · rintro rfl
        intro z hz
        rcases hz with hzX | hzv
        · exact hpₙX z hzX
        · rw [Set.mem_singleton_iff] at hzv
          subst z
          exact hvpn.symm
    have hp1notT : p₁ ∉ T := by
      intro hz
      obtain ⟨t, ht, hat, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0] at heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    have hp1outYXv : p₁ ∉ Y ∪ (X ∪ {v}) := by
      rintro (hy | hx | hv)
      · exact houtU p₁ (PathBasics.head_mem hhead) (Or.inr hy)
      · exact houtU p₁ (PathBasics.head_mem hhead) (Or.inl hx)
      · rw [Set.mem_singleton_iff] at hv
        exact hvP (hv ▸ PathBasics.head_mem hhead)
    have hp1compYXv : VertexComplete G p₁ (Y ∪ (X ∪ {v})) := by
      intro z hz
      rcases hz with hzY | hzX | hzv
      · exact hp₁Y z hzY
      · exact hp₁X z hzX
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        exact hv0.symm
    have hp1antiT : VertexAnticomplete G p₁ {z : V | z ∈ T} := by
      intro z hz
      obtain ⟨t, ht, hat, -, rfl⟩ :=
        (PathBasics.mem_slice_iff P (show a ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    have hTedgeEven : Even {e : Sym2 V | ∃ u ∈ T, ∃ w ∈ T,
        e = s(u, w) ∧ EdgeComplete G Y u w}.ncard := by
      rw [hTedgeEq]
      exact hRedgeEven
    exact Workspace.ProofLemmas.Thm185Claim6Bridge.even_complete_edges_absurd
      G hG Y X hXY.symm hYne hXne hYanti hXanti
      (fun y hy x hx => (hcompl x hx y hy).symm) v
      (by rintro (hy | hx); exact hvXY (Or.inr hy); exact hvXY (Or.inl hx))
      hvY hvX hXvanti
      (by simpa [Yv, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hXYvanti)
      T (P[a]'ha) pₙ hTfrom.1 hTodd hTlong hTfrom.2.1 hTfrom.2.2 hToutY
      (fun z hz hzX => hToutXv z hz (Or.inl hzX))
      (fun hvT => hToutXv v hvT (Or.inr rfl)) haY hTXuniq hTXvuniq p₁
      hp1outYXv hp1notT hp1compYXv hp1antiT hTedgeEven
  have hclaim7 : ∀ (m : ℕ) (hm : m < P.length), G.Adj v (P[m]'hm) →
      ∀ S : List V, IsAntipathFrom G S v (P[m]'hm) →
        (∀ z ∈ SPGT.interior S, z ∈ Y) → Odd (pathLength S) → False := by
    intro m hm hvm SY hSY hSYint hSYodd
    have hmpos : 0 < m := by
      by_contra hc
      have hm0 : m = 0 := by omega
      have hpm0 : P[m]'hm = p₁ := (depIndex P hm0 hm h0lt).trans hp0
      have hSYne1 : pathLength SY ≠ 1 := by
        intro hlen1
        have hadjc := PathBasics.isPathFrom_ends_adj_of_length_one hSY hlen1
        rw [SimpleGraph.compl_adj] at hadjc
        exact hadjc.2 (by rw [hpm0]; exact hv0)
      have hSYlen3 : 3 ≤ pathLength SY := by
        obtain ⟨r, hr⟩ := hSYodd
        omega
      have hlen4 : 4 ≤ SY.length := by rw [PathBasics.pathLength_eq] at hSYlen3; omega
      have hpen : SY[SY.length - 2]'(by omega) ∈ SPGT.interior SY :=
        PathBasics.getElem_mem_interior hSY.1 (by omega) (by omega) (by omega)
      have hpenY := hSYint _ hpen
      have hadjc : Gᶜ.Adj (SY[SY.length - 2]'(by omega))
          (SY[SY.length - 1]'(by omega)) :=
        by
          have hadj := PathBasics.path_adj_succ hSY.1 (i := SY.length - 2) (by omega)
          have heq : SY[SY.length - 2 + 1]'(by omega) =
              SY[SY.length - 1]'(by omega) := depIndex SY (by omega) (by omega) (by omega)
          rwa [heq] at hadj
      have hlastSY : SY[SY.length - 1]'(by omega) = p₁ := by
        have he := PathBasics.getElem_last_of_getLast? hSY.2.2 (by omega)
        simpa [hpm0] using he
      rw [hlastSY, SimpleGraph.compl_adj] at hadjc
      exact hadjc.2 (hp₁Y _ hpenY).symm
    have hmlast : m < P.length - 1 := by
      by_contra hc
      have hmeq : m = P.length - 1 := by omega
      apply hclaim6
      rw [← hpn]
      simpa [hmeq] using hvm
    have hpmNotX : P[m]'hm ∉ X := hPoutX _ (List.getElem_mem hm)
    have hpmNotY : P[m]'hm ∉ Y := fun hy => houtU _ (List.getElem_mem hm) (Or.inr hy)
    have hpmX : ¬ VertexComplete G (P[m]'hm) X := by
      intro hc
      rcases (hXuniq _ (List.getElem_mem hm)).mp hc with he | he
      · rw [← hp0] at he
        have := hnd.getElem_inj_iff.mp he
        omega
      · rw [← hpn] at he
        have := hnd.getElem_inj_iff.mp he
        omega
    have miss_of_not_complete : ∀ {z : V} {A : Set V},
        ¬ VertexComplete G z A → ∃ x ∈ A, ¬ G.Adj z x := by
      intro z A hn
      by_contra hc
      push_neg at hc
      exact hn hc
    obtain ⟨SX, hSX, hSXint⟩ :=
      InducedPathExtraction.exists_antipath_interior_in hXanti hvNotX hpmNotX
        (miss_of_not_complete hvX) (miss_of_not_complete hpmX)
    have hpar := AntiholeCompletion.even_add_pathLength_of_two_antipaths
      hBerge hXY hcompl hvm hvNotX hpmNotX hvNotY hpmNotY
      hSY hSYint hSX hSXint
    have hSXodd : Odd (pathLength SX) := by
      rw [Nat.even_iff] at hpar
      rw [Nat.odd_iff] at hSYodd ⊢
      omega
    have hmNear : m = P.length - 2 := by
      by_contra hne
      have hmGap : m + 2 ≤ P.length - 1 := by omega
      have hpnm : ¬ G.Adj pₙ (P[m]'hm) := by
        rw [← hpn]
        exact PathBasics.path_not_adj_of_gap hP hnlt hm (by omega) (by omega)
      have hpnv : ¬ G.Adj pₙ v := fun hadj => hclaim6 hadj.symm
      have hpnnv : pₙ ≠ v := by
        intro he
        exact hvP (by rw [← he]; exact PathBasics.getLast_mem hlast)
      have hpnmne : pₙ ≠ P[m]'hm := by
        rw [← hpn]
        exact PathBasics.path_ne_of_ne_index hP hnlt hm (by omega)
      have hSXeven := AntiholeCompletion.even_pathLength_of_witness hBerge hvm hpₙX
        hpnv hpnm hpnnv hpnmne hSX hSXint
      exact (Nat.not_even_iff_odd.mpr hSXodd) hSXeven
    have hmOdd : Odd m := by
      rw [hmNear, Nat.odd_iff]
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      omega
    have hcoverY : ∀ z : V, VertexComplete G z Y →
        G.Adj z v ∨ G.Adj z (P[m]'hm) := by
      intro z hzY
      by_cases hzv : z = v
      · subst z
        exact Or.inr hvm
      by_cases hzm : z = P[m]'hm
      · subst z
        exact Or.inl hvm.symm
      by_contra hnone
      push_neg at hnone
      have heven := AntiholeCompletion.even_pathLength_of_witness hBerge hvm hzY
        hnone.1 hnone.2 hzv hzm hSY hSYint
      exact (Nat.not_even_iff_odd.mpr hSYodd) heven
    have hvj : G.Adj v (P[j]'hj) := by
      rcases hcoverY _ hYj with hjv | hjm
      · exact hjv.symm
      · by_cases hjmEq : j = m
        · simpa [hjmEq] using hvm
        · have hidx := (PathBasics.path_adj_iff hP hj hm).mp hjm
          rw [Nat.odd_iff] at hjOdd hmOdd
          omega
    have hjNotN1 : j ≠ P.length - 2 := by
      intro he
      apply hclaim5
      intro z hz
      rcases hz with hzY | hzv
      · have := hYj z hzY
        simpa [he] using this
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        simpa [he] using hvj.symm
    have hjGap : j + 3 ≤ P.length - 1 := by
      have hjLast : j < P.length - 1 := by
        by_contra hc
        have he : j = P.length - 1 := by omega
        apply hpₙY
        rw [← hpn]
        simpa [he] using hYj
      rw [Nat.odd_iff] at hjOdd
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      omega
    let U : List V := (P.drop j).take ((P.length - 1) - j + 1)
    let RY : List V := U.reverse
    have hUfrom : IsPathFrom G U (P[j]'hj) pₙ := by
      have hs := PathBasics.isPathFrom_slice hP (show j < P.length - 1 by omega) hnlt
      rw [hpn] at hs
      simpa [U] using hs
    have hRYfrom : IsPathFrom G RY pₙ (P[j]'hj) := by
      simpa [RY] using PathBasics.isPathFrom_reverse hUfrom
    have hRYlen : pathLength RY = (P.length - 1) - j := by
      rw [show RY = U.reverse by rfl, PathBasics.pathLength_reverse,
        PathBasics.pathLength_eq]
      dsimp [U]
      rw [PathBasics.length_slice P (by omega) hnlt]
      omega
    have hRYodd : Odd (pathLength RY) := by
      rw [hRYlen, Nat.odd_iff]
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      rw [Nat.odd_iff] at hjOdd
      omega
    have hRYlong : 1 < pathLength RY := by rw [hRYlen]; omega
    have hRYoutX : ∀ z ∈ RY, z ∉ X := by
      intro z hz
      exact hPoutX z (List.drop_subset _ _ (List.take_subset _ _ (List.mem_reverse.mp hz)))
    have hRYoutYv : ∀ z ∈ RY, z ∉ Yv := by
      intro z hz
      exact hPoutYv z (List.drop_subset _ _ (List.take_subset _ _ (List.mem_reverse.mp hz)))
    have hRYXfirst : ∀ z ∈ RY, VertexComplete G z X ↔ z = pₙ := by
      intro z hz
      have hzU := List.mem_reverse.mp hz
      have hzP := List.drop_subset j P (List.take_subset _ (P.drop j) hzU)
      constructor
      · intro hzX
        rcases (hXuniq z hzP).mp hzX with hz1 | hzn
        · obtain ⟨t, ht, hjt, -, heq⟩ :=
            (PathBasics.mem_slice_iff P (show j ≤ P.length - 1 by omega) hnlt).mp hzU
          rw [← hp0] at hz1
          have := hnd.getElem_inj_iff.mp (heq.trans hz1)
          omega
        · exact hzn
      · rintro rfl
        exact hpₙX
    have hRYYvlast : ∀ z ∈ RY, VertexComplete G z Yv ↔ z = P[j]'hj := by
      intro z hz
      have hzU := List.mem_reverse.mp hz
      constructor
      · intro hzYv
        obtain ⟨t, ht, hjt, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show j ≤ P.length - 1 by omega) hnlt).mp hzU
        have htY : VertexComplete G (P[t]'ht) Y := fun y hy => hzYv y (Or.inl hy)
        have htj := (hminmax t ht (by omega) htY).2
        have heq : t = j := by omega
        exact depIndex P heq ht hj
      · rintro rfl
        intro z hz
        rcases hz with hzY | hzv
        · exact hYj z hzY
        · rw [Set.mem_singleton_iff] at hzv
          subst z
          exact hvj.symm
    have hp1notRY : p₁ ∉ RY := by
      intro hz
      have hzU := List.mem_reverse.mp hz
      obtain ⟨t, ht, hjt, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (show j ≤ P.length - 1 by omega) hnlt).mp hzU
      rw [← hp0] at heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    have hp1outXYv : p₁ ∉ X ∪ Yv := by
      rintro (hx | hyv)
      · exact hPoutX p₁ (PathBasics.head_mem hhead) hx
      · exact hPoutYv p₁ (PathBasics.head_mem hhead) hyv
    have hp1compXYv : VertexComplete G p₁ (X ∪ Yv) := by
      intro z hz
      rcases hz with hzX | hzYv
      · exact hp₁X z hzX
      · exact hp₁Yv z hzYv
    have hp1antiRY : VertexAnticomplete G p₁ {z : V | z ∈ RY} := by
      intro z hz
      have hzU := List.mem_reverse.mp hz
      obtain ⟨t, ht, hjt, -, rfl⟩ :=
        (PathBasics.mem_slice_iff P (show j ≤ P.length - 1 by omega) hnlt).mp hzU
      rw [← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    have hUlong : 1 < pathLength U := by
      simpa [RY, PathBasics.pathLength_reverse] using hRYlong
    have hUoutYv : ∀ z ∈ U, z ∉ Yv := by
      intro z hz
      exact hPoutYv z (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hUoutX : ∀ z ∈ U, z ∉ X := by
      intro z hz
      exact hPoutX z (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hUXlast : ∀ z ∈ U, VertexComplete G z X ↔ z = pₙ := by
      intro z hz
      apply hRYXfirst z
      simpa [RY] using List.mem_reverse.mpr hz
    have hjYv : VertexComplete G (P[j]'hj) Yv := by
      intro z hz
      rcases hz with hzY | hzv
      · exact hYj z hzY
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        exact hvj.symm
    have hUlast1 : U.dropLast.getLast? =
        some (P[P.length - 2]'(by omega)) := by
      dsimp [U]
      rw [Workspace.ProofLemmas.Thm182DropLastIndex.dropLast_getLast?_eq _ (by
        simp only [List.length_take, List.length_drop]
        omega)]
      congr 1
      simp only [List.getElem_take, List.getElem_drop, List.length_take, List.length_drop]
      congr 1 <;> omega
    have hp1notU : p₁ ∉ U := by
      intro hz
      apply hp1notRY
      simpa [RY] using List.mem_reverse.mpr hz
    have hp1antiU : VertexAnticomplete G p₁ {z : V | z ∈ U} := by
      intro z hz
      apply hp1antiRY z
      simpa [RY] using List.mem_reverse.mpr hz
    have hpₙNotYv : ¬ VertexComplete G pₙ Yv := by
      intro hpₙYv
      exact hpₙY (fun y hy => hpₙYv y (Or.inl hy))
    have hnot :=
      Workspace.ProofLemmas.Thm185TripleRRReduction.penultimate_not_adj_of_two_edge_antipath
        G hG U (P[j]'hj) (P[P.length - 2]'(by omega)) pₙ hUfrom.1 hUlong
        hUfrom.2.1 hUfrom.2.2 hUlast1 Yv X hUoutYv hUoutX hYvanti hXanti
        (by simpa [Set.union_comm] using hXYvanti) hjYv hUXlast
        p₁ (by simpa [Set.union_comm] using hp1outXYv) hp1notU
        (by simpa [Set.union_comm] using hp1compXYv) hp1antiU hpₙNotYv
        x0 v hx0X (Or.inr rfl) (fun h => hclaim6 h.symm) hvx0 (hpₙX x0 hx0X)
    apply hnot
    simpa [hmNear] using hvm.symm
  have hjk : j < k := by
    by_contra hc
    have hkj : k ≤ j := by omega
    have hkLast : k < P.length - 1 := by
      by_contra hklast
      have hkeq : k = P.length - 1 := by omega
      apply hclaim6
      rw [← hpn]
      simpa [hkeq] using hvk
    have hkN2 : k ≤ P.length - 3 := by
      by_contra hc2
      have hkeq : k = P.length - 2 := by omega
      have hjeq : j = P.length - 2 := by
        have hjLast : j < P.length - 1 := by
          by_contra hc3
          have hjEq : j = P.length - 1 := by omega
          apply hpₙY
          rw [← hpn]
          simpa [hjEq] using hYj
        omega
      apply hclaim5
      intro z hz
      rcases hz with hzY | hzv
      · simpa [hkeq, hjeq] using hYj z hzY
      · rw [Set.mem_singleton_iff] at hzv
        subst z
        simpa [hkeq] using hvk.symm
    let Suf : List V := (P.drop k).take ((P.length - 1) - k + 1)
    have hSufFrom : IsPathFrom G Suf (P[k]'hk) pₙ := by
      have hs := PathBasics.isPathFrom_slice hP (show k < P.length - 1 by omega) hnlt
      rw [hpn] at hs
      simpa [Suf] using hs
    have hvSuf : v ∉ Suf := by
      intro hz
      exact hvP (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hvSufOther : ∀ z ∈ Suf, z ≠ P[k]'hk → ¬ G.Adj v z := by
      intro z hz hzne hadj
      obtain ⟨t, ht, hkt, -, rfl⟩ :=
        (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
      have htk := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).2
      have hteq : t = k := by omega
      exact hzne (depIndex P hteq ht hk)
    have hvSufFrom : IsPathFrom G (v :: Suf) v pₙ :=
      PathAttach.isPathFrom_cons hSufFrom hvk hvSuf hvSufOther
    have hp1neV : p₁ ≠ v := by
      intro he
      exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
    have hp1notSuf : p₁ ∉ Suf := by
      intro hz
      obtain ⟨t, ht, hkt, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0] at heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    have hp1Other : ∀ z ∈ v :: Suf, z ≠ v → ¬ G.Adj p₁ z := by
      intro z hz hzv
      rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd rfl hzv
      · obtain ⟨t, ht, hkt, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
        rw [← hp0]
        exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    let B : List V := p₁ :: v :: Suf
    have hBfrom : IsPathFrom G B p₁ pₙ := by
      simpa [B] using PathAttach.isPathFrom_cons hvSufFrom hv0.symm
        (by simp [hp1neV, hp1notSuf]) hp1Other
    have hBlen : B.length = P.length - k + 2 := by
      simp [B, Suf]
      omega
    have hB5 : 5 ≤ B.length := by rw [hBlen]; omega
    have hBmem : ∀ z : V, z ∈ B ↔ z = p₁ ∨ z = v ∨ z ∈ Suf := by
      intro z
      simp [B]
    have hBout : ∀ z ∈ B, z ∉ X ∧ z ∉ Y := by
      intro z hz
      rcases (hBmem z).mp hz with hz1 | hzv | hzS
      · rw [hz1]
        exact ⟨hPoutX p₁ (PathBasics.head_mem hhead),
          fun hy => houtU p₁ (PathBasics.head_mem hhead) (Or.inr hy)⟩
      · rw [hzv]
        exact ⟨hvNotX, hvNotY⟩
      · have hzP := List.drop_subset k P (List.take_subset _ (P.drop k) hzS)
        exact ⟨hPoutX z hzP, fun hy => houtU z hzP (Or.inr hy)⟩
    have hBX : ∀ z ∈ B, VertexComplete G z X ↔ (z = p₁ ∨ z = pₙ) := by
      intro z hz
      rcases (hBmem z).mp hz with hz1 | hzv | hzS
      · rw [hz1]
        simp [hp₁X, hp1nePn]
      · rw [hzv]
        constructor
        · exact fun hc => absurd hc hvX
        · rintro (he | he)
          · exact absurd he.symm hp1neV
          · exact absurd (by rw [he]; exact PathBasics.getLast_mem hlast) hvP
      · have hzP := List.drop_subset k P (List.take_subset _ (P.drop k) hzS)
        constructor
        · intro hzX
          rcases (hXuniq z hzP).mp hzX with hz1 | hzn
          · exfalso
            obtain ⟨t, ht, hkt, -, heq⟩ :=
              (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
            rw [← hp0] at hz1
            have := hnd.getElem_inj_iff.mp (heq.trans hz1)
            omega
          · exact Or.inr hzn
        · rintro (hz1 | hzn)
          · exfalso
            exact hp1notSuf (by simpa [hz1] using hzS)
          · exact (hXuniq z hzP).mpr (Or.inr hzn)
    have hBj : P[j]'hj ∈ B := by
      apply (hBmem _).mpr
      right; right
      exact (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mpr
        ⟨j, hj, hkj, by omega, rfl⟩
    have hB2 : B.tail.head? = some v := by simp [B]
    have hBpw : IsPseudowheel G X Y B :=
      PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl
        hBfrom hB2 hBout hB5 hBX hp₁Y ⟨P[j]'hj, hBj, (by
          intro he
          rw [← hp0] at he
          have := hnd.getElem_inj_iff.mp he
          omega), hYj⟩ hvY hpₙY
    have hsubY : {z : V | z ∈ B ∧ VertexComplete G z Y} ⊆
        {z : V | z ∈ P ∧ VertexComplete G z Y} := by
      rintro z ⟨hzB, hzY⟩
      refine ⟨?_, hzY⟩
      rcases (hBmem z).mp hzB with rfl | rfl | hzS
      · exact PathBasics.head_mem hhead
      · exact absurd hzY hvY
      · exact List.drop_subset k P (List.take_subset _ (P.drop k) hzS)
    have hiNotB : P[i]'hi ∉ B := by
      intro hzB
      rcases (hBmem _).mp hzB with he | he | hzS
      · rw [← hp0] at he
        have := hnd.getElem_inj_iff.mp he
        omega
      · exact hvP (by rw [← he]; exact List.getElem_mem hi)
      · obtain ⟨t, ht, hkt, -, he⟩ :=
          (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
        have := hnd.getElem_inj_iff.mp he
        omega
    exact hopt.2.1 ⟨X, Y, B, hBpw, Set.ncard_lt_ncard
      ((Set.ssubset_iff_of_subset hsubY).mpr
        ⟨P[i]'hi, ⟨List.getElem_mem hi, hYi⟩, fun hz => hiNotB hz.1⟩)
      (Set.toFinite _)⟩
  have hQodd : Odd (pathLength Q) := by
    by_contra hnotOdd
    have hQeven : Even (pathLength Q) := Nat.not_odd_iff_even.mp hnotOdd
    have hp1notQ : p₁ ∉ Q := by
      intro hz
      by_cases he : p₁ = v
      · exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
      · obtain ⟨t, ht, hit, -, heq⟩ := hQsub p₁ hz he
        rw [← hp0] at heq
        have := hnd.getElem_inj_iff.mp heq
        omega
    have hp1Qother : ∀ z ∈ Q, z ≠ v → ¬ G.Adj p₁ z := by
      intro z hz hzv
      obtain ⟨t, ht, hit, -, rfl⟩ := hQsub z hz hzv
      rw [← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    let A : List V := p₁ :: Q
    have hAfrom : IsPathFrom G A p₁ q := by
      simpa [A] using PathAttach.isPathFrom_cons hQ hv0.symm hp1notQ hp1Qother
    have hAlen : pathLength A = pathLength Q + 1 := by
      rw [PathBasics.pathLength_eq, PathBasics.pathLength_eq]
      simp [A]
      omega
    have hAodd : Odd (pathLength A) := by
      rw [hAlen, Nat.odd_iff]
      rw [Nat.even_iff] at hQeven
      omega
    have hAmem : ∀ z : V, z ∈ A ↔ z = p₁ ∨ z ∈ Q := by
      intro z
      simp [A]
    have hAY : ∀ z ∈ A, VertexComplete G z Y ↔ (z = p₁ ∨ z = q) := by
      intro z hz
      rcases (hAmem z).mp hz with hz1 | hzQ
      · rw [hz1]
        constructor
        · exact fun _ => Or.inl rfl
        · rintro (_ | he)
          · exact hp₁Y
          · exfalso
            exact hp1notQ (by simpa [← he] using hqQ)
      · constructor
        · intro hzY
          exact Or.inr ((hQY z hzQ).mp hzY)
        · rintro (he | he)
          · exfalso
            exact hp1notQ (by simpa [he] using hzQ)
          · exact (hQY z hzQ).mpr he
    have hAoutY : ∀ z ∈ A, z ∉ Y := by
      intro z hz hzY
      rcases (hAmem z).mp hz with hz1 | hzQ
      · rw [hz1] at hzY
        exact houtU p₁ (PathBasics.head_mem hhead) (Or.inr hzY)
      · by_cases hzv : z = v
        · exact hvNotY (hzv ▸ hzY)
        · obtain ⟨t, ht, -, -, rfl⟩ := hQsub z hzQ hzv
          exact houtU _ (List.getElem_mem ht) (Or.inr hzY)
    have hp1q : ¬ G.Adj p₁ q := by
      obtain ⟨t, ht, hit, -, heq⟩ := hQsub q hqQ hvq.symm
      rw [← heq, ← hp0]
      exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    have hAnoedge : ¬ ∃ u ∈ A, ∃ w ∈ A, EdgeComplete G Y u w := by
      rintro ⟨u, hu, w, hw, huw, huY, hwY⟩
      rcases (hAY u hu).mp huY with rfl | rfl <;>
        rcases (hAY w hw).mp hwY with rfl | rfl
      · exact G.irrefl huw
      · exact hp1q huw
      · exact hp1q huw.symm
      · exact G.irrefl huw
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 A p₁ q
        hAfrom hAodd Y (fun y hy hyA => hAoutY y hyA hy) hYanti hp₁Y hqY with hedge |
        ⟨hAthree, c, d, hInt, SY, hSY, hSYodd, hSYint⟩
    · exact hAnoedge hedge
    · have hQtwo : pathLength Q = 2 := by rw [hAlen] at hAthree; omega
      have hQlen3 : Q.length = 3 := by rw [PathBasics.pathLength_eq] at hQtwo; omega
      obtain ⟨q0, q1, q2, hQeq⟩ := PrismBasics.length_eq_three hQlen3
      have hq0 : q0 = v := by
        rw [hQeq] at hQ
        exact Option.some_injective _ hQ.2.1
      have hq2 : q2 = q := by
        rw [hQeq] at hQ
        simpa using Option.some_injective _ hQ.2.2
      have hq1 : q1 = Q[1]'hQ1lt := by simp [hQeq]
      have hAshape : A = [p₁, v, q1, q] := by
        change p₁ :: Q = [p₁, v, q1, q]
        rw [hQeq, hq0, hq2]
      have hcd : c = v ∧ d = Q[1]'hQ1lt := by
        rw [hAshape] at hInt
        change [v, q1] = [c, d] at hInt
        have hpair := List.cons.inj hInt
        have htail := List.cons.inj hpair.2
        exact ⟨hpair.1.symm, htail.1.symm.trans hq1⟩
      apply hclaim7 tQ htQ hvtQ
      · simpa [hcd.1, hcd.2, hQ1eq] using hSY
      · exact hSYint
      · exact hSYodd
  have hkEven : Even k := by
    apply Nat.not_odd_iff_even.mp
    intro hkOdd
    have hkLast : k < P.length - 1 := by
      by_contra hc
      have hkeq : k = P.length - 1 := by omega
      apply hclaim6
      rw [← hpn]
      simpa [hkeq] using hvk
    let Suf : List V := (P.drop k).take ((P.length - 1) - k + 1)
    have hSufFrom : IsPathFrom G Suf (P[k]'hk) pₙ := by
      have hs := PathBasics.isPathFrom_slice hP (show k < P.length - 1 by omega) hnlt
      rw [hpn] at hs
      simpa [Suf] using hs
    have hvSuf : v ∉ Suf := by
      intro hz
      exact hvP (List.drop_subset _ _ (List.take_subset _ _ hz))
    have hvSufOther : ∀ z ∈ Suf, z ≠ P[k]'hk → ¬ G.Adj v z := by
      intro z hz hzne hadj
      obtain ⟨t, ht, hkt, -, rfl⟩ :=
        (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
      have htk := (hext t ht (Nat.zero_le _) ⟨ht, hadj⟩).2
      have hteq : t = k := by omega
      exact hzne (depIndex P hteq ht hk)
    have hvSufFrom : IsPathFrom G (v :: Suf) v pₙ :=
      PathAttach.isPathFrom_cons hSufFrom hvk hvSuf hvSufOther
    have hp1neV : p₁ ≠ v := by
      intro he
      exact hvP (by rw [← he]; exact PathBasics.head_mem hhead)
    have hp1notSuf : p₁ ∉ Suf := by
      intro hz
      obtain ⟨t, ht, hkt, -, heq⟩ :=
        (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
      rw [← hp0] at heq
      have := hnd.getElem_inj_iff.mp heq
      omega
    have hp1Other : ∀ z ∈ v :: Suf, z ≠ v → ¬ G.Adj p₁ z := by
      intro z hz hzv
      rcases List.mem_cons.mp hz with rfl | hz
      · exact absurd rfl hzv
      · obtain ⟨t, ht, hkt, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hz
        rw [← hp0]
        exact PathBasics.path_not_adj_of_gap hP h0lt ht (by omega) (by omega)
    let B : List V := p₁ :: v :: Suf
    have hBfrom : IsPathFrom G B p₁ pₙ := by
      simpa [B] using PathAttach.isPathFrom_cons hvSufFrom hv0.symm
        (by simp [hp1neV, hp1notSuf]) hp1Other
    have hBlen : pathLength B = (P.length - 1) - k + 2 := by
      rw [PathBasics.pathLength_eq]
      simp [B, Suf]
      omega
    have hBodd : Odd (pathLength B) := by
      rw [hBlen, Nat.odd_iff]
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hevenP
      rw [Nat.odd_iff] at hkOdd
      omega
    have hBmem : ∀ z : V, z ∈ B ↔ z = p₁ ∨ z = v ∨ z ∈ Suf := by
      intro z
      simp [B]
    have hBoutX : ∀ z ∈ B, z ∉ X := by
      intro z hz
      rcases (hBmem z).mp hz with hz1 | hzv | hzS
      · rw [hz1]
        exact hPoutX p₁ (PathBasics.head_mem hhead)
      · rw [hzv]
        exact hvNotX
      · exact hPoutX z (List.drop_subset _ _ (List.take_subset _ _ hzS))
    have hBX : ∀ z ∈ B, VertexComplete G z X ↔ (z = p₁ ∨ z = pₙ) := by
      intro z hz
      rcases (hBmem z).mp hz with hz1 | hzv | hzS
      · rw [hz1]
        exact ⟨fun _ => Or.inl rfl, fun _ => hp₁X⟩
      · rw [hzv]
        exact ⟨fun hc => absurd hc hvX, by
          rintro (he | he)
          · exact absurd he.symm hp1neV
          · exact absurd (by rw [he]; exact PathBasics.getLast_mem hlast) hvP⟩
      · have hzP := List.drop_subset k P (List.take_subset _ (P.drop k) hzS)
        constructor
        · intro hzX
          rcases (hXuniq z hzP).mp hzX with hz1 | hzn
          · exfalso
            exact hp1notSuf (by simpa [hz1] using hzS)
          · exact Or.inr hzn
        · rintro (hz1 | hzn)
          · exfalso
            exact hp1notSuf (by simpa [hz1] using hzS)
          · exact (hXuniq z hzP).mpr (Or.inr hzn)
    have hBnoedge : ¬ ∃ u ∈ B, ∃ w ∈ B, EdgeComplete G X u w := by
      rintro ⟨u, hu, w, hw, huw, huX, hwX⟩
      rcases (hBX u hu).mp huX with rfl | rfl <;>
        rcases (hBX w hw).mp hwX with rfl | rfl
      · exact G.irrefl huw
      · exact pathFrom_ends_not_adj hBfrom (by rw [hBlen]; omega) huw
      · exact pathFrom_ends_not_adj hBfrom (by rw [hBlen]; omega) huw.symm
      · exact G.irrefl huw
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_6 G hG.1.1 B p₁ pₙ
        hBfrom hBodd X (fun x hx hxB => hBoutX x hxB hx) hXanti hp₁X hpₙX with hedge |
        ⟨hBthree, c, d, hInt, SX, hSX, hSXodd, hSXint⟩
    · exact hBnoedge hedge
    · have hkNear : k = P.length - 2 := by rw [hBlen] at hBthree; omega
      have hBshape : B = [p₁, v, P[k]'hk, pₙ] := by
        have hSlen : Suf.length = 2 := by
          dsimp [Suf]
          rw [PathBasics.length_slice P (show k ≤ P.length - 1 by omega) hnlt]
          omega
        obtain ⟨s0, s1, hSeq⟩ := PathGlue.length_eq_two hSlen
        have hs0 : s0 = P[k]'hk := by
          have hh := hSufFrom.2.1
          rw [hSeq] at hh
          exact Option.some_injective _ hh
        have hs1 : s1 = pₙ := by
          have hh := hSufFrom.2.2
          rw [hSeq] at hh
          simpa using Option.some_injective _ hh
        simp [B, hSeq, hs0, hs1]
      have hcd : c = v ∧ d = P[k]'hk := by
        rw [hBshape] at hInt
        change [v, P[k]'hk] = [c, d] at hInt
        have hpair := List.cons.inj hInt
        have htail := List.cons.inj hpair.2
        exact ⟨hpair.1.symm, htail.1.symm⟩
      have hPkNotY : ¬ VertexComplete G (P[k]'hk) Y := by
        intro hkY
        apply hclaim5
        intro z hz
        rcases hz with hzY | hzv
        · simpa [hkNear] using hkY z hzY
        · rw [Set.mem_singleton_iff] at hzv
          subst z
          simpa [hkNear] using hvk.symm
      obtain ⟨SY, hSY, hSYint⟩ :=
        InducedPathExtraction.exists_antipath_interior_in hYanti hvNotY
          (fun hy => houtU _ (List.getElem_mem hk) (Or.inr hy))
          (by
            by_contra hc
            push_neg at hc
            exact hvY hc)
          (by
            by_contra hc
            push_neg at hc
            exact hPkNotY hc)
      have hpar := AntiholeCompletion.even_add_pathLength_of_two_antipaths
        hBerge hXY hcompl hvk hvNotX (hPoutX _ (List.getElem_mem hk))
        hvNotY (fun hy => houtU _ (List.getElem_mem hk) (Or.inr hy))
        hSY hSYint (by simpa [hcd.1, hcd.2] using hSX) hSXint
      have hSYodd : Odd (pathLength SY) := by
        rw [Nat.even_iff] at hpar
        rw [Nat.odd_iff] at hSXodd ⊢
        omega
      exact hclaim7 k hk hvk SY hSY hSYint hSYodd
  have hkLast : k < P.length - 1 := by
    by_contra hc
    have hkeq : k = P.length - 1 := by omega
    apply hclaim6
    rw [← hpn]
    simpa [hkeq] using hvk
  let Suf : List V := (P.drop k).take ((P.length - 1) - k + 1)
  have hSufFrom : IsPathFrom G Suf (P[k]'hk) pₙ := by
    have hs := PathBasics.isPathFrom_slice hP (show k < P.length - 1 by omega) hnlt
    rw [hpn] at hs
    simpa [Suf] using hs
  have hQrev : IsPathFrom G Q.reverse q v := PathBasics.isPathFrom_reverse hQ
  have hQSdisj : ∀ z ∈ Q.reverse, z ∉ Suf := by
    intro z hzQ hzS
    have hzQ' := List.mem_reverse.mp hzQ
    by_cases hzv : z = v
    · exact hvP (hzv ▸ List.drop_subset _ _ (List.take_subset _ _ hzS))
    · obtain ⟨t, ht, hit, htj, heq⟩ := hQsub z hzQ' hzv
      obtain ⟨s, hs, hks, -, heq'⟩ :=
        (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
      have := hnd.getElem_inj_iff.mp (heq.trans heq'.symm)
      omega
  have hQScross : ∀ x ∈ Q.reverse, ∀ z ∈ Suf,
      G.Adj x z ↔ (x = v ∧ z = P[k]'hk) := by
    intro x hxQ z hzS
    have hxQ' := List.mem_reverse.mp hxQ
    obtain ⟨s, hs, hks, -, heqS⟩ :=
      (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
    by_cases hxv : x = v
    · subst x
      constructor
      · intro hadj
        have hsk := (hext s hs (Nat.zero_le _) ⟨hs, by rw [heqS]; exact hadj⟩).2
        have heq : s = k := by omega
        exact ⟨rfl, by rw [← heqS]; exact depIndex P heq hs hk⟩
      · rintro ⟨-, rfl⟩
        exact hvk
    · obtain ⟨t, ht, hit, htj, heqQ⟩ := hQsub x hxQ' hxv
      constructor
      · intro hadj
        exfalso
        rw [← heqQ, ← heqS] at hadj
        exact PathBasics.path_not_adj_of_gap hP ht hs (by omega) (by omega) hadj
      · rintro ⟨he, -⟩
        exact absurd he hxv
  let R : List V := Q.reverse ++ Suf
  have hRfrom : IsPathFrom G R q pₙ := by
    simpa [R] using PathGlue.glue_path hQrev hSufFrom hQSdisj hQScross
  have hSufLen : Suf.length = (P.length - 1) - k + 1 := by
    dsimp [Suf]
    rw [PathBasics.length_slice P (show k ≤ P.length - 1 by omega) hnlt]
  have hRlen : pathLength R = pathLength Q + 1 + ((P.length - 1) - k) := by
    rw [PathBasics.pathLength_eq, PathBasics.pathLength_eq]
    simp [R, hSufLen]
    omega
  have hReven : Even (pathLength R) := by
    rw [hRlen, Nat.even_iff]
    rw [Nat.odd_iff] at hQodd
    rw [Nat.even_iff] at hkEven hevenP
    rw [PathBasics.pathLength_eq] at hevenP
    omega
  have hRlong : 2 < pathLength R := by rw [hRlen]; omega
  have hRmem : ∀ z : V, z ∈ R ↔ z ∈ Q ∨ z ∈ Suf := by
    intro z
    simp [R]
  have hRX : ∀ z ∈ R, VertexComplete G z X ↔ z = pₙ := by
    intro z hz
    rcases (hRmem z).mp hz with hzQ | hzS
    · constructor
      · intro hzX
        by_cases hzv : z = v
        · exact absurd (hzv ▸ hzX) hvX
        · obtain ⟨t, ht, hit, htj, rfl⟩ := hQsub z hzQ hzv
          rcases (hXuniq _ (List.getElem_mem ht)).mp hzX with hp | hn
          · rw [← hp0] at hp
            have := hnd.getElem_inj_iff.mp hp
            omega
          · rw [← hpn] at hn
            have := hnd.getElem_inj_iff.mp hn
            omega
      · intro hzp
        exfalso
        have hpnQrev : pₙ ∈ Q.reverse := List.mem_reverse.mpr (by
          simpa [hzp] using hzQ)
        exact hQSdisj pₙ hpnQrev (PathBasics.getLast_mem hSufFrom.2.2)
    · have hzP := List.drop_subset k P (List.take_subset _ (P.drop k) hzS)
      constructor
      · intro hzX
        rcases (hXuniq z hzP).mp hzX with hz1 | hzn
        · exfalso
          obtain ⟨t, ht, hkt, -, heq⟩ :=
            (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
          rw [← hp0] at hz1
          have := hnd.getElem_inj_iff.mp (heq.trans hz1)
          omega
        · exact hzn
      · rintro rfl
        exact hpₙX
  have hRY : ∀ z ∈ R, VertexComplete G z Y ↔ z = q := by
    intro z hz
    rcases (hRmem z).mp hz with hzQ | hzS
    · exact hQY z hzQ
    · constructor
      · intro hzY
        obtain ⟨t, ht, hkt, -, rfl⟩ :=
          (PathBasics.mem_slice_iff P (show k ≤ P.length - 1 by omega) hnlt).mp hzS
        have htj := (hminmax t ht (by omega) hzY).2
        omega
      · intro hzq
        exfalso
        have hqS : q ∈ Suf := by simpa [hzq] using hzS
        exact hQSdisj q (List.mem_reverse.mpr hqQ) hqS
  have hRout : ∀ z ∈ R, z ∉ X ∪ Y := by
    intro z hz hxy
    rcases (hRmem z).mp hz with hzQ | hzS
    · by_cases hzv : z = v
      · exact hvXY (hzv ▸ hxy)
      · obtain ⟨t, ht, -, -, rfl⟩ := hQsub z hzQ hzv
        exact houtU _ (List.getElem_mem ht) hxy
    · exact houtU z (List.drop_subset _ _ (List.take_subset _ _ hzS)) hxy
  have h137 := _root_.Workspace.Statements.S13.SPGT.thm_13_7 G hG.1.1 Y X
    (Disjoint.symm hXY) hYne hXne hYanti hXanti
    (fun y hy x hx => (hcompl x hx y hy).symm) R q pₙ hRfrom.1 hReven
    (by rw [hRlen]; omega) hRfrom.2.1 hRfrom.2.2 hRY hRX
  exact (by obtain ⟨hRtwo, -⟩ := h137; omega)

theorem singleton_good (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ v : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (hvXY : v ∉ X ∪ Y) (hvP : v ∉ P) (hvY : ¬ VertexComplete G v Y) :
    VertexGood G X Y P p₁ pₙ v := by
  classical
  by_cases hvX : VertexComplete G v X
  · exact xcomplete_good G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY hvX
  by_cases hv0 : G.Adj v p₁
  · exact nonx_adj_good G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY hvX hv0
  by_contra hbad
  obtain ⟨hP, -, -, -, -, -, -, -, hYex⟩ :=
    Thm185Helpers.setup G hG X Y P p₁ pₙ hopt.1 hhead hlast
  obtain ⟨i, j, hi, hj, h1i, hij, hYiEx, hYjEx, hminmax0⟩ :=
    Thm185Helpers.exists_minmax_index P.length 1
      (fun t => ∃ ht : t < P.length, VertexComplete G (P[t]'ht) Y)
      (by obtain ⟨t, ht, ht1, htY⟩ := hYex; exact ⟨t, ht, ht1, ht, htY⟩)
  have hYi : VertexComplete G (P[i]'hi) Y := by simpa only using hYiEx.choose_spec
  have hYj : VertexComplete G (P[j]'hj) Y := by simpa only using hYjEx.choose_spec
  have hminmax : ∀ (t : ℕ) (ht : t < P.length), 1 ≤ t →
      VertexComplete G (P[t]'ht) Y → i ≤ t ∧ t ≤ j := by
    intro t ht ht1 htY
    exact hminmax0 t ht ht1 ⟨ht, htY⟩
  rcases claim2_path G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY
      i j hi hj h1i hij hYi hYj hminmax with hdone | ⟨Q, q, hQ, hQY, hQsub⟩
  · exact hbad hdone
  · exact nonX_nonadj_absurd G hG X Y P p₁ pₙ v hopt hhead hlast
      hvXY hvP hvY hvX hv0 hbad i j hi hj h1i hij hYi hYj hminmax Q q hQ hQY hQsub

theorem two_le_ncard_of_counterexample (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hF : Workspace.ProofLemmas.Thm186Setup.Adm G X Y P F)
    (hne : ¬ Workspace.ProofLemmas.Thm186Setup.Good G X Y P p₁ pₙ F) :
    2 ≤ F.ncard := by
  classical
  by_contra hlt
  have hp₁P : p₁ ∈ P := PathBasics.head_mem hhead
  obtain ⟨s, t, hst⟩ := List.append_of_mem hp₁P
  have hinfix : [p₁] <:+: P := ⟨s, t, by rw [hst]; simp⟩
  have hint : ∀ w ∈ SPGT.interior [p₁], ¬ VertexComplete G w Y := by
    intro w hw
    simp [SPGT.interior] at hw
  refine hne ?_
  rcases (by omega : F.ncard = 0 ∨ F.ncard = 1) with h0 | h1
  · have hFe : F = ∅ := (Set.ncard_eq_zero (Set.toFinite F)).mp h0
    subst hFe
    refine ⟨[p₁], PathBasics.isPathList_singleton G p₁, hinfix, ?_, hint, ?_⟩
    · intro w hw
      obtain ⟨-, f, hf, -⟩ := hw
      exact absurd hf (Set.notMem_empty f)
    · rintro ⟨f, hf, -⟩
      exact absurd hf (Set.notMem_empty f)
  · obtain ⟨v, rfl⟩ := Set.ncard_eq_one.mp h1
    have hv : v ∈ ({v} : Set V) := rfl
    obtain ⟨hvXY, hvP⟩ := hF.1 v hv
    have hvY := hF.2.2 v hv
    obtain ⟨q, hq1, hq2, hq3, hq4, hq5⟩ :=
      singleton_good G hG X Y P p₁ pₙ v hopt hhead hlast hvXY hvP hvY
    refine ⟨q, hq1, hq2, ?_, hq4, ?_⟩
    · intro w hw
      obtain ⟨hwP, f, hf, hadj⟩ := hw
      rw [Set.mem_singleton_iff] at hf
      subst f
      exact hq3 w hwP hadj.symm
    · rintro ⟨f, hf, hfX⟩
      rw [Set.mem_singleton_iff] at hf
      subst f
      exact hq5 hfX

end Scratch186Singleton
