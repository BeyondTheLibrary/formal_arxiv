import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.OddWheelArc
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S13.Thm_13_6

/-!
# The NO branch of claim (1) of 16.1 — the rim configuration it forces

PAPER (16.1, printed p. 97), second half of the proof of claim (1), beginning at

> *"This proves that `v` has no neighbour in `{p_{j+2},…,p_{n−1}}`."*

`n = C.length`; `D t` is the rim vertex at cyclic position `k + t`, so the paper's `p_a` is
`D (a-1)`, its `j` is `L + 1`, its `i` is `s + 1`, its `k` is `c + 1` and its `m` is `d + 1`.
The paper's *"`j` is odd"* is `Even L`, its *"`i` is odd"* is `Even s`, its *"`k` is even"* is
`¬ Even c` and its *"`m` is odd"* is `Even d`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelClaimOneNoCore

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelArc

variable {V : Type*}

/-! ## Two small helpers -/

/-- If no two vertices of `q` form a `Z`-complete edge, the set 2.3 counts is empty. -/
theorem yEdges_empty {G : SimpleGraph V} {Z : Set V} {q : List V}
    (h : ∀ u ∈ q, ∀ w ∈ q, ¬ EdgeComplete G Z u w) :
    {e : Sym2 V | ∃ u ∈ q, ∃ w ∈ q, e = s(u, w) ∧ EdgeComplete G Z u w}.ncard = 0 := by
  have hset : {e : Sym2 V | ∃ u ∈ q, ∃ w ∈ q, e = s(u, w) ∧ EdgeComplete G Z u w} = ∅ := by
    ext e
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, w, hw, -, hE⟩
    exact h u hu w hw hE
  rw [hset, Set.ncard_empty]

/-- PAPER: *"Since `v-p_j-⋯-p_n-v` is not an odd hole …"* — an arc of the rim whose only
neighbours of `v` are its two ends closes, through `v`, into a hole, and `Berge` forbids it from
being odd.  Stated with the arc starting at offset `0`; every call site shifts the base. -/
theorem no_odd_hole {G : SimpleGraph V} {C : List V} {D : ℕ → V} {v : V} {k n b : ℕ}
    (hBerge : Berge G) (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n) (hvC : v ∉ C)
    (hb : b + 2 ≤ n) (hb2 : 2 ≤ b)
    (hv : ∀ t, t ≤ b → (G.Adj v (D t) ↔ (t = 0 ∨ t = b))) :
    Even (b + 2) := by
  have harc : IsPathFrom G (arc C k 0 b) (D 0) (D b) :=
    arc_isPathFrom' hC hn hD hnn (Nat.zero_le b) (by omega)
  have hmem : ∀ z : V, z ∈ arc C k 0 b ↔ ∃ t, 0 ≤ t ∧ t ≤ b ∧ z = D t :=
    fun z => arc_mem_iff hC hn hD hnn (Nat.zero_le b) (show b - 0 + 1 ≤ n by omega)
  have hlenarc : (arc C k 0 b).length = b + 1 := by
    have := arc_length C k 0 b (show b - 0 + 1 ≤ C.length by omega); omega
  have hhole : IsHoleList G (arc C k 0 b ++ [v]) := by
    refine PathGlue.glue_hole harc
      (⟨PathBasics.isPathList_singleton G v, rfl, rfl⟩ : IsPathFrom G [v] v v) ?_ ?_
      (by have hv1 : ([v] : List V).length = 1 := rfl; omega)
    · intro z hz
      obtain ⟨t, -, -, rfl⟩ := (hmem _).mp hz
      simp only [List.mem_singleton]
      intro hcon
      exact hvC (by rw [← hcon]; exact rim_mem hn hD t)
    · intro z hz w hw
      obtain ⟨t, h1, h2, rfl⟩ := (hmem _).mp hz
      rw [List.mem_singleton] at hw
      subst hw
      rw [SimpleGraph.adj_comm, hv t h2]
      constructor
      · rintro (rfl | rfl)
        · exact Or.inr ⟨rfl, rfl⟩
        · exact Or.inl ⟨rfl, rfl⟩
      · rintro (⟨h, -⟩ | ⟨h, -⟩)
        · exact Or.inr (rim_inj hC hn hD hnn (by omega) (by omega) h)
        · exact Or.inl (rim_inj hC hn hD hnn (by omega) (by omega) h)
  have hlen2 : (arc C k 0 b ++ [v]).length = b + 2 := by
    rw [List.length_append, hlenarc]; rfl
  have := hBerge.1 _ hhole
  rw [holeLength, hlen2] at this
  exact this

/-! ## Step 1 — the paper's `k` (here `c`), the first `Y'`-complete vertex past the arc -/

/-- PAPER: *"Choose `k` with `j ≤ k ≤ n` minimum such that `p_k` is `Y'`-complete.  Since there
is a `Y'`-complete vertex in `{p_{j+2},…,p_{n−1}}`, it follows that `k < n`."* -/
theorem exists_c {G : SimpleGraph V} {Y' : Set V} {D : ℕ → V} {n L s : ℕ}
    (hsL : s + 1 < L)
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hfar : ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y') :
    ∃ c, L + 1 ≤ c ∧ c ≤ n - 2 ∧ VertexComplete G (D c) Y' ∧
      (∀ t, t < c → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1)) := by
  obtain ⟨q, hq1, hq2, hq3⟩ := hfar
  obtain ⟨c, ⟨hc1, hc2, hc3⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun t : ℕ => L ≤ t ∧ t ≤ n - 2 ∧ VertexComplete G (D t) Y') id
      ⟨q, by omega, hq2, hq3⟩
  refine ⟨c, ?_, hc2, hc3, ?_⟩
  · rcases Nat.eq_or_lt_of_le hc1 with h | h
    · exact absurd (honly L le_rfl (by rw [h]; exact hc3)) (by omega)
    · omega
  · intro t ht hct
    by_cases htL : t ≤ L
    · exact honly t htL hct
    · exfalso
      have := hmin t ⟨by omega, by omega, hct⟩
      simp only [id] at this
      omega

/-! ## Step 2 — the parity of `c` -/

/-- PAPER: *"From 2.3 it follows that the path `p_{i+1}-⋯-p_k` is even, and so `k` is even."* -/
theorem c_odd [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {D : ℕ → V} {k n L s c : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hY'anti : AnticonnectedSet G Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L) (hL1 : 2 ≤ L)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (hcL : L + 1 ≤ c) (hcn : c ≤ n - 2) (hcc : VertexComplete G (D c) Y')
    (hlow : ∀ t, t < c → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1)) :
    ¬ Even c := by
  have hn2 : 4 ≤ n := by have := hC.1; omega
  have hq : IsPathFrom G (arc C k (s + 1) c) (D (s + 1)) (D c) :=
    arc_isPathFrom' hC hn hD hnn (by omega) (by omega)
  have hqmem : ∀ z : V, z ∈ arc C k (s + 1) c ↔ ∃ t, s + 1 ≤ t ∧ t ≤ c ∧ z = D t :=
    fun z => arc_mem_iff hC hn hD hnn (by omega) (by omega)
  have hqcomp : ∀ t, s + 1 ≤ t → t ≤ c → VertexComplete G (D t) Y' → (t = s + 1 ∨ t = c) := by
    intro t h1 h2 hct
    rcases Nat.eq_or_lt_of_le h2 with h | h
    · exact Or.inr h
    · rcases hlow t h hct with h' | h' <;> omega
  have hnoedge : ∀ u ∈ arc C k (s + 1) c, ∀ w ∈ arc C k (s + 1) c, ¬ EdgeComplete G Y' u w := by
    intro u hu w hw hE
    obtain ⟨t₁, ht₁a, ht₁b, rfl⟩ := (hqmem u).mp hu
    obtain ⟨t₂, ht₂a, ht₂b, rfl⟩ := (hqmem w).mp hw
    have e₁ := hqcomp t₁ ht₁a ht₁b hE.2.1
    have e₂ := hqcomp t₂ ht₂a ht₂b hE.2.2
    have hadj := (rim_adj hC hn hD hnn (show t₁ < n by omega) (show t₂ < n by omega)).mp hE.1
    omega
  have hpre : ∃ m : ℕ, arc C k (s + 1) c <+: C.rotate m :=
    ⟨k + (s + 1), List.take_prefix _ _⟩
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y' hY'anti C (Or.inr hC) hCY').1
      (arc C k (s + 1) c) (D (s + 1)) (D c) (Or.inr ⟨hC, hpre⟩) hq hcs1 hcc with hpar | hall
  · have hz : {e : Sym2 V | ∃ u ∈ arc C k (s + 1) c, ∃ w ∈ arc C k (s + 1) c,
        e = s(u, w) ∧ EdgeComplete G Y' u w}.ncard = 0 := yEdges_empty hnoedge
    have hlen : pathLength (arc C k (s + 1) c) = c - (s + 1) := by
      rw [PathBasics.pathLength_eq, arc_length C k (s + 1) c (by omega)]
      omega
    rw [hz, hlen] at hpar
    have hs2 : s % 2 = 0 := Nat.even_iff.mp hseven
    rw [Nat.even_iff]
    omega
  · exfalso
    rcases hall (D s) (rim_mem hn hD s) hcs with h | h
    · exact absurd (rim_inj hC hn hD hnn (show s < n by omega) (show s + 1 < n by omega) h)
        (by omega)
    · exact absurd (rim_inj hC hn hD hnn (show s < n by omega) (show c < n by omega) h) (by omega)

/-! ## Step 3 — `v` is adjacent to `p_{j+1}` -/

/-- PAPER: *"Suppose that `v` is not adjacent to `p_{j+1}`.  Since `v-p_j-⋯-p_n-v` is not an odd
hole, it follows that `v` is not adjacent to `p_n`, so `p_1, p_j` are its only neighbours in `C`.
But `p_i-⋯-p_1-v-p_j-⋯-p_k` is odd, and therefore has length 3 by 13.6; and by 2.2, every
`Y'`-complete vertex in `C` is adjacent to `v` except possibly `p_{j−1}, p_{j+1}`, a
contradiction since there is a `Y'`-complete vertex in `{p_{j+2},…,p_{n−1}}`.  So `v` is
adjacent to `p_{j+1}`."* -/
theorem adj_v_succ [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s c : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hneven : Even n) (hvC : v ∉ C)
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hY'anti : AnticonnectedSet G Y') (hvZ : ¬ VertexComplete G v Y') (hvY' : v ∉ Y')
    (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs : VertexComplete G (D s) Y')
    (hcL : L + 1 ≤ c) (hcn : c ≤ n - 2) (hcc : VertexComplete G (D c) Y') (hcodd : ¬ Even c)
    (hlow : ∀ t, t < c → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hfar : ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y')
    (hno : ∀ t, L + 2 ≤ t → t ≤ n - 2 → ¬ G.Adj v (D t)) :
    G.Adj v (D (L + 1)) := by
  have hBerge : Berge G := hG.1.1.1
  have hs2 : s % 2 = 0 := Nat.even_iff.mp hseven
  have hL2' : L % 2 = 0 := Nat.even_iff.mp hLeven
  have hn2' : n % 2 = 0 := Nat.even_iff.mp hneven
  have hc2 : c % 2 = 1 := by rw [Nat.even_iff] at hcodd; omega
  by_contra hcon
  -- PAPER: *"Since `v-p_j-⋯-p_n-v` is not an odd hole, `v` is not adjacent to `p_n`."*
  have hlast : ¬ G.Adj v (D (n - 1)) := by
    intro hh
    have hD₂ : ∀ t : ℕ, C[(k + L + t) % C.length]? = some ((fun t => D (L + t)) t) := by
      intro t
      have h := hD (L + t)
      rw [show k + L + t = k + (L + t) from by omega]
      exact h
    have hev := no_odd_hole (D := fun t => D (L + t)) (b := n - 1 - L) hBerge hC hn hD₂ hnn hvC
      (by omega) (by omega) ?_
    · rw [Nat.even_iff] at hev; omega
    · intro t ht
      simp only
      rcases Nat.eq_zero_or_pos t with rfl | hpos
      · simpa using (hvD L le_rfl).mpr (Or.inr rfl)
      · rcases eq_or_lt_of_le ht with rfl | hlt
        · rw [show L + (n - 1 - L) = n - 1 from by omega]
          exact iff_of_true hh (Or.inr rfl)
        · refine iff_of_false ?_ (by omega)
          rcases (show t = 1 ∨ 2 ≤ t by omega) with rfl | ht2
          · exact hcon
          · exact hno (L + t) (by omega) (by omega)
  -- so `p₁, p_j` are the only neighbours of `v` in `C`
  have hvonly : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)) := by
    intro t ht
    by_cases htL : t ≤ L
    · exact hvD t htL
    · refine iff_of_false ?_ (by omega)
      rcases (show t = L + 1 ∨ (L + 2 ≤ t ∧ t ≤ n - 2) ∨ t = n - 1 by omega) with h | h | h
      · rw [h]; exact hcon
      · exact hno t h.1 h.2
      · rw [h]; exact hlast
  -- PAPER: the path `p_i-⋯-p₁-v-p_j-⋯-p_k`
  have hA : IsPathFrom G ((arc C k 0 s).reverse) (D s) (D 0) :=
    arc_rev_isPathFrom hC hn hD hnn (Nat.zero_le s) (by omega)
  have hAmem : ∀ z : V, z ∈ (arc C k 0 s).reverse ↔ ∃ t, 0 ≤ t ∧ t ≤ s ∧ z = D t :=
    fun z => arc_rev_mem_iff hC hn hD hnn (Nat.zero_le s) (by omega)
  have hB : IsPathFrom G (arc C k L c) (D L) (D c) :=
    arc_isPathFrom' hC hn hD hnn (by omega) (by omega)
  have hBmem : ∀ z : V, z ∈ arc C k L c ↔ ∃ t, L ≤ t ∧ t ≤ c ∧ z = D t :=
    fun z => arc_mem_iff hC hn hD hnn (by omega) (by omega)
  have hP : IsPathFrom G ((arc C k 0 s).reverse ++ (v :: arc C k L c)) (D s) (D c) :=
    glue_two_arcs hC hn hD hnn hvC hA hAmem hB hBmem (by omega) (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun t h1 h2 => by
        rw [hvD t (by omega)]
        exact ⟨fun h => h.resolve_right (by omega), fun h => Or.inl h⟩)
      (fun t h1 h2 => by
        rw [hvonly t (by omega)]
        exact ⟨fun h => h.resolve_left (by omega), fun h => Or.inr h⟩)
  have hPmem : ∀ z : V, z ∈ (arc C k 0 s).reverse ++ (v :: arc C k L c) ↔
      ((∃ t, 0 ≤ t ∧ t ≤ s ∧ z = D t) ∨ z = v ∨ (∃ t, L ≤ t ∧ t ≤ c ∧ z = D t)) := by
    intro z
    rw [List.mem_append, List.mem_cons, hAmem z]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mp h))
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mpr h))
  have hPY' : ∀ w ∈ (arc C k 0 s).reverse ++ (v :: arc C k L c), w ∉ Y' := by
    intro w hw
    rcases (hPmem w).mp hw with ⟨t, -, -, rfl⟩ | rfl | ⟨t, -, -, rfl⟩
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
    · exact hCY' _ (rim_mem hn hD t)
  -- the only `Y'`-complete vertices of the path are its two ends
  have hPcomp : ∀ z ∈ (arc C k 0 s).reverse ++ (v :: arc C k L c), VertexComplete G z Y' →
      (z = D s ∨ z = D c) := by
    intro z hz hcz
    rcases (hPmem z).mp hz with ⟨t, -, ht, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
    · rcases hlow t (by omega) hcz with h | h
      · exact Or.inl (by rw [h])
      · omega
    · exact absurd hcz hvZ
    · rcases Nat.eq_or_lt_of_le ht2 with h | h
      · exact Or.inr (by rw [h])
      · rcases hlow t h hcz with h' | h' <;> omega
  have hsc : ¬ G.Adj (D s) (D c) := by
    intro hadj
    have := (rim_adj hC hn hD hnn (show s < n by omega) (show c < n by omega)).mp hadj
    omega
  have hPnoedge : ¬ ∃ u ∈ (arc C k 0 s).reverse ++ (v :: arc C k L c),
      ∃ w ∈ (arc C k 0 s).reverse ++ (v :: arc C k L c), EdgeComplete G Y' u w := by
    rintro ⟨u, hu, w, hw, hE⟩
    rcases hPcomp u hu hE.2.1 with rfl | rfl <;> rcases hPcomp w hw hE.2.2 with rfl | rfl
    · exact G.irrefl hE.1
    · exact hsc hE.1
    · exact hsc hE.1.symm
    · exact G.irrefl hE.1
  have hPlen : ((arc C k 0 s).reverse ++ (v :: arc C k L c)).length = s + (c - L) + 3 := by
    rw [List.length_append, List.length_reverse, arc_length C k 0 s (by omega),
      List.length_cons, arc_length C k L c (by omega)]
    omega
  have hPodd : Odd (pathLength ((arc C k 0 s).reverse ++ (v :: arc C k L c))) := by
    rw [PathBasics.pathLength_eq, hPlen, Nat.odd_iff]
    omega
  -- PAPER: *"therefore has length 3 by 13.6"*
  have h136 := Workspace.Statements.S13.SPGT.thm_13_6 G hG.1 _ (D s) (D c) hP hPodd Y'
    (by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hmem
      exact hPY' y hmem hy)
    hY'anti hcs hcc
  have hlen3 : pathLength ((arc C k 0 s).reverse ++ (v :: arc C k L c)) = 3 := by
    rcases h136 with hedge | ⟨h3, -⟩
    · exact absurd hedge hPnoedge
    · exact h3
  rw [PathBasics.pathLength_eq, hPlen] at hlen3
  have hs0 : s = 0 := by omega
  have hcL1 : c = L + 1 := by omega
  -- PAPER: *"and by 2.2, every `Y'`-complete vertex in `C` is adjacent to `v` except possibly
  -- `p_{j−1}, p_{j+1}`"*
  obtain ⟨q, hq1, hq2, hq3⟩ := hfar
  obtain ⟨z, hzint, hzadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y' hY'anti _ (D s) (D c) hP hPY' hPodd
      hcs hcc hPnoedge (D q) hq3
  rw [PathBasics.mem_interior_iff_of_pathFrom hP] at hzint
  obtain ⟨hzm, hz1, hz2⟩ := hzint
  rcases (hPmem z).mp hzm with ⟨t, -, ht, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
  · exact hz1 (by rw [show t = s from by omega])
  · exact hno q hq1 hq2 hzadj.symm
  · have hcase := (rim_adj hC hn hD hnn (show q < n by omega) (show t < n by omega)).mp hzadj
    have : t = L := by
      rcases (show t = L ∨ t = L + 1 from by omega) with h | h
      · exact h
      · exact absurd (by rw [h, ← hcL1] : D t = D c) hz2
    omega

/-! ## Step 4 — `v` is adjacent to `p_n`, so it has exactly four neighbours in `C` -/

/-- PAPER: *"Since `v-p_{j+1}-⋯-p_n-p_1-v` is not an odd hole, it follows that `v` is also
adjacent to `p_n`, so it has exactly four neighbours in `C`."* -/
theorem adj_v_last {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {v : V} {D : ℕ → V} {k n L : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hneven : Even n) (hvC : v ∉ C)
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hvL1 : G.Adj v (D (L + 1)))
    (hno : ∀ t, L + 2 ≤ t → t ≤ n - 2 → ¬ G.Adj v (D t)) :
    G.Adj v (D (n - 1)) := by
  have hL2' : L % 2 = 0 := Nat.even_iff.mp hLeven
  have hn2' : n % 2 = 0 := Nat.even_iff.mp hneven
  by_contra hcon
  have hDn : D n = D 0 := rim_congr hC hD (by rw [hnn]; simp)
  have hD₂ : ∀ t : ℕ, C[(k + (L + 1) + t) % C.length]? = some ((fun t => D (L + 1 + t)) t) := by
    intro t
    have h := hD (L + 1 + t)
    rw [show k + (L + 1) + t = k + (L + 1 + t) from by omega]
    exact h
  have hev := no_odd_hole (D := fun t => D (L + 1 + t)) (b := n - L - 1) hBerge hC hn hD₂ hnn hvC
    (by omega) (by omega) ?_
  · rw [Nat.even_iff] at hev; omega
  · intro t ht
    simp only
    rcases Nat.eq_zero_or_pos t with rfl | hpos
    · exact iff_of_true (by simpa using hvL1) (Or.inl rfl)
    · rcases eq_or_lt_of_le ht with rfl | hlt
      · rw [show L + 1 + (n - L - 1) = n from by omega, hDn]
        exact iff_of_true ((hvD 0 (by omega)).mpr (Or.inl rfl)) (Or.inr rfl)
      · refine iff_of_false ?_ (by omega)
        rcases (show L + 1 + t ≤ n - 2 ∨ L + 1 + t = n - 1 from by omega) with h | h
        · exact hno (L + 1 + t) (by omega) h
        · rw [h]; exact hcon

/-! ## Step 5a — the paper's `m` is `< n` -/

/-- PAPER: *"If `m = n` then a `Y'`-complete vertex in `{p_{j+2},…,p_{n−1}}` has no neighbours in
the interior of the odd path `p_{i+1}-⋯-p_j-v-p_n`, and the ends of this path are `Y'`-complete
and its internal vertices are not, contrary to 2.2.  So `m < n`."* -/
theorem d_le [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s c d : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hneven : Even n) (hvC : v ∉ C)
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvfull : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1)))
    (hY'anti : AnticonnectedSet G Y') (hvZ : ¬ VertexComplete G v Y') (hvY' : v ∉ Y')
    (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hdc : L + 2 ≤ d) (hdn : d ≤ n - 1) (hcd : VertexComplete G (D d) Y')
    (hq1 : L + 2 ≤ c) (hq2 : c ≤ n - 2) (hq3 : VertexComplete G (D c) Y')
    (hno : ∀ t, L + 2 ≤ t → t ≤ n - 2 → ¬ G.Adj v (D t)) :
    d ≤ n - 2 := by
  have hs2 : s % 2 = 0 := Nat.even_iff.mp hseven
  have hL2' : L % 2 = 0 := Nat.even_iff.mp hLeven
  by_contra hcon
  have hdeq : d = n - 1 := by omega
  subst hdeq
  have hA : IsPathFrom G (arc C k (s + 1) L) (D (s + 1)) (D L) :=
    arc_isPathFrom' hC hn hD hnn (by omega) (by omega)
  have hAmem : ∀ z : V, z ∈ arc C k (s + 1) L ↔ ∃ t, s + 1 ≤ t ∧ t ≤ L ∧ z = D t :=
    fun z => arc_mem_iff hC hn hD hnn (by omega) (by omega)
  have hB : IsPathFrom G (arc C k (n - 1) (n - 1)) (D (n - 1)) (D (n - 1)) :=
    arc_isPathFrom' hC hn hD hnn (le_refl _) (by omega)
  have hBmem : ∀ z : V, z ∈ arc C k (n - 1) (n - 1) ↔ ∃ t, n - 1 ≤ t ∧ t ≤ n - 1 ∧ z = D t :=
    fun z => arc_mem_iff hC hn hD hnn (le_refl _) (by omega)
  have hP : IsPathFrom G (arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)))
      (D (s + 1)) (D (n - 1)) :=
    glue_two_arcs hC hn hD hnn hvC hA hAmem hB hBmem (by omega) (le_refl _) (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨le_refl _, le_refl _⟩
      (fun t h1 h2 => by
        rw [hvfull t (by omega)]
        constructor
        · rintro (h | h | h | h) <;> omega
        · intro h; exact Or.inr (Or.inl h))
      (fun t h1 h2 => by
        rw [hvfull t (by omega)]
        constructor
        · rintro (h | h | h | h) <;> omega
        · intro h; exact Or.inr (Or.inr (Or.inr h)))
  have hPmem : ∀ z : V, z ∈ arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)) ↔
      ((∃ t, s + 1 ≤ t ∧ t ≤ L ∧ z = D t) ∨ z = v ∨
        (∃ t, n - 1 ≤ t ∧ t ≤ n - 1 ∧ z = D t)) := by
    intro z
    rw [List.mem_append, List.mem_cons, hAmem z]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mp h))
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mpr h))
  have hPY' : ∀ w ∈ arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)), w ∉ Y' := by
    intro w hw
    rcases (hPmem w).mp hw with ⟨t, -, -, rfl⟩ | rfl | ⟨t, -, -, rfl⟩
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
    · exact hCY' _ (rim_mem hn hD t)
  have hPcomp : ∀ z ∈ arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)),
      VertexComplete G z Y' → (z = D (s + 1) ∨ z = D (n - 1)) := by
    intro z hz hcz
    rcases (hPmem z).mp hz with ⟨t, ht, ht2, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
    · rcases honly t ht2 hcz with h | h
      · omega
      · exact Or.inl (by rw [h])
    · exact absurd hcz hvZ
    · exact Or.inr (by rw [show t = n - 1 from by omega])
  have hends : ¬ G.Adj (D (s + 1)) (D (n - 1)) := by
    intro hadj
    have := (rim_adj hC hn hD hnn (show s + 1 < n by omega) (show n - 1 < n by omega)).mp hadj
    omega
  have hPnoedge : ¬ ∃ u ∈ arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)),
      ∃ w ∈ arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)), EdgeComplete G Y' u w := by
    rintro ⟨u, hu, w, hw, hE⟩
    rcases hPcomp u hu hE.2.1 with rfl | rfl <;> rcases hPcomp w hw hE.2.2 with rfl | rfl
    · exact G.irrefl hE.1
    · exact hends hE.1
    · exact hends hE.1.symm
    · exact G.irrefl hE.1
  have hPlen : (arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1))).length = L - s + 2 := by
    rw [List.length_append, arc_length C k (s + 1) L (by omega), List.length_cons,
      arc_length C k (n - 1) (n - 1) (by omega)]
    omega
  have hPodd : Odd (pathLength (arc C k (s + 1) L ++ (v :: arc C k (n - 1) (n - 1)))) := by
    rw [PathBasics.pathLength_eq, hPlen, Nat.odd_iff]
    omega
  obtain ⟨z, hzint, hzadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y' hY'anti _ (D (s + 1)) (D (n - 1)) hP hPY'
      hPodd hcs1 hcd hPnoedge (D c) hq3
  rw [PathBasics.mem_interior_iff_of_pathFrom hP] at hzint
  obtain ⟨hzm, hz1, hz2⟩ := hzint
  rcases (hPmem z).mp hzm with ⟨t, ht, ht2, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
  · have htne : t ≠ s + 1 := fun h => hz1 (by rw [h])
    have := (rim_adj hC hn hD hnn (show c < n by omega) (show t < n by omega)).mp hzadj
    omega
  · exact hno c hq1 hq2 hzadj.symm
  · exact hz2 (by rw [show t = n - 1 from by omega])

/-! ## Step 5b — the parity of the paper's `m` -/

/-- PAPER: *"Then 2.3 applied to the path `p_m-⋯-p_n-p_1-⋯-p_i` implies that `m` is odd, and
therefore `m > k`."* -/
theorem d_even [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {D : ℕ → V} {k n L s d : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hneven : Even n)
    (hY'anti : AnticonnectedSet G Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L) (hL1 : 2 ≤ L) (hn4 : L + 4 ≤ n)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hdc : L + 2 ≤ d) (hdn : d ≤ n - 2) (hcd : VertexComplete G (D d) Y')
    (hhigh : ∀ t, d < t → t ≤ n - 1 → ¬ VertexComplete G (D t) Y') :
    Even d := by
  have hs2 : s % 2 = 0 := Nat.even_iff.mp hseven
  have hn2' : n % 2 = 0 := Nat.even_iff.mp hneven
  have hD₃ : ∀ t : ℕ, C[(k + d + t) % C.length]? = some ((fun t => D (d + t)) t) := by
    intro t
    have h := hD (d + t)
    rw [show k + d + t = k + (d + t) from by omega]
    exact h
  have hP : IsPathFrom G (arc C (k + d) 0 (n - d + s)) (D d) (D (d + (n - d + s))) :=
    arc_isPathFrom' hC hn hD₃ hnn (Nat.zero_le _) (by omega)
  have hDend : D (d + (n - d + s)) = D s := by
    rw [show d + (n - d + s) = n + s from by omega]
    exact rim_congr hC hD (by rw [hnn]; exact Nat.add_mod_left n s)
  rw [hDend] at hP
  have hmem : ∀ z : V, z ∈ arc C (k + d) 0 (n - d + s) ↔
      ∃ t, 0 ≤ t ∧ t ≤ n - d + s ∧ z = D (d + t) :=
    fun z => arc_mem_iff hC hn hD₃ hnn (Nat.zero_le _) (by omega)
  have hcomp : ∀ t, t ≤ n - d + s → VertexComplete G (D (d + t)) Y' →
      (t = 0 ∨ t = n - d + s) := by
    intro t ht hct
    by_cases hcase : d + t ≤ n - 1
    · rcases Nat.eq_zero_or_pos t with rfl | hpos
      · exact Or.inl rfl
      · exact absurd hct (hhigh (d + t) (by omega) hcase)
    · have hlt : d + t - n ≤ s := by omega
      have hmod : (d + t) % C.length = (d + t - n) % C.length := by
        rw [hnn]
        conv_lhs => rw [show d + t = (d + t - n) + n from by omega]
        exact Nat.add_mod_right _ n
      have heq : D (d + t) = D (d + t - n) := rim_congr hC hD hmod
      rw [heq] at hct
      rcases honly (d + t - n) (by omega) hct with h | h <;> omega
  have hends : ¬ G.Adj (D d) (D s) := by
    intro hadj
    have := (rim_adj hC hn hD hnn (show d < n by omega) (show s < n by omega)).mp hadj
    omega
  have hnoedge : ∀ u ∈ arc C (k + d) 0 (n - d + s), ∀ w ∈ arc C (k + d) 0 (n - d + s),
      ¬ EdgeComplete G Y' u w := by
    intro u hu w hw hE
    obtain ⟨t₁, -, ht₁, rfl⟩ := (hmem u).mp hu
    obtain ⟨t₂, -, ht₂, rfl⟩ := (hmem w).mp hw
    have e₁ := hcomp t₁ ht₁ hE.2.1
    have e₂ := hcomp t₂ ht₂ hE.2.2
    have hd0 : D (d + 0) = D d := by norm_num
    rcases e₁ with rfl | rfl <;> rcases e₂ with rfl | rfl
    · exact G.irrefl hE.1
    · rw [hd0, hDend] at hE
      exact hends hE.1
    · rw [hd0, hDend] at hE
      exact hends hE.1.symm
    · exact G.irrefl hE.1
  have hpre : ∃ m : ℕ, arc C (k + d) 0 (n - d + s) <+: C.rotate m :=
    ⟨k + d + 0, List.take_prefix _ _⟩
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y' hY'anti C (Or.inr hC) hCY').1
      (arc C (k + d) 0 (n - d + s)) (D d) (D s) (Or.inr ⟨hC, hpre⟩) hP hcd hcs with hpar | hall
  · have hz : {e : Sym2 V | ∃ u ∈ arc C (k + d) 0 (n - d + s),
        ∃ w ∈ arc C (k + d) 0 (n - d + s), e = s(u, w) ∧ EdgeComplete G Y' u w}.ncard = 0 :=
      yEdges_empty hnoedge
    have hlen : pathLength (arc C (k + d) 0 (n - d + s)) = n - d + s := by
      rw [PathBasics.pathLength_eq, arc_length C (k + d) 0 (n - d + s) (by omega)]
      omega
    rw [hz, hlen] at hpar
    rw [Nat.even_iff]
    omega
  · exfalso
    rcases hall (D (s + 1)) (rim_mem hn hD (s + 1)) hcs1 with h | h
    · exact absurd (rim_inj hC hn hD hnn (show s + 1 < n by omega) (show d < n by omega) h)
        (by omega)
    · exact absurd (rim_inj hC hn hD hnn (show s + 1 < n by omega) (show s < n by omega) h)
        (by omega)

/-! ## Step 5c — `m = k + 1` -/

/-- PAPER: *"Suppose that `m > k+1`.  Then `p_m-⋯-p_n-v-p_{j+1}-⋯-p_k` is an odd path, and
`p_{i+1}` has no neighbour in its interior, contrary to 2.2.  So `m = k+1`."* -/
theorem d_eq [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s c d : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hneven : Even n) (hvC : v ∉ C)
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvfull : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1)))
    (hY'anti : AnticonnectedSet G Y') (hvZ : ¬ VertexComplete G v Y') (hvY' : v ∉ Y')
    (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs1 : VertexComplete G (D (s + 1)) Y')
    (hcL : L + 1 ≤ c) (hcn : c ≤ n - 2) (hcc : VertexComplete G (D c) Y') (hcodd : ¬ Even c)
    (hlow : ∀ t, t < c → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hdL : L + 2 ≤ d) (hdc : c ≤ d) (hdn : d ≤ n - 2) (hcd : VertexComplete G (D d) Y')
    (hdeven : Even d)
    (hhigh : ∀ t, d < t → t ≤ n - 1 → ¬ VertexComplete G (D t) Y') :
    d = c + 1 := by
  have hs2 : s % 2 = 0 := Nat.even_iff.mp hseven
  have hL2' : L % 2 = 0 := Nat.even_iff.mp hLeven
  have hn2' : n % 2 = 0 := Nat.even_iff.mp hneven
  have hc2 : c % 2 = 1 := by rw [Nat.even_iff] at hcodd; omega
  have hd2 : d % 2 = 0 := Nat.even_iff.mp hdeven
  by_contra hcon
  have hgap : c + 2 ≤ d := by omega
  have hA : IsPathFrom G ((arc C k (L + 1) c).reverse) (D c) (D (L + 1)) :=
    arc_rev_isPathFrom hC hn hD hnn (by omega) (by omega)
  have hAmem : ∀ z : V, z ∈ (arc C k (L + 1) c).reverse ↔ ∃ t, L + 1 ≤ t ∧ t ≤ c ∧ z = D t :=
    fun z => arc_rev_mem_iff hC hn hD hnn (by omega) (by omega)
  have hB : IsPathFrom G ((arc C k d (n - 1)).reverse) (D (n - 1)) (D d) :=
    arc_rev_isPathFrom hC hn hD hnn (by omega) (by omega)
  have hBmem : ∀ z : V, z ∈ (arc C k d (n - 1)).reverse ↔ ∃ t, d ≤ t ∧ t ≤ n - 1 ∧ z = D t :=
    fun z => arc_rev_mem_iff hC hn hD hnn (by omega) (by omega)
  have hP : IsPathFrom G ((arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse))
      (D c) (D d) :=
    glue_two_arcs hC hn hD hnn hvC hA hAmem hB hBmem (by omega) (by omega) (by omega)
      (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun t h1 h2 => by
        rw [hvfull t (by omega)]
        constructor
        · rintro (h | h | h | h) <;> omega
        · intro h; exact Or.inr (Or.inr (Or.inl h)))
      (fun t h1 h2 => by
        rw [hvfull t (by omega)]
        constructor
        · rintro (h | h | h | h) <;> omega
        · intro h; exact Or.inr (Or.inr (Or.inr h)))
  have hPmem : ∀ z : V, z ∈ (arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse) ↔
      ((∃ t, L + 1 ≤ t ∧ t ≤ c ∧ z = D t) ∨ z = v ∨ (∃ t, d ≤ t ∧ t ≤ n - 1 ∧ z = D t)) := by
    intro z
    rw [List.mem_append, List.mem_cons, hAmem z]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mp h))
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hBmem z).mpr h))
  have hPY' : ∀ w ∈ (arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse), w ∉ Y' := by
    intro w hw
    rcases (hPmem w).mp hw with ⟨t, -, -, rfl⟩ | rfl | ⟨t, -, -, rfl⟩
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
    · exact hCY' _ (rim_mem hn hD t)
  have hPcomp : ∀ z ∈ (arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse),
      VertexComplete G z Y' → (z = D c ∨ z = D d) := by
    intro z hz hcz
    rcases (hPmem z).mp hz with ⟨t, ht, ht2, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
    · rcases Nat.eq_or_lt_of_le ht2 with h | h
      · exact Or.inl (by rw [h])
      · rcases hlow t h hcz with h' | h' <;> omega
    · exact absurd hcz hvZ
    · rcases Nat.eq_or_lt_of_le ht with h | h
      · exact Or.inr (by rw [h])
      · exact absurd hcz (hhigh t h ht2)
  have hends : ¬ G.Adj (D c) (D d) := by
    intro hadj
    have := (rim_adj hC hn hD hnn (show c < n by omega) (show d < n by omega)).mp hadj
    omega
  have hPnoedge : ¬ ∃ u ∈ (arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse),
      ∃ w ∈ (arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse),
        EdgeComplete G Y' u w := by
    rintro ⟨u, hu, w, hw, hE⟩
    rcases hPcomp u hu hE.2.1 with rfl | rfl <;> rcases hPcomp w hw hE.2.2 with rfl | rfl
    · exact G.irrefl hE.1
    · exact hends hE.1
    · exact hends hE.1.symm
    · exact G.irrefl hE.1
  have hPlen : ((arc C k (L + 1) c).reverse ++ (v :: (arc C k d (n - 1)).reverse)).length
      = (c - L) + 1 + (n - d) := by
    rw [List.length_append, List.length_reverse, arc_length C k (L + 1) c (by omega),
      List.length_cons, List.length_reverse, arc_length C k d (n - 1) (by omega)]
    omega
  have hPodd : Odd (pathLength ((arc C k (L + 1) c).reverse ++
      (v :: (arc C k d (n - 1)).reverse))) := by
    rw [PathBasics.pathLength_eq, hPlen, Nat.odd_iff]
    omega
  obtain ⟨z, hzint, hzadj⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y' hY'anti _ (D c) (D d) hP hPY'
      hPodd hcc hcd hPnoedge (D (s + 1)) hcs1
  rw [PathBasics.mem_interior_iff_of_pathFrom hP] at hzint
  obtain ⟨hzm, hz1, hz2⟩ := hzint
  rcases (hPmem z).mp hzm with ⟨t, ht, ht2, rfl⟩ | rfl | ⟨t, ht, ht2, rfl⟩
  · have htne : t ≠ c := fun h => hz1 (by rw [h])
    have := (rim_adj hC hn hD hnn (show s + 1 < n by omega) (show t < n by omega)).mp hzadj
    omega
  · have := (hvfull (s + 1) (by omega)).mp hzadj.symm
    omega
  · have htne : t ≠ d := fun h => hz2 (by rw [h])
    have := (rim_adj hC hn hD hnn (show s + 1 < n by omega) (show t < n by omega)).mp hzadj
    omega

/-! ## The NO branch's output configuration -/

/-- The configuration the NO branch of claim (1) of 16.1 forces on the rim: `v` has exactly the
four neighbours `p₁, p_j, p_{j+1}, p_n`, and the `Y'`-complete vertices of `C` are exactly
`p_i, p_{i+1}, p_k, p_{k+1}` with `k` even. -/
theorem no_config [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L s : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length) (hnn : C.length = n) (hneven : Even n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t))
    (hvC : v ∉ C)
    (hL1 : 2 ≤ L) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hY'anti : AnticonnectedSet G Y') (hvY' : v ∉ Y')
    (hvZ : ¬ VertexComplete G v Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hfar : ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y')
    (hno : ∀ t, L + 2 ≤ t → t ≤ n - 2 → ¬ G.Adj v (D t)) :
    ∃ c : ℕ, ¬ Even c ∧ L + 1 ≤ c ∧ c + 1 ≤ n - 2 ∧
      (∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1))) ∧
      (∀ t, t < n → (VertexComplete G (D t) Y' ↔
        (t = s ∨ t = s + 1 ∨ t = c ∨ t = c + 1))) := by
  have hBerge : Berge G := hG.1.1.1
  obtain ⟨c, hcL, hcn, hcc, hlow⟩ := exists_c hsL honly hfar
  have hcodd : ¬ Even c :=
    c_odd hBerge hC hn hD hnn hY'anti hCY' hseven hsL hL1 hcs hcs1 hcL hcn hcc hlow
  have hvL1 : G.Adj v (D (L + 1)) :=
    adj_v_succ hG hC hn hD hnn hneven hvC hL1 hLeven hn4 hvD hY'anti hvZ hvY' hCY' hseven hsL
      hcs hcL hcn hcc hcodd hlow hfar hno
  have hvn1 : G.Adj v (D (n - 1)) :=
    adj_v_last hBerge hC hn hD hnn hneven hvC hL1 hLeven hn4 hvD hvL1 hno
  have hvfull : ∀ t, t < n → (G.Adj v (D t) ↔ (t = 0 ∨ t = L ∨ t = L + 1 ∨ t = n - 1)) := by
    intro t ht
    constructor
    · intro hadj
      by_cases htL : t ≤ L
      · rcases (hvD t htL).mp hadj with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · rcases (show t = L + 1 ∨ (L + 2 ≤ t ∧ t ≤ n - 2) ∨ t = n - 1 from by omega) with h | h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact absurd hadj (hno t h.1 h.2)
        · exact Or.inr (Or.inr (Or.inr h))
    · intro hcase
      rcases hcase with h | h | h | h
      · rw [h]; exact (hvD 0 (by omega)).mpr (Or.inl rfl)
      · rw [h]; exact (hvD L le_rfl).mpr (Or.inr rfl)
      · rw [h]; exact hvL1
      · rw [h]; exact hvn1
  obtain ⟨q, hq1, hq2, hq3⟩ := hfar
  have hcq : c ≤ q := by
    by_contra hh
    rcases hlow q (by omega) hq3 with h | h <;> omega
  obtain ⟨d, ⟨hd1, hd2, hd3⟩, hmax⟩ :=
    ExtremalChoice.exists_max_nat
      (fun t : ℕ => c ≤ t ∧ t ≤ n - 1 ∧ VertexComplete G (D t) Y') id (n - 1)
      (fun a ha => ha.2.1) ⟨q, hcq, by omega, hq3⟩
  have hhigh : ∀ t, d < t → t ≤ n - 1 → ¬ VertexComplete G (D t) Y' := by
    intro t h1 h2 hct
    have := hmax t ⟨by omega, h2, hct⟩
    simp only [id] at this
    omega
  have hdq : q ≤ d := by
    have := hmax q ⟨hcq, by omega, hq3⟩
    simpa using this
  have hdL : L + 2 ≤ d := by omega
  have hdn : d ≤ n - 2 :=
    d_le (c := q) hBerge hC hn hD hnn hneven hvC hL1 hLeven hn4 hvfull hY'anti hvZ hvY' hCY'
      hseven hsL hcs1 honly hdL hd2 hd3 hq1 hq2 hq3 hno
  have hdeven : Even d :=
    d_even hBerge hC hn hD hnn hneven hY'anti hCY' hseven hsL hL1 hn4 hcs hcs1 honly hdL hdn
      hd3 hhigh
  have hdeq : d = c + 1 :=
    d_eq hBerge hC hn hD hnn hneven hvC hL1 hLeven hn4 hvfull hY'anti hvZ hvY' hCY' hseven hsL
      hcs1 hcL hcn hcc hcodd hlow hdL hd1 hdn hd3 hdeven hhigh
  subst hdeq
  refine ⟨c, hcodd, hcL, by omega, hvfull, ?_⟩
  intro t ht
  constructor
  · intro hct
    by_cases h1 : t < c
    · rcases hlow t h1 hct with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · rcases (show t = c ∨ t = c + 1 ∨ c + 1 < t from by omega) with h | h | h
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd hct (hhigh t (by omega) (by omega))
  · intro hcase
    rcases hcase with h | h | h | h
    · rw [h]; exact hcs
    · rw [h]; exact hcs1
    · rw [h]; exact hcc
    · rw [h]; exact hd3

end Workspace.ProofLemmas.OddWheelClaimOneNoCore

