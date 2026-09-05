/-  Proof attempt 1 for statement 15.6 (printed p. 94, proof printed pp. 94-95).

    Reproduces the printed proof step for step.  Throughout, `D t` is the paper's
    `p_{t+1}` (the rim of the hole read from `C[0]`), `Z_1 = {q_1,...,q_{n-1}}` is
    `(interior Q).dropLast` and `Z_2 = {q_2,...,q_n}` is `(interior Q).tail`.

    * `odd_antihole_absurd` / `odd_antihole_absurd_2` package the five odd antiholes.

    * First paragraph -- *"Suppose first that one of `q_1,...,q_n` belongs to the hole."*
      Such a `q_i` is `p_3` or `p_m`; both cases are carried out (the paper's *"we may
      assume that it is `p_m`"* is a reflection of the hole about the edge `p_1 p_2`,
      which is not available as a transport here, so the mirrored case is written out).
      In each case: no other `q_j` is on `C`, then for every remaining index the vertex
      is not adjacent to the `q` on the hole, so it is complete to the other side and
      `p_i-p_1-q_1-...-q_n-p_i` is an odd antihole; the one boundary index is handled by
      15.5 on `p_{m-1}-p_m-p_1-p_2` (resp. its mirror) followed by the odd antihole
      `p_2-p_{m-1}-q_1-...-q_n-p_2`.

    * Second paragraph -- *"So we may assume that none of `q_1,...,q_n` belong to `C`."*
      `hcl1`/`hcl2` are claim (1) (*"proved as in the proof of 3.3"*): a vertex of `Y_1`
      not in `Y_2` closes `Q \ p_2` into an odd antihole through `q_n-p_i-p_1`, forcing
      `i = m`.  `hcl3` is claim (2), following the printed argument verbatim: minimal
      `i`, 15.5 four times, 15.4 on `p_j-...-p_m-p_1-...-p_4`, maximal `j`, and the odd
      antihole `p_3-q_1-...-q_n-p_m-p_3`.  `hcl4` is its mirror.  The last paragraph is
      the odd antihole `p_2-p_m-p_3-p_1` completing `Q`, followed by the two-way case
      split and 15.5 on `p_3-p_4-...-p_m`.

    `h155arc` is 15.5 applied to the arc of `C` running from cyclic position `a` to
    cyclic position `b`; `OddWheelArc.arc C 0 a b` is by construction a prefix of
    `C.rotate a`, which is exactly the *"a path in `C`"* hypothesis of 15.5.        -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.Types.Wheels
import Workspace.Statements.S15.Thm_15_4
import Workspace.Statements.S15.Thm_15_5
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.OddWheelArc
import Workspace.ProofLemmas.HoleArithmetic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

open Workspace.ProofLemmas

/-! ### the two odd-antihole closures -/

private theorem not_adj_of_compl_adj {G : SimpleGraph V} {u v : V} (h : Gᶜ.Adj u v) :
    ¬ G.Adj u v := by
  rw [SimpleGraph.compl_adj] at h; exact h.2

/-- *"`w-u-R-v-w` is an odd antihole"*: an odd antipath `R` whose two ends are nonadjacent to
`w`, while every internal vertex of `R` is adjacent to `w`, closes into an antihole of odd
length. -/
private theorem odd_antihole_absurd {G : SimpleGraph V} (hBerge : Berge G)
    {R : List V} {u v w : V} (hR : IsAntipathFrom G R u v) (hlen : 2 ≤ pathLength R)
    (hwune : w ≠ u) (hwu : ¬ G.Adj w u) (hwvne : w ≠ v) (hwv : ¬ G.Adj w v)
    (hwR : w ∉ R) (hwint : ∀ y ∈ SPGT.interior R, G.Adj w y)
    (hodd : Odd (pathLength R)) : False := by
  have hhole : IsHoleList Gᶜ (w :: R) :=
    PrismBasics.isHoleList_of_path_add_vertex (G := Gᶜ) hR hlen
      (by rw [SimpleGraph.compl_adj]; exact ⟨hwune, hwu⟩)
      (by rw [SimpleGraph.compl_adj]; exact ⟨hwvne, hwv⟩) hwR
      (fun y hy hc => not_adj_of_compl_adj hc (hwint y hy))
  have hev := hBerge.2 _ hhole
  rw [PrismBasics.holeLength_cons _ (PathBasics.path_ne_nil hR.1)] at hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨j, hj⟩ := hodd
  omega

/-- *"`t-s-u-R-v-t` is an odd antihole"*: an even antipath `R` with an extra vertex attached at
each end, the two extra vertices being nonadjacent to each other. -/
private theorem odd_antihole_absurd_two {G : SimpleGraph V} (hBerge : Berge G)
    {R : List V} {u v s t : V} (hR : IsAntipathFrom G R u v) (hlen : 1 ≤ pathLength R)
    (hsune : s ≠ u) (hsu : ¬ G.Adj s u) (htvne : t ≠ v) (htv : ¬ G.Adj t v)
    (hstne : s ≠ t) (hst : ¬ G.Adj s t)
    (hsR : s ∉ R) (htR : t ∉ R) (hsv : G.Adj s v) (htu : G.Adj t u)
    (hsint : ∀ y ∈ SPGT.interior R, G.Adj s y) (htint : ∀ y ∈ SPGT.interior R, G.Adj t y)
    (hpar : Even (pathLength R)) : False := by
  have hhole : IsHoleList Gᶜ (t :: s :: R) :=
    PrismBasics.isHoleList_of_path_add_two_vertices (G := Gᶜ) hR hlen
      (by rw [SimpleGraph.compl_adj]; exact ⟨hsune, hsu⟩)
      (by rw [SimpleGraph.compl_adj]; exact ⟨htvne, htv⟩)
      (by rw [SimpleGraph.compl_adj]; exact ⟨hstne, hst⟩) hsR htR
      (fun hc => not_adj_of_compl_adj hc hsv)
      (fun hc => not_adj_of_compl_adj hc htu)
      (fun y hy hc => not_adj_of_compl_adj hc (hsint y hy))
      (fun y hy hc => not_adj_of_compl_adj hc (htint y hy))
  have hev := hBerge.2 _ hhole
  rw [PrismBasics.holeLength_cons_cons _ _ (PathBasics.path_ne_nil hR.1)] at hev
  obtain ⟨k, hk⟩ := hev
  obtain ⟨j, hj⟩ := hpar
  omega

theorem thm_15_6 (G : SimpleGraph V) (hG : InF6 G)
    (C : List V) (m : ℕ) (hC : IsHoleList G C) (hCm : C.length = m) (hm : 6 ≤ m)
    (Q : List V) (hQ : IsAntipathFrom G Q C[0] C[1])
    (hQlen : 4 ≤ pathLength Q) (hQeven : Even (pathLength Q)) :
    {w : V | w ∈ C.drop 2 ∧
        (VertexComplete G w {x : V | x ∈ (SPGT.interior Q).dropLast} ∨
          VertexComplete G w {x : V | x ∈ (SPGT.interior Q).tail})}.Subsingleton ∧
    (∀ w ∈ C.drop 2,
      (VertexComplete G w {x : V | x ∈ (SPGT.interior Q).dropLast} ∨
        VertexComplete G w {x : V | x ∈ (SPGT.interior Q).tail}) →
      w = C[2] ∨ w = C[m - 1]) := by
  classical
  have hBerge : Berge G := hG.1.1.1
  have hn : 0 < C.length := by omega
  ---------------------------------------------------------------------------
  -- ###  the rim `D t = p_{t+1}`
  ---------------------------------------------------------------------------
  obtain ⟨D, hD⟩ := OddWheelArc.rim_exists (C := C) hn 0
  have hDeq : ∀ (t : ℕ) (ht : t < C.length), C[t]'ht = D t := by
    intro t ht
    rw [← OddWheelArc.rim_eq_getElem hn hD t]
    exact HoleArithmetic.getElem_congr_idx C ht (Nat.mod_lt _ hn)
      (by rw [Nat.zero_add, Nat.mod_eq_of_lt ht])
  have radj : ∀ {a b : ℕ}, a < m → b < m →
      (G.Adj (D a) (D b) ↔ (b = a + 1 ∨ a = b + 1 ∨ (a = 0 ∧ b = m - 1) ∨ (b = 0 ∧ a = m - 1))) :=
    fun {a b} ha hb => OddWheelArc.rim_adj hC hn hD hCm ha hb
  have rne : ∀ {a b : ℕ}, a < m → b < m → a ≠ b → D a ≠ D b :=
    fun {a b} ha hb hab => OddWheelArc.rim_ne hC hn hD hCm ha hb hab
  have rmem : ∀ t : ℕ, D t ∈ C := OddWheelArc.rim_mem hn hD
  have rsurj : ∀ {z : V}, z ∈ C → ∃ t, t < m ∧ z = D t :=
    fun {z} hz => OddWheelArc.rim_surj hC hn hD hCm hz
  have hD0 : D 0 = C[0]'(by omega) := (hDeq 0 (by omega)).symm
  have hD1 : D 1 = C[1]'(by omega) := (hDeq 1 (by omega)).symm
  have hD2 : D 2 = C[2]'(by omega) := (hDeq 2 (by omega)).symm
  have hDm : D (m - 1) = C[m - 1]'(by omega) := (hDeq (m - 1) (by omega)).symm
  have hDmod0 : D m = D 0 :=
    OddWheelArc.rim_congr hC hD (show m % C.length = 0 % C.length by rw [hCm]; simp)
  have hDmod1 : D (m + 1) = D 1 :=
    OddWheelArc.rim_congr hC hD
      (show (m + 1) % C.length = 1 % C.length by rw [hCm]; exact Nat.add_mod_left m 1)
  have hDmod3 : D (m + 3) = D 3 :=
    OddWheelArc.rim_congr hC hD
      (show (m + 3) % C.length = 3 % C.length by rw [hCm]; exact Nat.add_mod_left m 3)
  have hmeven : Even m := by
    have := hBerge.1 C hC
    simpa [holeLength, hCm] using this
  ---------------------------------------------------------------------------
  -- ###  `{p₃, …, p_m}` is `C.drop 2`
  ---------------------------------------------------------------------------
  have hdrop : ∀ w : V, w ∈ C.drop 2 ↔ ∃ t, 2 ≤ t ∧ t < m ∧ w = D t := by
    intro w
    constructor
    · intro hw
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hw
      rw [List.length_drop] at hj
      refine ⟨2 + j, by omega, by omega, ?_⟩
      rw [← hje, List.getElem_drop]
      exact (hDeq (2 + j) (by omega)).symm ▸ rfl
    · rintro ⟨t, ht2, htm, rfl⟩
      have hjm : t - 2 < (C.drop 2).length := by rw [List.length_drop]; omega
      have : (C.drop 2)[t - 2]'hjm = D t := by
        rw [List.getElem_drop]
        rw [HoleArithmetic.getElem_congr_idx C (by omega) (show t < C.length by omega)
          (show 2 + (t - 2) = t by omega)]
        exact hDeq t (by omega)
      rw [← this]
      exact List.getElem_mem hjm
  ---------------------------------------------------------------------------
  -- ###  the antipath `Q = p₁-q₁-⋯-q_n-p₂`
  ---------------------------------------------------------------------------
  have hQp : IsPathFrom Gᶜ Q (D 0) (D 1) := by rw [hD0, hD1]; exact hQ
  have hQpos : 0 < Q.length := PathBasics.path_length_pos hQp.1
  have hQlen5 : 5 ≤ Q.length := by
    have := PathBasics.pathLength_eq Q; omega
  set n : ℕ := (SPGT.interior Q).length with hndef
  have hQn : Q.length = n + 2 := by
    have := PathBasics.interior_length Q; omega
  have hn3 : 3 ≤ n := by omega
  have hnodd : Odd n := by
    have hpl : pathLength Q = n + 1 := by
      have := PathBasics.pathLength_eq Q; omega
    rw [hpl] at hQeven
    obtain ⟨k, hk⟩ := hQeven
    exact ⟨k - 1, by omega⟩
  have hQ0 : Q[0]'(by omega) = D 0 := PathBasics.getElem_zero_of_head? hQp.2.1 (by omega)
  have hQlast : Q[n + 1]'(by omega) = D 1 := by
    have h := PathBasics.getElem_last_of_getLast? hQp.2.2 hQpos
    rw [HoleArithmetic.getElem_congr_idx Q (show n + 1 < Q.length by omega)
      (show Q.length - 1 < Q.length by omega) (by omega)]
    exact h
  have hQadj : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length),
      (Gᶜ.Adj (Q[i]'hi) (Q[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := hQp.1.2.2
  have hQne : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i ≠ j →
      (Q[i]'hi) ≠ (Q[j]'hj) :=
    fun i j hi hj hij => PathBasics.path_ne_of_ne_index hQp.1 hi hj hij
  -- the `G`-adjacency reading of `Q`: non-consecutive positions are `G`-adjacent
  have hQGadj : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length), i ≠ j →
      (i + 1 ≠ j) → (j + 1 ≠ i) → G.Adj (Q[i]'hi) (Q[j]'hj) := by
    intro i j hi hj hij h1 h2
    by_contra hc
    exact absurd ((hQadj i j hi hj).mp
      (by rw [SimpleGraph.compl_adj]; exact ⟨hQne i j hi hj hij, hc⟩)) (by omega)
  have hQnotGadj : ∀ (i j : ℕ) (hi : i < Q.length) (hj : j < Q.length),
      (i + 1 = j ∨ j + 1 = i) → ¬ G.Adj (Q[i]'hi) (Q[j]'hj) := by
    intro i j hi hj hc
    exact not_adj_of_compl_adj ((hQadj i j hi hj).mpr hc)
  ---------------------------------------------------------------------------
  -- ###  `{q₁,…,q_{n−1}}` and `{q₂,…,q_n}` in terms of the indices of `Q`
  ---------------------------------------------------------------------------
  have hqsget : ∀ (j : ℕ) (hj : j < n), (SPGT.interior Q)[j]'(by omega) =
      Q[j + 1]'(by omega) := by
    intro j hj
    simp only [SPGT.interior, List.getElem_dropLast, List.getElem_tail]
  have hZ1 : ∀ x : V, x ∈ (SPGT.interior Q).dropLast ↔
      ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ i + 1 ≤ n ∧ (Q[i]'hi) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hx
      rw [List.length_dropLast] at hj
      refine ⟨j + 1, by omega, by omega, by omega, ?_⟩
      rw [← hje, List.getElem_dropLast, hqsget j (by omega)]
    · rintro ⟨i, hi, h1, h2, rfl⟩
      have hj : i - 1 < ((SPGT.interior Q).dropLast).length := by
        rw [List.length_dropLast]; omega
      have he : ((SPGT.interior Q).dropLast)[i - 1]'hj = Q[i]'hi := by
        rw [List.getElem_dropLast, hqsget (i - 1) (by omega)]
        exact HoleArithmetic.getElem_congr_idx Q (by omega) hi (by omega)
      rw [← he]
      exact List.getElem_mem hj
  have hZ2 : ∀ x : V, x ∈ (SPGT.interior Q).tail ↔
      ∃ (i : ℕ) (hi : i < Q.length), 2 ≤ i ∧ i ≤ n ∧ (Q[i]'hi) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hx
      rw [List.length_tail] at hj
      refine ⟨j + 2, by omega, by omega, by omega, ?_⟩
      rw [← hje, List.getElem_tail, hqsget (j + 1) (by omega)]
    · rintro ⟨i, hi, h1, h2, rfl⟩
      have hj : i - 2 < ((SPGT.interior Q).tail).length := by
        rw [List.length_tail]; omega
      have he : ((SPGT.interior Q).tail)[i - 2]'hj = Q[i]'hi := by
        rw [List.getElem_tail, hqsget (i - 2 + 1) (by omega)]
        exact HoleArithmetic.getElem_congr_idx Q (by omega) hi (by omega)
      rw [← he]
      exact List.getElem_mem hj
  have hVC1 : ∀ w : V, VertexComplete G w {x : V | x ∈ (SPGT.interior Q).dropLast} ↔
      ∀ (i : ℕ) (hi : i < Q.length), 1 ≤ i → i + 1 ≤ n → G.Adj w (Q[i]'hi) := by
    intro w
    constructor
    · intro h i hi h1 h2
      exact h _ ((hZ1 _).mpr ⟨i, hi, h1, h2, rfl⟩)
    · intro h y hy
      obtain ⟨i, hi, h1, h2, rfl⟩ := (hZ1 y).mp hy
      exact h i hi h1 h2
  have hVC2 : ∀ w : V, VertexComplete G w {x : V | x ∈ (SPGT.interior Q).tail} ↔
      ∀ (i : ℕ) (hi : i < Q.length), 2 ≤ i → i ≤ n → G.Adj w (Q[i]'hi) := by
    intro w
    constructor
    · intro h i hi h1 h2
      exact h _ ((hZ2 _).mpr ⟨i, hi, h1, h2, rfl⟩)
    · intro h y hy
      obtain ⟨i, hi, h1, h2, rfl⟩ := (hZ2 y).mp hy
      exact h i hi h1 h2
  have hZ1anti : AnticonnectedSet G {x : V | x ∈ (SPGT.interior Q).dropLast} := by
    have hset : {x : V | x ∈ (SPGT.interior Q).dropLast} =
        {x : V | x ∈ (Q.drop 1).take (n - 1 - 1 + 1)} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [hZ1 y, PathBasics.mem_slice_iff Q (show 1 ≤ n - 1 by omega)
        (show n - 1 < Q.length by omega)]
      constructor
      · rintro ⟨i, hi, h1, h2, rfl⟩; exact ⟨i, hi, h1, by omega, rfl⟩
      · rintro ⟨i, hi, h1, h2, rfl⟩; exact ⟨i, hi, h1, by omega, rfl⟩
    rw [hset]
    exact InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      (PathBasics.isPathList_slice hQp.1 (show 1 < n - 1 by omega)
        (show n - 1 < Q.length by omega))
  have hZ2anti : AnticonnectedSet G {x : V | x ∈ (SPGT.interior Q).tail} := by
    have hset : {x : V | x ∈ (SPGT.interior Q).tail} =
        {x : V | x ∈ (Q.drop 2).take (n - 2 + 1)} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [hZ2 y, PathBasics.mem_slice_iff Q (show 2 ≤ n by omega)
        (show n < Q.length by omega)]
    rw [hset]
    exact InducedPathExtraction.anticonnectedSet_setOf_mem_of_isAntipathList
      (PathBasics.isPathList_slice hQp.1 (show 2 < n by omega) (show n < Q.length by omega))
  have hZ0 : ∀ x : V, x ∈ SPGT.interior Q ↔
      ∃ (i : ℕ) (hi : i < Q.length), 1 ≤ i ∧ i ≤ n ∧ (Q[i]'hi) = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨j, hj, hje⟩ := List.getElem_of_mem hx
      exact ⟨j + 1, by omega, by omega, by omega, by rw [← hje, hqsget j (by omega)]⟩
    · rintro ⟨i, hi, h1, h2, rfl⟩
      have hj : i - 1 < (SPGT.interior Q).length := by omega
      have he : (SPGT.interior Q)[i - 1]'hj = Q[i]'hi := by
        rw [hqsget (i - 1) (by omega)]
        exact HoleArithmetic.getElem_congr_idx Q (by omega) hi (by omega)
      rw [← he]
      exact List.getElem_mem hj
  ---------------------------------------------------------------------------
  -- ###  the ends of `Q` against its interior
  ---------------------------------------------------------------------------
  have hp1adj : ∀ (k : ℕ) (hk : k < Q.length), 2 ≤ k → G.Adj (D 0) (Q[k]'hk) := by
    intro k hk h2
    rw [← hQ0]; exact hQGadj 0 k (by omega) hk (by omega) (by omega) (by omega)
  have hp2adj : ∀ (k : ℕ) (hk : k < Q.length), k + 1 ≤ n → G.Adj (D 1) (Q[k]'hk) := by
    intro k hk h2
    rw [← hQlast]; exact hQGadj (n + 1) k (by omega) hk (by omega) (by omega) (by omega)
  have hp1nadj : ¬ G.Adj (D 0) (Q[1]'(by omega)) := by
    rw [← hQ0]; exact hQnotGadj 0 1 (by omega) (by omega) (Or.inl rfl)
  have hp2nadj : ¬ G.Adj (D 1) (Q[n]'(by omega)) := by
    rw [← hQlast]; exact hQnotGadj (n + 1) n (by omega) (by omega) (Or.inr rfl)
  have hp2VC1 : VertexComplete G (D 1) {x : V | x ∈ (SPGT.interior Q).dropLast} :=
    (hVC1 (D 1)).mpr (fun k hk _ h2 => hp2adj k hk h2)
  have hp1VC2 : VertexComplete G (D 0) {x : V | x ∈ (SPGT.interior Q).tail} :=
    (hVC2 (D 0)).mpr (fun k hk h1 _ => hp1adj k hk h1)
  have hp1nVC1 : ¬ VertexComplete G (D 0) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
    intro h; exact hp1nadj ((hVC1 (D 0)).mp h 1 (by omega) (by omega) (by omega))
  have hp2nVC2 : ¬ VertexComplete G (D 1) {x : V | x ∈ (SPGT.interior Q).tail} := by
    intro h; exact hp2nadj ((hVC2 (D 1)).mp h n (by omega) (by omega) (by omega))
  have hqnVC1 : ¬ VertexComplete G (Q[n]'(by omega))
      {x : V | x ∈ (SPGT.interior Q).dropLast} := by
    intro h
    exact hQnotGadj n (n - 1) (by omega) (by omega) (Or.inr (by omega))
      ((hVC1 _).mp h (n - 1) (by omega) (by omega) (by omega))
  have hq1nVC2 : ¬ VertexComplete G (Q[1]'(by omega))
      {x : V | x ∈ (SPGT.interior Q).tail} := by
    intro h
    exact hQnotGadj 1 2 (by omega) (by omega) (Or.inl rfl)
      ((hVC2 _).mp h 2 (by omega) (by omega) (by omega))
  ---------------------------------------------------------------------------
  -- ###  the statement, read off the rim
  ---------------------------------------------------------------------------
  set Pt : ℕ → Prop := fun t =>
    VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast} ∨
      VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).tail} with hPtdef
  have final : (∀ t, 2 ≤ t → t < m → Pt t → (t = 2 ∨ t = m - 1)) ∧ ¬ (Pt 2 ∧ Pt (m - 1)) := by
    -- where a `qₖ` lying on the hole can sit
    have hposn : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k ≤ n → ∀ s, s < m →
        (Q[k]'hk) = D s → ((2 ≤ k → s = m - 1) ∧ (k + 1 ≤ n → s = 2)) := by
      intro k hk hk1 hkn s hs hks
      have hs0 : s ≠ 0 := by
        intro h; subst h
        exact hQne k 0 hk (by omega) (by omega) (by rw [hks, hQ0])
      have hs1 : s ≠ 1 := by
        intro h; subst h
        exact hQne k (n + 1) hk (by omega) (by omega) (by rw [hks, hQlast])
      refine ⟨fun h2 => ?_, fun h2 => ?_⟩
      · have hadj : G.Adj (D s) (D 0) := by
          rw [← hks, ← hQ0]
          exact hQGadj k 0 hk (by omega) (by omega) (by omega) (by omega)
        have := (radj hs (show 0 < m by omega)).mp hadj
        omega
      · have hadj : G.Adj (D s) (D 1) := by
          rw [← hks, ← hQlast]
          exact hQGadj k (n + 1) hk (by omega) (by omega) (by omega) (by omega)
        have := (radj hs (show 1 < m by omega)).mp hadj
        omega
    -- **15.5 applied to the arc `p_{a+1}-⋯-p_{b+1}` of the hole.**
    have h155arc : ∀ Z : Set V, (∀ y ∈ Z, y ∉ C) → AnticonnectedSet G Z →
        ∀ a b : ℕ, a < b → b - a + 2 ≤ m → 1 < b - a →
        VertexComplete G (D a) Z → VertexComplete G (D b) Z →
        (∀ s, a < s → s < b → ¬ VertexComplete G (D s) Z) → Even (b - a) := by
      intro Z hZC hZanti a b hab hlen hlen2 hA hB hint
      have hP : IsPathFrom G (OddWheelArc.arc C 0 a b) (D a) (D b) :=
        OddWheelArc.arc_isPathFrom' hC hn hD hCm (le_of_lt hab) hlen
      have hplen : pathLength (OddWheelArc.arc C 0 a b) = b - a := by
        rw [PathBasics.pathLength_eq, OddWheelArc.arc_length C 0 a b (by omega)]
        omega
      have h := Workspace.Statements.S15.SPGT.thm_15_5 G hG C hC Z hZC hZanti
        (OddWheelArc.arc C 0 a b) (D a) (D b) hP
        ⟨0 + a, Or.inl (List.take_prefix _ _)⟩ (by rw [hplen]; omega) hA hB ?_
      · rw [hplen] at h; exact h
      · intro w hw hwc
        have hwd := (PathBasics.mem_interior_iff_of_pathFrom hP).mp hw
        obtain ⟨s, hs1, hs2, rfl⟩ :=
          (OddWheelArc.arc_mem_iff hC hn hD hCm (le_of_lt hab) (by omega)).mp hwd.1
        have hsa : s ≠ a := fun h => hwd.2.1 (by rw [h])
        have hsb : s ≠ b := fun h => hwd.2.2 (by rw [h])
        exact hint s (by omega) (by omega) hwc
    by_cases hcase : ∃ x : V, x ∈ SPGT.interior Q ∧ x ∈ C
    · ---------------------------------------------------------------------
      -- ###  first paragraph: some `qᵢ` lies on the hole
      ---------------------------------------------------------------------
      obtain ⟨x, hxQ, hxC⟩ := hcase
      obtain ⟨i, hi, hi1, hin, rfl⟩ := (hZ0 x).mp hxQ
      obtain ⟨t, htm, hteq⟩ := rsurj hxC
      obtain ⟨hA1, hA2⟩ := hposn i hi hi1 hin t htm hteq
      have hor : i = 1 ∨ i = n := by
        by_contra hcon
        push Not at hcon
        have e1 := hA1 (by omega)
        have e2 := hA2 (by omega)
        omega
      rcases hor with rfl | rfl
      · ---------------------------------------------------------------
        -- ###  `q₁ = p₃`
        ---------------------------------------------------------------
        have ht2 : t = 2 := hA2 (by omega)
        subst ht2
        have hother : ∀ (k : ℕ) (hk : k < Q.length), 2 ≤ k → k ≤ n → (Q[k]'hk) ∉ C := by
          intro k hk hk1 hkn hkC
          obtain ⟨s, hs, hseq⟩ := rsurj hkC
          obtain ⟨hB1, hB2⟩ := hposn k hk (by omega) hkn s hs hseq
          have hsm : s = m - 1 := hB1 hk1
          have hkn' : k = n := by
            by_contra hne
            have := hB2 (by omega)
            omega
          have hadj : G.Adj (Q[1]'hi) (Q[k]'hk) :=
            hQGadj 1 k hi hk (by omega) (by omega) (by omega)
          rw [hteq, hseq, hsm] at hadj
          have := (radj (show 2 < m by omega) (show m - 1 < m by omega)).mp hadj
          omega
        have hZ2C : ∀ y : V, y ∈ {x : V | x ∈ (SPGT.interior Q).tail} → y ∉ C := by
          intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ2 y).mp hy
          exact hother k hk hk1 hkn
        have hnone : ∀ t', 3 ≤ t' → t' < m → ¬ Pt t' := by
          intro t' h3 htm' hP
          rcases Nat.lt_or_ge t' 4 with hlt | hge
          · -- `t' = 3`:  15.5 on the path `p₄-p₃-p₂-p₁`
            have ht3 : t' = 3 := by omega
            subst ht3
            have hPrev : IsPathFrom G (OddWheelArc.arc C 0 0 3).reverse (D 3) (D 0) :=
              OddWheelArc.arc_rev_isPathFrom hC hn hD hCm (by omega) (by omega)
            have hlen4 : (OddWheelArc.arc C 0 0 3).length = 4 := by
              rw [OddWheelArc.arc_length C 0 0 3 (by omega)]
            have hplen : pathLength (OddWheelArc.arc C 0 0 3).reverse = 3 := by
              rw [PathBasics.pathLength_reverse, PathBasics.pathLength_eq, hlen4]
            have hnVC2 : ¬ VertexComplete G (D 3) {x : V | x ∈ (SPGT.interior Q).tail} := by
              intro hc
              have h155 := Workspace.Statements.S15.SPGT.thm_15_5 G hG C hC
                {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti
                (OddWheelArc.arc C 0 0 3).reverse (D 3) (D 0) hPrev
                ⟨0 + 0, Or.inr (by rw [List.reverse_reverse]; exact List.take_prefix _ _)⟩
                (by rw [hplen]; omega) hc hp1VC2 ?_
              · rw [hplen] at h155
                obtain ⟨k, hk⟩ := h155; omega
              · intro w hw hwc
                rw [PathBasics.mem_interior_reverse] at hw
                obtain ⟨s, hs1, hs2, rfl⟩ :=
                  (OddWheelArc.arc_mem_iff hC hn hD hCm (show (0:ℕ) ≤ 3 by omega)
                    (by omega)).mp (PathBasics.interior_subset hw)
                have hwd := (PathBasics.mem_interior_iff_of_pathFrom
                  (OddWheelArc.arc_isPathFrom' hC hn hD hCm (show (0:ℕ) ≤ 3 by omega)
                    (by omega))).mp hw
                have hne0 : D s ≠ D 0 := hwd.2.1
                have hne3 : D s ≠ D 3 := hwd.2.2
                have hs12 : s = 1 ∨ s = 2 := by
                  rcases Nat.lt_or_ge s 1 with h | h
                  · exact absurd (show D s = D 0 by rw [show s = 0 by omega]) hne0
                  rcases Nat.lt_or_ge s 3 with h' | h'
                  · omega
                  · exact absurd (show D s = D 3 by rw [show s = 3 by omega]) hne3
                rcases hs12 with rfl | rfl
                · exact hp2nVC2 hwc
                · exact hq1nVC2 (by rw [hteq]; exact hwc)
            have hVC1 : VertexComplete G (D 3) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
              rcases hP with h | h
              · exact h
              · exact absurd h hnVC2
            -- the odd antihole `p₄-p₁-q₁-⋯-qₙ-p₄`
            have hnadjqn : ¬ G.Adj (D 3) (Q[n]'(by omega)) := by
              intro hadj
              refine hnVC2 ((hVC2 _).mpr ?_)
              intro k hk h2 h3
              rcases Nat.lt_or_ge k n with h | h
              · exact hVC1 _ ((hZ1 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
              · rw [HoleArithmetic.getElem_congr_idx Q hk (show n < Q.length by omega)
                  (by omega)]
                exact hadj
            have hslice : IsAntipathFrom G ((Q.drop 0).take (n - 0 + 1))
                (Q[0]'(by omega)) (Q[n]'(by omega)) :=
              PathBasics.isPathFrom_slice hQp.1 (show 0 < n by omega)
                (show n < Q.length by omega)
            have hsl : pathLength ((Q.drop 0).take (n - 0 + 1)) = n := by
              rw [PathBasics.pathLength_eq,
                PathBasics.length_slice Q (show (0:ℕ) ≤ n by omega)
                  (show n < Q.length by omega)]
              omega
            refine odd_antihole_absurd (w := D 3) hBerge hslice (by omega) ?_ ?_ ?_ ?_ ?_ ?_
              (by rw [hsl]; exact hnodd)
            · rw [hQ0]; exact rne (by omega) (by omega) (by omega)
            · rw [hQ0]
              intro hadj
              have := (radj (show 3 < m by omega) (show 0 < m by omega)).mp hadj
              omega
            · exact fun h => hother n (by omega) (by omega) (by omega) (h ▸ rmem 3)
            · exact hnadjqn
            · intro hmem
              obtain ⟨k, hk, hk0, hkn, hke⟩ :=
                (PathBasics.mem_slice_iff Q (show (0:ℕ) ≤ n by omega)
                  (show n < Q.length by omega)).mp hmem
              rcases Nat.lt_or_ge k 1 with h | h
              · have he : (Q[0]'(by omega) : V) = D 3 := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
                rw [hQ0] at he
                exact rne (by omega) (by omega) (by omega) he
              rcases Nat.lt_or_ge k 2 with h' | h'
              · have he : (Q[1]'hi : V) = D 3 := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q hi hk (by omega)
                rw [hteq] at he
                exact rne (show (2:ℕ) < m by omega) (show (3:ℕ) < m by omega) (by omega) he
              · exact hother k hk h' hkn (hke ▸ rmem 3)
            · intro y hy
              obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
                (PathBasics.mem_interior_slice_iff hQp.1 (show 0 < n by omega)
                  (show n < Q.length by omega)).mp hy
              exact hVC1 _ ((hZ1 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
          · -- `t' ≥ 4`:  `p_{t'+1}` is not adjacent to `q₁ = p₃`
            have hnadjq1 : ¬ G.Adj (D t') (Q[1]'hi) := by
              rw [hteq]
              intro hadj
              have := (radj (show t' < m by omega) (show 2 < m by omega)).mp hadj
              omega
            have hVC2' : VertexComplete G (D t') {x : V | x ∈ (SPGT.interior Q).tail} := by
              rcases hP with h | h
              · exact absurd ((hVC1 _).mp h 1 hi (by omega) (by omega)) hnadjq1
              · exact h
            have hslice : IsAntipathFrom G ((Q.drop 1).take (n + 1 - 1 + 1))
                (Q[1]'(by omega)) (Q[n + 1]'(by omega)) :=
              PathBasics.isPathFrom_slice hQp.1 (show 1 < n + 1 by omega)
                (show n + 1 < Q.length by omega)
            have hsl : pathLength ((Q.drop 1).take (n + 1 - 1 + 1)) = n := by
              rw [PathBasics.pathLength_eq,
                PathBasics.length_slice Q (show (1:ℕ) ≤ n + 1 by omega)
                  (show n + 1 < Q.length by omega)]
              omega
            refine odd_antihole_absurd (w := D t') hBerge hslice (by omega) ?_ ?_ ?_ ?_ ?_ ?_
              (by rw [hsl]; exact hnodd)
            · rw [hteq]; exact rne (by omega) (by omega) (by omega)
            · exact hnadjq1
            · rw [hQlast]; exact rne (by omega) (by omega) (by omega)
            · rw [hQlast]
              intro hadj
              have := (radj (show t' < m by omega) (show 1 < m by omega)).mp hadj
              omega
            · intro hmem
              obtain ⟨k, hk, hk0, hkn, hke⟩ :=
                (PathBasics.mem_slice_iff Q (show (1:ℕ) ≤ n + 1 by omega)
                  (show n + 1 < Q.length by omega)).mp hmem
              rcases Nat.lt_or_ge k 2 with h | h
              · have he : (Q[1]'hi : V) = D t' := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q hi hk (by omega)
                rw [hteq] at he
                exact rne (show (2:ℕ) < m by omega) (show t' < m by omega) (by omega) he
              rcases Nat.lt_or_ge k (n + 1) with h' | h'
              · exact hother k hk h (by omega) (hke ▸ rmem t')
              · have he : (Q[n + 1]'(by omega) : V) = D t' := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
                rw [hQlast] at he
                exact rne (show (1:ℕ) < m by omega) (show t' < m by omega) (by omega) he
            · intro y hy
              obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
                (PathBasics.mem_interior_slice_iff hQp.1 (show 1 < n + 1 by omega)
                  (show n + 1 < Q.length by omega)).mp hy
              exact hVC2' _ ((hZ2 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
        exact ⟨fun s hs2 hsm hPs => Or.inl (by by_contra hne; exact hnone s (by omega) hsm hPs),
          fun h => hnone (m - 1) (by omega) (by omega) h.2⟩
      · ---------------------------------------------------------------
        -- ###  `q_n = p_m`
        ---------------------------------------------------------------
        have htm1 : t = m - 1 := hA1 (by omega)
        subst htm1
        have hother : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k + 1 ≤ n → (Q[k]'hk) ∉ C := by
          intro k hk hk1 hkn hkC
          obtain ⟨s, hs, hseq⟩ := rsurj hkC
          obtain ⟨hB1, hB2⟩ := hposn k hk hk1 (by omega) s hs hseq
          have hs2 : s = 2 := hB2 hkn
          have hk1' : k = 1 := by
            by_contra hne
            have := hB1 (by omega)
            omega
          have hadj : G.Adj (Q[k]'hk) (Q[n]'hi) :=
            hQGadj k n hk hi (by omega) (by omega) (by omega)
          rw [hseq, hteq, hs2] at hadj
          have := (radj (show 2 < m by omega) (show m - 1 < m by omega)).mp hadj
          omega
        have hZ1C : ∀ y : V, y ∈ {x : V | x ∈ (SPGT.interior Q).dropLast} → y ∉ C := by
          intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ1 y).mp hy
          exact hother k hk hk1 hkn
        have hnone : ∀ t', 2 ≤ t' → t' + 2 ≤ m → ¬ Pt t' := by
          intro t' h2 hle hP
          rcases Nat.lt_or_ge (t' + 2) m with hlt | hge
          · -- `t' ≤ m − 3`
            have hnadjqn : ¬ G.Adj (D t') (Q[n]'hi) := by
              rw [hteq]
              intro hadj
              have := (radj (show t' < m by omega) (show m - 1 < m by omega)).mp hadj
              omega
            have hVCa : VertexComplete G (D t') {x : V | x ∈ (SPGT.interior Q).dropLast} := by
              rcases hP with h | h
              · exact h
              · exact absurd ((hVC2 _).mp h n hi (by omega) (by omega)) hnadjqn
            have hslice : IsAntipathFrom G ((Q.drop 0).take (n - 0 + 1))
                (Q[0]'(by omega)) (Q[n]'(by omega)) :=
              PathBasics.isPathFrom_slice hQp.1 (show 0 < n by omega)
                (show n < Q.length by omega)
            have hsl : pathLength ((Q.drop 0).take (n - 0 + 1)) = n := by
              rw [PathBasics.pathLength_eq,
                PathBasics.length_slice Q (show (0:ℕ) ≤ n by omega)
                  (show n < Q.length by omega)]
              omega
            refine odd_antihole_absurd (w := D t') hBerge hslice (by omega) ?_ ?_ ?_ ?_ ?_ ?_
              (by rw [hsl]; exact hnodd)
            · rw [hQ0]; exact rne (by omega) (by omega) (by omega)
            · rw [hQ0]
              intro hadj
              have := (radj (show t' < m by omega) (show 0 < m by omega)).mp hadj
              omega
            · rw [hteq]; exact rne (by omega) (by omega) (by omega)
            · exact hnadjqn
            · intro hmem
              obtain ⟨k, hk, hk0, hkn, hke⟩ :=
                (PathBasics.mem_slice_iff Q (show (0:ℕ) ≤ n by omega)
                  (show n < Q.length by omega)).mp hmem
              rcases Nat.lt_or_ge k 1 with h | h
              · have he : (Q[0]'(by omega) : V) = D t' := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
                rw [hQ0] at he
                exact rne (by omega) (show t' < m by omega) (by omega) he
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h' | h'
              · exact hother k hk h (by omega) (hke ▸ rmem t')
              · have he : (Q[n]'hi : V) = D t' := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q hi hk (by omega)
                rw [hteq] at he
                exact rne (show m - 1 < m by omega) (show t' < m by omega) (by omega) he
            · intro y hy
              obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
                (PathBasics.mem_interior_slice_iff hQp.1 (show 0 < n by omega)
                  (show n < Q.length by omega)).mp hy
              exact hVCa _ ((hZ1 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
          · -- `t' = m − 2`:  15.5 on the path `p_{m−1}-p_m-p₁-p₂`
            have ht' : t' = m - 2 := by omega
            subst ht'
            have hDm1 : D (m + 1) = D 1 :=
              OddWheelArc.rim_congr hC hD
                (show (m + 1) % C.length = 1 % C.length by rw [hCm]; exact Nat.add_mod_left m 1)
            have hDm0 : D m = D 0 :=
              OddWheelArc.rim_congr hC hD
                (show m % C.length = 0 % C.length by rw [hCm]; simp)
            have hP4 : IsPathFrom G (OddWheelArc.arc C 0 (m - 2) (m + 1)) (D (m - 2))
                (D (m + 1)) :=
              OddWheelArc.arc_isPathFrom' hC hn hD hCm (by omega) (by omega)
            have hplen : pathLength (OddWheelArc.arc C 0 (m - 2) (m + 1)) = 3 := by
              rw [PathBasics.pathLength_eq,
                OddWheelArc.arc_length C 0 (m - 2) (m + 1) (by omega)]
              omega
            have hnVC1 : ¬ VertexComplete G (D (m - 2))
                {x : V | x ∈ (SPGT.interior Q).dropLast} := by
              intro hc
              have h155 := Workspace.Statements.S15.SPGT.thm_15_5 G hG C hC
                {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti
                (OddWheelArc.arc C 0 (m - 2) (m + 1)) (D (m - 2)) (D (m + 1)) hP4
                ⟨0 + (m - 2), Or.inl (List.take_prefix _ _)⟩
                (by rw [hplen]; omega) hc (by rw [hDm1]; exact hp2VC1) ?_
              · rw [hplen] at h155
                obtain ⟨k, hk⟩ := h155; omega
              · intro w hw hwc
                have hwd := (PathBasics.mem_interior_iff_of_pathFrom hP4).mp hw
                obtain ⟨s, hs1, hs2, rfl⟩ :=
                  (OddWheelArc.arc_mem_iff hC hn hD hCm (show m - 2 ≤ m + 1 by omega)
                    (by omega)).mp hwd.1
                have hne1 : D s ≠ D (m - 2) := hwd.2.1
                have hne2 : D s ≠ D (m + 1) := hwd.2.2
                have hs12 : s = m - 1 ∨ s = m := by
                  rcases Nat.lt_or_ge s (m - 1) with h | h
                  · exact absurd (show D s = D (m - 2) by rw [show s = m - 2 by omega]) hne1
                  rcases Nat.lt_or_ge s (m + 1) with h' | h'
                  · omega
                  · exact absurd (show D s = D (m + 1) by rw [show s = m + 1 by omega]) hne2
                rcases hs12 with rfl | rfl
                · exact hqnVC1 (by rw [hteq]; exact hwc)
                · exact hp1nVC1 (by rw [← hDm0]; exact hwc)
            have hVCb : VertexComplete G (D (m - 2)) {x : V | x ∈ (SPGT.interior Q).tail} := by
              rcases hP with h | h
              · exact absurd h hnVC1
              · exact h
            have hnadjq1 : ¬ G.Adj (D (m - 2)) (Q[1]'(by omega)) := by
              intro hadj
              refine hnVC1 ((hVC1 _).mpr ?_)
              intro k hk h1 h2
              rcases Nat.lt_or_ge k 2 with h | h
              · rw [HoleArithmetic.getElem_congr_idx Q hk (show 1 < Q.length by omega)
                  (by omega)]
                exact hadj
              · exact hVCb _ ((hZ2 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
            have hslice : IsAntipathFrom G ((Q.drop 1).take (n + 1 - 1 + 1))
                (Q[1]'(by omega)) (Q[n + 1]'(by omega)) :=
              PathBasics.isPathFrom_slice hQp.1 (show 1 < n + 1 by omega)
                (show n + 1 < Q.length by omega)
            have hsl : pathLength ((Q.drop 1).take (n + 1 - 1 + 1)) = n := by
              rw [PathBasics.pathLength_eq,
                PathBasics.length_slice Q (show (1:ℕ) ≤ n + 1 by omega)
                  (show n + 1 < Q.length by omega)]
              omega
            refine odd_antihole_absurd (w := D (m - 2)) hBerge hslice (by omega) ?_ ?_ ?_ ?_
              ?_ ?_ (by rw [hsl]; exact hnodd)
            · exact fun h => hother 1 (by omega) (by omega) (by omega) (h ▸ rmem (m - 2))
            · exact hnadjq1
            · rw [hQlast]; exact rne (by omega) (by omega) (by omega)
            · rw [hQlast]
              intro hadj
              have := (radj (show m - 2 < m by omega) (show 1 < m by omega)).mp hadj
              omega
            · intro hmem
              obtain ⟨k, hk, hk0, hkn, hke⟩ :=
                (PathBasics.mem_slice_iff Q (show (1:ℕ) ≤ n + 1 by omega)
                  (show n + 1 < Q.length by omega)).mp hmem
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
              · exact hother k hk hk0 (by omega) (hke ▸ rmem (m - 2))
              rcases Nat.lt_or_ge k (n + 1) with h' | h'
              · have he : (Q[n]'hi : V) = D (m - 2) := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q hi hk (by omega)
                rw [hteq] at he
                exact rne (show m - 1 < m by omega) (show m - 2 < m by omega) (by omega) he
              · have he : (Q[n + 1]'(by omega) : V) = D (m - 2) := by
                  rw [← hke]
                  exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
                rw [hQlast] at he
                exact rne (show (1:ℕ) < m by omega) (show m - 2 < m by omega) (by omega) he
            · intro y hy
              obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
                (PathBasics.mem_interior_slice_iff hQp.1 (show 1 < n + 1 by omega)
                  (show n + 1 < Q.length by omega)).mp hy
              exact hVCb _ ((hZ2 _).mpr ⟨k, hk, by omega, by omega, rfl⟩)
        exact ⟨fun s hs2 hsm hPs => Or.inr (by by_contra hne; exact hnone s (by omega) (by omega) hPs),
          fun h => hnone 2 (by omega) (by omega) h.1⟩
    · -------------------------------------------------------------------
      -- ###  *"So we may assume that none of `q₁,…,q_n` belong to `C`."*
      -------------------------------------------------------------------
      have hQC : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k ≤ n → (Q[k]'hk) ∉ C := by
        intro k hk h1 h2 hkC
        exact hcase ⟨Q[k]'hk, (hZ0 _).mpr ⟨k, hk, h1, h2, rfl⟩, hkC⟩
      have hZ1C : ∀ y ∈ {x : V | x ∈ (SPGT.interior Q).dropLast}, y ∉ C := by
        intro y hy
        obtain ⟨k, hk, h1, h2, rfl⟩ := (hZ1 y).mp hy
        exact hQC k hk h1 (by omega)
      have hZ2C : ∀ y ∈ {x : V | x ∈ (SPGT.interior Q).tail}, y ∉ C := by
        intro y hy
        obtain ⟨k, hk, h1, h2, rfl⟩ := (hZ2 y).mp hy
        exact hQC k hk (by omega) h2
      -- the two antipath slices used by every antihole below
      have hsliceA : IsAntipathFrom G ((Q.drop 0).take (n - 0 + 1))
          (Q[0]'(by omega)) (Q[n]'(by omega)) :=
        PathBasics.isPathFrom_slice hQp.1 (show 0 < n by omega) (show n < Q.length by omega)
      have hslA : pathLength ((Q.drop 0).take (n - 0 + 1)) = n := by
        rw [PathBasics.pathLength_eq,
          PathBasics.length_slice Q (show (0:ℕ) ≤ n by omega) (show n < Q.length by omega)]
        omega
      have hsliceB : IsAntipathFrom G ((Q.drop 1).take (n + 1 - 1 + 1))
          (Q[1]'(by omega)) (Q[n + 1]'(by omega)) :=
        PathBasics.isPathFrom_slice hQp.1 (show 1 < n + 1 by omega)
          (show n + 1 < Q.length by omega)
      have hslB : pathLength ((Q.drop 1).take (n + 1 - 1 + 1)) = n := by
        rw [PathBasics.pathLength_eq,
          PathBasics.length_slice Q (show (1:ℕ) ≤ n + 1 by omega)
            (show n + 1 < Q.length by omega)]
        omega
      -------------------------------------------------------------------
      -- ###  (1)  `Y₁ ⊆ Y₂ ∪ {p_m}`, and `Y₂ ⊆ Y₁ ∪ {p₃}`
      -------------------------------------------------------------------
      have hcl1 : ∀ t, 2 ≤ t → t < m →
          VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast} →
          (VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).tail} ∨ t = m - 1) := by
        intro t h2 htm h1
        by_contra hcon
        push Not at hcon
        obtain ⟨hnot2, htne⟩ := hcon
        have hqn : ¬ G.Adj (D t) (Q[n]'(by omega)) := by
          intro hadj
          refine hnot2 ((hVC2 _).mpr ?_)
          intro k hk hk2 hkn
          rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
          · exact (hVC1 _).mp h1 k hk (by omega) (by omega)
          · rw [HoleArithmetic.getElem_congr_idx Q hk (show n < Q.length by omega) (by omega)]
            exact hadj
        refine odd_antihole_absurd (w := D t) hBerge hsliceA (by omega) ?_ ?_ ?_ ?_ ?_ ?_
          (by rw [hslA]; exact hnodd)
        · rw [hQ0]; exact rne (by omega) (by omega) (by omega)
        · rw [hQ0]
          intro hadj
          have := (radj (show t < m by omega) (show 0 < m by omega)).mp hadj
          omega
        · exact fun h => hQC n (by omega) (by omega) (by omega) (h ▸ rmem t)
        · exact hqn
        · intro hmem
          obtain ⟨k, hk, hk0, hkn, hke⟩ :=
            (PathBasics.mem_slice_iff Q (show (0:ℕ) ≤ n by omega)
              (show n < Q.length by omega)).mp hmem
          rcases Nat.lt_or_ge k 1 with h | h
          · have he : (Q[0]'(by omega) : V) = D t := by
              rw [← hke]; exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
            rw [hQ0] at he
            exact rne (by omega) (show t < m by omega) (by omega) he
          · exact hQC k hk h hkn (hke ▸ rmem t)
        · intro y hy
          obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
            (PathBasics.mem_interior_slice_iff hQp.1 (show 0 < n by omega)
              (show n < Q.length by omega)).mp hy
          exact (hVC1 _).mp h1 k hk (by omega) (by omega)
      have hcl2 : ∀ t, 2 ≤ t → t < m →
          VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).tail} →
          (VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast} ∨ t = 2) := by
        intro t h2 htm h1
        by_contra hcon
        push Not at hcon
        obtain ⟨hnot1, htne⟩ := hcon
        have hq1 : ¬ G.Adj (D t) (Q[1]'(by omega)) := by
          intro hadj
          refine hnot1 ((hVC1 _).mpr ?_)
          intro k hk hk1 hkn
          rcases Nat.lt_or_ge k 2 with h | h
          · rw [HoleArithmetic.getElem_congr_idx Q hk (show 1 < Q.length by omega) (by omega)]
            exact hadj
          · exact (hVC2 _).mp h1 k hk (by omega) (by omega)
        refine odd_antihole_absurd (w := D t) hBerge hsliceB (by omega) ?_ ?_ ?_ ?_ ?_ ?_
          (by rw [hslB]; exact hnodd)
        · exact fun h => hQC 1 (by omega) (by omega) (by omega) (h ▸ rmem t)
        · exact hq1
        · rw [hQlast]; exact rne (by omega) (by omega) (by omega)
        · rw [hQlast]
          intro hadj
          have := (radj (show t < m by omega) (show 1 < m by omega)).mp hadj
          omega
        · intro hmem
          obtain ⟨k, hk, hk0, hkn, hke⟩ :=
            (PathBasics.mem_slice_iff Q (show (1:ℕ) ≤ n + 1 by omega)
              (show n + 1 < Q.length by omega)).mp hmem
          rcases Nat.lt_or_ge k (n + 1) with h | h
          · exact hQC k hk hk0 (by omega) (hke ▸ rmem t)
          · have he : (Q[n + 1]'(by omega) : V) = D t := by
              rw [← hke]; exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
            rw [hQlast] at he
            exact rne (by omega) (show t < m by omega) (by omega) he
        · intro y hy
          obtain ⟨k, hk, hk0, hkn, rfl⟩ :=
            (PathBasics.mem_interior_slice_iff hQp.1 (show 1 < n + 1 by omega)
              (show n + 1 < Q.length by omega)).mp hy
          exact (hVC2 _).mp h1 k hk (by omega) (by omega)
      -------------------------------------------------------------------
      -- ###  the odd antihole `p₃-q₁-⋯-q_n-p_m-p₃`
      -------------------------------------------------------------------
      have hantiK : VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail} →
          ¬ VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).dropLast} →
          VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).dropLast} →
          ¬ VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).tail} → False := by
        intro h2VC2 h2nVC1 hmVC1 hmnVC2
        have hnq1 : ¬ G.Adj (D 2) (Q[1]'(by omega)) := by
          intro hadj
          refine h2nVC1 ((hVC1 _).mpr ?_)
          intro k hk hk1 hkn
          rcases Nat.lt_or_ge k 2 with h | h
          · rw [HoleArithmetic.getElem_congr_idx Q hk (show 1 < Q.length by omega) (by omega)]
            exact hadj
          · exact (hVC2 _).mp h2VC2 k hk (by omega) (by omega)
        have hnqn : ¬ G.Adj (D (m - 1)) (Q[n]'(by omega)) := by
          intro hadj
          refine hmnVC2 ((hVC2 _).mpr ?_)
          intro k hk hk2 hkn
          rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
          · exact (hVC1 _).mp hmVC1 k hk (by omega) (by omega)
          · rw [HoleArithmetic.getElem_congr_idx Q hk (show n < Q.length by omega) (by omega)]
            exact hadj
        have hsliceC : IsAntipathFrom G ((Q.drop 1).take (n - 1 + 1))
            (Q[1]'(by omega)) (Q[n]'(by omega)) :=
          PathBasics.isPathFrom_slice hQp.1 (show 1 < n by omega) (show n < Q.length by omega)
        have hslC : pathLength ((Q.drop 1).take (n - 1 + 1)) = n - 1 := by
          rw [PathBasics.pathLength_eq,
            PathBasics.length_slice Q (show (1:ℕ) ≤ n by omega) (show n < Q.length by omega)]
          omega
        have hmemC : ∀ y : V, y ∈ (Q.drop 1).take (n - 1 + 1) →
            ∃ (k : ℕ) (hk : k < Q.length), 1 ≤ k ∧ k ≤ n ∧ (Q[k]'hk) = y :=
          fun y hy => (PathBasics.mem_slice_iff Q (show (1:ℕ) ≤ n by omega)
            (show n < Q.length by omega)).mp hy
        refine odd_antihole_absurd_two (s := D 2) (t := D (m - 1)) hBerge hsliceC (by omega)
          ?_ hnq1 ?_ hnqn ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
          (by rw [hslC]; obtain ⟨k, hk⟩ := hnodd; exact ⟨k, by omega⟩)
        · exact fun h => hQC 1 (by omega) (by omega) (by omega) (h ▸ rmem 2)
        · exact fun h => hQC n (by omega) (by omega) (by omega) (h ▸ rmem (m - 1))
        · exact rne (by omega) (by omega) (by omega)
        · intro hadj
          have := (radj (show 2 < m by omega) (show m - 1 < m by omega)).mp hadj
          omega
        · intro hmem
          obtain ⟨k, hk, hk1, hkn, hke⟩ := hmemC _ hmem
          exact hQC k hk hk1 hkn (hke ▸ rmem 2)
        · intro hmem
          obtain ⟨k, hk, hk1, hkn, hke⟩ := hmemC _ hmem
          exact hQC k hk hk1 hkn (hke ▸ rmem (m - 1))
        · exact (hVC2 _).mp h2VC2 n (by omega) (by omega) (by omega)
        · exact (hVC1 _).mp hmVC1 1 (by omega) (by omega) (by omega)
        · intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ :=
            (PathBasics.mem_interior_slice_iff hQp.1 (show 1 < n by omega)
              (show n < Q.length by omega)).mp hy
          exact (hVC2 _).mp h2VC2 k hk (by omega) (by omega)
        · intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ :=
            (PathBasics.mem_interior_slice_iff hQp.1 (show 1 < n by omega)
              (show n < Q.length by omega)).mp hy
          exact (hVC1 _).mp hmVC1 k hk (by omega) (by omega)
      -------------------------------------------------------------------
      -- ###  *"not both `p₃, p_m` are in `Y₁ ∩ Y₂`"*
      -------------------------------------------------------------------
      have hnotboth : ¬ ((VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
            VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail}) ∧
          (VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
            VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).tail})) := by
        rintro ⟨⟨h21, h22⟩, hm1, hm2⟩
        have hall2 : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k ≤ n → G.Adj (D 2) (Q[k]'hk) := by
          intro k hk h1 h2
          rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
          · exact (hVC1 _).mp h21 k hk h1 (by omega)
          · exact (hVC2 _).mp h22 k hk (by omega) h2
        have hallm : ∀ (k : ℕ) (hk : k < Q.length), 1 ≤ k → k ≤ n →
            G.Adj (D (m - 1)) (Q[k]'hk) := by
          intro k hk h1 h2
          rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
          · exact (hVC1 _).mp hm1 k hk h1 (by omega)
          · exact (hVC2 _).mp hm2 k hk (by omega) h2
        have hnotQ : ∀ (w : ℕ), 2 ≤ w → w < m → D w ∉ Q := by
          intro w hw2 hwm hmem
          obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hmem
          rcases Nat.lt_or_ge k 1 with h | h
          · have he : (Q[0]'(by omega) : V) = D w := by
              rw [← hke]; exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
            rw [hQ0] at he
            exact rne (by omega) (show w < m by omega) (by omega) he
          rcases Nat.lt_or_ge k (n + 1) with h' | h'
          · exact hQC k hk h (by omega) (hke ▸ rmem w)
          · have he : (Q[n + 1]'(by omega) : V) = D w := by
              rw [← hke]; exact HoleArithmetic.getElem_congr_idx Q (by omega) hk (by omega)
            rw [hQlast] at he
            exact rne (by omega) (show w < m by omega) (by omega) he
        refine odd_antihole_absurd_two (s := D 2) (t := D (m - 1)) hBerge hQp (by omega)
          ?_ ?_ ?_ ?_ ?_ ?_ (hnotQ 2 (by omega) (by omega)) (hnotQ (m - 1) (by omega) (by omega))
          ?_ ?_ ?_ ?_ hQeven
        · exact rne (by omega) (by omega) (by omega)
        · intro hadj
          have := (radj (show 2 < m by omega) (show 0 < m by omega)).mp hadj
          omega
        · exact rne (by omega) (by omega) (by omega)
        · intro hadj
          have := (radj (show m - 1 < m by omega) (show 1 < m by omega)).mp hadj
          omega
        · exact rne (by omega) (by omega) (by omega)
        · intro hadj
          have := (radj (show 2 < m by omega) (show m - 1 < m by omega)).mp hadj
          omega
        · exact (radj (show 2 < m by omega) (show 1 < m by omega)).mpr (Or.inr (Or.inl rfl))
        · exact (radj (show m - 1 < m by omega) (show 0 < m by omega)).mpr
            (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))
        · intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ0 y).mp hy
          exact hall2 k hk hk1 hkn
        · intro y hy
          obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ0 y).mp hy
          exact hallm k hk hk1 hkn
      -------------------------------------------------------------------
      -- ###  (2)  *"If `Y₁ ⊄ {p_m}` then `p₃ ∈ Y₁ ∩ Y₂`"*
      -------------------------------------------------------------------
      have hcl3 : (∃ t, 2 ≤ t ∧ t + 2 ≤ m ∧
            VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast}) →
          (VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
            VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail}) := by
        intro hex
        obtain ⟨tt, ⟨htt2, httm, httVC1⟩, httmin⟩ :
            ∃ tt, (2 ≤ tt ∧ tt + 2 ≤ m ∧
                VertexComplete G (D tt) {x : V | x ∈ (SPGT.interior Q).dropLast}) ∧
              ∀ s, s < tt → ¬ (2 ≤ s ∧ s + 2 ≤ m ∧
                VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).dropLast}) :=
          ⟨Nat.find hex, Nat.find_spec hex, fun s hs => Nat.find_min hex hs⟩
        have httVC2 : VertexComplete G (D tt) {x : V | x ∈ (SPGT.interior Q).tail} := by
          rcases hcl1 tt htt2 (by omega) httVC1 with h | h
          · exact h
          · omega
        by_cases htt : tt = 2
        · rw [htt] at httVC1 httVC2; exact ⟨httVC1, httVC2⟩
        exfalso
        have htt3 : 3 ≤ tt := by omega
        -- (a)  *"By 15.5 applied to the anticonnected set `X \ {q_n}`, `i` is even."*
        have httodd : Odd tt := by
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti 1 tt
            (by omega) (by omega) (by omega) hp2VC1 httVC1
            (fun s h1 h2 hs => httmin s h2 ⟨by omega, by omega, hs⟩)
          obtain ⟨k, hk⟩ := h
          exact ⟨k, by omega⟩
        -- (b)  *"The path `p₁-⋯-p_i` is odd … so by 15.5 it contains another in its interior."*
        obtain ⟨s0, hs01, hs02, hs0VC2⟩ : ∃ s, 0 < s ∧ s < tt ∧
            VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).tail} := by
          by_contra hcon
          push Not at hcon
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti 0 tt
            (by omega) (by omega) (by omega) hp1VC2 httVC2
            (fun s h1 h2 => hcon s h1 h2)
          obtain ⟨k, hk⟩ := h
          obtain ⟨j, hj⟩ := httodd
          omega
        -- (c)  *"From the minimality of `i`, `p_h ∉ Y₁`, so by (1) `h = 3`."*
        have hs0ne1 : s0 ≠ 1 := by
          intro h; rw [h] at hs0VC2; exact hp2nVC2 hs0VC2
        have hs0eq : s0 = 2 := by
          rcases hcl2 s0 (by omega) (by omega) hs0VC2 with h | h
          · exact (httmin s0 hs02 ⟨by omega, by omega, h⟩).elim
          · exact h
        have h2VC2 : VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail} := by
          rw [← hs0eq]; exact hs0VC2
        have h2nVC1 : ¬ VertexComplete G (D 2)
            {x : V | x ∈ (SPGT.interior Q).dropLast} := fun hc =>
          httmin 2 (by omega) ⟨by omega, by omega, hc⟩
        -- (d)  *"15.5 applied to the path `p₃-⋯-p_i` implies that `i = 4`."*
        have htteq : tt = 3 := by
          by_contra hne
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti 2 tt
            (by omega) (by omega) (by omega) h2VC2 httVC2 ?_
          · obtain ⟨k, hk⟩ := h
            obtain ⟨j, hj⟩ := httodd
            omega
          · intro s h1 h2 hs
            rcases hcl2 s (by omega) (by omega) hs with h' | h'
            · exact httmin s h2 ⟨by omega, by omega, h'⟩
            · omega
        subst htteq
        -- (e)  *"Choose `j` with `4 ≤ j ≤ m` maximum such that `p_j ∈ Y₂`."*
        obtain ⟨jj, ⟨hjj3, hjjm, hjjVC2⟩, hjjmax⟩ :
            ∃ jj, (3 ≤ jj ∧ jj + 1 ≤ m ∧
                VertexComplete G (D jj) {x : V | x ∈ (SPGT.interior Q).tail}) ∧
              ∀ s, jj < s → s + 1 ≤ m →
                ¬ VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).tail} := by
          set S : Finset ℕ := (Finset.range m).filter (fun j => 3 ≤ j ∧ j + 1 ≤ m ∧
            VertexComplete G (D j) {x : V | x ∈ (SPGT.interior Q).tail}) with hSdef
          have hmemS : ∀ j : ℕ, j ∈ S ↔ (j < m ∧ 3 ≤ j ∧ j + 1 ≤ m ∧
              VertexComplete G (D j) {x : V | x ∈ (SPGT.interior Q).tail}) := by
            intro j
            rw [hSdef]
            simp only [Finset.mem_filter, Finset.mem_range]
          have h3S : (3 : ℕ) ∈ S := (hmemS 3).mpr ⟨by omega, by omega, by omega, httVC2⟩
          have hSne : S.Nonempty := ⟨3, h3S⟩
          have h3le : (3 : ℕ) ≤ S.max' hSne := Finset.le_max' _ 3 h3S
          refine ⟨S.max' hSne, ?_, ?_⟩
          · have h := (hmemS _).mp (Finset.max'_mem _ hSne)
            exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
          · intro s hs hsm hsVC
            have hle : s ≤ S.max' hSne :=
              Finset.le_max' _ s ((hmemS s).mpr ⟨by omega, by omega, hsm, hsVC⟩)
            omega
        -- (f)  *"By (1), `p_j` is `X`-complete."*
        have hjjVC1 : VertexComplete G (D jj) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
          rcases hcl2 jj (by omega) (by omega) hjjVC2 with h | h
          · exact h
          · omega
        -- (g)  *"By 15.4 applied to `p_j-⋯-p_m-p₁-⋯-p₄` we deduce that `j ≤ 5`."*
        have hjj4 : jj ≤ 4 := by
          by_contra hcon
          push Not at hcon
          have hlenP : (OddWheelArc.arc C 0 jj (m + 3)).length = m - jj + 4 := by
            rw [OddWheelArc.arc_length C 0 jj (m + 3) (by omega)]; omega
          have hPlist : IsPathList G (OddWheelArc.arc C 0 jj (m + 3)) :=
            OddWheelArc.arc_isPathList hC hn (by omega)
          have hget : ∀ (k : ℕ) (hk : k < (OddWheelArc.arc C 0 jj (m + 3)).length),
              (OddWheelArc.arc C 0 jj (m + 3))[k]'hk = D (jj + k) :=
            fun k hk => OddWheelArc.arc_get hn hD jj (m + 3) k hk
          have e0 : (OddWheelArc.arc C 0 jj (m + 3))[m - jj + 1 - 1]'(by omega) = D 0 := by
            rw [hget _ (by omega), show jj + (m - jj + 1 - 1) = m by omega]; exact hDmod0
          have e1 : (OddWheelArc.arc C 0 jj (m + 3))[m - jj + 1]'(by omega) = D 1 := by
            rw [hget _ (by omega), show jj + (m - jj + 1) = m + 1 by omega]; exact hDmod1
          have e2 : (OddWheelArc.arc C 0 jj (m + 3))[0]'(by omega) = D jj := by
            rw [hget _ (by omega)]; simp
          have e3 : (OddWheelArc.arc C 0 jj (m + 3))[m - jj + 4 - 1]'(by omega) = D 3 := by
            rw [hget _ (by omega), show jj + (m - jj + 4 - 1) = m + 3 by omega]; exact hDmod3
          have h154 := Workspace.Statements.S15.SPGT.thm_15_4 G hG
            (OddWheelArc.arc C 0 jj (m + 3)) (m - jj + 4) hPlist hlenP
            (m - jj + 1) (by omega) (by omega) Q n hQn (by omega)
            (by rw [e0, e1]; exact hQp) ?_
          · obtain ⟨hev, -⟩ := h154
            obtain ⟨k, hk⟩ := hnodd
            obtain ⟨k', hk'⟩ := hev
            omega
          · intro q hq
            obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ0 q).mp hq
            constructor
            · rw [e2]
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
              · exact (hVC1 _).mp hjjVC1 k hk hk1 (by omega)
              · exact (hVC2 _).mp hjjVC2 k hk (by omega) hkn
            · rw [e3]
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
              · exact (hVC1 _).mp httVC1 k hk hk1 (by omega)
              · exact (hVC2 _).mp httVC2 k hk (by omega) hkn
        -- (h)  *"By 15.5 applied to `p_j-⋯-p_m-p₁` … `j` is odd, and so `j = 5`."*
        have hjjeven : Even (m - jj) :=
          h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti jj m (by omega) (by omega)
            (by omega) hjjVC2 (by rw [hDmod0]; exact hp1VC2)
            (fun s h1 h2 hs => hjjmax s h1 (by omega) hs)
        have hjjeq : jj = 4 := by
          obtain ⟨k, hk⟩ := hjjeven
          obtain ⟨k', hk'⟩ := hmeven
          omega
        subst hjjeq
        -- (i)  *"From 15.5 applied to the path `p₅-⋯-p_m-p₁-p₂` … there exists `k`."*
        obtain ⟨s1, hs11, hs12, hs1VC1⟩ : ∃ s, 4 < s ∧ s < m + 1 ∧
            VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
          by_contra hcon
          push Not at hcon
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti 4 (m + 1)
            (by omega) (by omega) (by omega) hjjVC1 (by rw [hDmod1]; exact hp2VC1)
            (fun s h1 h2 => hcon s h1 h2)
          obtain ⟨k, hk⟩ := h
          obtain ⟨k', hk'⟩ := hmeven
          omega
        -- (j)  *"Since it is not in `Y₂`, it follows from (1) that `k = m`."*
        have hs1ne : s1 ≠ m := by
          intro h; rw [h, hDmod0] at hs1VC1; exact hp1nVC1 hs1VC1
        have hs1eq : s1 = m - 1 := by
          rcases hcl1 s1 (by omega) (by omega) hs1VC1 with h | h
          · exact absurd h (hjjmax s1 (by omega) (by omega))
          · exact h
        -- (k)  *"But then `p₃-q₁-⋯-q_n-p_m-p₃` is an odd antihole."*
        refine hantiK h2VC2 h2nVC1 (by rw [← hs1eq]; exact hs1VC1) ?_
        exact hjjmax (m - 1) (by omega) (by omega)
      -------------------------------------------------------------------
      -- ###  (2), mirrored:  *"if `Y₂ ⊄ {p₃}` then `p_m ∈ Y₁ ∩ Y₂`"*
      -------------------------------------------------------------------
      have hcl4 : (∃ t, 3 ≤ t ∧ t < m ∧
            VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).tail}) →
          (VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
            VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).tail}) := by
        intro hex
        obtain ⟨tt, ⟨htt3, httm, httVC2⟩, httmax⟩ :
            ∃ tt, (3 ≤ tt ∧ tt < m ∧
                VertexComplete G (D tt) {x : V | x ∈ (SPGT.interior Q).tail}) ∧
              ∀ s, tt < s → s < m →
                ¬ VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).tail} := by
          obtain ⟨t0, ht01, ht02, ht03⟩ := hex
          set S : Finset ℕ := (Finset.range m).filter (fun j => 3 ≤ j ∧ j < m ∧
            VertexComplete G (D j) {x : V | x ∈ (SPGT.interior Q).tail}) with hSdef
          have hmemS : ∀ j : ℕ, j ∈ S ↔ (j < m ∧ 3 ≤ j ∧ j < m ∧
              VertexComplete G (D j) {x : V | x ∈ (SPGT.interior Q).tail}) := by
            intro j
            rw [hSdef]
            simp only [Finset.mem_filter, Finset.mem_range]
          have h0S : t0 ∈ S := (hmemS t0).mpr ⟨by omega, ht01, ht02, ht03⟩
          have hSne : S.Nonempty := ⟨t0, h0S⟩
          have h0le : t0 ≤ S.max' hSne := Finset.le_max' _ t0 h0S
          refine ⟨S.max' hSne, ?_, ?_⟩
          · have h := (hmemS _).mp (Finset.max'_mem _ hSne)
            exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
          · intro s hs hsm hsVC
            have hle : s ≤ S.max' hSne :=
              Finset.le_max' _ s ((hmemS s).mpr ⟨by omega, by omega, hsm, hsVC⟩)
            omega
        have httVC1 : VertexComplete G (D tt) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
          rcases hcl2 tt (by omega) httm httVC2 with h | h
          · exact h
          · omega
        by_cases htt : tt = m - 1
        · rw [htt] at httVC1 httVC2; exact ⟨httVC1, httVC2⟩
        exfalso
        have httlt : tt < m - 1 := by omega
        -- (a')
        have htteven : Even (m - tt) :=
          h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti tt m (by omega) (by omega)
            (by omega) httVC2 (by rw [hDmod0]; exact hp1VC2)
            (fun s h1 h2 => httmax s h1 h2)
        have httev : Even tt := by
          obtain ⟨k, hk⟩ := htteven
          obtain ⟨k', hk'⟩ := hmeven
          exact ⟨k' - k, by omega⟩
        -- (b')
        obtain ⟨s1, hs11, hs12, hs1VC1⟩ : ∃ s, tt < s ∧ s < m + 1 ∧
            VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).dropLast} := by
          by_contra hcon
          push Not at hcon
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti tt (m + 1)
            (by omega) (by omega) (by omega) httVC1 (by rw [hDmod1]; exact hp2VC1)
            (fun s h1 h2 => hcon s h1 h2)
          obtain ⟨k, hk⟩ := h
          obtain ⟨k', hk'⟩ := httev
          obtain ⟨k'', hk''⟩ := hmeven
          omega
        -- (c')
        have hs1ne : s1 ≠ m := by
          intro h; rw [h, hDmod0] at hs1VC1; exact hp1nVC1 hs1VC1
        have hs1eq : s1 = m - 1 := by
          rcases hcl1 s1 (by omega) (by omega) hs1VC1 with h | h
          · exact absurd h (httmax s1 hs11 (by omega))
          · exact h
        have hmVC1 : VertexComplete G (D (m - 1))
            {x : V | x ∈ (SPGT.interior Q).dropLast} := by rw [← hs1eq]; exact hs1VC1
        have hmnVC2 : ¬ VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).tail} :=
          httmax (m - 1) (by omega) (by omega)
        -- (d')
        have htteq : tt = m - 2 := by
          by_contra hne
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti tt (m - 1)
            (by omega) (by omega) (by omega) httVC1 hmVC1 ?_
          · obtain ⟨k, hk⟩ := h
            obtain ⟨k', hk'⟩ := httev
            obtain ⟨k'', hk''⟩ := hmeven
            omega
          · intro s h1 h2 hs
            rcases hcl1 s (by omega) (by omega) hs with h' | h'
            · exact httmax s h1 (by omega) h'
            · omega
        -- (e')
        have hexj : ∃ t, 2 ≤ t ∧ t + 2 ≤ m ∧
            VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast} :=
          ⟨tt, by omega, by omega, httVC1⟩
        obtain ⟨jj, ⟨hjj2, hjjm, hjjVC1⟩, hjjmin⟩ :
            ∃ jj, (2 ≤ jj ∧ jj + 2 ≤ m ∧
                VertexComplete G (D jj) {x : V | x ∈ (SPGT.interior Q).dropLast}) ∧
              ∀ s, s < jj → ¬ (2 ≤ s ∧ s + 2 ≤ m ∧
                VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).dropLast}) :=
          ⟨Nat.find hexj, Nat.find_spec hexj, fun s hs => Nat.find_min hexj hs⟩
        -- (f')
        have hjjVC2 : VertexComplete G (D jj) {x : V | x ∈ (SPGT.interior Q).tail} := by
          rcases hcl1 jj (by omega) (by omega) hjjVC1 with h | h
          · exact h
          · omega
        -- (g')  15.4 applied to `p_{jj+1}-⋯-p₁-p_m-⋯-p_{m-1}`
        have hjjge : m - 3 ≤ jj := by
          by_contra hcon
          push Not at hcon
          have hDmjj : D (m + jj) = D jj :=
            OddWheelArc.rim_congr hC hD
              (show (m + jj) % C.length = jj % C.length by rw [hCm]; exact Nat.add_mod_left m jj)
          have hlenP : (OddWheelArc.arc C 0 (m - 2) (m + jj)).length = jj + 3 := by
            rw [OddWheelArc.arc_length C 0 (m - 2) (m + jj) (by omega)]; omega
          have hPlist : IsPathList G (OddWheelArc.arc C 0 (m - 2) (m + jj)) :=
            OddWheelArc.arc_isPathList hC hn (by omega)
          have hget : ∀ (k : ℕ) (hk : k < (OddWheelArc.arc C 0 (m - 2) (m + jj)).length),
              (OddWheelArc.arc C 0 (m - 2) (m + jj))[k]'hk = D (m - 2 + k) :=
            fun k hk => OddWheelArc.arc_get hn hD (m - 2) (m + jj) k hk
          have e0 : (OddWheelArc.arc C 0 (m - 2) (m + jj))[3 - 1]'(by omega) = D 0 := by
            rw [hget _ (by omega), show m - 2 + (3 - 1) = m by omega]; exact hDmod0
          have e1 : (OddWheelArc.arc C 0 (m - 2) (m + jj))[3]'(by omega) = D 1 := by
            rw [hget _ (by omega), show m - 2 + 3 = m + 1 by omega]; exact hDmod1
          have e2 : (OddWheelArc.arc C 0 (m - 2) (m + jj))[0]'(by omega) = D (m - 2) := by
            rw [hget _ (by omega)]; simp
          have e3 : (OddWheelArc.arc C 0 (m - 2) (m + jj))[jj + 3 - 1]'(by omega) = D jj := by
            rw [hget _ (by omega), show m - 2 + (jj + 3 - 1) = m + jj by omega]; exact hDmjj
          have h154 := Workspace.Statements.S15.SPGT.thm_15_4 G hG
            (OddWheelArc.arc C 0 (m - 2) (m + jj)) (jj + 3) hPlist hlenP
            3 (by omega) (by omega) Q n hQn (by omega)
            (by rw [e0, e1]; exact hQp) ?_
          · obtain ⟨hev, -⟩ := h154
            obtain ⟨k, hk⟩ := hnodd
            obtain ⟨k', hk'⟩ := hev
            omega
          · intro q hq
            obtain ⟨k, hk, hk1, hkn, rfl⟩ := (hZ0 q).mp hq
            constructor
            · rw [e2, ← htteq]
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
              · exact (hVC1 _).mp httVC1 k hk hk1 (by omega)
              · exact (hVC2 _).mp httVC2 k hk (by omega) hkn
            · rw [e3]
              rcases Nat.lt_or_ge (k + 1) (n + 1) with h | h
              · exact (hVC1 _).mp hjjVC1 k hk hk1 (by omega)
              · exact (hVC2 _).mp hjjVC2 k hk (by omega) hkn
        -- (h')
        have hjjodd : Odd jj := by
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti 1 jj
            (by omega) (by omega) (by omega) hp2VC1 hjjVC1
            (fun s h1 h2 hs => hjjmin s h2 ⟨by omega, by omega, hs⟩)
          obtain ⟨k, hk⟩ := h
          exact ⟨k, by omega⟩
        have hjjeq : jj = m - 3 := by
          obtain ⟨k, hk⟩ := hjjodd
          obtain ⟨k', hk'⟩ := hmeven
          omega
        -- (i')
        obtain ⟨s2, hs21, hs22, hs2VC2⟩ : ∃ s, 0 < s ∧ s < m - 3 ∧
            VertexComplete G (D s) {x : V | x ∈ (SPGT.interior Q).tail} := by
          by_contra hcon
          push Not at hcon
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti 0 (m - 3)
            (by omega) (by omega) (by omega) hp1VC2 (by rw [← hjjeq]; exact hjjVC2)
            (fun s h1 h2 => hcon s h1 h2)
          obtain ⟨k, hk⟩ := h
          obtain ⟨k', hk'⟩ := hmeven
          omega
        -- (j')
        have hs2ne1 : s2 ≠ 1 := by
          intro h; rw [h] at hs2VC2; exact hp2nVC2 hs2VC2
        have hs2eq : s2 = 2 := by
          rcases hcl2 s2 (by omega) (by omega) hs2VC2 with h | h
          · exact (hjjmin s2 (by omega) ⟨by omega, by omega, h⟩).elim
          · exact h
        have h2VC2 : VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail} := by
          rw [← hs2eq]; exact hs2VC2
        have h2nVC1 : ¬ VertexComplete G (D 2)
            {x : V | x ∈ (SPGT.interior Q).dropLast} := fun hc =>
          hjjmin 2 (by omega) ⟨by omega, by omega, hc⟩
        exact hantiK h2VC2 h2nVC1 hmVC1 hmnVC2
      -------------------------------------------------------------------
      -- ###  the last paragraph
      -------------------------------------------------------------------
      by_cases hA : VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
          VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail}
      · have hB : ¬ (VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).dropLast} ∧
            VertexComplete G (D (m - 1)) {x : V | x ∈ (SPGT.interior Q).tail}) :=
          fun h => hnotboth ⟨hA, h⟩
        have hno2 : ∀ t, 3 ≤ t → t < m →
            ¬ VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).tail} :=
          fun t h1 h2 hc => hB (hcl4 ⟨t, h1, h2, hc⟩)
        constructor
        · intro t ht2 htm hPt
          rcases hPt with h | h
          · rcases hcl1 t ht2 htm h with h' | h'
            · exact Or.inl (by by_contra hne; exact hno2 t (by omega) htm h')
            · exact Or.inr h'
          · exact Or.inl (by by_contra hne; exact hno2 t (by omega) htm h)
        · rintro ⟨hP2, hPm⟩
          have hmVC1 : VertexComplete G (D (m - 1))
              {x : V | x ∈ (SPGT.interior Q).dropLast} := by
            rcases hPm with h | h
            · exact h
            · exact absurd h (hno2 (m - 1) (by omega) (by omega))
          have h := h155arc {x : V | x ∈ (SPGT.interior Q).dropLast} hZ1C hZ1anti 2 (m - 1)
            (by omega) (by omega) (by omega) hA.1 hmVC1 ?_
          · obtain ⟨k, hk⟩ := h
            obtain ⟨k', hk'⟩ := hmeven
            omega
          · intro s h1 h2 hs
            rcases hcl1 s (by omega) (by omega) hs with h' | h'
            · exact hno2 s (by omega) (by omega) h'
            · omega
      · have hno1 : ∀ t, 2 ≤ t → t + 2 ≤ m →
            ¬ VertexComplete G (D t) {x : V | x ∈ (SPGT.interior Q).dropLast} :=
          fun t h1 h2 hc => hA (hcl3 ⟨t, h1, h2, hc⟩)
        constructor
        · intro t ht2 htm hPt
          rcases hPt with h | h
          · exact Or.inr (by by_contra hne; exact hno1 t ht2 (by omega) h)
          · rcases hcl2 t ht2 htm h with h' | h'
            · exact Or.inr (by by_contra hne; exact hno1 t ht2 (by omega) h')
            · exact Or.inl h'
        · rintro ⟨hP2, hPm⟩
          have h2VC2 : VertexComplete G (D 2) {x : V | x ∈ (SPGT.interior Q).tail} := by
            rcases hP2 with h | h
            · exact absurd h (hno1 2 (by omega) (by omega))
            · exact h
          have h2nVC1 : ¬ VertexComplete G (D 2)
              {x : V | x ∈ (SPGT.interior Q).dropLast} := hno1 2 (by omega) (by omega)
          have hmVC1 : VertexComplete G (D (m - 1))
              {x : V | x ∈ (SPGT.interior Q).dropLast} := by
            rcases hPm with h | h
            · exact h
            · rcases hcl2 (m - 1) (by omega) (by omega) h with h' | h'
              · exact h'
              · omega
          have hmnVC2 : ¬ VertexComplete G (D (m - 1))
              {x : V | x ∈ (SPGT.interior Q).tail} := by
            intro hc
            have h := h155arc {x : V | x ∈ (SPGT.interior Q).tail} hZ2C hZ2anti 2 (m - 1)
              (by omega) (by omega) (by omega) h2VC2 hc ?_
            · obtain ⟨k, hk⟩ := h
              obtain ⟨k', hk'⟩ := hmeven
              omega
            · intro s h1 h2 hs
              rcases hcl2 s (by omega) (by omega) hs with h' | h'
              · exact hno1 s (by omega) (by omega) h'
              · omega
          exact hantiK h2VC2 h2nVC1 hmVC1 hmnVC2
  obtain ⟨hmain, hmain2⟩ := final
  constructor
  · rintro w ⟨hwC, hwP⟩ w' ⟨hw'C, hw'P⟩
    obtain ⟨t, ht2, htm, rfl⟩ := (hdrop w).mp hwC
    obtain ⟨t', ht'2, ht'm, rfl⟩ := (hdrop w').mp hw'C
    rcases hmain t ht2 htm hwP with rfl | rfl <;> rcases hmain t' ht'2 ht'm hw'P with h' | h'
    · rw [h']
    · rw [h']; exact absurd ⟨hwP, h' ▸ hw'P⟩ hmain2
    · rw [h']; exact absurd ⟨h' ▸ hw'P, hwP⟩ hmain2
    · rw [h']
  · intro w hwC hwP
    obtain ⟨t, ht2, htm, rfl⟩ := (hdrop w).mp hwC
    rcases hmain t ht2 htm hwP with rfl | rfl
    · exact Or.inl hD2
    · exact Or.inr hDm


end SPGT

end Workspace.Statements.S15
