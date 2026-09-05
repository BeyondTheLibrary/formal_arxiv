import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.OddWheelSpan
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.HoleArithmetic
import Workspace.ProofLemmas.BalancedNoLeap
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_10
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S15.Thm_15_3
import Workspace.Statements.S15.Thm_15_5

/-!
# The rim-index layer shared by the two branches of claim (1) of 16.1

PAPER (16.1, printed p. 96), claim (1):

> *"Let `P` be a path in `C` of length ≥ 1, such that its ends are adjacent to `v` and have
> opposite wheel-parity.  Then either some internal vertex of `P` is a neighbour of `v`, or `P`
> has length 1."*

This module fixes the index conventions in which the printed proof of that claim is carried out,
and proves everything the printed argument establishes **before** its case split on whether *"`v`
has a neighbour in `{p_{j+2},…,p_{n−1}}`"*.

Conventions.  `n = C.length`; `D t` is the rim vertex at cyclic position `k + t`, so the paper's
`p_a` is `D (a-1)` and the paper's `j` is `L + 1`.  Every statement is phrased for offsets `< n`,
which turns all cyclic-index reasoning into `omega` (via `rim_adj`, the `%`-free reading of hole
adjacency).  In these conventions the paper's *"`j` is odd"* is `Even L`, its *"`i` is odd"* is
`Even s`, and its *"`n ≥ j+3`"* is `L + 4 ≤ n`.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelArc

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT

variable {V : Type*} {G : SimpleGraph V} {C : List V}

/-! ## The rim, indexed by cyclic offset from a base position `k`

Throughout, `n = C.length`, and `D t` is the vertex at cyclic position `k + t` of the rim.
Every statement below is phrased for offsets `< n`, so that all index reasoning is `omega`. -/

/-- The arc of the rim from cyclic position `k + a` to cyclic position `k + b`. -/
def arc (C : List V) (k a b : ℕ) : List V := (C.rotate (k + a)).take (b - a + 1)

theorem arc_length (C : List V) (k a b : ℕ) (h : b - a + 1 ≤ C.length) :
    (arc C k a b).length = b - a + 1 := by
  simp only [arc, List.length_take, List.length_rotate]
  omega

theorem arc_getElem (hn : 0 < C.length) (k a b t : ℕ) (ht : t < (arc C k a b).length) :
    (arc C k a b)[t]'ht = C[(k + a + t) % C.length]'(Nat.mod_lt _ hn) :=
  SegmentBasics.arc_getElem hn ht

/-- The rim position function.  `hDget` is the only interface: everything else is derived. -/
theorem rim_exists (hn : 0 < C.length) (k : ℕ) :
    ∃ D : ℕ → V, ∀ t : ℕ, C[(k + t) % C.length]? = some (D t) :=
  ⟨fun t => C[(k + t) % C.length]'(Nat.mod_lt _ hn), fun t => List.getElem?_eq_getElem _⟩

section Rim

variable {k n : ℕ} {D : ℕ → V}

theorem rim_mem (hn : 0 < C.length) (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (t : ℕ) :
    D t ∈ C := SegmentBasics.mem_of_pos hn (hD t)

theorem rim_congr (hC : IsHoleList G C) (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t))
    {a b : ℕ} (h : a % C.length = b % C.length) : D a = D b := by
  have h1 : (k + a) % C.length = (k + b) % C.length := by
    have := SegmentBasics.add_mod_congr (n := C.length) h k
    rw [Nat.add_comm a k, Nat.add_comm b k] at this
    exact this
  have hx := hD a
  rw [h1, hD b] at hx
  exact (Option.some_injective _ hx).symm

theorem rim_eq_getElem (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (t : ℕ) :
    C[(k + t) % C.length]'(Nat.mod_lt _ hn) = D t :=
  Option.some_injective _ ((List.getElem?_eq_getElem (Nat.mod_lt _ hn)).symm.trans (hD t))

/-- The rotated rim, on which the offsets `0, 1, …, n-1` are literal list indices. -/
theorem rim_rot (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n) :
    IsHoleList G (C.rotate k) ∧ (C.rotate k).length = n ∧
      ∀ (t : ℕ) (ht : t < (C.rotate k).length), (C.rotate k)[t]'ht = D t := by
  refine ⟨HoleBasics.isHoleList_rotate hC k, by simpa using hnn, fun t ht => ?_⟩
  rw [WheelParity.getElem_rotate_eq hn ht, Nat.add_comm t k]
  exact rim_eq_getElem hn hD t

/-- The `%`-free reading of rim adjacency, in terms of cyclic offsets from `k`. -/
theorem rim_adj (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) :
    G.Adj (D a) (D b) ↔ (b = a + 1 ∨ a = b + 1 ∨ (a = 0 ∧ b = n - 1) ∨ (b = 0 ∧ a = n - 1)) := by
  obtain ⟨hE, hElen, hEget⟩ := rim_rot hC hn hD hnn
  have ha' : a < (C.rotate k).length := by omega
  have hb' : b < (C.rotate k).length := by omega
  constructor
  · intro hadj
    rw [← hEget a ha', ← hEget b hb'] at hadj
    have := WheelParity.hole_adj_index hE ha' hb' hadj
    rw [hElen] at this
    exact this
  · intro hcase
    rw [← hEget a ha', ← hEget b hb']
    rw [HoleBasics.hole_adj_iff hE ha' hb', hElen]
    rcases hcase with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl (by rw [h, Nat.mod_eq_of_lt (by omega)])
    · exact Or.inr (by rw [h, Nat.mod_eq_of_lt (by omega)])
    · exact Or.inr (by subst h1; subst h2; rw [Nat.sub_add_cancel (by omega), Nat.mod_self])
    · exact Or.inl (by subst h1; subst h2; rw [Nat.sub_add_cancel (by omega), Nat.mod_self])

theorem rim_ne (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (hab : a ≠ b) : D a ≠ D b := by
  obtain ⟨hE, hElen, hEget⟩ := rim_rot hC hn hD hnn
  have ha' : a < (C.rotate k).length := by omega
  have hb' : b < (C.rotate k).length := by omega
  rw [← hEget a ha', ← hEget b hb']
  exact HoleBasics.hole_ne_of_ne_index hE ha' hb' hab

/-- Every rim vertex is `D t` for a unique offset `t < n`. -/
theorem rim_surj (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {z : V} (hz : z ∈ C) : ∃ t, t < n ∧ z = D t := by
  obtain ⟨hE, hElen, hEget⟩ := rim_rot hC hn hD hnn
  obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem (HoleBasics.mem_rotate_iff.mpr hz : z ∈ C.rotate k)
  exact ⟨t, by omega, by rw [← hteq, hEget t ht]⟩

theorem rim_inj (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (h : D a = D b) : a = b := by
  by_contra hne
  exact rim_ne hC hn hD hnn ha hb hne h

/-! ## Arcs -/

theorem arc_get (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (a b t : ℕ)
    (ht : t < (arc C k a b).length) : (arc C k a b)[t]'ht = D (a + t) := by
  have h1 : (arc C k a b)[t]'ht = C[(k + a + t) % C.length]'(Nat.mod_lt _ hn) :=
    arc_getElem hn k a b t ht
  have h2 : C[(k + (a + t)) % C.length]'(Nat.mod_lt _ hn) = D (a + t) :=
    rim_eq_getElem hn hD (a + t)
  exact h1.trans ((HoleArithmetic.getElem_congr_idx C _ _ (by congr 1; omega)).trans h2)

theorem arc_mem_iff (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (hab : a ≤ b) (hlen : b - a + 1 ≤ n) {z : V} :
    z ∈ arc C k a b ↔ ∃ t, a ≤ t ∧ t ≤ b ∧ z = D t := by
  have hL : (arc C k a b).length = b - a + 1 := arc_length C k a b (by omega)
  constructor
  · intro hz
    obtain ⟨t, ht, hteq⟩ := List.getElem_of_mem hz
    exact ⟨a + t, by omega, by omega, by rw [← hteq, arc_get hn hD a b t ht]⟩
  · rintro ⟨t, hta, htb, rfl⟩
    have ht : t - a < (arc C k a b).length := by omega
    have : (arc C k a b)[t - a]'ht = D t := by
      rw [arc_get hn hD a b (t - a) ht]
      congr 1
      omega
    rw [← this]
    exact List.getElem_mem ht

theorem arc_isPathFrom (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (hab : a < b) (hlen : b - a + 2 ≤ n) :
    IsPathFrom G (arc C k a b) (D a) (D b) := by
  have h1 : 2 ≤ b - a + 1 := by omega
  have h2 : (b - a + 1) + 1 ≤ C.length := by omega
  have hp : (k + a) % C.length < C.length := Nat.mod_lt _ hn
  have hq : (k + b) % C.length < C.length := Nat.mod_lt _ hn
  have key := WheelParity.arc_isPathFrom (k := k + a) (L := b - a + 1) hC hp hq h1 h2 rfl
    (show (k + a + (b - a + 1) - 1) % C.length = (k + b) % C.length by
      congr 1; omega)
  rw [rim_eq_getElem hn hD a, rim_eq_getElem hn hD b] at key
  exact key

theorem arc_isPathList (hC : IsHoleList G C) (hn : 0 < C.length)
    {a b : ℕ} (hlen : b - a + 2 ≤ C.length) :
    IsPathList G (arc C k a b) :=
  WheelParity.isPathList_rotate_take hC (by omega) (by omega)


theorem arc_singleton (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (a : ℕ) (h2 : 2 ≤ C.length) :
    arc C k a a = [D a] := by
  have hL : (arc C k a a).length = 1 := by
    have := arc_length C k a a (show a - a + 1 ≤ C.length by omega); omega
  obtain ⟨z, hz⟩ := List.length_eq_one_iff.mp hL
  have e1 : (arc C k a a)[0]? = some z := by rw [hz]; rfl
  have e2 : (arc C k a a)[0]? = some ((arc C k a a)[0]'(by omega)) :=
    List.getElem?_eq_getElem (by omega)
  have h0 : (arc C k a a)[0]'(by omega) = D (a + 0) := arc_get hn hD a a 0 (by omega)
  have e3 := e2.symm.trans e1
  rw [h0] at e3
  have hz0 : z = D a := by simpa using (Option.some_injective _ e3).symm
  rw [hz, hz0]

theorem arc_isPathFrom' (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (hab : a ≤ b) (hlen : b - a + 2 ≤ n) :
    IsPathFrom G (arc C k a b) (D a) (D b) := by
  rcases eq_or_lt_of_le hab with rfl | hlt
  · rw [arc_singleton hn hD a (by omega)]
    exact ⟨PathBasics.isPathList_singleton G _, rfl, rfl⟩
  · exact arc_isPathFrom hC hn hD hnn hlt hlen

theorem arc_rev_isPathFrom (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (hab : a ≤ b) (hlen : b - a + 2 ≤ n) :
    IsPathFrom G (arc C k a b).reverse (D b) (D a) :=
  PathBasics.isPathFrom_reverse (arc_isPathFrom' hC hn hD hnn hab hlen)

theorem arc_rev_mem_iff (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {a b : ℕ} (hab : a ≤ b) (hlen : b - a + 1 ≤ n) {z : V} :
    z ∈ (arc C k a b).reverse ↔ ∃ t, a ≤ t ∧ t ≤ b ∧ z = D t := by
  rw [List.mem_reverse]
  exact arc_mem_iff hC hn hD hnn hab hlen

/-! ## Gluing two arcs through `v`

Every path the printed proof of claim (1) builds has the shape *arc — `v` — arc*, where `v` is
adjacent to the last vertex of the first arc and to the first vertex of the second, and to no
other vertex of either. -/

theorem glue_two_arcs (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    {v : V} (hvC : v ∉ C)
    {A B : List V} {a₁ b₁ a₂ b₂ e₁ e₂ : ℕ} {f₁ f₂ : V}
    (hA : IsPathFrom G A f₁ (D e₁))
    (hAmem : ∀ z, z ∈ A ↔ ∃ t, a₁ ≤ t ∧ t ≤ b₁ ∧ z = D t)
    (hB : IsPathFrom G B (D e₂) f₂)
    (hBmem : ∀ z, z ∈ B ↔ ∃ t, a₂ ≤ t ∧ t ≤ b₂ ∧ z = D t)
    (hsep : b₁ + 1 < a₂) (ha₂ : a₂ ≤ b₂) (hb₂ : b₂ < n)
    (hwrap : ¬ (a₁ = 0 ∧ b₂ = n - 1))
    (he₁ : a₁ ≤ e₁ ∧ e₁ ≤ b₁) (he₂ : a₂ ≤ e₂ ∧ e₂ ≤ b₂)
    (hv₁ : ∀ t, a₁ ≤ t → t ≤ b₁ → (G.Adj v (D t) ↔ t = e₁))
    (hv₂ : ∀ t, a₂ ≤ t → t ≤ b₂ → (G.Adj v (D t) ↔ t = e₂)) :
    IsPathFrom G (A ++ (v :: B)) f₁ f₂ := by
  have hvB : IsPathFrom G (v :: B) v f₂ := by
    refine PathAttach.isPathFrom_cons hB ((hv₂ e₂ he₂.1 he₂.2).mpr rfl) ?_ ?_
    · intro hvB
      obtain ⟨t, _, _, hvt⟩ := (hBmem v).mp hvB
      exact hvC (hvt ▸ rim_mem hn hD t)
    · intro x hx hxe
      obtain ⟨t, ht1, ht2, rfl⟩ := (hBmem x).mp hx
      intro hadj
      exact hxe (by rw [(hv₂ t ht1 ht2).mp hadj])
  refine PathGlue.glue_path hA hvB ?_ ?_
  · intro x hx hxmem
    obtain ⟨t₁, ht11, ht12, rfl⟩ := (hAmem x).mp hx
    rcases List.mem_cons.mp hxmem with heq | hxB
    · exact hvC (heq ▸ rim_mem hn hD t₁)
    · obtain ⟨t₂, ht21, ht22, ht2eq⟩ := (hBmem _).mp hxB
      have : t₁ = t₂ := rim_inj hC hn hD hnn (by omega) (by omega) ht2eq
      omega
  · intro x hx y hy
    obtain ⟨t₁, ht11, ht12, rfl⟩ := (hAmem x).mp hx
    rcases List.mem_cons.mp hy with rfl | hyB
    · constructor
      · intro hadj
        exact ⟨by rw [rim_inj hC hn hD hnn (by omega) (by omega)
            ((hv₁ t₁ ht11 ht12).mp hadj.symm ▸ rfl : D t₁ = D e₁)], rfl⟩
      · rintro ⟨h1, -⟩
        have : t₁ = e₁ := rim_inj hC hn hD hnn (by omega) (by omega) h1
        exact ((hv₁ t₁ ht11 ht12).mpr this).symm
    · obtain ⟨t₂, ht21, ht22, rfl⟩ := (hBmem y).mp hyB
      have hne : ¬ G.Adj (D t₁) (D t₂) := by
        rw [rim_adj hC hn hD hnn (show t₁ < n by omega) (show t₂ < n by omega)]
        push Not
        refine ⟨by omega, by omega, ?_, by omega⟩
        rintro rfl
        exact fun hh => hwrap ⟨by omega, by omega⟩
      refine iff_of_false hne ?_
      rintro ⟨-, h2⟩
      exact hvC (h2 ▸ rim_mem hn hD t₂)

end Rim


/-! ## The hole `v-p₁-⋯-p_j-v` and the arc edge-count -/

section Setup

variable {k n L : ℕ} {D : ℕ → V} {Y : Set V} {v : V}

/-- PAPER: the hole `v-p₁-⋯-p_j-v`.  Here `v` is put **last**, which removes all wrap-around
bookkeeping from the index arithmetic. -/
def bigHole (C : List V) (k L : ℕ) (v : V) : List V := arc C k 0 L ++ [v]

theorem bigHole_length (h : L + 1 ≤ C.length) : (bigHole C k L v).length = L + 2 := by
  simp only [bigHole, List.length_append, List.length_cons, List.length_nil,
    arc_length C k 0 L (by omega)]
  omega

theorem bigHole_get (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (h : L + 1 ≤ C.length)
    {t : ℕ} (ht : t ≤ L) : (bigHole C k L v)[t]? = some (D t) := by
  have hal : (arc C k 0 L).length = L + 1 := arc_length C k 0 L (by omega)
  have h1 : (bigHole C k L v)[t]? = (arc C k 0 L)[t]? :=
    List.getElem?_append_left (by omega)
  rw [h1, List.getElem?_eq_getElem (show t < (arc C k 0 L).length by omega),
    arc_get hn hD 0 L t (by omega)]
  simp

theorem bigHole_get_v (h : L + 1 ≤ C.length) :
    (bigHole C k L v)[L + 1]? = some v := by
  have hal : (arc C k 0 L).length = L + 1 := arc_length C k 0 L (by omega)
  rw [bigHole, List.getElem?_append_right (by omega)]
  simp [hal]

theorem bigHole_mem_iff (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (h : L + 1 ≤ n) {z : V} :
    z ∈ bigHole C k L v ↔ ((∃ t, t ≤ L ∧ z = D t) ∨ z = v) := by
  simp only [bigHole, List.mem_append, List.mem_singleton,
    arc_mem_iff hC hn hD hnn (Nat.zero_le L) (by omega)]
  constructor
  · rintro (⟨t, -, ht, rfl⟩ | rfl)
    · exact Or.inl ⟨t, ht, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨t, ht, rfl⟩ | rfl)
    · exact Or.inl ⟨t, Nat.zero_le _, ht, rfl⟩
    · exact Or.inr rfl

/-- `v` is adjacent to `D t` for `t ≤ L` exactly at the two ends of the arc. -/
theorem adj_v_iff (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL2 : L + 2 ≤ n) {x y : V}
    (hx : C[k % C.length]? = some x) (hy : C[(k + L) % C.length]? = some y)
    (hvx : G.Adj v x) (hvy : G.Adj v y)
    (hnb : ∀ t, 0 < t → t < L → ¬ SegmentBasics.CycVert G ({v} : Set V) C (k + t)) :
    ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)) := by
  have hD0 : D 0 = x := by
    have h0 := hD 0
    rw [Nat.add_zero, hx] at h0
    exact (Option.some_injective _ h0).symm
  have hDL : D L = y := by
    have h0 := hD L
    rw [hy] at h0
    exact (Option.some_injective _ h0).symm
  intro t ht
  constructor
  · intro hadj
    by_contra hcon
    push Not at hcon
    exact hnb t (by omega) (by omega) ⟨D t, hD t, fun z hz => by
      rw [Set.mem_singleton_iff] at hz; subst hz; exact hadj.symm⟩
  · rintro (rfl | rfl)
    · rw [hD0]; exact hvx
    · rw [hDL]; exact hvy

theorem bigHole_isHole (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hvC : v ∉ C)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L))) :
    IsHoleList G (bigHole C k L v) := by
  have hal : (arc C k 0 L).length = L + 1 := arc_length C k 0 L (by omega)
  refine PathGlue.glue_hole (arc_isPathFrom' hC hn hD hnn (Nat.zero_le L) (by omega))
    (⟨PathBasics.isPathList_singleton G v, rfl, rfl⟩ : IsPathFrom G [v] v v) ?_ ?_
    (by have hv1 : ([v] : List V).length = 1 := rfl; omega)
  · intro z hz
    rw [arc_mem_iff hC hn hD hnn (Nat.zero_le L) (by omega)] at hz
    obtain ⟨t, -, ht, rfl⟩ := hz
    simp only [List.mem_singleton]
    intro hcon
    exact hvC (hcon ▸ rim_mem hn hD t)
  · intro z hz w hw
    rw [arc_mem_iff hC hn hD hnn (Nat.zero_le L) (by omega)] at hz
    obtain ⟨t, -, ht, rfl⟩ := hz
    rw [List.mem_singleton] at hw
    subst hw
    rw [SimpleGraph.adj_comm, hvD t ht]
    constructor
    · rintro (rfl | rfl)
      · exact Or.inr ⟨rfl, rfl⟩
      · exact Or.inl ⟨rfl, rfl⟩
    · rintro (⟨h1, -⟩ | ⟨h1, -⟩)
      · exact Or.inr (rim_inj hC hn hD hnn (by omega) (by omega) h1)
      · exact Or.inl (rim_inj hC hn hD hnn (by omega) (by omega) h1)

/-- PAPER: *"From the hole `v-p₁-⋯-p_j-v` it follows that `j` is odd."* -/
theorem even_L (hBerge : Berge G) (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hvC : v ∉ C)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L))) :
    Even L := by
  have hH := bigHole_isHole hC hn hD hnn hL1 hL2 hvC hvD
  have := hBerge.1 _ hH
  rw [holeLength, bigHole_length (v := v) (show L + 1 ≤ C.length by omega)] at this
  obtain ⟨r, hr⟩ := this
  exact ⟨r - 1, by omega⟩

/-! ### The number of `Z`-complete edges on the arc -/

/-- The number of `Z`-complete edges among the `L` edges of the arc from cyclic position `k`
to cyclic position `k + L`. -/
noncomputable def arcCount (G : SimpleGraph V) (Z : Set V) (C : List V) (k L : ℕ) : ℕ :=
  WheelParity.cycCount G Z C (k + L) - WheelParity.cycCount G Z C k

theorem arcCount_eq (Z : Set V) (k L : ℕ) :
    WheelParity.cycCount G Z C (k + L) = WheelParity.cycCount G Z C k + arcCount G Z C k L := by
  have h := WheelParity.cycCount_add (G := G) (Y := Z) (C := C) k L
  simp only [arcCount]
  omega


theorem arcCount_zero (Z : Set V) (k : ℕ) : arcCount G Z C k 0 = 0 := by
  simp [arcCount]

theorem arcCount_split (Z : Set V) (k a b : ℕ) :
    arcCount G Z C k (a + b) = arcCount G Z C k a + arcCount G Z C (k + a) b := by
  have h1 := arcCount_eq (G := G) (C := C) Z k (a + b)
  have h2 := arcCount_eq (G := G) (C := C) Z k a
  have h3 := arcCount_eq (G := G) (C := C) Z (k + a) b
  rw [show k + a + b = k + (a + b) from by omega] at h3
  omega

theorem arcCount_one_pos {Z : Set V} {k : ℕ} (h : WheelParity.CycEdge G Z C k) :
    arcCount G Z C k 1 = 1 := by
  have h1 := WheelParity.cycCount_add (G := G) (Y := Z) (C := C) k 1
  have h2 := arcCount_eq (G := G) (C := C) Z k 1
  simp only [Finset.sum_range_one, Nat.add_zero] at h1
  rw [if_pos h] at h1
  omega

theorem arcCount_one_neg {Z : Set V} {k : ℕ} (h : ¬ WheelParity.CycEdge G Z C k) :
    arcCount G Z C k 1 = 0 := by
  have h1 := WheelParity.cycCount_add (G := G) (Y := Z) (C := C) k 1
  have h2 := arcCount_eq (G := G) (C := C) Z k 1
  simp only [Finset.sum_range_one, Nat.add_zero] at h1
  rw [if_neg h] at h1
  omega

/-- Two hubs with the same `CycEdge` pattern along an arc have the same arc-count. -/
theorem arcCount_congr {Z Z' : Set V} {k : ℕ} : ∀ m : ℕ,
    (∀ t, t < m → (WheelParity.CycEdge G Z C (k + t) ↔ WheelParity.CycEdge G Z' C (k + t))) →
    arcCount G Z C k m = arcCount G Z' C k m := by
  intro m
  induction m with
  | zero => intro _; rw [arcCount_zero, arcCount_zero]
  | succ m ih =>
      intro h
      have h1 : arcCount G Z C k (m + 1) = arcCount G Z C k m + arcCount G Z C (k + m) 1 :=
        arcCount_split Z k m 1
      have h2 : arcCount G Z' C k (m + 1) = arcCount G Z' C k m + arcCount G Z' C (k + m) 1 :=
        arcCount_split Z' k m 1
      have hm := ih (fun t ht => h t (by omega))
      have hlast : arcCount G Z C (k + m) 1 = arcCount G Z' C (k + m) 1 := by
        by_cases hc : WheelParity.CycEdge G Z C (k + m)
        · rw [arcCount_one_pos hc, arcCount_one_pos ((h m (by omega)).mp hc)]
        · rw [arcCount_one_neg hc, arcCount_one_neg (fun hh => hc ((h m (by omega)).mpr hh))]
      omega

/-- The total number of `Z`-complete edges of the rim, read off from the base point `k`. -/
theorem arcCount_full (Z : Set V) (k n : ℕ) (hnn : C.length = n) :
    arcCount G Z C k n = WheelParity.cycCount G Z C C.length := by
  have h1 := arcCount_eq (G := G) (C := C) Z k n
  have h2 := WheelParity.cycCount_add_length (G := G) (Y := Z) (C := C) k
  rw [hnn] at h2
  rw [hnn]
  omega

end Setup


/-! ## `Y'`: a minimal anticonnected subset with an odd arc-count, to which `v` is not complete -/

section Choice

variable {k n L : ℕ} {D : ℕ → V} {Y : Set V} {v : V}

theorem cycEdge_iff' {W : List V} {Z : Set V} {p : ℕ} {α β : V}
    (ha : W[p % W.length]? = some α) (hb : W[(p + 1) % W.length]? = some β) :
    WheelParity.CycEdge G Z W p ↔ EdgeComplete G Z α β := by
  constructor
  · rintro ⟨u, w, hu, hw, hE⟩
    obtain rfl : α = u := Option.some_injective _ (ha.symm.trans hu)
    obtain rfl : β = w := Option.some_injective _ (hb.symm.trans hw)
    exact hE
  · intro hE
    exact ⟨α, β, ha, hb, hE⟩

theorem getElem_eq_of_getElem? {W : List V} {i : ℕ} {z : V} (hi : i < W.length)
    (h : W[i]? = some z) : W[i]'hi = z :=
  Option.some_injective _ ((List.getElem?_eq_getElem hi).symm.trans h)

/-- PAPER: *"Since `p₁, p_j` have opposite wheel-parity with respect to `(C,Y)`, there are an odd
number of `Y`-complete edges in `P`."* -/
theorem odd_arcCount [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y : Set V} (hw : IsWheel G C Y) (hn : 0 < C.length) {k L : ℕ} {x y : V}
    (hx : C[k % C.length]? = some x) (hy : C[(k + L) % C.length]? = some y)
    (hopp : OppositeWheelParity G C Y x y) :
    Odd (arcCount G Y C k L) := by
  have hC : IsHoleList G C := hw.1.1
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hw
  have hi : k % C.length < C.length := Nat.mod_lt _ hn
  have hj : (k + L) % C.length < C.length := Nat.mod_lt _ hn
  have hxe : C[k % C.length]'hi = x := getElem_eq_of_getElem? hi hx
  have hye : C[(k + L) % C.length]'hj = y := getElem_eq_of_getElem? hj hy
  have hij : k % C.length ≠ (k + L) % C.length := fun h =>
    hopp.1 (hxe.symm.trans ((HoleArithmetic.getElem_congr_idx C hi hj h).trans hye))
  have hsw := WheelParity.sameWheelParity_iff (Y := Y) hC heven hi hj hij
  rw [hxe, hye] at hsw
  have hne : ¬ (WheelParity.cycCount G Y C (k % C.length) % 2
      = WheelParity.cycCount G Y C ((k + L) % C.length) % 2) := fun h => hopp.2.2.2 (hsw.mpr h)
  have e1 := WheelParity.cycCount_mod_two (G := G) (Y := Y) (C := C) heven k
  have e2 := WheelParity.cycCount_mod_two (G := G) (Y := Y) (C := C) heven (k + L)
  have e3 := arcCount_eq (G := G) (C := C) Y k L
  rw [Nat.odd_iff]
  omega

theorem exists_minimal [Fintype V] [DecidableEq V] {G : SimpleGraph V} {C : List V} {Y : Set V}
    {v : V} {k L : ℕ} (hYanti : AnticonnectedSet G Y) (hvnc : ¬ VertexComplete G v Y)
    (hodd : Odd (arcCount G Y C k L)) :
    ∃ Y' : Set V, Y' ⊆ Y ∧ AnticonnectedSet G Y' ∧ Odd (arcCount G Y' C k L) ∧
      ¬ VertexComplete G v Y' ∧
      ∀ Z : Set V, Z ⊆ Y' → AnticonnectedSet G Z → Odd (arcCount G Z C k L) →
        ¬ VertexComplete G v Z → Z = Y' := by
  obtain ⟨Y', ⟨h1, h2, h3, h4⟩, hmin⟩ :=
    ExtremalChoice.exists_min_nat
      (fun Z : Set V => Z ⊆ Y ∧ AnticonnectedSet G Z ∧ Odd (arcCount G Z C k L) ∧
        ¬ VertexComplete G v Z)
      (fun Z => Z.ncard) ⟨Y, subset_rfl, hYanti, hodd, hvnc⟩
  refine ⟨Y', h1, h2, h3, h4, fun Z hZY' hZa hZodd hZv => ?_⟩
  exact Set.eq_of_subset_of_ncard_le hZY'
    (hmin Z ⟨hZY'.trans h1, hZa, hZodd, hZv⟩) (Set.toFinite _)

/-- The `Y'`-complete edges of the hole `v-p₁-⋯-p_j-v` are exactly those of the arc, because `v`
itself is not `Y'`-complete. -/
theorem cycCount_bigHole (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) {Z : Set V} (hvZ : ¬ VertexComplete G v Z) :
    WheelParity.cycCount G Z (bigHole C k L v) (bigHole C k L v).length
      = arcCount G Z C k L := by
  have hlen : (bigHole C k L v).length = L + 2 := bigHole_length (v := v) (by omega)
  have hHm : ∀ m, m ≤ L → (bigHole C k L v)[m % (bigHole C k L v).length]? = some (D m) := by
    intro m hm
    rw [hlen, Nat.mod_eq_of_lt (by omega)]
    exact bigHole_get hn hD (by omega) hm
  have hHv : (bigHole C k L v)[(L + 1) % (bigHole C k L v).length]? = some v := by
    rw [hlen, Nat.mod_eq_of_lt (by omega)]
    exact bigHole_get_v (by omega)
  have hHw : (bigHole C k L v)[(L + 1 + 1) % (bigHole C k L v).length]? = some (D 0) := by
    rw [hlen, show L + 1 + 1 = L + 2 from rfl, Nat.mod_self]
    exact bigHole_get hn hD (by omega) (Nat.zero_le L)
  have hCm : ∀ m, WheelParity.CycEdge G Z C (k + m) ↔ EdgeComplete G Z (D m) (D (m + 1)) := by
    intro m
    refine cycEdge_iff' (hD m) ?_
    have := hD (m + 1)
    rw [show k + (m + 1) = k + m + 1 from by omega] at this
    exact this
  have hHedge : ∀ m, m < L →
      (WheelParity.CycEdge G Z (bigHole C k L v) m ↔ WheelParity.CycEdge G Z C (k + m)) := by
    intro m hm
    rw [cycEdge_iff' (hHm m (by omega)) (hHm (m + 1) (by omega)), hCm m]
  have hHL : ¬ WheelParity.CycEdge G Z (bigHole C k L v) L := by
    rw [cycEdge_iff' (hHm L le_rfl) (by simpa using hHv)]
    exact fun hE => hvZ hE.2.2
  have hHL1 : ¬ WheelParity.CycEdge G Z (bigHole C k L v) (L + 1) := by
    rw [cycEdge_iff' hHv hHw]
    exact fun hE => hvZ hE.2.1
  have hsum := WheelParity.cycCount_eq_sum (G := G) (Y := Z) (C := bigHole C k L v) (L + 2)
  have hadd := WheelParity.cycCount_add (G := G) (Y := Z) (C := C) k L
  have hac := arcCount_eq (G := G) (C := C) Z k L
  rw [hlen, hsum, Finset.sum_range_succ, Finset.sum_range_succ,
    if_neg hHL1, if_neg hHL, arcCount, hadd, Nat.add_sub_cancel_left, Nat.add_zero]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hiff := hHedge m (Finset.mem_range.mp hm)
  by_cases hcase : WheelParity.CycEdge G Z (bigHole C k L v) m
  · rw [if_pos hcase, if_pos (hiff.mp hcase)]
  · rw [if_neg hcase, if_neg (fun hh => hcase (hiff.mpr hh))]

end Choice


/-! ## The two `Y'`-complete vertices of the hole, and the far `Y'`-complete vertex -/

section Config

variable {k n L : ℕ} {D : ℕ → V} {Y : Set V} {v : V}

/-- PAPER: *"From 2.3 applied to the hole `v-p₁-⋯-p_j-v`, it contains just one `Y'`-complete edge
and only two `Y'`-complete vertices.  Hence there exists `i` with `1 ≤ i < j` such that
`p_i, p_{i+1}` are the only `Y'`-complete vertices in `P`."* -/
theorem two_complete [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y' : Set V} {v : V} {D : ℕ → V} {k n L : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hvC : v ∉ C) (hvY' : v ∉ Y')
    (hY'anti : AnticonnectedSet G Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hvZ : ¬ VertexComplete G v Y') (hodd : Odd (arcCount G Y' C k L)) :
    ∃ s, s + 1 ≤ L ∧ VertexComplete G (D s) Y' ∧ VertexComplete G (D (s + 1)) Y' ∧
      ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1) := by
  have hH : IsHoleList G (bigHole C k L v) := bigHole_isHole hC hn hD hnn hL1 hL2 hvC hvD
  have hmem : ∀ z : V, z ∈ bigHole C k L v ↔ ((∃ t, t ≤ L ∧ z = D t) ∨ z = v) :=
    fun z => bigHole_mem_iff (v := v) hC hn hD hnn (show L + 1 ≤ n by omega)
  have hHY' : ∀ w ∈ bigHole C k L v, w ∉ Y' := by
    intro w hwmem
    rcases (hmem w).mp hwmem with ⟨t, ht, rfl⟩ | rfl
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
  have hcnt := cycCount_bigHole (v := v) hC hn hD hnn hL1 hL2 (Z := Y') hvZ
  have hnc := WheelParity.ncard_yEdges_eq_cycCount (Y := Y') hH
  have hoddset : Odd {e : Sym2 V | ∃ u ∈ bigHole C k L v, ∃ w ∈ bigHole C k L v,
      e = s(u, w) ∧ EdgeComplete G Y' u w}.ncard := by
    rw [hnc, hcnt]; exact hodd
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y' hY'anti (bigHole C k L v)
      (Or.inr hH) hHY').2 hH with heven | ⟨a, b, hset, hab, hadjab⟩
  · exact absurd heven (by simpa [Nat.odd_iff, Nat.even_iff] using hoddset)
  · have ha : a ∈ bigHole C k L v ∧ VertexComplete G a Y' := by
      have : a ∈ ({a, b} : Set V) := Set.mem_insert _ _
      rw [← hset] at this; exact this
    have hb : b ∈ bigHole C k L v ∧ VertexComplete G b Y' := by
      have : b ∈ ({a, b} : Set V) := Set.mem_insert_of_mem _ rfl
      rw [← hset] at this; exact this
    obtain ⟨ta, hta, rfl⟩ : ∃ t, t ≤ L ∧ a = D t := by
      rcases (hmem a).mp ha.1 with h | rfl
      · exact h
      · exact absurd ha.2 hvZ
    obtain ⟨tb, htb, rfl⟩ : ∃ t, t ≤ L ∧ b = D t := by
      rcases (hmem b).mp hb.1 with h | rfl
      · exact h
      · exact absurd hb.2 hvZ
    have hcase := (rim_adj hC hn hD hnn (show ta < n by omega) (show tb < n by omega)).mp hadjab
    have honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = ta ∨ t = tb) := by
      intro t ht hcomp
      have hin : D t ∈ ({D ta, D tb} : Set V) := by
        rw [← hset]; exact ⟨(hmem (D t)).mpr (Or.inl ⟨t, ht, rfl⟩), hcomp⟩
      rcases hin with h | h
      · exact Or.inl (rim_inj hC hn hD hnn (by omega) (by omega) h)
      · exact Or.inr (rim_inj hC hn hD hnn (by omega) (by omega) h)
    rcases hcase with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨ta, by omega, ha.2, by rw [← h]; exact hb.2, fun t h1 h2 => by
        rcases honly t h1 h2 with hh | hh
        · exact Or.inl hh
        · exact Or.inr (by omega)⟩
    · exact ⟨tb, by omega, hb.2, by rw [← h]; exact ha.2, fun t h1 h2 => by
        rcases honly t h1 h2 with hh | hh
        · exact Or.inr (by omega)
        · exact Or.inl hh⟩
    · omega
    · omega

/-- PAPER: *"There are two disjoint `Y'`-complete edges in `C`, so one of them does not use `p_i`;
… Hence both its ends are in `{p_{j+1},…,p_n}`.  Consequently `n ≥ j+2`, and since `n` is even and
`j` is odd it follows that `n ≥ j+3`.  Therefore there is a `Y'`-complete vertex in
`{p_{j+2},…,p_{n−1}}`."* -/
theorem far_complete [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hBerge : Berge G)
    {C : List V} {Y Y' : Set V} {D : ℕ → V} {k n L s : ℕ}
    (hw : IsWheel G C Y) (hY'Y : Y' ⊆ Y)
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hLeven : Even L) (hseven : Even s) (hsL : s + 1 ≤ L)
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1)) :
    L + 4 ≤ n ∧ ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y' := by
  have hneven : Even n := by
    have := hBerge.1 C hC
    rw [holeLength, hnn] at this
    exact this
  have hsL' : s + 1 < L := by
    rcases hLeven with ⟨r, hr⟩; rcases hseven with ⟨r', hr'⟩; omega
  obtain ⟨a, b, c, d, haC, hbC, hcC, hdC, hEab, hEcd, hac, had, hbc, hbd⟩ := hw.2.2
  have hmono : ∀ u : V, VertexComplete G u Y → VertexComplete G u Y' :=
    fun u hu z hz => hu z (hY'Y hz)
  -- index the four ends
  obtain ⟨ia, hia, rfl⟩ := rim_surj hC hn hD hnn haC
  obtain ⟨ib, hib, rfl⟩ := rim_surj hC hn hD hnn hbC
  obtain ⟨ic, hic, rfl⟩ := rim_surj hC hn hD hnn hcC
  obtain ⟨id', hid, rfl⟩ := rim_surj hC hn hD hnn hdC
  have hiac : ia ≠ ic := fun h => hac (by rw [h])
  have hiad : ia ≠ id' := fun h => had (by rw [h])
  have hibc : ib ≠ ic := fun h => hbc (by rw [h])
  have hibd : ib ≠ id' := fun h => hbd (by rw [h])
  -- the key: an edge whose two ends are `Y'`-complete and whose indices avoid `s` lies beyond `L`
  have key : ∀ p q : ℕ, p < n → q < n → G.Adj (D p) (D q) →
      VertexComplete G (D p) Y' → VertexComplete G (D q) Y' → p ≠ s → q ≠ s →
      (L + 1 ≤ p ∧ L + 1 ≤ q) := by
    intro p q hp hq hadj hcp hcq hps hqs
    have hcase := (rim_adj hC hn hD hnn hp hq).mp hadj
    constructor
    · by_contra hcon
      have hpL : p ≤ L := by omega
      have := honly p hpL hcp
      have hp1 : p = s + 1 := by omega
      -- the other end is `s` or `s+2`, both impossible
      have hq2 : q = s + 2 := by omega
      have := honly q (by omega) hcq
      omega
    · by_contra hcon
      have hqL : q ≤ L := by omega
      have := honly q hqL hcq
      have hq1 : q = s + 1 := by omega
      have hp2 : p = s + 2 := by omega
      have := honly p (by omega) hcp
      omega
  -- one of the two edges avoids `D s`
  have hpair : ∃ p q : ℕ, p < n ∧ q < n ∧ G.Adj (D p) (D q) ∧
      VertexComplete G (D p) Y' ∧ VertexComplete G (D q) Y' ∧ p ≠ s ∧ q ≠ s := by
    by_cases h1 : ia = s
    · exact ⟨ic, id', hic, hid, hEcd.1, hmono _ hEcd.2.1, hmono _ hEcd.2.2,
        fun h => hiac (h1.trans h.symm), fun h => hiad (h1.trans h.symm)⟩
    · by_cases h2 : ib = s
      · exact ⟨ic, id', hic, hid, hEcd.1, hmono _ hEcd.2.1, hmono _ hEcd.2.2,
          fun h => hibc (h2.trans h.symm), fun h => hibd (h2.trans h.symm)⟩
      · exact ⟨ia, ib, hia, hib, hEab.1, hmono _ hEab.2.1, hmono _ hEab.2.2, h1, h2⟩
  obtain ⟨p, q, hp, hq, hadj, hcp, hcq, hps, hqs⟩ := hpair
  obtain ⟨hpL, hqL⟩ := key p q hp hq hadj hcp hcq hps hqs
  have hcase := (rim_adj hC hn hD hnn hp hq).mp hadj
  have hpq : p ≠ q := by rintro rfl; exact G.irrefl hadj
  have hn3 : L + 3 ≤ n := by omega
  have hn4 : L + 4 ≤ n := by
    rcases hLeven with ⟨r, hr⟩; rcases hneven with ⟨r', hr'⟩; omega
  refine ⟨hn4, ?_⟩
  rcases hcase with hc | hc | ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
  · rcases (show L + 2 ≤ p ∨ p = L + 1 by omega) with h | h
    · exact ⟨p, h, by omega, hcp⟩
    · exact ⟨q, by omega, by omega, hcq⟩
  · rcases (show L + 2 ≤ q ∨ q = L + 1 by omega) with h | h
    · exact ⟨q, h, by omega, hcq⟩
    · exact ⟨p, by omega, by omega, hcp⟩
  · omega
  · omega

end Config

end Workspace.ProofLemmas.OddWheelArc
