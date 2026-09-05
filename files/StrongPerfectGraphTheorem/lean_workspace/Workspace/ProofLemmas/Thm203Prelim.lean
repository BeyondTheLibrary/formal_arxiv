import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.ProofLemmas.WheelSystemBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.Thm134RegionAux

/-!
# §19–20 bookkeeping used silently by the printed proof of 20.3

The proof of 20.3 (printed pp. 125–127) uses four facts about the sets `Xᵢ`, `Aᵢ`
of a wheel system without ever stating them:

* `anticonnected_wheelSystemX` — every `Xᵢ` is **anticonnected**.  This is what makes
  the phrase *"let `Q` be an antipath between `u` and `v` with interior in `X_{t−2}`"*
  meaningful.  It holds because clause 3 of the wheel-system definition says `xᵢ` is
  not `X_{i−1}`-complete, i.e. `xᵢ` has a neighbour in `Ḡ|X_{i−1}`.

* `A₀_no_complete` / `A₀_subset_wheelSystemA'` — `A₀ ⊆ Aᵢ` for every `i ≥ 1`: no vertex
  of `A₀` is `{x₀,x₁}`-complete (part of the wheel-system definition), hence none is
  `Xᵢ`-complete.

* `notMem_wheelSystemA_of_adj_z` — a neighbour of `z` is never in `Aᵢ`.

* `vertexComplete_of_nbr_of_notMem` — the paper's *"from the maximality of `A_{t−3}` it
  follows that `q` is `X_{t−3}`-complete"*: a vertex `v ∉ Aᵢ` which is not adjacent to
  `z` but has a neighbour in `Aᵢ` **must** be `Xᵢ`-complete, since otherwise
  `Aᵢ ∪ {v}` would belong to the family defining `Aᵢ`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm203Prelim

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## `Xᵢ` -/

theorem wheelSystemX_succ (x : ℕ → V) (i : ℕ) :
    wheelSystemX x (i + 1) = wheelSystemX x i ∪ {x (i + 1)} := by
  ext v
  simp only [wheelSystemX, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    rcases Nat.lt_or_ge k (i + 1) with h | h
    · exact Or.inl ⟨k, by omega, rfl⟩
    · have : k = i + 1 := by omega
      exact Or.inr (by rw [this])
  · rintro (⟨k, hk, rfl⟩ | rfl)
    · exact ⟨k, by omega, rfl⟩
    · exact ⟨i + 1, le_rfl, rfl⟩

/-- **Every `Xᵢ` is anticonnected.**  Induction on `i`: `X₀ = {x₀}` is a singleton, and
`xᵢ₊₁` is not `Xᵢ`-complete, so it has a `Ḡ`-neighbour in `Xᵢ`. -/
theorem anticonnected_wheelSystemX {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (hws : IsWheelSystem G z A₀ x t) :
    ∀ i ≤ t, AnticonnectedSet G (wheelSystemX x i) := by
  intro i
  induction i with
  | zero =>
    intro _
    rw [WheelSystemBasics.wheelSystemX_zero]
    exact Thm134RegionAux.connectedSet_singleton Gᶜ (x 0)
  | succ n ih =>
    intro hn
    have hIH := ih (by omega)
    obtain ⟨w, hw, hnadj⟩ : ∃ w ∈ wheelSystemX x n, ¬ G.Adj (x (n + 1)) w := by
      by_contra hcon
      push_neg at hcon
      exact hws.2.2.2.2.2.1 (n + 1) (by omega) hn (by
        intro w hw
        have h := hcon w hw
        exact h)
    have hne : x (n + 1) ∉ wheelSystemX x n := by
      intro hmem
      obtain ⟨k, hk, hkeq⟩ := hmem
      have := hws.2.1 (n + 1) hn k (by omega) hkeq
      omega
    rw [wheelSystemX_succ]
    refine ConnectedSetUnionAttach.connectedSet_union_singleton (G := Gᶜ) hIH ⟨w, hw, ?_⟩
    rw [SimpleGraph.compl_adj]
    exact ⟨fun h => hne (h ▸ hw), hnadj⟩

/-! ## `Aᵢ` -/

/-- No vertex of `A₀` is `Xᵢ`-complete, for `i ≥ 1`. -/
theorem A₀_no_complete {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V} {t : ℕ}
    (hws : IsWheelSystem G z A₀ x t) {i : ℕ} (hi : 1 ≤ i) :
    ∀ v ∈ A₀, ¬ VertexComplete G v (wheelSystemX x i) := by
  intro v hv hcon
  refine hws.2.2.2.1.2.2 v hv ?_
  intro w hw
  rcases hw with hw | hw
  · exact hcon w (WheelSystemBasics.mem_wheelSystemX.2 ⟨0, by omega, hw⟩)
  · rw [Set.mem_singleton_iff] at hw
    exact hcon w (WheelSystemBasics.mem_wheelSystemX.2 ⟨1, by omega, hw⟩)

/-- `A₀ ⊆ Aᵢ` for `i ≥ 1`. -/
theorem A₀_subset_wheelSystemA' {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t) {i : ℕ}
    (hi : 1 ≤ i) : A₀ ⊆ wheelSystemA G z A₀ x i :=
  WheelSystemBasics.A₀_subset_wheelSystemA hframe (A₀_no_complete hws hi)

/-- A neighbour of `z` never lies in `Aᵢ`. -/
theorem notMem_wheelSystemA_of_adj_z {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {i : ℕ} {v : V} (h : G.Adj z v) : v ∉ wheelSystemA G z A₀ x i :=
  fun hv => WheelSystemBasics.wheelSystemA_no_nbr hv h

/-- No `xⱼ` lies in any `Aᵢ`: `z` is adjacent to every `xⱼ`. -/
theorem x_notMem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hws : IsWheelSystem G z A₀ x t) {i j : ℕ} (hj : j ≤ t) :
    x j ∉ wheelSystemA G z A₀ x i :=
  notMem_wheelSystemA_of_adj_z (hws.2.2.2.2.2.2 j hj)

/-- `z ∉ Aᵢ` for `i ≤ t`: `z` is `Xᵢ`-complete, and `Aᵢ` has no `Xᵢ`-complete vertex. -/
theorem z_notMem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hws : IsWheelSystem G z A₀ x t) {i : ℕ} (hi : i ≤ t) :
    z ∉ wheelSystemA G z A₀ x i := by
  intro hz
  refine WheelSystemBasics.wheelSystemA_no_complete hz ?_
  rintro w ⟨j, hj, rfl⟩
  exact hws.2.2.2.2.2.2 j (by omega)

/-- **Condition 2 of the wheel-system definition, in `Aᵢ` form.**  `xᵢ` has a neighbour in
`A_{i−1}`, hence in every `A_k` with `k ≥ i − 1` (and `k ≥ 1`).  For `i = 0, 1` the
neighbour is supplied by the frame clause and `A₀ ⊆ A_k`. -/
theorem exists_nbr_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t)
    {i k : ℕ} (hi : i ≤ t) (hk : 1 ≤ k) (hik : i ≤ k + 1) :
    ∃ a ∈ wheelSystemA G z A₀ x k, G.Adj (x i) a := by
  have hA₀ : A₀ ⊆ wheelSystemA G z A₀ x k := A₀_subset_wheelSystemA' hframe hws hk
  rcases Nat.lt_or_ge i 2 with hlt | hge
  · interval_cases i
    · obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.1
      exact ⟨a, hA₀ ha, hadj⟩
    · obtain ⟨a, ha, hadj⟩ := hws.2.2.2.1.2.1
      exact ⟨a, hA₀ ha, hadj⟩
  · obtain ⟨B, hB0, hBc, ⟨b, hb, hadj⟩, hBz, hBnc⟩ := hws.2.2.2.2.1 i hge hi
    exact ⟨b, WheelSystemBasics.wheelSystemA_mono (by omega)
      (WheelSystemBasics.mem_wheelSystemA_of_witness hB0 hBc hBz hBnc hb), hadj⟩

/-- **The hub misses every `Aⱼ` with `j < t`.**  Every `y ∈ Y` is adjacent to `x₀,…,x_{t−1}`
(that is what *"`x₀,…,x_{t−1}` are `Y`-complete"* says), hence is `Xⱼ`-complete for `j < t`,
hence is not in `Aⱼ`.  The paper uses this silently whenever it needs a vertex of `A_{t−2}`
to lie outside the hub. -/
theorem Y_notMem_wheelSystemA {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {t : ℕ} {Y : Set V} (hVC : ∀ i < t, VertexComplete G (x i) Y) {j : ℕ} (hj : j < t)
    {y : V} (hy : y ∈ Y) : y ∉ wheelSystemA G z A₀ x j := by
  intro hmem
  refine WheelSystemBasics.wheelSystemA_no_complete hmem ?_
  rintro w ⟨k, hk, rfl⟩
  exact (hVC k (by omega) y hy).symm

/-- **The maximality of `Aᵢ`.**  If `v ∉ Aᵢ`, `z` is not adjacent to `v`, and `v` has a
neighbour in `Aᵢ`, then `v` is `Xᵢ`-complete — otherwise `Aᵢ ∪ {v}` would be a member of
the family whose union is `Aᵢ`. -/
theorem vertexComplete_of_nbr_of_notMem {G : SimpleGraph V} {z : V} {A₀ : Set V}
    {x : ℕ → V} {t : ℕ} (hframe : IsFrame G z A₀) (hws : IsWheelSystem G z A₀ x t)
    {i : ℕ} (hi : 1 ≤ i) {v : V} (hz : ¬ G.Adj z v)
    (hnot : v ∉ wheelSystemA G z A₀ x i)
    (hnbr : ∃ a ∈ wheelSystemA G z A₀ x i, G.Adj v a) :
    VertexComplete G v (wheelSystemX x i) := by
  by_contra hcon
  refine hnot ?_
  refine WheelSystemBasics.mem_wheelSystemA_of_witness
    (B := wheelSystemA G z A₀ x i ∪ {v})
    (Set.Subset.trans (A₀_subset_wheelSystemA' hframe hws hi) Set.subset_union_left)
    (ConnectedSetUnionAttach.connectedSet_union_singleton
      (WheelSystemBasics.connectedSet_wheelSystemA hframe.1) hnbr)
    ?_ ?_ (Or.inr rfl)
  · rintro w (hw | hw)
    · exact WheelSystemBasics.wheelSystemA_no_nbr hw
    · rw [Set.mem_singleton_iff] at hw; subst hw; exact hz
  · rintro w (hw | hw)
    · exact WheelSystemBasics.wheelSystemA_no_complete hw
    · rw [Set.mem_singleton_iff] at hw; subst hw; exact hcon

end Workspace.ProofLemmas.Thm203Prelim
