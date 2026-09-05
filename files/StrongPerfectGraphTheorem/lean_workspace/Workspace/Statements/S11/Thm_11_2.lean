import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S10.Thm_10_1
import Workspace.Statements.S11.Thm_11_1
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

namespace Workspace.Statements.S11

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace SPGT

section Helpers

variable {V : Type*}

private theorem exists_least {Q : ℕ → Prop} (n : ℕ) (h : ∃ k, k < n ∧ Q k) :
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < k → ¬ Q m := by
  classical
  obtain ⟨k, hk, hQk⟩ := h
  have hex : ∃ m, Q m := ⟨k, hQk⟩
  exact ⟨Nat.find hex, lt_of_le_of_lt (Nat.find_min' hex hQk) hk, Nat.find_spec hex,
    fun m hm => Nat.find_min hex hm⟩

private theorem mem_take_iff (p : List V) (k : ℕ) (x : V) :
    x ∈ p.take k ↔ ∃ (i : ℕ) (hi : i < p.length), i < k ∧ p[i]'hi = x := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_take, lt_min_iff] at hj
    exact ⟨j, hj.2, hj.1, by rw [← hjx]; simp⟩
  · rintro ⟨i, hi, hik, rfl⟩
    refine List.mem_iff_getElem.mpr ⟨i, ?_, ?_⟩
    · rw [List.length_take, lt_min_iff]; exact ⟨hik, hi⟩
    · simp

private theorem mem_drop_iff (p : List V) (k : ℕ) (x : V) :
    x ∈ p.drop k ↔ ∃ (i : ℕ) (hi : i < p.length), k ≤ i ∧ p[i]'hi = x := by
  constructor
  · intro hx
    obtain ⟨j, hj, hjx⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_drop] at hj
    refine ⟨k + j, by omega, by omega, ?_⟩
    rw [← hjx, List.getElem_drop]
  · rintro ⟨i, hi, hki, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, i = k + j := ⟨i - k, by omega⟩
    exact List.mem_iff_getElem.mpr
      ⟨j, by rw [List.length_drop]; omega, by rw [List.getElem_drop]⟩

/-- Every vertex of a rung of the strip `(A, C, B)` lies in `V(S) = A ∪ B ∪ C`. -/
private theorem rung_mem_ABC {G : SimpleGraph V} {A C B : Set V} {a b : V} {p : List V}
    (h : IsRungOfStrip G A C B a p b) : ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (by rw [hwa]; exact h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (by rw [hwb]; exact h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr ⟨hw, hwa, hwb⟩))

/-- The paper's *"`R₀`, `R₁`, `R₂` form a prism"*, edge clause between the banister and a
rung: the only edges between a banister `a₀-R₀-b₀` and a rung `a-R-b` are `a₀a` and `b₀b`. -/
private theorem banister_rung_edges {G : SimpleGraph V} {A C B : Set V} {a₀ b₀ a b : V}
    {R₀ R : List V} (hban : IsBanister G A C B a₀ R₀ b₀)
    (hr : IsRungOfStrip G A C B a R b) :
    ∀ u ∈ R₀, ∀ w ∈ R, (G.Adj u w ↔ (u = a₀ ∧ w = a) ∨ (u = b₀ ∧ w = b)) := by
  obtain ⟨hR₀path, hR₀avoid, hLS, hRS, hR₀int⟩ := hban
  intro u hu w hw
  constructor
  · intro hadj
    have hwS : w ∈ A ∪ B ∪ C := rung_mem_ABC hr w hw
    by_cases hua : u = a₀
    · subst hua
      refine Or.inl ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact hr.2.2.2.1 w hw hwA
      · exact absurd hadj (hLS.2.2 w (Or.inl hwB))
      · exact absurd hadj (hLS.2.2 w (Or.inr hwC))
    by_cases hub : u = b₀
    · subst hub
      refine Or.inr ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact absurd hadj (hRS.2.2 w (Or.inl hwA))
      · exact hr.2.2.2.2.1 w hw hwB
      · exact absurd hadj (hRS.2.2 w (Or.inr hwC))
    · exact absurd hadj (hR₀int u
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
          ⟨hu, hua, hub⟩) w hwS)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hLS.2.1 w hr.2.1
    · exact hRS.2.1 w hr.2.2.1

/-- If every neighbour of `w` among `x, y, z` equals `c`, then `w` has at most one neighbour
in `{x, y, z}`, so it does not saturate a triangle. -/
private theorem not_two_le_ncard {G : SimpleGraph V} {x y z c w : V}
    (hx : G.Adj w x → x = c) (hy : G.Adj w y → y = c) (hz : G.Adj w z → z = c) :
    ¬ (2 ≤ (({x, y, z} : Set V) ∩ G.neighborSet w).ncard) := by
  have hsub : ({x, y, z} : Set V) ∩ G.neighborSet w ⊆ ({c} : Set V) := by
    rintro t ⟨ht1, ht2⟩
    have ht2' : G.Adj w t := ht2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht1 ⊢
    rcases ht1 with rfl | rfl | rfl
    · exact hx ht2'
    · exact hy ht2'
    · exact hz ht2'
  intro hle
  have hcard := Set.ncard_le_ncard hsub (Set.finite_singleton _)
  rw [Set.ncard_singleton] at hcard
  omega

end Helpers

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem thm_11_2 (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (A C B : Set V) (hS : StepConnected G A C B)
    (a₀ b₀ : V) (R₀ : List V) (hban : IsBanister G A C B a₀ R₀ b₀)
    (v : V) (hv : v ∉ A ∪ B ∪ C)
    (hvS : ∃ x ∈ A ∪ B ∪ C, G.Adj v x)
    (hvb₀ : ¬ G.Adj v b₀)
    (P Q : List V)
    (hP : IsPathFrom G P v a₀)
    (hPavoid : ∀ w ∈ P, w ∉ (A ∪ B ∪ C) ∪ ({b₀} : Set V))
    (hQ : IsPathFrom G Q v b₀)
    (hQavoid : ∀ w ∈ Q, w ∉ (A ∪ B ∪ C) ∪ ({a₀} : Set V))
    (hPQint : SPGT.Anticomplete G
      ({w : V | w ∈ SPGT.interior P} ∪ {w : V | w ∈ SPGT.interior Q}) (A ∪ B ∪ C)) :
    SPGT.VertexComplete G v B ∨ IsLeftStar G A C B v := by
  classical
  obtain ⟨hR₀path, hR₀avoid, hLS, hRS, hR₀int⟩ := id hban
  obtain ⟨⟨hdAB, hdAC, hdBC⟩, ⟨hAne, hBne⟩, -, -, hpart⟩ := id hS
  -- Degenerate positions of `v` on the banister, left implicit by the paper.
  by_cases hvne_b₀ : v = b₀
  · exact Or.inl (by rw [hvne_b₀]; exact hRS.2.1)
  by_cases hvne_a₀ : v = a₀
  · exact Or.inr (by rw [hvne_a₀]; exact hLS)
  have hvR₀ : v ∉ R₀ := by
    intro hc
    obtain ⟨x, hxS, hadjx⟩ := hvS
    exact hR₀int v
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
        ⟨hc, hvne_a₀, hvne_b₀⟩) x hxS hadjx
  -- "If `v` has no neighbours in `B`, then by 11.1 `v` is a left-star"
  by_cases hvBanti : SPGT.VertexAnticomplete G v B
  · refine Or.inr (thm_11_1 G hG ?_ A C B hS a₀ b₀ R₀ hban v hv ?_ hvBanti Q hQ hQavoid ?_)
    · rintro ⟨n, H, K', happ, -⟩
      exact hK4 ⟨n, H, K', happ⟩
    · obtain ⟨x, hxS, hadjx⟩ := hvS
      rcases hxS with (hxA | hxB) | hxC
      · exact ⟨x, Or.inl hxA, hadjx⟩
      · exact absurd hadjx (hvBanti x hxB)
      · exact ⟨x, Or.inr hxC, hadjx⟩
    · exact fun w hw => hPQint w (Or.inr hw)
  -- "so we may assume `v` has a neighbour in `B`.  Since we may assume it is not
  -- `B`-complete, ..."
  by_cases hvBcomp : SPGT.VertexComplete G v B
  · exact Or.inl hvBcomp
  exfalso
  have hy₁ : ∃ y ∈ B, G.Adj v y := by
    by_contra hc
    exact hvBanti (fun x hx hadj => hc ⟨x, hx, hadj⟩)
  have hy₂ : ∃ y ∈ B, ¬ G.Adj v y := by
    by_contra hc
    exact hvBcomp (fun x hx => not_not.mp (fun h => hc ⟨x, hx, h⟩))
  obtain ⟨y₁, hy₁B, hvy₁⟩ := hy₁
  obtain ⟨y₂, hy₂B, hvy₂⟩ := hy₂
  -- "... there is a step `a₁-R₁-b₁`, `a₂-R₂-b₂` such that `v` is adjacent to `b₁` and not
  -- to `b₂`" — apply step-connectivity to the partition of `B` into neighbours and
  -- non-neighbours of `v`.
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hXend, hYend⟩ :=
    hpart {x : V | x ∈ B ∧ G.Adj v x} {x : V | x ∈ B ∧ ¬ G.Adj v x}
      (Or.inr (by
        ext x
        simp only [Set.mem_union, Set.mem_setOf_eq]
        constructor
        · rintro (⟨hx, -⟩ | ⟨hx, -⟩) <;> exact hx
        · intro hx
          by_cases h : G.Adj v x
          · exact Or.inl ⟨hx, h⟩
          · exact Or.inr ⟨hx, h⟩))
      (Set.disjoint_left.mpr (fun x hx hx' => hx'.2 hx.2))
      ⟨y₁, hy₁B, hvy₁⟩ ⟨y₂, hy₂B, hvy₂⟩
  obtain ⟨hr₁, hr₂, hdisj12, hcross12⟩ := id hstep
  have ha₁A : a₁ ∈ A := hr₁.2.1
  have hb₁B : b₁ ∈ B := hr₁.2.2.1
  have ha₂A : a₂ ∈ A := hr₂.2.1
  have hb₂B : b₂ ∈ B := hr₂.2.2.1
  have hvb₁ : G.Adj v b₁ := by
    rcases hXend with h | h
    · exact absurd h.1 (Set.disjoint_left.mp hdAB ha₁A)
    · exact h.2
  have hvb₂ : ¬ G.Adj v b₂ := by
    rcases hYend with h | h
    · exact absurd h.1 (Set.disjoint_left.mp hdAB ha₂A)
    · exact h.2
  have ha₁R₁ : a₁ ∈ R₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).1
  have hb₁R₁ : b₁ ∈ R₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₁.1).2
  have ha₂R₂ : a₂ ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).1
  have hb₂R₂ : b₂ ∈ R₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hr₂.1).2
  -- "Now `R₀`, `R₁`, `R₂` form a prism `K` say."
  have hAdj_a0a1 : G.Adj a₀ a₁ := hLS.2.1 a₁ ha₁A
  have hAdj_a0a2 : G.Adj a₀ a₂ := hLS.2.1 a₂ ha₂A
  have hAdj_a1a2 : G.Adj a₁ a₂ := (hcross12 a₁ ha₁R₁ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩)
  have hAdj_b0b1 : G.Adj b₀ b₁ := hRS.2.1 b₁ hb₁B
  have hAdj_b0b2 : G.Adj b₀ b₂ := hRS.2.1 b₂ hb₂B
  have hAdj_b1b2 : G.Adj b₁ b₂ := (hcross12 b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
  have hne_a0b0 : a₀ ≠ b₀ := by
    intro hc
    exact hRS.2.2 a₁ (Or.inl ha₁A) (by rw [← hc]; exact hAdj_a0a1)
  have hne_a0b1 : a₀ ≠ b₁ := by
    intro hc; exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₁B))
  have hne_a0b2 : a₀ ≠ b₂ := by
    intro hc; exact hLS.1 (by rw [hc]; exact Or.inl (Or.inr hb₂B))
  have hne_a1b0 : a₁ ≠ b₀ := by
    intro hc; exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₁A))
  have hne_a2b0 : a₂ ≠ b₀ := by
    intro hc; exact hRS.1 (by rw [← hc]; exact Or.inl (Or.inl ha₂A))
  have hne_a1b1 : a₁ ≠ b₁ := by
    intro hc; exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a1b2 : a₁ ≠ b₂ := by
    intro hc; exact Set.disjoint_left.mp hdAB ha₁A (by rw [← hc] at hb₂B; exact hb₂B)
  have hne_a2b1 : a₂ ≠ b₁ := by
    intro hc; exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₁B; exact hb₁B)
  have hne_a2b2 : a₂ ≠ b₂ := by
    intro hc; exact Set.disjoint_left.mp hdAB ha₂A (by rw [← hc] at hb₂B; exact hb₂B)
  have hcross01 : ∀ u ∈ R₀, ∀ w ∈ R₁,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₁) ∨ (u = b₀ ∧ w = b₁)) := banister_rung_edges hban hr₁
  have hcross02 : ∀ u ∈ R₀, ∀ w ∈ R₂,
      (G.Adj u w ↔ (u = a₀ ∧ w = a₂) ∨ (u = b₀ ∧ w = b₂)) := banister_rung_edges hban hr₂
  have hprism : FormPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ :=
    Workspace.ProofLemmas.PrismBasics.formPrism_of_data hAdj_a0a1 hAdj_a0a2 hAdj_a1a2
      hAdj_b0b1 hAdj_b0b2 hAdj_b1b2 hne_a0b0 hne_a0b1 hne_a0b2 hne_a1b0 hne_a1b1 hne_a1b2
      hne_a2b0 hne_a2b1 hne_a2b2 hR₀path hr₁.1 hr₂.1 hcross01 hcross02 hcross12
  -- "Let `F ⊆ V(Q)` be connected, containing `v` and disjoint from `V(R₀)`, with an
  -- attachment in `R₀ \ b₀`."  (The path the paper calls `Q` is the one called `P` here,
  -- namely the path from `v` to `a₀`.)  `F` is the stretch of `P` before it first meets
  -- `V(R₀)`; it does meet `V(R₀)`, since `a₀` is its last vertex.
  have hPlen : 0 < P.length := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have hP0 : ∀ h : 0 < P.length, P[0]'h = v := fun h =>
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 h
  have hPlast : ∀ h : P.length - 1 < P.length, P[P.length - 1]'h = a₀ := fun _ =>
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hPlen
  have ha₀R₀ : a₀ ∈ R₀ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR₀path).1
  obtain ⟨k, hk, hkR₀, hkmin⟩ :=
    exists_least (Q := fun m => ∃ h : m < P.length, P[m]'h ∈ R₀) P.length
      ⟨P.length - 1, by omega, (by omega : P.length - 1 < P.length),
        by rw [hPlast]; exact ha₀R₀⟩
  obtain ⟨hkP, hkmem⟩ := hkR₀
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | h
    · rw [hP0] at hkmem; exact absurd hkmem hvR₀
    · exact h
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hFmem : ∀ x ∈ P.take (j + 1), x ∈ P := fun x hx => List.mem_of_mem_take hx
  have hFnotR₀ : ∀ x ∈ P.take (j + 1), x ∉ R₀ := by
    intro x hx hc
    obtain ⟨i, hi, hik, rfl⟩ := (mem_take_iff P (j + 1) x).mp hx
    exact hkmin i hik ⟨hi, hc⟩
  have hFnotS : ∀ x ∈ P.take (j + 1), x ∉ A ∪ B ∪ C := fun x hx hc =>
    hPavoid x (hFmem x hx) (Or.inl hc)
  have hvF : v ∈ P.take (j + 1) := (mem_take_iff P (j + 1) v).mpr ⟨0, hPlen, by omega, hP0 hPlen⟩
  have hFint : ∀ x ∈ P.take (j + 1), x ≠ v → x ∈ SPGT.interior P := by
    intro x hx hxv
    obtain ⟨i, hi, hik, rfl⟩ := (mem_take_iff P (j + 1) x).mp hx
    have hi0 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with rfl | h
      · exact absurd (hP0 hi) hxv
      · exact h
    exact Workspace.ProofLemmas.PathBasics.getElem_mem_interior hP.1 hi hi0 (by omega)
  have hFanti : ∀ x ∈ P.take (j + 1), x ≠ v → SPGT.VertexAnticomplete G x (A ∪ B ∪ C) :=
    fun x hx hxv => hPQint x (Or.inl (hFint x hx hxv))
  have hR₁S : ∀ w ∈ R₁, w ∈ A ∪ B ∪ C := rung_mem_ABC hr₁
  have hR₂S : ∀ w ∈ R₂, w ∈ A ∪ B ∪ C := rung_mem_ABC hr₂
  have hFK : {x : V | x ∈ P.take (j + 1)} ⊆
      ({x : V | x ∈ R₀} ∪ {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂})ᶜ := by
    intro x hx
    rintro ((h | h) | h)
    · exact hFnotR₀ x hx h
    · exact hFnotS x hx (hR₁S x h)
    · exact hFnotS x hx (hR₂S x h)
  have hFconn : ConnectedSet G {x : V | x ∈ P.take (j + 1)} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathBasics.isPathList_take hP.1 (by omega))
  -- the attachment of `F` in `R₀ \ b₀`, and the attachment `b₁`
  have hattR₀ : P[j + 1]'hkP ∈ attachments G {x : V | x ∈ P.take (j + 1)}
      ({x : V | x ∈ R₀} ∪ {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂}) :=
    ⟨Or.inl (Or.inl hkmem), P[j]'(by omega),
      (mem_take_iff P (j + 1) _).mpr ⟨j, by omega, by omega, rfl⟩,
      (Workspace.ProofLemmas.PathBasics.path_adj_succ hP.1 (i := j) hkP).symm⟩
  have hb₁att : b₁ ∈ attachments G {x : V | x ∈ P.take (j + 1)}
      ({x : V | x ∈ R₀} ∪ {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂}) :=
    ⟨Or.inl (Or.inr hb₁R₁), v, hvF, hvb₁.symm⟩
  have hPjS : P[j + 1]'hkP ∉ A ∪ B ∪ C := hR₀avoid _ hkmem
  have hPjneb₀ : P[j + 1]'hkP ≠ b₀ := fun hc =>
    hPavoid _ (List.getElem_mem hkP) (Or.inr (by rw [hc]; rfl))
  -- "But there is an attachment of `F` in `R₀ \ b₀`, and `b₁` is also an attachment of `F`,
  -- so its set of attachments is not local with respect to the prism."
  have hFloc : ¬ LocalForPrism ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂
      (attachments G {x : V | x ∈ P.take (j + 1)}
        ({x : V | x ∈ R₀} ∪ {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂})) := by
    intro hloc
    rcases hloc with h | h | h | h | h
    · exact hR₀avoid b₁ (h hb₁att) (Or.inl (Or.inr hb₁B))
    · exact hPjS (hR₁S _ (h hattR₀))
    · exact hPjS (hR₂S _ (h hattR₀))
    · have hb := h hb₁att
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with h' | h' | h'
      · exact hne_a0b1 h'.symm
      · exact hne_a1b1 h'.symm
      · exact hne_a2b1 h'.symm
    · have hb := h hattR₀
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with h' | h' | h'
      · exact hPjneb₀ h'
      · exact hPjS (by rw [h']; exact Or.inl (Or.inr hb₁B))
      · exact hPjS (by rw [h']; exact Or.inl (Or.inr hb₂B))
  -- "no vertex of `F` is major with respect to `K`, since none of them has two neighbours
  -- in `{b₀, b₁, b₂}`"
  have hFmaj : ∀ x ∈ {x : V | x ∈ P.take (j + 1)},
      ¬ MajorForPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] x := by
    intro x hx hmaj
    have h2 := hmaj.2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h2
    by_cases hxv : x = v
    · subst hxv
      exact not_two_le_ncard (x := b₀) (y := b₁) (z := b₂) (c := b₁)
        (fun h => absurd h hvb₀) (fun _ => rfl) (fun h => absurd h hvb₂) h2
    · exact not_two_le_ncard (x := b₀) (y := b₁) (z := b₂) (c := b₀)
        (fun _ => rfl)
        (fun h => absurd h (hFanti x hx hxv b₁ (Or.inl (Or.inr hb₁B))))
        (fun h => absurd h (hFanti x hx hxv b₂ (Or.inl (Or.inr hb₂B)))) h2
  -- "By 10.1, one of 10.1.1–4 holds."
  obtain ⟨f, f₁, fn, hfpath, hfF, hflen, a', b', R', σ, hR'eq, hab', hcase⟩ :=
    _root_.Workspace.Statements.S10.SPGT.thm_10_1 G hG ![a₀, a₁, a₂] ![b₀, b₁, b₂]
      ![R₀, R₁, R₂] ({x : V | x ∈ R₀} ∪ {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂})
      {x : V | x ∈ P.take (j + 1)} hprism rfl hFK hFconn hFloc hFmaj
  -- bookkeeping for the relabelling `σ` of the prism supplied by 10.1
  have h3 : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
  have hcoord : ∀ (c : Fin 3 → V) (x₀ x₁ x₂ : V), (c = fun i => ![x₀, x₁, x₂] (σ i)) →
      ∀ i : Fin 3, (σ i = 0 → c i = x₀) ∧ (σ i = 1 → c i = x₁) ∧ (σ i = 2 → c i = x₂) := by
    intro c x₀ x₁ x₂ hc i
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩ <;> rw [hc] <;> simp [h]
  have hσ01 : σ 0 ≠ σ 1 := fun hc => absurd (σ.injective hc) (by decide)
  have hσne : σ 0 ≠ 0 ∨ σ 1 ≠ 0 := by
    by_cases h : σ 0 = 0
    · exact Or.inr (fun hc => hσ01 (h.trans hc.symm))
    · exact Or.inl h
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? hfpath.2.1
  have hfnmem : fn ∈ f := List.mem_of_mem_getLast? hfpath.2.2
  have hf₁F : f₁ ∈ P.take (j + 1) := hfF f₁ hf₁mem
  have hfnF : fn ∈ P.take (j + 1) := hfF fn hfnmem
  -- "`v` is the only vertex in `F` with neighbours in `A ∪ B`"
  have honlyv : ∀ x ∈ P.take (j + 1), ∀ y ∈ A ∪ B ∪ C, G.Adj x y → x = v := by
    intro x hx y hy hadj
    by_contra hxv
    exact hFanti x hx hxv y hy hadj
  -- "none of them has two neighbours in `{b₀, b₁, b₂}`"
  have htwob : ∀ x ∈ P.take (j + 1), ∀ s t : V,
      (s = b₀ ∨ s = b₁ ∨ s = b₂) → (t = b₀ ∨ t = b₁ ∨ t = b₂) →
      G.Adj x s → G.Adj x t → s = t := by
    intro x hx s t hs ht hxs hxt
    by_cases hxv : x = v
    · subst hxv
      have key : ∀ z : V, (z = b₀ ∨ z = b₁ ∨ z = b₂) → G.Adj x z → z = b₁ := by
        rintro z (rfl | rfl | rfl) hz
        · exact absurd hz hvb₀
        · rfl
        · exact absurd hz hvb₂
      rw [key s hs hxs, key t ht hxt]
    · have hanti := hFanti x hx hxv
      have key : ∀ z : V, (z = b₀ ∨ z = b₁ ∨ z = b₂) → G.Adj x z → z = b₀ := by
        rintro z (rfl | rfl | rfl) hz
        · rfl
        · exact absurd hz (hanti _ (Or.inl (Or.inr hb₁B)))
        · exact absurd hz (hanti _ (Or.inl (Or.inr hb₂B)))
      rw [key s hs hxs, key t ht hxt]
  have hne_f : 2 ≤ f.length → f₁ ≠ fn := fun h2 =>
    Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hfpath
      (by rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]; omega)
  have hA1 : a₁ ∈ A ∪ B ∪ C := Or.inl (Or.inl ha₁A)
  have hA2 : a₂ ∈ A ∪ B ∪ C := Or.inl (Or.inl ha₂A)
  have hB1 : b₁ ∈ A ∪ B ∪ C := Or.inl (Or.inr hb₁B)
  have hB2 : b₂ ∈ A ∪ B ∪ C := Or.inl (Or.inr hb₂B)
  -- the middle vertex of the relabelled triangles always lies in `V(S)`
  have hkey : ∀ i : Fin 3, σ i ≠ 0 → (a' i ∈ A ∪ B ∪ C) ∧ (b' i ∈ A ∪ B ∪ C) := by
    intro i hi
    rcases h3 (σ i) with h | h | h
    · exact absurd h hi
    · rcases hab' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨by rw [(hcoord a' a₀ a₁ a₂ e1 i).2.1 h]; exact hA1,
              by rw [(hcoord b' b₀ b₁ b₂ e2 i).2.1 h]; exact hB1⟩
      · exact ⟨by rw [(hcoord a' b₀ b₁ b₂ e1 i).2.1 h]; exact hB1,
              by rw [(hcoord b' a₀ a₁ a₂ e2 i).2.1 h]; exact hA1⟩
    · rcases hab' with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact ⟨by rw [(hcoord a' a₀ a₁ a₂ e1 i).2.2 h]; exact hA2,
              by rw [(hcoord b' b₀ b₁ b₂ e2 i).2.2 h]; exact hB2⟩
      · exact ⟨by rw [(hcoord a' b₀ b₁ b₂ e1 i).2.2 h]; exact hB2,
              by rw [(hcoord b' a₀ a₁ a₂ e2 i).2.2 h]; exact hA2⟩
  rcases hcase with hc1 | hc2 | hc3 | hc4
  -- "Since there is no appearance of `K₄` in `G`, 10.1.1 does not hold."
  · obtain ⟨u, u', -, -, -, -, -, w, w', -, -, -, -, -, -, happ⟩ := hc1
    exact hK4 happ
  -- "Also 10.1.2 does not hold, since `v` is the only vertex in `F` with neighbours in
  -- `A ∪ B`."
  · obtain ⟨hlen2, hfa, hfb, -⟩ := hc2
    obtain ⟨hai, hbi⟩ := hkey (σ.symm 1) (by rw [Equiv.apply_symm_apply]; decide)
    exact hne_f hlen2 ((honlyv f₁ hf₁F _ hai (hfa _)).trans
      (honlyv fn hfnF _ hbi (hfb _)).symm)
  -- "... and neither does 10.1.3."
  · obtain ⟨hlen2, hfa0, hfa1, hfb0, hfb1, -⟩ := hc3
    rcases hσne with hne | hne
    · obtain ⟨ha, hb⟩ := hkey 0 hne
      exact hne_f hlen2 ((honlyv f₁ hf₁F _ ha hfa0).trans (honlyv fn hfnF _ hb hfb0).symm)
    · obtain ⟨ha, hb⟩ := hkey 1 hne
      exact hne_f hlen2 ((honlyv f₁ hf₁F _ ha hfa1).trans (honlyv fn hfnF _ hb hfb1).symm)
  -- "So 10.1.4 holds, and therefore `F` has an attachment in `R₂`, and so `v` has a
  -- neighbour in `R₂`."
  · obtain ⟨hfa0, hfa1, -, hno⟩ := hc4
    -- `f₁` has a neighbour in `V(S)`, so `f₁ = v`
    have hf₁v : f₁ = v := by
      rcases hσne with hne | hne
      · exact honlyv f₁ hf₁F _ (hkey 0 hne).1 hfa0
      · exact honlyv f₁ hf₁F _ (hkey 1 hne).1 hfa1
    rcases hab' with ⟨hA'eq, hB'eq⟩ | ⟨hA'eq, hB'eq⟩
    · -- the triangle `{a' 0, a' 1, a' 2}` is `{a₀, a₁, a₂}`
      have hmem_a' : ∀ i : Fin 3, a' i = a₀ ∨ a' i = a₁ ∨ a' i = a₂ := by
        intro i
        rcases h3 (σ i) with h | h | h
        · exact Or.inl ((hcoord a' a₀ a₁ a₂ hA'eq i).1 h)
        · exact Or.inr (Or.inl ((hcoord a' a₀ a₁ a₂ hA'eq i).2.1 h))
        · exact Or.inr (Or.inr ((hcoord a' a₀ a₁ a₂ hA'eq i).2.2 h))
      have hb₁nea' : ∀ i : Fin 3, b₁ ≠ a' i := by
        intro i hc
        rcases hmem_a' i with h | h | h
        · exact hne_a0b1 (hc.trans h).symm
        · exact hne_a1b1 (hc.trans h).symm
        · exact hne_a2b1 (hc.trans h).symm
      -- `v = f₁` is adjacent to `b₁`, and `b₁ ≠ a' 2`, so by the "no other edges" clause
      -- of 10.1.4, `b₁ ∈ V(R' 2)`
      have hb₁R'2 : b₁ ∈ R' 2 := by
        rcases hno f₁ hf₁mem b₁ (Or.inl (Or.inr hb₁R₁)) (hb₁nea' 2)
            (by rw [hf₁v]; exact hvb₁) with ⟨-, hb⟩ | ⟨-, hb⟩
        · exact absurd hb (by rintro (h | h); exacts [hb₁nea' 0 h, hb₁nea' 1 h])
        · exact hb
      -- hence `R' 2 = R₁`, i.e. `σ 2 = 1`
      have hσ2 : σ 2 = 1 := by
        rcases h3 (σ 2) with h | h | h
        · exact absurd (by rw [hR'eq] at hb₁R'2; simpa [h] using hb₁R'2)
            (fun hc => hR₀avoid b₁ hc hB1)
        · exact h
        · exact absurd (by rw [hR'eq] at hb₁R'2; simpa [h] using hb₁R'2) (hdisj12 b₁ hb₁R₁)
      -- so `{σ 0, σ 1} = {0, 2}`, and in particular `v` is adjacent to `a₂ ∈ V(R₂)`
      have hva₂ : G.Adj v a₂ := by
        have hσ0 : σ 0 = 0 ∨ σ 0 = 2 := by
          rcases h3 (σ 0) with h | h | h
          · exact Or.inl h
          · exact absurd (σ.injective (h.trans hσ2.symm)) (by decide)
          · exact Or.inr h
        have hσ1 : σ 1 = 0 ∨ σ 1 = 2 := by
          rcases h3 (σ 1) with h | h | h
          · exact Or.inl h
          · exact absurd (σ.injective (h.trans hσ2.symm)) (by decide)
          · exact Or.inr h
        rcases hσ0 with h0 | h0
        · have h1' : σ 1 = 2 := by
            rcases hσ1 with h | h
            · exact absurd (h0.trans h.symm) hσ01
            · exact h
          rw [← hf₁v, ← (hcoord a' a₀ a₁ a₂ hA'eq 1).2.2 h1']
          exact hfa1
        · rw [← hf₁v, ← (hcoord a' a₀ a₁ a₂ hA'eq 0).2.2 h0]
          exact hfa0
      -- "But then `v` can be linked onto the triangle `{b₀, b₁, b₂}`, via `v-P-b₀`,
      -- `v-b₁`, and the path from `v` to `b₂` with interior in `R₂`, contrary to 2.4."
      -- (The paper's `P` is the path called `Q` here: the one from `v` to `b₀`.)
      have hQlen0 : 0 < Q.length := Workspace.ProofLemmas.PathBasics.path_length_pos hQ.1
      have hQ0 : ∀ h : 0 < Q.length, Q[0]'h = v := fun h =>
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hQ.2.1 h
      have hQlast : ∀ h : Q.length - 1 < Q.length, Q[Q.length - 1]'h = b₀ := fun _ =>
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hQ.2.2 hQlen0
      have hQlen2 : 2 ≤ Q.length := by
        by_contra hcon
        obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp (by omega : Q.length = 1)
        have hQ' := hQ
        rw [hc] at hQ'
        exact hvne_b₀ ((by simpa using hQ'.2.1 : c = v).symm.trans (by simpa using hQ'.2.2))
      have hp₁path : IsPathList G (Q.drop 1) :=
        Workspace.ProofLemmas.PathBasics.isPathList_drop hQ.1 (by omega)
      have hp₁last : (Q.drop 1).getLast? = some b₀ := by
        rw [List.getLast?_drop, if_neg (by omega)]
        exact hQ.2.2
      have hp₁sub : ∀ x ∈ Q.drop 1, x ∈ Q := fun x hx => List.mem_of_mem_drop hx
      have hp₁anti : ∀ x ∈ Q.drop 1, ∀ y ∈ A ∪ B ∪ C, x ≠ b₀ → ¬ G.Adj x y := by
        intro x hx y hy hxb
        obtain ⟨i, hi, h1i, rfl⟩ := (mem_drop_iff Q 1 x).mp hx
        by_cases hlast : i + 2 ≤ Q.length
        · exact hPQint _
            (Or.inr (Workspace.ProofLemmas.PathBasics.getElem_mem_interior hQ.1 hi h1i hlast))
            y hy
        · have hie : i = Q.length - 1 := by omega
          subst hie
          exact absurd (hQlast hi) hxb
      have hlink : VertexLinkedOntoTriangle G v b₀ b₁ b₂ (Q.drop 1) [b₁] R₂ := by
        refine ⟨⟨hp₁path, Workspace.ProofLemmas.PathBasics.isPathList_singleton G b₁, hr₂.1.1⟩,
          ⟨?_, ?_, ?_⟩, ⟨Or.inr hp₁last, Or.inl rfl, Or.inr hr₂.1.2.2⟩, ⟨?_, ?_, ?_⟩,
          ⟨?_, ⟨b₁, by simp, hvb₁⟩, ⟨a₂, ha₂R₂, hva₂⟩⟩⟩
        · intro x hx hc
          rw [List.mem_singleton] at hc
          subst hc
          exact hQavoid x (hp₁sub x hx) (Or.inl hB1)
        · intro x hx hc
          exact hQavoid x (hp₁sub x hx) (Or.inl (hR₂S x hc))
        · intro x hx
          rw [List.mem_singleton] at hx
          subst hx
          exact hdisj12 x hb₁R₁
        · intro x hx y hy
          rw [List.mem_singleton] at hy
          subst hy
          constructor
          · intro hadj
            refine ⟨?_, rfl⟩
            by_contra hxb
            exact hp₁anti x hx y hB1 hxb hadj
          · rintro ⟨rfl, -⟩
            exact hAdj_b0b1
        · intro x hx y hy
          constructor
          · intro hadj
            have hxb : x = b₀ := by
              by_contra hxb
              exact hp₁anti x hx y (hR₂S y hy) hxb hadj
            subst hxb
            refine ⟨rfl, ?_⟩
            rcases hR₂S y hy with (hyA | hyB) | hyC
            · exact absurd hadj (hRS.2.2 y (Or.inl hyA))
            · exact hr₂.2.2.2.2.1 y hy hyB
            · exact absurd hadj (hRS.2.2 y (Or.inr hyC))
          · rintro ⟨rfl, rfl⟩
            exact hAdj_b0b2
        · intro x hx y hy
          rw [List.mem_singleton] at hx
          subst hx
          constructor
          · intro hadj
            rcases (hcross12 x hb₁R₁ y hy).mp hadj with ⟨he, -⟩ | ⟨-, he⟩
            · exact absurd he.symm hne_a1b1
            · exact ⟨rfl, he⟩
          · rintro ⟨-, rfl⟩
            exact hAdj_b1b2
        · refine ⟨Q[1]'(by omega), (mem_drop_iff Q 1 _).mpr ⟨1, by omega, le_refl 1, rfl⟩, ?_⟩
          have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hQ.1 (i := 0) (by omega)
          rw [hQ0] at hadj
          exact hadj
      rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG v b₀ b₁ b₂
        ⟨Q.drop 1, [b₁], R₂, hlink⟩ with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h⟩
      · exact hvb₀ h
      · exact hvb₀ h
      · exact hvb₂ h
    · -- the swapped labelling is impossible: `f₁ = v` would have two neighbours in
      -- `{b₀, b₁, b₂}`
      have hmem_a' : ∀ i : Fin 3, a' i = b₀ ∨ a' i = b₁ ∨ a' i = b₂ := by
        intro i
        rcases h3 (σ i) with h | h | h
        · exact Or.inl ((hcoord a' b₀ b₁ b₂ hA'eq i).1 h)
        · exact Or.inr (Or.inl ((hcoord a' b₀ b₁ b₂ hA'eq i).2.1 h))
        · exact Or.inr (Or.inr ((hcoord a' b₀ b₁ b₂ hA'eq i).2.2 h))
      have hne01 : a' 0 ≠ a' 1 := by
        rw [hA'eq]
        exact (hprism.2.1 (σ 0) (σ 1) hσ01).ne
      exact hne01 (htwob f₁ hf₁F (a' 0) (a' 1) (hmem_a' 0) (hmem_a' 1) hfa0 hfa1)
