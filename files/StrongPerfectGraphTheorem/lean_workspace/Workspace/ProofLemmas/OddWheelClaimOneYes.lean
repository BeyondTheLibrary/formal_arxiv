import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.OddWheelArc
import Workspace.ProofLemmas.OddWheelSpan
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.Statements.S02.Thm_2_2
import Workspace.Statements.S02.Thm_2_3
import Workspace.Statements.S13.Thm_13_6
import Workspace.Statements.S15.Thm_15_3

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.OddWheelClaimOneYes

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.OddWheelArc

variable {V : Type*}

/-- Everything 2.2 / 13.6 need about a path *arc — `v` — arc* of the rim: it is an induced path
with prescribed ends, it misses the hub, and its only `Y'`-complete vertices are its two ends
(so it carries no `Y'`-complete edge). -/
private theorem path_pack {G : SimpleGraph V} {C : List V} {Y' : Set V} {v : V}
    {D : ℕ → V} {k n : ℕ} {A A₂ : List V} {a₁ b₁ mn mx e₁ e₂ c₁ β : ℕ}
    (hC : IsHoleList G C) (hn : 0 < C.length)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hvC : v ∉ C) (hvY' : v ∉ Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hA : IsPathFrom G A (D c₁) (D e₁))
    (hAmem : ∀ z, z ∈ A ↔ ∃ t, a₁ ≤ t ∧ t ≤ b₁ ∧ z = D t)
    (hA₂ : IsPathFrom G A₂ (D e₂) (D β))
    (hA₂mem : ∀ z, z ∈ A₂ ↔ ∃ t, mn ≤ t ∧ t ≤ mx ∧ z = D t)
    (hsep : b₁ + 1 < mn) (hmnmx : mn ≤ mx) (hmx : mx < n)
    (hwrap : ¬ (a₁ = 0 ∧ mx = n - 1))
    (he₁ : a₁ ≤ e₁ ∧ e₁ ≤ b₁) (he₂ : mn ≤ e₂ ∧ e₂ ≤ mx)
    (hv₁ : ∀ t, a₁ ≤ t → t ≤ b₁ → (G.Adj v (D t) ↔ t = e₁))
    (hv₂ : ∀ t, mn ≤ t → t ≤ mx → (G.Adj v (D t) ↔ t = e₂))
    (hvZ : ¬ VertexComplete G v Y')
    (hcA : ∀ t, a₁ ≤ t → t ≤ b₁ → VertexComplete G (D t) Y' → t = c₁)
    (hcA₂ : ∀ t, mn ≤ t → t ≤ mx → VertexComplete G (D t) Y' → t = β)
    (hc₁ : a₁ ≤ c₁ ∧ c₁ ≤ b₁) (hβ : mn ≤ β ∧ β ≤ mx) :
    IsPathFrom G (A ++ (v :: A₂)) (D c₁) (D β) ∧
      (∀ z, z ∈ A ++ (v :: A₂) ↔ ((∃ t, a₁ ≤ t ∧ t ≤ b₁ ∧ z = D t) ∨ z = v ∨
        (∃ t, mn ≤ t ∧ t ≤ mx ∧ z = D t))) ∧
      (∀ w ∈ A ++ (v :: A₂), w ∉ Y') ∧
      (¬ ∃ u ∈ A ++ (v :: A₂), ∃ w ∈ A ++ (v :: A₂), EdgeComplete G Y' u w) := by
  have hpath : IsPathFrom G (A ++ (v :: A₂)) (D c₁) (D β) :=
    glue_two_arcs hC hn hD hnn hvC hA hAmem hA₂ hA₂mem hsep hmnmx hmx hwrap he₁ he₂ hv₁ hv₂
  have hmem : ∀ z, z ∈ A ++ (v :: A₂) ↔ ((∃ t, a₁ ≤ t ∧ t ≤ b₁ ∧ z = D t) ∨ z = v ∨
      (∃ t, mn ≤ t ∧ t ≤ mx ∧ z = D t)) := by
    intro z
    rw [List.mem_append, List.mem_cons, hAmem z]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hA₂mem z).mp h))
    · rintro (h | h | h)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((hA₂mem z).mpr h))
  refine ⟨hpath, hmem, ?_, ?_⟩
  · intro w hw
    rcases (hmem w).mp hw with ⟨t, -, -, rfl⟩ | rfl | ⟨t, -, -, rfl⟩
    · exact hCY' _ (rim_mem hn hD t)
    · exact hvY'
    · exact hCY' _ (rim_mem hn hD t)
  · rintro ⟨u, hu, w, hw, hE⟩
    have hidx : ∀ z, z ∈ A ++ (v :: A₂) → VertexComplete G z Y' →
        ∃ t, (t = c₁ ∨ t = β) ∧ z = D t := by
      intro z hz hcz
      rcases (hmem z).mp hz with ⟨t, h1, h2, rfl⟩ | rfl | ⟨t, h1, h2, rfl⟩
      · exact ⟨t, Or.inl (hcA t h1 h2 hcz), rfl⟩
      · exact absurd hcz hvZ
      · exact ⟨t, Or.inr (hcA₂ t h1 h2 hcz), rfl⟩
    obtain ⟨tu, htu, rfl⟩ := hidx u hu hE.2.1
    obtain ⟨tw, htw, rfl⟩ := hidx w hw hE.2.2
    have hcn : c₁ < n := by omega
    have hbn : β < n := by omega
    have hcase := (rim_adj hC hn hD hnn (show tu < n by omega) (show tw < n by omega)).mp hE.1
    have hne : tu ≠ tw := by
      rintro rfl
      exact G.irrefl hE.1
    rcases hcase with h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · omega
    · omega
    · exact hwrap ⟨by omega, by omega⟩
    · omega


theorem branch_yes [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : InF6 G)
    {C : List V} {Y Y' : Set V} {v : V} {D : ℕ → V} {k n L s : ℕ}
    (hw : IsWheel G C Y)
    (hC : IsHoleList G C) (hn : 0 < C.length) (hn6 : 6 ≤ n) (hneven : Even n)
    (hD : ∀ t : ℕ, C[(k + t) % C.length]? = some (D t)) (hnn : C.length = n)
    (hvC : v ∉ C) (hvY : v ∉ Y)
    (hL1 : 2 ≤ L) (hL2 : L + 2 ≤ n) (hLeven : Even L) (hn4 : L + 4 ≤ n)
    (hvD : ∀ t, t ≤ L → (G.Adj v (D t) ↔ (t = 0 ∨ t = L)))
    (hY'Y : Y' ⊆ Y) (hY'anti : AnticonnectedSet G Y') (hvY' : v ∉ Y')
    (hvZ : ¬ VertexComplete G v Y') (hCY' : ∀ w ∈ C, w ∉ Y')
    (hseven : Even s) (hsL : s + 1 < L)
    (hcs : VertexComplete G (D s) Y') (hcs1 : VertexComplete G (D (s + 1)) Y')
    (honly : ∀ t, t ≤ L → VertexComplete G (D t) Y' → (t = s ∨ t = s + 1))
    (hfar : ∃ q, L + 2 ≤ q ∧ q ≤ n - 2 ∧ VertexComplete G (D q) Y')
    (hyes : ∃ t, L + 2 ≤ t ∧ t ≤ n - 2 ∧ G.Adj v (D t)) :
    False := by
  have hBerge : Berge G := hG.1.1.1
  have hLe2 : L % 2 = 0 := Nat.even_iff.mp hLeven
  have hse2 : s % 2 = 0 := Nat.even_iff.mp hseven
  obtain ⟨q₀, hq₀1, hq₀2, hq₀c⟩ := hfar
  obtain ⟨t₀, ht₀1, ht₀2, ht₀a⟩ := hyes
  -- ### Step 1: the path `Q` of the printed proof
  obtain ⟨ab, hab, hminp⟩ :=
    ExtremalChoice.exists_min_nat
      (fun p : ℕ × ℕ => L + 2 ≤ p.1 ∧ p.1 ≤ n - 2 ∧ G.Adj v (D p.1) ∧
        L + 2 ≤ p.2 ∧ p.2 ≤ n - 2 ∧ VertexComplete G (D p.2) Y')
      (fun p => (p.1 - p.2) + (p.2 - p.1))
      ⟨(t₀, q₀), ht₀1, ht₀2, ht₀a, hq₀1, hq₀2, hq₀c⟩
  obtain ⟨α, β⟩ := ab
  obtain ⟨hα1, hα2, hvα, hβ1, hβ2, hcβ⟩ := hab
  have hα1 : L + 2 ≤ α := hα1
  have hα2 : α ≤ n - 2 := hα2
  have hvα : G.Adj v (D α) := hvα
  have hβ1 : L + 2 ≤ β := hβ1
  have hβ2 : β ≤ n - 2 := hβ2
  have hcβ : VertexComplete G (D β) Y' := hcβ
  have hAdjV : ∀ t, min α β ≤ t → t ≤ max α β → G.Adj v (D t) → t = α := by
    intro t h1 h2 hadj
    have hb := hminp (t, β) ⟨by omega, by omega, hadj, hβ1, hβ2, hcβ⟩
    simp only at hb
    omega
  have hComplete : ∀ t, min α β ≤ t → t ≤ max α β → VertexComplete G (D t) Y' → t = β := by
    intro t h1 h2 hcomp
    have hb := hminp (α, t) ⟨hα1, hα2, hvα, by omega, by omega, hcomp⟩
    simp only at hb
    omega
  obtain ⟨A₂, hA₂from, hA₂mem, hA₂len⟩ :
      ∃ A₂ : List V, IsPathFrom G A₂ (D α) (D β) ∧
        (∀ z, z ∈ A₂ ↔ ∃ t, min α β ≤ t ∧ t ≤ max α β ∧ z = D t) ∧
        A₂.length = max α β - min α β + 1 := by
    rcases le_total α β with h | h
    · refine ⟨arc C k α β, arc_isPathFrom' hC hn hD hnn h (by omega), ?_, ?_⟩
      · intro z
        rw [arc_mem_iff hC hn hD hnn h (by omega)]
        constructor
        · rintro ⟨t, h1, h2, rfl⟩; exact ⟨t, by omega, by omega, rfl⟩
        · rintro ⟨t, h1, h2, rfl⟩; exact ⟨t, by omega, by omega, rfl⟩
      · rw [arc_length C k α β (by omega)]; omega
    · refine ⟨(arc C k β α).reverse, arc_rev_isPathFrom hC hn hD hnn h (by omega), ?_, ?_⟩
      · intro z
        rw [arc_rev_mem_iff hC hn hD hnn h (by omega)]
        constructor
        · rintro ⟨t, h1, h2, rfl⟩; exact ⟨t, by omega, by omega, rfl⟩
        · rintro ⟨t, h1, h2, rfl⟩; exact ⟨t, by omega, by omega, rfl⟩
      · rw [List.length_reverse, arc_length C k β α (by omega)]; omega
  -- ### Step 2: `p_i-⋯-p₁-v-Q-u` is even, i.e. `Q` is odd
  obtain ⟨hP2, hP2mem, hP2Y, hP2noedge⟩ :=
    path_pack (a₁ := 0) (b₁ := s) (c₁ := s) (e₁ := 0) (e₂ := α)
      hC hn hD hnn hvC hvY' hCY'
      (arc_rev_isPathFrom hC hn hD hnn (Nat.zero_le s) (by omega))
      (fun z => arc_rev_mem_iff hC hn hD hnn (Nat.zero_le s) (by omega))
      hA₂from hA₂mem
      (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun t h1 h2 => by
        rw [hvD t (by omega)]
        exact ⟨fun h => h.resolve_right (by omega), fun h => Or.inl h⟩)
      (fun t h1 h2 => ⟨fun hadj => hAdjV t h1 h2 hadj, fun he => by rw [he]; exact hvα⟩)
      hvZ
      (fun t h1 h2 hcomp => by
        rcases honly t (by omega) hcomp with h | h
        · exact h
        · omega)
      hComplete ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hP2len : ((arc C k 0 s).reverse ++ (v :: A₂)).length = s + 1 + 1 + A₂.length := by
    rw [List.length_append, List.length_reverse, arc_length C k 0 s (by omega),
      List.length_cons]
    omega
  have hP2even : Even (pathLength ((arc C k 0 s).reverse ++ (v :: A₂))) := by
    by_contra hcon
    rw [Nat.not_even_iff_odd] at hcon
    obtain ⟨wv, hwint, hadjw⟩ :=
      Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y' hY'anti _ (D s) (D β)
        hP2 hP2Y hcon hcs hcβ hP2noedge (D (s + 1)) hcs1
    rw [PathBasics.mem_interior_iff_of_pathFrom hP2] at hwint
    obtain ⟨hwmem, hw1, hw2⟩ := hwint
    rcases (hP2mem wv).mp hwmem with ⟨t, h1, h2, rfl⟩ | rfl | ⟨t, h1, h2, rfl⟩
    · have hts : t ≠ s := fun h => hw1 (by rw [h])
      have hcase := (rim_adj hC hn hD hnn (show s + 1 < n by omega) (show t < n by omega)).mp hadjw
      omega
    · have hcase := (hvD (s + 1) (by omega)).mp hadjw.symm
      omega
    · have hcase := (rim_adj hC hn hD hnn (show s + 1 < n by omega) (show t < n by omega)).mp hadjw
      omega
  have hpar : (max α β - min α β) % 2 = 0 := by
    rw [PathBasics.pathLength_eq, hP2len, hA₂len, Nat.even_iff] at hP2even
    omega
  -- ### Step 3: `p_{i+1}-⋯-p_j-v-Q-u` is odd, so by 13.6 it has length 3
  obtain ⟨hP3, hP3mem, hP3Y, hP3noedge⟩ :=
    path_pack (a₁ := s + 1) (b₁ := L) (c₁ := s + 1) (e₁ := L) (e₂ := α)
      hC hn hD hnn hvC hvY' hCY'
      (arc_isPathFrom' hC hn hD hnn (show s + 1 ≤ L by omega) (by omega))
      (fun z => arc_mem_iff hC hn hD hnn (show s + 1 ≤ L by omega) (by omega))
      hA₂from hA₂mem
      (by omega) (by omega) (by omega) (by omega) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
      (fun t h1 h2 => by
        rw [hvD t (by omega)]
        exact ⟨fun h => h.resolve_left (by omega), fun h => Or.inr h⟩)
      (fun t h1 h2 => ⟨fun hadj => hAdjV t h1 h2 hadj, fun he => by rw [he]; exact hvα⟩)
      hvZ
      (fun t h1 h2 hcomp => by
        rcases honly t (by omega) hcomp with h | h
        · omega
        · exact h)
      hComplete ⟨by omega, by omega⟩ ⟨by omega, by omega⟩
  have hP3len : (arc C k (s + 1) L ++ (v :: A₂)).length = (L - s) + 1 + A₂.length := by
    rw [List.length_append, arc_length C k (s + 1) L (by omega), List.length_cons]
    omega
  have hP3odd : Odd (pathLength (arc C k (s + 1) L ++ (v :: A₂))) := by
    rw [PathBasics.pathLength_eq, hP3len, hA₂len, Nat.odd_iff]
    omega
  have h136 := Workspace.Statements.S13.SPGT.thm_13_6 G hG.1 _ (D (s + 1)) (D β) hP3 hP3odd Y'
    (by
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      intro hmem
      exact hP3Y y hmem hy)
    hY'anti hcs1 hcβ
  obtain ⟨hlen3, -⟩ : pathLength (arc C k (s + 1) L ++ (v :: A₂)) = 3 ∧ True := by
    rcases h136 with hedge | ⟨h3, -⟩
    · exact absurd hedge hP3noedge
    · exact ⟨h3, trivial⟩
  rw [PathBasics.pathLength_eq, hP3len, hA₂len] at hlen3
  have hLs : L = s + 2 := by omega
  have hαβ : α = β := by omega
  -- ### Step 4: `s = 0`, hence `L = 2`
  have h22 := Workspace.Statements.S02.SPGT.thm_2_2 G hBerge Y' hY'anti _ (D (s + 1)) (D β)
    hP3 hP3Y hP3odd hcs1 hcβ hP3noedge
  have hint : ∀ z, z ∈ SPGT.interior (arc C k (s + 1) L ++ (v :: A₂)) → (z = D L ∨ z = v) := by
    intro z hz
    rw [PathBasics.mem_interior_iff_of_pathFrom hP3] at hz
    obtain ⟨hzm, hz1, hz2⟩ := hz
    rcases (hP3mem z).mp hzm with ⟨t, h1, h2, rfl⟩ | rfl | ⟨t, h1, h2, rfl⟩
    · have hts : t ≠ s + 1 := fun h => hz1 (by rw [h])
      exact Or.inl (by rw [show t = L by omega])
    · exact Or.inr rfl
    · exact absurd (show D t = D β by rw [show t = β by omega]) hz2
  have hstar : ∀ t, t < n → VertexComplete G (D t) Y' →
      (t = s + 1 ∨ t = s + 3 ∨ G.Adj v (D t)) := by
    intro t ht hcomp
    obtain ⟨z, hzint, hadjz⟩ := h22 (D t) hcomp
    rcases hint z hzint with rfl | rfl
    · rcases (rim_adj hC hn hD hnn ht (show L < n by omega)).mp hadjz with
        h | h | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (by omega)
      · exact Or.inr (Or.inl (by omega))
      · omega
      · omega
    · exact Or.inr (Or.inr hadjz.symm)
  have hs0 : s = 0 := by
    rcases hstar s (by omega) hcs with h | h | h
    · omega
    · omega
    · rcases (hvD s (by omega)).mp h with h' | h'
      · exact h'
      · omega
  subst hs0
  have hL2' : L = 2 := by omega
  subst hL2'
  -- ### Step 5: the counting
  have hadj01 : G.Adj (D 0) (D 1) :=
    (rim_adj hC hn hD hnn (by omega) (by omega)).mpr (Or.inl rfl)
  have hD2nc : ¬ VertexComplete G (D 2) Y' := by
    intro hcomp
    rcases honly 2 (by omega) hcomp with h | h <;> omega
  have hnadj0β : ¬ G.Adj (D 0) (D β) := by
    intro hadj
    have := (rim_adj hC hn hD hnn (by omega) (show β < n by omega)).mp hadj
    omega
  have hD0v : G.Adj (D 0) v := ((hvD 0 (by omega)).mpr (Or.inl rfl)).symm
  have hDβv : G.Adj (D β) v := by rw [← hαβ]; exact hvα.symm
  have hD1v : ¬ G.Adj v (D 1) := by
    intro h
    rcases (hvD 1 (by omega)).mp h with h' | h' <;> omega
  have hWanti : AnticonnectedSet G (Y' ∪ {v}) :=
    KiteTailBasics.anticonnectedSet_union_singleton hY'anti hvZ
  have hWC : ∀ w ∈ C, w ∉ Y' ∪ {v} := by
    intro w hwC hmem
    rcases hmem with h | h
    · exact hCY' w hwC h
    · rw [Set.mem_singleton_iff] at h
      exact hvC (by rw [← h]; exact hwC)
  have hWcomp : ∀ z : V, VertexComplete G z (Y' ∪ {v}) ↔ (VertexComplete G z Y' ∧ G.Adj z v) :=
    fun z => OddWheelSpan.vertexComplete_union
  have hWY : ∀ u w : V, EdgeComplete G (Y' ∪ {v}) u w → EdgeComplete G Y' u w :=
    fun u w h => ⟨h.1, ((hWcomp u).mp h.2.1).1, ((hWcomp w).mp h.2.2).1⟩
  have h23Y : Even {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧
      EdgeComplete G Y' u w}.ncard := by
    rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge Y' hY'anti C (Or.inr hC) hCY').2 hC with
      h | ⟨a, b, hset, hab, hadjab⟩
    · exact h
    · exfalso
      have hmemD : ∀ t, t < n → VertexComplete G (D t) Y' → D t = a ∨ D t = b := by
        intro t ht hcomp
        have hin : D t ∈ ({a, b} : Set V) := by
          rw [← hset]; exact ⟨rim_mem hn hD t, hcomp⟩
        exact hin
      have h0 := hmemD 0 (by omega) hcs
      have h1 := hmemD 1 (by omega) hcs1
      have hbb := hmemD β (by omega) hcβ
      have hne01 : D 0 ≠ D 1 := rim_ne hC hn hD hnn (by omega) (by omega) (by omega)
      have hne0b : D 0 ≠ D β := rim_ne hC hn hD hnn (by omega) (show β < n by omega) (by omega)
      have hne1b : D 1 ≠ D β := rim_ne hC hn hD hnn (by omega) (show β < n by omega) (by omega)
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
      · exact hne01 (h0.trans h1.symm)
      · rcases hbb with hbb | hbb
        · exact hne0b (h0.trans hbb.symm)
        · exact hne1b (h1.trans hbb.symm)
      · rcases hbb with hbb | hbb
        · exact hne1b (h1.trans hbb.symm)
        · exact hne0b (h0.trans hbb.symm)
      · exact hne01 (h0.trans h1.symm)
  have h23W : Even {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧
      EdgeComplete G (Y' ∪ {v}) u w}.ncard := by
    rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hBerge (Y' ∪ {v}) hWanti C (Or.inr hC)
      hWC).2 hC with h | ⟨a, b, hset, hab, hadjab⟩
    · exact h
    · exfalso
      have hmemD : ∀ t, t < n → VertexComplete G (D t) (Y' ∪ {v}) → D t = a ∨ D t = b := by
        intro t ht hcomp
        have hin : D t ∈ ({a, b} : Set V) := by
          rw [← hset]; exact ⟨rim_mem hn hD t, hcomp⟩
        exact hin
      have h0 := hmemD 0 (by omega) ((hWcomp _).mpr ⟨hcs, hD0v⟩)
      have hbb := hmemD β (by omega) ((hWcomp _).mpr ⟨hcβ, hDβv⟩)
      have hne0b : D 0 ≠ D β := rim_ne hC hn hD hnn (by omega) (show β < n by omega) (by omega)
      rcases h0 with h0 | h0 <;> rcases hbb with hbb | hbb
      · exact hne0b (h0.trans hbb.symm)
      · exact hnadj0β (by rw [h0, hbb]; exact hadjab)
      · exact hnadj0β (by rw [h0, hbb]; exact hadjab.symm)
      · exact hne0b (h0.trans hbb.symm)
  have hcount : ∀ Z : Set V,
      {e : Sym2 V | ∃ u ∈ C, ∃ w ∈ C, e = s(u, w) ∧ EdgeComplete G Z u w}.ncard
        = arcCount G Z C k n := by
    intro Z
    rw [WheelParity.ncard_yEdges_eq_cycCount (Y := Z) hC,
      ← arcCount_full (G := G) (C := C) Z k n hnn]
  have hCE : ∀ (Z : Set V) (m : ℕ),
      WheelParity.CycEdge G Z C (k + m) ↔ EdgeComplete G Z (D m) (D (m + 1)) := by
    intro Z m
    refine cycEdge_iff' (hD m) ?_
    have hh := hD (m + 1)
    rw [show k + (m + 1) = k + m + 1 from by omega] at hh
    exact hh
  have hCE0 : ∀ Z : Set V, WheelParity.CycEdge G Z C k ↔ EdgeComplete G Z (D 0) (D 1) := by
    intro Z
    have hh := hCE Z 0
    rw [Nat.add_zero] at hh
    exact hh
  have hsplit : ∀ Z : Set V, arcCount G Z C k n
      = arcCount G Z C k 1 + arcCount G Z C (k + 1) 1 + arcCount G Z C (k + 2) 1
        + arcCount G Z C (k + 3) 1 + arcCount G Z C (k + 4) (n - 4) := by
    intro Z
    have e1 := arcCount_split (G := G) (C := C) Z k 1 (n - 1)
    rw [show 1 + (n - 1) = n from by omega] at e1
    have e2 := arcCount_split (G := G) (C := C) Z (k + 1) 1 (n - 2)
    rw [show 1 + (n - 2) = n - 1 from by omega, show k + 1 + 1 = k + 2 from by omega] at e2
    have e3 := arcCount_split (G := G) (C := C) Z (k + 2) 1 (n - 3)
    rw [show 1 + (n - 3) = n - 2 from by omega, show k + 2 + 1 = k + 3 from by omega] at e3
    have e4 := arcCount_split (G := G) (C := C) Z (k + 3) 1 (n - 4)
    rw [show 1 + (n - 4) = n - 3 from by omega, show k + 3 + 1 = k + 4 from by omega] at e4
    omega
  have hY0 : arcCount G Y' C k 1 = 1 :=
    arcCount_one_pos ((hCE0 Y').mpr ⟨hadj01, hcs, hcs1⟩)
  have hW0 : arcCount G (Y' ∪ {v}) C k 1 = 0 := by
    refine arcCount_one_neg (fun hcon => ?_)
    exact hD1v (((hWcomp (D 1)).mp ((hCE0 (Y' ∪ {v})).mp hcon).2.2).2).symm
  have hY1 : arcCount G Y' C (k + 1) 1 = 0 :=
    arcCount_one_neg (fun hcon => hD2nc ((hCE Y' 1).mp hcon).2.2)
  have hY2 : arcCount G Y' C (k + 2) 1 = 0 :=
    arcCount_one_neg (fun hcon => hD2nc ((hCE Y' 2).mp hcon).2.1)
  have hW1 : arcCount G (Y' ∪ {v}) C (k + 1) 1 = 0 :=
    arcCount_one_neg (fun hcon => hD2nc (hWY _ _ ((hCE _ 1).mp hcon)).2.2)
  have hW2 : arcCount G (Y' ∪ {v}) C (k + 2) 1 = 0 :=
    arcCount_one_neg (fun hcon => hD2nc (hWY _ _ ((hCE _ 2).mp hcon)).2.1)
  have htail : arcCount G (Y' ∪ {v}) C (k + 4) (n - 4) = arcCount G Y' C (k + 4) (n - 4) := by
    refine arcCount_congr (n - 4) (fun t ht => ?_)
    have hm : ∀ Z : Set V, WheelParity.CycEdge G Z C (k + 4 + t)
        ↔ EdgeComplete G Z (D (4 + t)) (D (4 + t + 1)) := by
      intro Z
      have hh := hCE Z (4 + t)
      rw [show k + (4 + t) = k + 4 + t from by omega] at hh
      exact hh
    rw [hm, hm]
    refine ⟨fun h => hWY _ _ h, fun h => ⟨h.1, (hWcomp _).mpr ⟨h.2.1, ?_⟩,
      (hWcomp _).mpr ⟨h.2.2, ?_⟩⟩⟩
    · rcases hstar (4 + t) (by omega) h.2.1 with hh | hh | hh
      · omega
      · omega
      · exact hh.symm
    · by_cases hlast : 4 + t + 1 = n
      · have hDn : D (4 + t + 1) = D 0 := by
          refine rim_congr hC hD ?_
          rw [hlast, hnn]
          simp
        rw [hDn]
        exact hD0v
      · rcases hstar (4 + t + 1) (by omega) h.2.2 with hh | hh | hh
        · omega
        · omega
        · exact hh.symm
  have hkey : WheelParity.CycEdge G Y' C (k + 3) ∧
      ¬ WheelParity.CycEdge G (Y' ∪ {v}) C (k + 3) := by
    rw [hcount Y', hsplit Y', hY0, hY1, hY2, Nat.even_iff] at h23Y
    rw [hcount (Y' ∪ {v}), hsplit (Y' ∪ {v}), hW0, hW1, hW2, htail, Nat.even_iff] at h23W
    by_cases hcW : WheelParity.CycEdge G (Y' ∪ {v}) C (k + 3)
    · exfalso
      have hcY : WheelParity.CycEdge G Y' C (k + 3) :=
        (hCE Y' 3).mpr (hWY _ _ ((hCE _ 3).mp hcW))
      rw [arcCount_one_pos hcY] at h23Y
      rw [arcCount_one_pos hcW] at h23W
      omega
    · by_cases hcY : WheelParity.CycEdge G Y' C (k + 3)
      · exact ⟨hcY, hcW⟩
      · exfalso
        rw [arcCount_one_neg hcY] at h23Y
        rw [arcCount_one_neg hcW] at h23W
        omega
  obtain ⟨hc3Y, hc3W⟩ := hkey
  have hE3 : EdgeComplete G Y' (D 3) (D 4) := (hCE Y' 3).mp hc3Y
  have hD4v : G.Adj v (D 4) := by
    rcases hstar 4 (by omega) hE3.2.2 with h | h | h
    · omega
    · omega
    · exact h
  have hD3v : ¬ G.Adj v (D 3) := by
    intro h
    exact hc3W ((hCE _ 3).mpr ⟨hE3.1, (hWcomp _).mpr ⟨hE3.2.1, h.symm⟩,
      (hWcomp _).mpr ⟨hE3.2.2, hD4v.symm⟩⟩)
  -- ### Step 6: the vertices `v, p₁, …, p₅` violate 15.3
  have hD2v : G.Adj v (D 2) := (hvD 2 (by omega)).mpr (Or.inr rfl)
  have hnadj : ∀ a b : ℕ, a < n → b < n →
      ¬ (b = a + 1) → ¬ (a = b + 1) → ¬ (a = 0 ∧ b = n - 1) → ¬ (b = 0 ∧ a = n - 1) →
      ¬ G.Adj (D a) (D b) := by
    intro a b ha hb h1 h2 h3 h4 hadj
    rcases (rim_adj hC hn hD hnn ha hb).mp hadj with h | h | h | h
    · exact h1 h
    · exact h2 h
    · exact h3 h
    · exact h4 h
  have hdne : ∀ a b : ℕ, a < n → b < n → a ≠ b → D a ≠ D b :=
    fun a b ha hb hab => rim_ne hC hn hD hnn ha hb hab
  have hvne : ∀ t : ℕ, t < n → D t ≠ v := fun t ht h => hvC (by rw [← h]; exact rim_mem hn hD t)
  -- the six edges of the 6-cycle `p₂-p₃-p₄-p₅-v-p₁-p₂`, in both orientations
  have e0 : G.Adj (D 1) (D 2) := (rim_adj hC hn hD hnn (by omega) (by omega)).mpr (Or.inl rfl)
  have e1 : G.Adj (D 2) (D 3) := (rim_adj hC hn hD hnn (by omega) (by omega)).mpr (Or.inl rfl)
  have e2 : G.Adj (D 3) (D 4) := (rim_adj hC hn hD hnn (by omega) (by omega)).mpr (Or.inl rfl)
  have e3 : G.Adj (D 4) v := hD4v.symm
  have e4 : G.Adj v (D 0) := hD0v.symm
  have e5 : G.Adj (D 0) (D 1) := hadj01
  have e0' : G.Adj (D 2) (D 1) := e0.symm
  have e1' : G.Adj (D 3) (D 2) := e1.symm
  have e2' : G.Adj (D 4) (D 3) := e2.symm
  have e3' : G.Adj v (D 4) := e3.symm
  have e4' : G.Adj (D 0) v := e4.symm
  have e5' : G.Adj (D 1) (D 0) := e5.symm
  have ech : G.Adj (D 2) v := hD2v.symm
  have ech' : G.Adj v (D 2) := hD2v
  -- the eight non-edges, in both orientations
  have m02 : ¬ G.Adj (D 1) (D 3) :=
    hnadj 1 3 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m03 : ¬ G.Adj (D 1) (D 4) :=
    hnadj 1 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m13 : ¬ G.Adj (D 2) (D 4) :=
    hnadj 2 4 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m15 : ¬ G.Adj (D 2) (D 0) :=
    hnadj 2 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m25 : ¬ G.Adj (D 3) (D 0) :=
    hnadj 3 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m35 : ¬ G.Adj (D 4) (D 0) :=
    hnadj 4 0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have m04 : ¬ G.Adj (D 1) v := fun h => hD1v h.symm
  have m24 : ¬ G.Adj (D 3) v := fun h => hD3v h.symm
  have m02' : ¬ G.Adj (D 3) (D 1) := fun h => m02 h.symm
  have m03' : ¬ G.Adj (D 4) (D 1) := fun h => m03 h.symm
  have m13' : ¬ G.Adj (D 4) (D 2) := fun h => m13 h.symm
  have m15' : ¬ G.Adj (D 0) (D 2) := fun h => m15 h.symm
  have m25' : ¬ G.Adj (D 0) (D 3) := fun h => m25 h.symm
  have m35' : ¬ G.Adj (D 0) (D 4) := fun h => m35 h.symm
  have m04' : ¬ G.Adj v (D 1) := hD1v
  have m24' : ¬ G.Adj v (D 3) := hD3v
  have a12 := hdne 1 2 (by omega) (by omega) (by omega)
  have a13 := hdne 1 3 (by omega) (by omega) (by omega)
  have a14 := hdne 1 4 (by omega) (by omega) (by omega)
  have a10 := hdne 1 0 (by omega) (by omega) (by omega)
  have a23 := hdne 2 3 (by omega) (by omega) (by omega)
  have a24 := hdne 2 4 (by omega) (by omega) (by omega)
  have a20 := hdne 2 0 (by omega) (by omega) (by omega)
  have a34 := hdne 3 4 (by omega) (by omega) (by omega)
  have a30 := hdne 3 0 (by omega) (by omega) (by omega)
  have a40 := hdne 4 0 (by omega) (by omega) (by omega)
  have w1 := hvne 1 (by omega)
  have w2 := hvne 2 (by omega)
  have w3 := hvne 3 (by omega)
  have w4 := hvne 4 (by omega)
  have w0 := hvne 0 (by omega)
  have w0' : v ≠ D 0 := w0.symm
  have hnodup : ([D 1, D 2, D 3, D 4, v, D 0] : List V).Nodup := by
    simp [a12, a13, a14, a10, a23, a24, a20, a34, a30, a40, w1, w2, w3, w4, w0, w0']
  have hcontra := Workspace.Statements.S15.SPGT.thm_15_3 G hG
    ([D 1, D 2, D 3, D 4, v, D 0] : List V) 6 2 3 5 rfl (by omega) (by omega) (by omega)
    (by omega) (by omega) hnodup
    (by
      intro a b ha hb
      have ha' : a < 6 := ha
      have hb' : b < 6 := hb
      interval_cases a <;> interval_cases b <;> intro hab <;> simp at hab <;> assumption)
    (by
      intro a b ha hb
      have ha' : a < 6 := ha
      have hb' : b < 6 := hb
      interval_cases a <;> interval_cases b <;> intro hadj <;>
        first
          | exact absurd hadj (by assumption)
          | exact absurd hadj G.irrefl
          | exact Or.inr (Or.inl ⟨rfl, rfl⟩)
          | exact Or.inr (Or.inr ⟨rfl, rfl⟩)
          | (left; simp))
    Y'
    (by
      intro y hy hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hCY' _ (rim_mem hn hD 1) hy
      · exact hCY' _ (rim_mem hn hD 2) hy
      · exact hCY' _ (rim_mem hn hD 3) hy
      · exact hCY' _ (rim_mem hn hD 4) hy
      · exact hvY' hy
      · exact hCY' _ (rim_mem hn hD 0) hy)
    hY'anti
    (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
      · exact iff_of_true hcs1 (Or.inr (Or.inl rfl))
      · refine iff_of_false hD2nc ?_
        rintro (h | h | h | h)
        · exact a20 h
        · exact a12 h.symm
        · exact a23 h
        · exact a24 h
      · exact iff_of_true hE3.2.1 (Or.inr (Or.inr (Or.inl rfl)))
      · exact iff_of_true hE3.2.2 (Or.inr (Or.inr (Or.inr rfl)))
      · refine iff_of_false hvZ ?_
        rintro (h | h | h | h)
        · exact w0' h
        · exact w1 h.symm
        · exact w3 h.symm
        · exact w4 h.symm
      · exact iff_of_true hcs (Or.inl rfl))
    ([D 2, v] : List V) ⟨PathBasics.isPathList_pair ech, rfl, rfl⟩
    (by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hCY' _ (rim_mem hn hD 2)
      · exact hvY')
    (by
      intro x hx
      simp [SPGT.interior] at hx)
  obtain ⟨wv, hwF, hwc⟩ := hcontra
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hwF
  rcases hwF with rfl | rfl
  · exact hD2nc hwc
  · exact hvZ hwc

end Workspace.ProofLemmas.OddWheelClaimOneYes
