import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S02.Thm_2_2

/-!
# 12.4(2), second step: *"So `s`, `t` are adjacent."*

PAPER (printed p. 74, inside claim (2) of the proof of 12.4):

*"Assume `s`, `t` are nonadjacent; then the subpath of `R₀` between them is odd, and `a₁` has no
neighbour in its interior, so by 2.2 it contains another `Q`-complete vertex `u` say; and then
`s`-`S`-`a₀`-`a₂`-`R₂`-`b₂`-`b₀`-`T`-`t` is an odd path, its ends are `Q`-complete and its
internal vertices are not, and `u` has no neighbour in its interior, contrary to 2.2.  So `s`,
`t` are adjacent."*

The two appeals to 2.2 are run in that order.  The long path is assembled from the three
stretches `s`-`S`-`a₀` (the reversed initial stretch of the banister), `a₂`-`R₂`-`b₂` (the rung)
and `b₀`-`T`-`t` (the reversed terminal stretch), glued along the two edges `a₀a₂` and `b₂b₀`
which the prism supplies.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm124SAdjT

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- *"So `s`, `t` are adjacent."* -/
theorem s_adj_t
    (G : SimpleGraph V) (hG : Berge G) (Q : Set V) (hQanti : AnticonnectedSet G Q)
    (a₀ a₁ a₂ b₀ b₂ : V) (R₀ R₂ : List V)
    (hR₀ : IsPathFrom G R₀ a₀ b₀) (hR₂ : IsPathFrom G R₂ a₂ b₂)
    (hc02 : ∀ u ∈ R₀, ∀ v ∈ R₂, (G.Adj u v ↔ (u = a₀ ∧ v = a₂) ∨ (u = b₀ ∧ v = b₂)))
    (ha₁R₀ : ∀ (k : ℕ) (hk : k < R₀.length), (G.Adj a₁ (R₀[k]'hk) ↔ k = 0))
    (hdisj : ∀ x ∈ R₀, x ∉ R₂)
    (hR₀Q : ∀ w ∈ R₀, w ∉ Q) (hR₂Q : ∀ w ∈ R₂, w ∉ Q)
    (hR₂nc : ∀ w ∈ R₂, ¬ VertexComplete G w Q)
    (ha₁Q : VertexComplete G a₁ Q)
    (iS iT : ℕ) (hiS : iS < R₀.length) (hiT : iT < R₀.length)
    (hiS0 : 0 < iS) (hiTlast : iT < R₀.length - 1) (hlt : iS < iT)
    (hminS : ∀ (k : ℕ) (hk : k < R₀.length), k < iS → ¬ VertexComplete G (R₀[k]'hk) Q)
    (hmaxT : ∀ (k : ℕ) (hk : k < R₀.length), iT < k → ¬ VertexComplete G (R₀[k]'hk) Q)
    (hsQ : VertexComplete G (R₀[iS]'hiS) Q) (htQ : VertexComplete G (R₀[iT]'hiT) Q)
    (hoddS : Odd iS) (hoddT : Odd (R₀.length - 1 - iT)) (hoddR₀ : Odd (pathLength R₀))
    (hoddR₂ : Odd (pathLength R₂)) :
    G.Adj (R₀[iS]'hiS) (R₀[iT]'hiT) := by
  classical
  by_contra hst
  have hlen0 : 0 < R₀.length := PathBasics.path_length_pos hR₀.1
  have hlen2 : 0 < R₂.length := PathBasics.path_length_pos hR₂.1
  have h00 : R₀[0]'hlen0 = a₀ := PathBasics.getElem_zero_of_head? hR₀.2.1 hlen0
  have h0last : R₀[R₀.length - 1]'(by omega) = b₀ :=
    PathBasics.getElem_last_of_getLast? hR₀.2.2 hlen0
  have h20 : R₂[0]'hlen2 = a₂ := PathBasics.getElem_zero_of_head? hR₂.2.1 hlen2
  have h2last : R₂[R₂.length - 1]'(by omega) = b₂ :=
    PathBasics.getElem_last_of_getLast? hR₂.2.2 hlen2
  have hget0 : ∀ (k l : ℕ) (hk : k < R₀.length) (hl : l < R₀.length),
      k = l → (R₀[k]'hk) = (R₀[l]'hl) := by rintro k l hk hl rfl; rfl
  -- `s` and `t` are not consecutive, so `iT ≥ iS + 2`
  have hgap : iS + 2 ≤ iT := by
    by_contra hcon
    have hiTs : iT = iS + 1 := by omega
    refine hst ?_
    have h := PathBasics.path_adj_succ hR₀.1 (i := iS) (by omega)
    rw [hget0 iT (iS + 1) hiT (by omega) hiTs]
    exact h
  -- *"the subpath of `R₀` between them is odd"*
  have hoddD : Odd (iT - iS) := by
    obtain ⟨p, hp⟩ := hoddS
    obtain ⟨q, hq⟩ := hoddT
    obtain ⟨r, hr⟩ := hoddR₀
    rw [PathBasics.pathLength_eq] at hr
    exact ⟨r - p - q - 1, by omega⟩
  -- ==================================================================
  -- first appeal to 2.2, on the stretch `s … t`
  -- ==================================================================
  set M : List V := (R₀.drop iS).take (iT - iS + 1) with hMdef
  have hMlen : M.length = iT - iS + 1 := PathBasics.length_slice R₀ (by omega) hiT
  have hMfrom : IsPathFrom G M (R₀[iS]'hiS) (R₀[iT]'hiT) :=
    PathBasics.isPathFrom_slice hR₀.1 hlt hiT
  have hMmem : ∀ x ∈ M, ∃ (k : ℕ) (hk : k < R₀.length), iS ≤ k ∧ k ≤ iT ∧ (R₀[k]'hk) = x := by
    intro x hx
    exact (PathBasics.mem_slice_iff R₀ (le_of_lt hlt) hiT).mp hx
  have hMsub : ∀ x ∈ M, x ∈ R₀ := by
    intro x hx; obtain ⟨k, hk, -, -, rfl⟩ := hMmem x hx; exact List.getElem_mem hk
  have hMQ : ∀ x ∈ M, x ∉ Q := fun x hx => hR₀Q x (hMsub x hx)
  have hMlength : pathLength M = iT - iS := by
    rw [PathBasics.pathLength_eq, hMlen]; omega
  -- *"and `a₁` has no neighbour in its interior, so by 2.2 it contains another `Q`-complete
  -- vertex `u` say"*
  have hMedge : ∃ u ∈ M, ∃ v ∈ M, EdgeComplete G Q u v := by
    by_contra hno
    obtain ⟨w, hwint, hadj⟩ :=
      Workspace.Statements.S02.SPGT.thm_2_2 G hG Q hQanti M (R₀[iS]'hiS) (R₀[iT]'hiT) hMfrom
        hMQ (by rw [hMlength]; exact hoddD) hsQ htQ hno a₁ ha₁Q
    obtain ⟨k, hk, hk1, hk2, rfl⟩ :=
      (PathBasics.mem_interior_slice_iff hR₀.1 hlt hiT).mp hwint
    have := (ha₁R₀ k hk).mp hadj
    omega
  obtain ⟨u, huM, v, hvM, hadjuv, huQ, hvQ⟩ := hMedge
  obtain ⟨p, hp, hp1, hp2, rfl⟩ := hMmem u huM
  obtain ⟨q, hq, hq1, hq2, rfl⟩ := hMmem v hvM
  have hpq : p + 1 = q ∨ q + 1 = p := (PathBasics.path_adj_iff hR₀.1 hp hq).mp hadjuv
  -- one of the two ends of that `Q`-complete edge lies strictly between `s` and `t`
  obtain ⟨m, hm, hm1, hm2, hmQ⟩ :
      ∃ (m : ℕ) (hm : m < R₀.length), iS < m ∧ m < iT ∧ VertexComplete G (R₀[m]'hm) Q := by
    rcases (show (iS < p ∧ p < iT) ∨ (iS < q ∧ q < iT) by omega) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨p, hp, h1, h2, huQ⟩
    · exact ⟨q, hq, h1, h2, hvQ⟩
  -- ==================================================================
  -- the long path `s`-`S`-`a₀`-`a₂`-`R₂`-`b₂`-`b₀`-`T`-`t`
  -- ==================================================================
  set W₁ : List V := ((R₀.drop 0).take (iS - 0 + 1)).reverse with hW₁def
  set W₃ : List V := ((R₀.drop iT).take (R₀.length - 1 - iT + 1)).reverse with hW₃def
  have hW₁len : W₁.length = iS + 1 := by
    rw [hW₁def, List.length_reverse, PathBasics.length_slice R₀ (by omega) hiS]; omega
  have hW₃len : W₃.length = R₀.length - 1 - iT + 1 := by
    rw [hW₃def, List.length_reverse,
      PathBasics.length_slice R₀ (by omega) (show R₀.length - 1 < R₀.length by omega)]
  have hW₁from : IsPathFrom G W₁ (R₀[iS]'hiS) a₀ := by
    have h := PathBasics.isPathFrom_reverse (PathBasics.isPathFrom_slice hR₀.1 hiS0 hiS)
    rwa [h00] at h
  have hW₃from : IsPathFrom G W₃ b₀ (R₀[iT]'hiT) := by
    have h := PathBasics.isPathFrom_reverse
      (PathBasics.isPathFrom_slice hR₀.1 (show iT < R₀.length - 1 from hiTlast)
        (show R₀.length - 1 < R₀.length by omega))
    rwa [h0last] at h
  have hW₁mem : ∀ x ∈ W₁, ∃ (k : ℕ) (hk : k < R₀.length), k ≤ iS ∧ (R₀[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, -, h2, h3⟩ :=
      (PathBasics.mem_slice_iff R₀ (by omega) hiS).mp (List.mem_reverse.mp hx)
    exact ⟨k, hk, h2, h3⟩
  have hW₃mem : ∀ x ∈ W₃, ∃ (k : ℕ) (hk : k < R₀.length), iT ≤ k ∧ (R₀[k]'hk) = x := by
    intro x hx
    obtain ⟨k, hk, h1, -, h3⟩ :=
      (PathBasics.mem_slice_iff R₀ (by omega) (show R₀.length - 1 < R₀.length by omega)).mp
        (List.mem_reverse.mp hx)
    exact ⟨k, hk, h1, h3⟩
  have hW₁sub : ∀ x ∈ W₁, x ∈ R₀ := by
    intro x hx; obtain ⟨k, hk, -, rfl⟩ := hW₁mem x hx; exact List.getElem_mem hk
  have hW₃sub : ∀ x ∈ W₃, x ∈ R₀ := by
    intro x hx; obtain ⟨k, hk, -, rfl⟩ := hW₃mem x hx; exact List.getElem_mem hk
  -- glue `s`-`S`-`a₀` to `a₂`-`R₂`-`b₂`
  have hglue1 : IsPathFrom G (W₁ ++ R₂) (R₀[iS]'hiS) b₂ := by
    refine PathGlue.glue_path hW₁from hR₂ (fun x hx => hdisj x (hW₁sub x hx)) ?_
    intro x hx y hy
    obtain ⟨k, hk, hkS, rfl⟩ := hW₁mem x hx
    rw [hc02 _ (List.getElem_mem hk) y hy]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
      · exact ⟨h1, h2⟩
      · exact absurd (h1.trans h0last.symm)
          (PathBasics.path_ne_of_ne_index hR₀.1 hk (by omega) (by omega))
    · exact Or.inl
  -- glue on `b₀`-`T`-`t`
  have hW : IsPathFrom G ((W₁ ++ R₂) ++ W₃) (R₀[iS]'hiS) (R₀[iT]'hiT) := by
    refine PathGlue.glue_path hglue1 hW₃from ?_ ?_
    · intro x hx hxW₃
      rcases List.mem_append.mp hx with hx1 | hx2
      · obtain ⟨k, hk, hkS, rfl⟩ := hW₁mem x hx1
        obtain ⟨l, hl, hlT, hlx⟩ := hW₃mem _ hxW₃
        exact PathBasics.path_ne_of_ne_index hR₀.1 hl hk (by omega) hlx
      · exact hdisj x (hW₃sub x hxW₃) hx2
    · intro x hx y hy
      obtain ⟨l, hl, hlT, rfl⟩ := hW₃mem y hy
      rcases List.mem_append.mp hx with hx1 | hx2
      · obtain ⟨k, hk, hkS, rfl⟩ := hW₁mem x hx1
        constructor
        · intro hadj
          have := (PathBasics.path_adj_iff hR₀.1 hk hl).mp hadj
          omega
        · rintro ⟨h1, -⟩
          exact absurd (h1.trans h2last.symm)
            (fun he => hdisj _ (List.getElem_mem hk) (he ▸ List.getElem_mem (by omega)))
      · constructor
        · intro hadj
          rcases (hc02 _ (List.getElem_mem hl) x hx2).mp hadj.symm with ⟨h1, -⟩ | ⟨h1, h2⟩
          · exact absurd (h1.trans h00.symm)
              (PathBasics.path_ne_of_ne_index hR₀.1 hl hlen0 (by omega))
          · exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩
          exact ((hc02 _ (List.getElem_mem hl) x hx2).mpr (Or.inr ⟨h2, h1⟩)).symm
  -- ==================================================================
  -- second appeal to 2.2, on the long path
  -- ==================================================================
  set W : List V := (W₁ ++ R₂) ++ W₃ with hWdef
  have hWmem : ∀ x ∈ W, x ∈ W₁ ∨ x ∈ R₂ ∨ x ∈ W₃ := by
    intro x hx
    rcases List.mem_append.mp hx with hx1 | hx3
    · rcases List.mem_append.mp hx1 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr hx3)
  have hWQ : ∀ x ∈ W, x ∉ Q := by
    intro x hx
    rcases hWmem x hx with h | h | h
    · exact hR₀Q x (hW₁sub x h)
    · exact hR₂Q x h
    · exact hR₀Q x (hW₃sub x h)
  -- the only `Q`-complete vertices of `W` are its two ends `s` and `t`
  have hWcomplete : ∀ x ∈ W, VertexComplete G x Q →
      x = (R₀[iS]'hiS) ∨ x = (R₀[iT]'hiT) := by
    intro x hx hxQ
    rcases hWmem x hx with h | h | h
    · obtain ⟨k, hk, hkS, rfl⟩ := hW₁mem x h
      rcases lt_or_eq_of_le hkS with hlt' | rfl
      · exact absurd hxQ (hminS k hk hlt')
      · exact Or.inl rfl
    · exact absurd hxQ (hR₂nc x h)
    · obtain ⟨k, hk, hkT, rfl⟩ := hW₃mem x h
      rcases lt_or_eq_of_le hkT with hlt' | rfl
      · exact absurd hxQ (hmaxT k hk hlt')
      · exact Or.inr rfl
  have hWnoedge : ¬ ∃ x ∈ W, ∃ y ∈ W, EdgeComplete G Q x y := by
    rintro ⟨x, hx, y, hy, hadj, hxQ, hyQ⟩
    rcases hWcomplete x hx hxQ with rfl | rfl <;> rcases hWcomplete y hy hyQ with rfl | rfl
    · exact G.irrefl hadj
    · exact hst hadj
    · exact hst hadj.symm
    · exact G.irrefl hadj
  have hWodd : Odd (pathLength W) := by
    have hlenW : W.length = W₁.length + R₂.length + W₃.length := by
      rw [hWdef, List.length_append, List.length_append]
    have h2 : R₂.length = pathLength R₂ + 1 := PathBasics.length_eq_pathLength_add_one hR₂.1
    obtain ⟨p', hp'⟩ := hoddS
    obtain ⟨q', hq'⟩ := hoddT
    obtain ⟨r', hr'⟩ := hoddR₂
    refine ⟨p' + q' + r' + 2, ?_⟩
    rw [PathBasics.pathLength_eq, hlenW, hW₁len, hW₃len, h2]
    omega
  obtain ⟨w, hwint, hadjw⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hG Q hQanti W (R₀[iS]'hiS) (R₀[iT]'hiT) hW hWQ
      hWodd hsQ htQ hWnoedge (R₀[m]'hm) hmQ
  rw [PathBasics.mem_interior_iff_of_pathFrom hW] at hwint
  obtain ⟨hwW, hws, hwt⟩ := hwint
  -- *"and `u` has no neighbour in its interior"*
  rcases hWmem w hwW with h | h | h
  · obtain ⟨k, hk, hkS, rfl⟩ := hW₁mem w h
    have := (PathBasics.path_adj_iff hR₀.1 hm hk).mp hadjw
    have hkm : k = iS := by omega
    exact hws (hget0 k iS hk hiS hkm)
  · rcases (hc02 _ (List.getElem_mem hm) w h).mp hadjw with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd (h1.trans h00.symm)
        (PathBasics.path_ne_of_ne_index hR₀.1 hm hlen0 (by omega))
    · exact absurd (h1.trans h0last.symm)
        (PathBasics.path_ne_of_ne_index hR₀.1 hm (by omega) (by omega))
  · obtain ⟨k, hk, hkT, rfl⟩ := hW₃mem w h
    have := (PathBasics.path_adj_iff hR₀.1 hm hk).mp hadjw
    have hkm : k = iT := by omega
    exact hwt (hget0 k iT hk hiT hkm)

end Workspace.ProofLemmas.Thm124SAdjT
