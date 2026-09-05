import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.Thm244Shapes
import Workspace.ProofLemmas.Thm244Parity

/-!
# The first case of the printed proof of 24.4

Chudnovsky–Robertson–Seymour–Thomas, *The Strong Perfect Graph Theorem*, printed
p. 144:

> Suppose that the first holds, and let `P₁,P₂,P₃` be as in the first case.  Then some
> two of `P₁,P₂,P₃` have lengths of the same parity, and their union violates (1).

Transcription.  For `i ≠ j` the union `Pᵢ ∪ Pⱼ` is an induced path from `vᵢ` to `vⱼ`:
the two legs meet only in the centre `u` and there is no edge between `V(Pᵢ \ u)` and
`V(Pⱼ \ u)`, which is exactly the hypothesis of `PathGlue.glue_path` once the centre is
deleted from one of the two legs (`Thm244Parity.chop`).  Its number of vertices is
`|Pᵢ| + |Pⱼ| - 1`, and `vᵢ`, `vⱼ` are the unique `Xᵢ`-, `Xⱼ`-complete vertices on it
because they already are inside `F`.  So claim (1) — `Thm244Parity.even_length_of_unique_ends`
— gives `|Pᵢ| + |Pⱼ| - 1` even, i.e. `Pᵢ` and `Pⱼ` have lengths of *opposite* parity, for
**every** pair `i ≠ j`.  Three natural numbers cannot be pairwise of opposite parity, which
is the paper's *"some two of `P₁,P₂,P₃` have lengths of the same parity"* and the
contradiction in one step (`omega`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm244Case1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm244Shapes

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {a b : ℕ} (h : a = b)
    (ha : a < q.length) (hb : b < q.length) : q[a]'ha = q[b]'hb := by
  subst h; rfl

/-- *"their union violates (1)"* — for a single pair of legs. -/
private theorem legs_even (G : SimpleGraph V) (hG : InF11 G) (X : Fin 3 → Set V)
    (hXdisj : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Disjoint (X l₁) (X l₂))
    (hXne : ∀ l : Fin 3, (X l).Nonempty)
    (hXanti : ∀ l : Fin 3, AnticonnectedSet G (X l))
    (hXcomp : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Complete G (X l₁) (X l₂))
    (F : Set V) (v : Fin 3 → V) (u : V) (P : Fin 3 → List V)
    (hv : ∀ l : Fin 3, VertexComplete G (v l) (X l))
    (huniq : ∀ l : Fin 3, ∀ w ∈ F, VertexComplete G w (X l) → w = v l)
    (hune : ∀ l : Fin 3, u ≠ v l)
    (hpath : ∀ l : Fin 3, IsPathFrom G (P l) (v l) u)
    (hsub : ∀ l : Fin 3, ∀ w ∈ P l, w ∈ F)
    (hcr : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → ∀ a ∈ P l₁, ∀ b ∈ P l₂, a ≠ u → b ≠ u →
      a ≠ b ∧ ¬ G.Adj a b)
    (hlen : ∀ l : Fin 3, 2 ≤ (P l).length)
    (l₁ l₂ : Fin 3) (hl : l₁ ≠ l₂) :
    Even ((P l₁).length + (P l₂).length - 1) := by
  have hp1 := hpath l₁
  have hp2 := hpath l₂
  have hl1 : 2 ≤ (P l₁).length := hlen l₁
  have hl2 : 2 ≤ (P l₂).length := hlen l₂
  have h2pos : 0 < (P l₂).length := by omega
  have hu2 : (P l₂)[(P l₂).length - 1]'(by have := hlen l₂; omega) = u :=
    PathBasics.getElem_last_of_getLast? hp2.2.2 h2pos
  have hnd2 : (P l₂).Nodup := PathBasics.path_nodup hp2.1
  obtain ⟨D, hD, hDlen, hDmem⟩ := Thm244Parity.chop hp2 (hlen l₂)
  have hS : IsPathFrom G D.reverse ((P l₂)[(P l₂).length - 2]'(by have := hlen l₂; omega))
      (v l₂) := PathBasics.isPathFrom_reverse hD
  have hSmem : ∀ y ∈ D.reverse,
      ∃ (k : ℕ) (hk : k < (P l₂).length), k ≤ (P l₂).length - 2 ∧ (P l₂)[k]'hk = y := by
    intro y hy; exact (hDmem y).mp (List.mem_reverse.mp hy)
  have hSneU : ∀ y ∈ D.reverse, y ≠ u := by
    intro y hy hyu
    obtain ⟨k, hk, hkm, hky⟩ := hSmem y hy
    have heq : (P l₂)[k]'hk = (P l₂)[(P l₂).length - 1]'(by omega) := by
      rw [hky, hyu, hu2]
    have hkk : k = (P l₂).length - 1 := hnd2.getElem_inj_iff.mp heq
    omega
  have hSinP2 : ∀ y ∈ D.reverse, y ∈ P l₂ := by
    intro y hy
    obtain ⟨k, hk, -, hky⟩ := hSmem y hy
    rw [← hky]; exact List.getElem_mem hk
  -- the two legs are disjoint apart from the centre, which `D.reverse` no longer contains
  have hdisj : ∀ x ∈ P l₁, x ∉ D.reverse := by
    intro x hx hxS
    by_cases hxu : x = u
    · exact hSneU x hxS hxu
    · exact (hcr l₁ l₂ hl x hx x (hSinP2 x hxS) hxu (hSneU x hxS)).1 rfl
  -- and the only edge across is the one at the centre
  have hcross : ∀ x ∈ P l₁, ∀ y ∈ D.reverse,
      (G.Adj x y ↔ (x = u ∧ y = (P l₂)[(P l₂).length - 2]'(by have := hlen l₂; omega))) := by
    intro x hx y hy
    obtain ⟨k, hk, hkm, hky⟩ := hSmem y hy
    have hyu : y ≠ u := hSneU y hy
    by_cases hxu : x = u
    · subst hxu
      have hadj := PathBasics.path_adj_iff hp2.1
        (show (P l₂).length - 1 < (P l₂).length by omega) hk
      rw [hu2] at hadj
      have hyeq : ((P l₂)[k]'hk = (P l₂)[(P l₂).length - 2]'(by omega)) ↔
          k = (P l₂).length - 2 := hnd2.getElem_inj_iff
      rw [← hky, hadj, hyeq]
      constructor
      · intro h; exact ⟨rfl, by omega⟩
      · rintro ⟨-, h⟩; omega
    · refine iff_of_false ?_ (by tauto)
      exact (hcr l₁ l₂ hl x hx y (hSinP2 y hy) hxu hyu).2
  have hglue : IsPathFrom G (P l₁ ++ D.reverse) (v l₁) (v l₂) :=
    PathGlue.glue_path hp1 hS hdisj hcross
  have hsubg : ∀ w ∈ (P l₁ ++ D.reverse), w ∈ F := by
    intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hsub l₁ w h
    · exact hsub l₂ w (hSinP2 w h)
  have hvne : v l₁ ≠ v l₂ :=
    (hcr l₁ l₂ hl (v l₁) (PathBasics.head_mem hp1.2.1) (v l₂) (PathBasics.head_mem hp2.2.1)
      (hune l₁).symm (hune l₂).symm).1
  have heven := Thm244Parity.even_length_of_unique_ends G hG (X l₁) (X l₂)
    (hXdisj l₁ l₂ hl) (hXne l₁) (hXne l₂) (hXanti l₁) (hXanti l₂) (hXcomp l₁ l₂ hl)
    (P l₁ ++ D.reverse) (v l₁) (v l₂) hglue.1 hglue.2.1 hglue.2.2 hvne
    (fun w hw => ⟨fun hc => huniq l₁ w (hsubg w hw) hc, fun he => he ▸ hv l₁⟩)
    (fun w hw => ⟨fun hc => huniq l₂ w (hsubg w hw) hc, fun he => he ▸ hv l₂⟩)
  have hlength : (P l₁ ++ D.reverse).length = (P l₁).length + (P l₂).length - 1 := by
    simp only [List.length_append, List.length_reverse, hDlen]
    have := hlen l₂; omega
  rwa [hlength] at heven

/-- **Case 1 of the printed proof of 24.4 is impossible.** -/
theorem case1_refute (G : SimpleGraph V) (hG : InF11 G)
    (X : Fin 3 → Set V)
    (hXdisj : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Disjoint (X l₁) (X l₂))
    (hXne : ∀ l : Fin 3, (X l).Nonempty)
    (hXanti : ∀ l : Fin 3, AnticonnectedSet G (X l))
    (hXcomp : ∀ l₁ l₂ : Fin 3, l₁ ≠ l₂ → Complete G (X l₁) (X l₂))
    (F : Set V) (v : Fin 3 → V) (u : V) (P : Fin 3 → List V)
    (hshape : Spider G F (fun l => {w : V | VertexComplete G w (X l)}) v u P) :
    False := by
  obtain ⟨hv, huniq, hune, hpath, hsub, hcr⟩ := hshape
  simp only [Set.mem_setOf_eq] at hv huniq
  -- every leg has at least two vertices, since `u ≠ vᵢ`
  have hlen : ∀ l : Fin 3, 2 ≤ (P l).length := by
    intro l
    have hp := hpath l
    have hpos : 0 < (P l).length := PathBasics.path_length_pos hp.1
    by_contra hc
    refine hune l ?_
    have h0 := PathBasics.getElem_zero_of_head? hp.2.1 hpos
    have hlst := PathBasics.getElem_last_of_getLast? hp.2.2 hpos
    rw [← hlst, ← h0]
    exact gidx (P l) (by omega) (by omega) hpos
  have e01 := legs_even G hG X hXdisj hXne hXanti hXcomp F v u P hv huniq hune hpath hsub hcr
    hlen 0 1 (by decide)
  have e02 := legs_even G hG X hXdisj hXne hXanti hXcomp F v u P hv huniq hune hpath hsub hcr
    hlen 0 2 (by decide)
  have e12 := legs_even G hG X hXdisj hXne hXanti hXcomp F v u P hv huniq hune hpath hsub hcr
    hlen 1 2 (by decide)
  have h0 := hlen 0
  have h1 := hlen 1
  have h2 := hlen 2
  rw [Nat.even_iff] at e01 e02 e12
  omega

end Workspace.ProofLemmas.Thm244Case1
