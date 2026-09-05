import Workspace.ProofLemmas.Thm175Claim2Basics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim2Slices

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim2Basics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The slice form of the smaller-counterexample argument in claim (2).
The slice starts after `p₁`, and its unique complete vertices are its ends. -/
theorem even_short_slice (G : SimpleGraph V) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (A B : Set V) (hA : AnticonnectedSet G A) (hB : AnticonnectedSet G B)
    (hAB : AnticonnectedSet G (A ∪ B))
    (hAsub : A ⊆ c.X ∪ c.Y) (hBsub : B ⊆ c.X ∪ c.Y)
    (a b : ℕ) (ha : 0 < a) (hab : a + 1 < b) (hb : b < c.core.p.length)
    (hAa : Marked G A c.core.p a) (hBb : Marked G B c.core.p b)
    (honlyA : ∀ k, a ≤ k → k ≤ b → Marked G A c.core.p k → k = a)
    (honlyB : ∀ k, a ≤ k → k ≤ b → Marked G B c.core.p k → k = b) :
    Even (b - a) := by
  have hal : a < c.core.p.length := by omega
  let q := (c.core.p.drop a).take (b - a + 1)
  have hq := PathBasics.isPathFrom_slice c.core.hp.1 (show a < b by omega) hb
  have hlen : q.length = b - a + 1 :=
    PathBasics.length_slice c.core.p (by omega) hb
  have hplen : pathLength q = b - a := by rw [pathLength, hlen]; omega
  have hsub : ∀ w ∈ q, w ∈ c.core.p :=
    fun _ hw => List.drop_subset _ _ (List.take_subset _ _ hw)
  have hout : ∀ w ∈ q, w ∉ c.X ∪ c.Y := by
    intro w hw
    rintro (hx | hy)
    · exact c.core.houtX w (hsub w hw) hx
    · exact c.core.houtY w (hsub w hw) hy
  have huniqA : ∀ w ∈ q, VertexComplete G w A → w = c.core.p[a]'hal := by
    intro w hw hc
    obtain ⟨k, hk, hka, hkb, rfl⟩ :=
      (PathBasics.mem_slice_iff c.core.p (by omega) hb).mp hw
    have he := honlyA k hka hkb ⟨hk, hc⟩
    subst k
    rfl
  have huniqB : ∀ w ∈ q, VertexComplete G w B ↔ w = c.core.p[b]'hb := by
    intro w hw
    constructor
    · intro hc
      obtain ⟨k, hk, hka, hkb, rfl⟩ :=
        (PathBasics.mem_slice_iff c.core.p (by omega) hb).mp hw
      have he := honlyB k hka hkb ⟨hk, hc⟩
      subst k
      rfl
    · rintro rfl
      exact hBb.2
  apply Nat.not_odd_iff_even.mp
  intro hodd
  apply shorter_unique_not_odd G z c hopt A B hA hB hAB q
    (c.core.p[a]'hal) (c.core.p[b]'hb) hq
    (by rw [hplen]; omega) (by rw [hlen]; omega)
    (fun w hw hwA => hout w hw (hAsub hwA))
    (fun w hw hwB => hout w hw (hBsub hwB))
    hAa.2 huniqA huniqB
    (fun hz => c.hz (hz.elim (fun h => hAsub h) (fun h => hBsub h)))
    (fun w hw => c.hzXY w (hw.elim (fun h => hAsub h) (fun h => hBsub h)))
    (fun hz => c.core.hzP (hsub z hz))
    (fun w hw => c.core.hzanti w (hsub w hw))
  rwa [hplen]

/-- PAPER: "If the path `p_j-⋯-p_n` has odd length, then
`p_j,…,p_n, X \ {x_k}, Y` is a counterexample ... So `n-j` is even."
Here `i` is the last complete index for the first side. -/
theorem tail_even (G : SimpleGraph V) (z : V) (c : Counterexample G z)
    (hopt : IsOptimal c) (A : Set V) (hA : AnticonnectedSet G A)
    (hAY : AnticonnectedSet G (A ∪ c.Y)) (hAsub : A ⊆ c.X)
    (i : ℕ) (hi : 0 < i) (hin : i + 2 ≤ pathLength c.core.p)
    (hAi : Marked G A c.core.p i)
    (hlast : ∀ k, i < k → ¬ Marked G A c.core.p k) :
    Even (pathLength c.core.p - i) := by
  have hpos := PathBasics.path_length_pos c.core.hp.1
  have hlastidx : c.core.p[c.core.p.length - 1]'(by omega) = c.core.pₙ :=
    PathBasics.getElem_last_of_getLast? c.core.hp.2.2 hpos
  apply even_short_slice G z c hopt A c.Y hA c.hYa hAY
    (fun _ h => Or.inl (hAsub h)) (fun _ h => Or.inr h)
    i (c.core.p.length - 1) hi (by simpa [pathLength] using hin) (by omega) hAi
  · refine ⟨by omega, ?_⟩
    rw [hlastidx]
    exact (c.core.hYuniq _ (PathBasics.getLast_mem c.core.hp.2.2)).mpr rfl
  · intro k hik _ hk
    by_contra hn
    exact hlast k (by omega) hk
  · intro k _ _ hk
    obtain ⟨hkl, hkc⟩ := hk
    have he := (c.core.hYuniq _ (List.getElem_mem hkl)).mp hkc
    exact c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hlastidx.symm)

/-- PAPER: "If some line `L` has odd length greater than 1, then the
triple `L, X \ {x₁}, X \ {x₂}` is another counterexample ... Hence
every line is even." The antihole argument supplies the nonadjacent ends. -/
theorem oriented_line_even (G : SimpleGraph V) (z : V)
    (c : Counterexample G z) (hopt : IsOptimal c)
    (A B : Set V) (hA : AnticonnectedSet G A) (hB : AnticonnectedSet G B)
    (hAB : AnticonnectedSet G (A ∪ B))
    (hAsub : A ⊆ c.X ∪ c.Y) (hBsub : B ⊆ c.X ∪ c.Y)
    (hsep : ∀ i, Marked G A c.core.p i → Marked G B c.core.p i → i = 0)
    (a b : ℕ) (hl : Line (Marked G A c.core.p) (Marked G B c.core.p) a b)
    (haA : Marked G A c.core.p a) (hbB : Marked G B c.core.p b)
    (hnadj : ¬ G.Adj (c.core.p[a]'haA.1) (c.core.p[b]'hbB.1)) :
    Even (b - a) := by
  have ha := hl.1
  have hab := hl.2.1
  have hablong : a + 1 < b := by
    by_contra hn
    have he : a + 1 = b := by omega
    exact hnadj ((PathBasics.path_adj_iff c.core.hp.1 haA.1 hbB.1).mpr (Or.inl he))
  apply even_short_slice G z c hopt A B hA hB hAB hAsub hBsub
    a b ha hablong hbB.1 haA hbB
  · intro k hka hkb hk
    by_contra hne
    by_cases he : k = b
    · have := hsep b (he ▸ hk) hbB
      omega
    · exact (hl.2.2.2 k (by omega) (by omega)).1 hk
  · intro k hka hkb hk
    by_contra hne
    by_cases he : k = a
    · have := hsep a haA (he ▸ hk)
      omega
    · exact (hl.2.2.2 k (by omega) (by omega)).2 hk

end Workspace.ProofLemmas.Thm175Claim2Slices
