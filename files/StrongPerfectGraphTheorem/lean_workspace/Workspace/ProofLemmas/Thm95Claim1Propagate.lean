import Workspace.ProofLemmas.Thm95Claim1Step

/-!
# The five consequences of 9.3.3 in claim (1) of 9.5

PAPER (9.5(1), printed p. 52): *"Second, every vertex of `Qⱼ` is in `X`, and since this holds
for all `Qⱼ` it follows that `V(Tⱼ) ⊆ X`.  … Third, this shows that there are no edges between
`{f₂,…,f_{k-1}}` and `V(T₁) ∪ ⋯ ∪ V(T_n)`.  Fourth, for `1 ≤ j ≤ n` every vertex in `Zⱼ` is
adjacent to both `f₁, f_k`. … Fifth, every vertex in `X₁ ∪ Y₁ ⋯ ∪ X_n ∪ Y_n` is adjacent to
exactly one of `f₁, f_k`."*

Everything here rests on one fact, proved by repeating `Thm95Claim1Step.claim1_step`: for every
vertex `z` of every antistrip there is a rung of some strip, parallel or co-parallel to that
antistrip, whose two ends have the same adjacency to `z` as `f₁` and `f_k` do.  The fourth and
fifth consequences are then read off the definition of *parallel* by
`Thm95GapBasics.end_pattern`, and the second by `Thm95GapBasics.cover_strip`.

The sentence *"`f₁, f_k` cannot become exchanged"* is, as in the closing paragraph, the
observation that `f₁` and `f_k` are the only two vertices of `F` with a neighbour on the base
antirung, and that they are told apart there by `Thm95GapBasics.anchor`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95Claim1Propagate

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(1)):** the path `f₁-⋯-f_k` together with the local picture of `F` on every
antistrip of the striation. -/
theorem claim1_facts {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gx.induce K'),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gxᶜ.induce K'),
      IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ)
    (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ) (hFconn : ConnectedSet Gx F)
    (hminEq : ∀ F' : Set V, F' ⊆ F → ConnectedSet Gx F' →
      ¬ LocalForStriation Gx S T (attachments Gx F' (striationVertices S T)) → F' = F)
    (hno : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    {j : Fin n} {Q : List V} (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, ∃ f ∈ F, Gx.Adj v f) :
    ∃ (R : List V) (r s : V), IsPathFrom Gx R r s ∧ Odd (pathLength R) ∧
      {v : V | v ∈ R} = F ∧ r ≠ s ∧
      (∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) →
        ∃ (Sx : Set V × Set V × Set V) (a b : V),
          (ParallelStripAntistrip Gx Sx (T k) ∨ CoParallel Gx Sx (T k)) ∧
          a ∈ Sx.1 ∧ b ∈ Sx.2.2 ∧
          (Gx.Adj r z ↔ Gx.Adj a z) ∧ (Gx.Adj s z ↔ Gx.Adj b z)) ∧
      (∀ k : Fin n, Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k))) := by
  classical
  have hm2 : 2 ≤ m := hL.2.2.2.2.2.2.2.1
  have hn2 : 2 ≤ n := hL.2.2.2.2.2.2.2.2.1
  let i₀ : Fin m := ⟨0, by omega⟩
  obtain ⟨j', hjj'⟩ : ∃ j' : Fin n, j ≠ j' := by
    by_cases hj : (j : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have : (j : ℕ) = 1 := congrArg Fin.val h
      omega
    · exact ⟨⟨0, by omega⟩, fun h => hj (congrArg Fin.val h)⟩
  obtain ⟨Q', hQ'⟩ := exists_rung (hL.2.1 j' : IsStrip Gxᶜ (T j'))
  obtain ⟨Sx₀, c₀, d₀, R, r, s, hc₀, hd₀, hpar₀, hR, hodd, hRset, hcopy₁, hcopy₂, hint⟩ :=
    Thm95Claim1Step.claim1_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq hno
      i₀ hjj' hQ hQ' hQall
  have hrs : r ≠ s := PathBasics.isPathFrom_ends_ne hR (by obtain ⟨t, ht⟩ := hodd; omega)
  have hrF : r ∈ F := by rw [← hRset]; exact PathBasics.head_mem hR.2.1
  have hsF : s ∈ F := by rw [← hRset]; exact PathBasics.getLast_mem hR.2.2
  -- every vertex of the second antistrip is an attachment as well
  have hQ'all : ∀ v ∈ Q', ∃ f ∈ F, Gx.Adj v f := by
    intro v hv
    rcases cover_strip (hpar₀ j') hc₀ hd₀ v
        (KnotFromTwist.mem_stripVertices_of_isSRung hQ' hv) with h | h
    · exact ⟨r, hrF, ((hcopy₁ v (Or.inr hv)).mpr h).symm⟩
    · exact ⟨s, hsF, ((hcopy₂ v (Or.inr hv)).mpr h).symm⟩
  -- the two ends of `F` are told apart on either of the two antirungs
  have hsep : ∀ (jb : Fin n) (Qb : List V), IsSRung Gxᶜ (T jb) Qb →
      (∀ z ∈ Qb, (Gx.Adj r z ↔ Gx.Adj c₀ z)) → (∀ z ∈ Qb, (Gx.Adj s z ↔ Gx.Adj d₀ z)) →
      (∃ zA ∈ Qb, Gx.Adj r zA ∧ ¬ Gx.Adj s zA) ∧ (∃ zB ∈ Qb, Gx.Adj s zB ∧ ¬ Gx.Adj r zB) := by
    intro jb Qb hQb h1 h2
    obtain ⟨zA, hzA, zB, hzB, hazA, hbzA, hbzB, hazB⟩ :=
      anchor (hpar₀ jb) hc₀ hd₀ hQb
    exact ⟨⟨zA, hzA, (h1 zA hzA).mpr hazA, fun h => hbzA ((h2 zA hzA).mp h)⟩,
      ⟨zB, hzB, (h2 zB hzB).mpr hbzB, fun h => hazB ((h1 zB hzB).mp h)⟩⟩
  -- one propagation step
  have propagate : ∀ (jb : Fin n) (Qb : List V), IsSRung Gxᶜ (T jb) Qb →
      (∀ v ∈ Qb, ∃ f ∈ F, Gx.Adj v f) →
      (∃ zA ∈ Qb, Gx.Adj r zA ∧ ¬ Gx.Adj s zA) → (∃ zB ∈ Qb, Gx.Adj s zB ∧ ¬ Gx.Adj r zB) →
      ∀ (k : Fin n), jb ≠ k → ∀ (Qk : List V), IsSRung Gxᶜ (T k) Qk →
        (∀ z ∈ Qk, ∃ (Sx : Set V × Set V × Set V) (a b : V),
          (ParallelStripAntistrip Gx Sx (T k) ∨ CoParallel Gx Sx (T k)) ∧
          a ∈ Sx.1 ∧ b ∈ Sx.2.2 ∧
          (Gx.Adj r z ↔ Gx.Adj a z) ∧ (Gx.Adj s z ↔ Gx.Adj b z)) ∧
        (∀ v ∈ SPGT.interior R, ∀ z ∈ Qk, ¬ Gx.Adj v z) := by
    rintro jb Qb hQb hQball ⟨zA, hzAQ, hrzA, hszA⟩ ⟨zB, hzBQ, hszB, hrzB⟩ k hbk Qk hQk
    obtain ⟨Sx, c, d, R', r', s', hc, hd, hpar, hR', hodd', hRset', hco₁, hco₂, hint'⟩ :=
      Thm95Claim1Step.claim1_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq hno
        i₀ hbk hQb hQk hQball
    have hmemF' : ∀ v : V, v ∈ F → v = r' ∨ v = s' ∨ v ∈ SPGT.interior R' := by
      intro v hv
      by_cases h1 : v = r'
      · exact Or.inl h1
      · by_cases h2 : v = s'
        · exact Or.inr (Or.inl h2)
        · refine Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hR').mpr ⟨?_, h1, h2⟩))
          have : v ∈ {y : V | y ∈ R'} := by rw [hRset']; exact hv
          exact this
    have hrcase : r = r' ∨ r = s' := by
      rcases hmemF' r hrF with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hrzA (hint' r h zA (Or.inl hzAQ))
    have hscase : s = r' ∨ s = s' := by
      rcases hmemF' s hsF with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd hszB (hint' s h zB (Or.inl hzBQ))
    -- the interiors coincide, both being `F` without its two ends
    have hIsub : ∀ v ∈ SPGT.interior R, v ∈ SPGT.interior R' := by
      intro v hv
      have hvF : v ∈ F := by rw [← hRset]; exact PathBasics.interior_subset hv
      have hvne := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hv
      rcases hmemF' v hvF with h | h | h
      · rcases hrcase with hr | hr
        · exact absurd (h.trans hr.symm) hvne.2.1
        · rcases hscase with hs | hs
          · exact absurd (h.trans hs.symm) hvne.2.2
          · exact absurd (hr.trans hs.symm) hrs
      · rcases hscase with hs | hs
        · rcases hrcase with hr | hr
          · exact absurd (hr.trans hs.symm) hrs
          · exact absurd (h.trans hr.symm) hvne.2.1
        · exact absurd (h.trans hs.symm) hvne.2.2
      · exact h
    refine ⟨fun z hz => ?_, fun v hv z hz => hint' v (hIsub v hv) z (Or.inr hz)⟩
    rcases hrcase with hr | hr
    · have hs : s = s' := by
        rcases hscase with h | h
        · exact absurd (hr.trans h.symm) hrs
        · exact h
      exact ⟨Sx, c, d, hpar k, hc, hd, by rw [hr]; exact hco₁ z (Or.inr hz),
        by rw [hs]; exact hco₂ z (Or.inr hz)⟩
    · have hs : s = r' := by
        rcases hscase with h | h
        · exact h
        · exact absurd (hr.trans h.symm) hrs
      refine ⟨reverseStrip Sx, d, c, ?_, ?_, ?_,
        by rw [hr]; exact hco₂ z (Or.inr hz), by rw [hs]; exact hco₁ z (Or.inr hz)⟩
      · rcases hpar k with h | h
        · exact Or.inr ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr h)
        · exact Or.inl ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr h)
      · obtain ⟨A, C, B⟩ := Sx; exact hd
      · obtain ⟨A, C, B⟩ := Sx; exact hc
  -- the base data on the two antirungs already treated
  have hbQ : (∀ z ∈ Q, (Gx.Adj r z ↔ Gx.Adj c₀ z)) ∧ (∀ z ∈ Q, (Gx.Adj s z ↔ Gx.Adj d₀ z)) :=
    ⟨fun z hz => hcopy₁ z (Or.inl hz), fun z hz => hcopy₂ z (Or.inl hz)⟩
  have hbQ' : (∀ z ∈ Q', (Gx.Adj r z ↔ Gx.Adj c₀ z)) ∧ (∀ z ∈ Q', (Gx.Adj s z ↔ Gx.Adj d₀ z)) :=
    ⟨fun z hz => hcopy₁ z (Or.inr hz), fun z hz => hcopy₂ z (Or.inr hz)⟩
  have hall : ∀ (k : Fin n) (Qk : List V), IsSRung Gxᶜ (T k) Qk →
      (∀ z ∈ Qk, ∃ (Sx : Set V × Set V × Set V) (a b : V),
        (ParallelStripAntistrip Gx Sx (T k) ∨ CoParallel Gx Sx (T k)) ∧
        a ∈ Sx.1 ∧ b ∈ Sx.2.2 ∧
        (Gx.Adj r z ↔ Gx.Adj a z) ∧ (Gx.Adj s z ↔ Gx.Adj b z)) ∧
      (∀ v ∈ SPGT.interior R, ∀ z ∈ Qk, ¬ Gx.Adj v z) := by
    intro k Qk hQk
    by_cases hkj : k = j
    · subst k
      exact propagate j' Q' hQ' hQ'all (hsep j' Q' hQ' hbQ'.1 hbQ'.2).1
        (hsep j' Q' hQ' hbQ'.1 hbQ'.2).2 j hjj'.symm Qk hQk
    · exact propagate j Q hQ hQall (hsep j Q hQ hbQ.1 hbQ.2).1 (hsep j Q hQ hbQ.1 hbQ.2).2
        k (Ne.symm hkj) Qk hQk
  refine ⟨R, r, s, hR, hodd, hRset, hrs, ?_, ?_⟩
  · intro k z hz
    obtain ⟨Qk, hQk, hzQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hz
    exact (hall k Qk hQk).1 z hzQ
  · intro k v hv z hz
    obtain ⟨Qk, hQk, hzQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hz
    exact (hall k Qk hQk).2 v hv z hzQ

end Workspace.ProofLemmas.Thm95Claim1Propagate
