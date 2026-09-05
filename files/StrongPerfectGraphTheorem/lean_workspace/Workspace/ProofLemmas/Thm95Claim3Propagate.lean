import Workspace.ProofLemmas.Thm95Claim3Step

/-!
# Repeating 9.3.3 over every antirung, in claim (3) of 9.5

PAPER (9.5(3), printed p. 53): *"Third, let `x'ⱼ-Q'ⱼ-y'ⱼ` be some other `Tⱼ`-antirung.  By the
same argument applied to the knot `(P₁, Pᵢ, Q₁, Q'ⱼ)`, we deduce that again 9.3.3 holds, and so
one of `f₁, f_k` is adjacent to `x'ⱼ` and the other to `y'ⱼ`.  Furthermore, the one adjacent to
`x'ⱼ` is also adjacent to `a₁`; and so in fact `f₁` is adjacent to `x'ⱼ`.  Since this holds for
all choices of `Qⱼ` and of `j`, it follows that `f₁, a₁` have the same neighbours in
`V(T₁) ∪ ⋯ ∪ V(T_n)`, and so do `f_k, b₁`."*

The step that lets the paper say *"`f₁, f_k` cannot become exchanged"* is that `f₁` is the
**only** vertex of `F` with a neighbour at the end of the base antirung on the `a₁` side: the
other end `f_k` copies `b₁` there, and `b₁` is not adjacent to that vertex.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95Claim3Propagate

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(3)):** the whole of claim (3) up to the maximality contradiction.

The conclusion is the paper's *"`f₁, a₁` have the same neighbours in `V(T₁) ∪ ⋯ ∪ V(T_n)`, and
so do `f_k, b₁`"*, together with *"`{f₂,…,f_{k-1}}` is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`"*. -/
theorem claim3_global {Gx : SimpleGraph V} {m n : ℕ}
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
    (hone : ∀ k k' : Fin m,
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S k)).Nonempty →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S k')).Nonempty → k = k')
    {i : Fin m} {j : Fin n} {Q : List V}
    (hi : (attachments Gx F (striationVertices S T) ∩ stripVertices (S i)).Nonempty)
    (hQ : IsSRung Gxᶜ (T j) Q)
    (hQall : ∀ v ∈ Q, v ∈ attachments Gx F (striationVertices S T)) :
    ∃ (R : List V) (r s a b : V), IsPathFrom Gx R r s ∧ Odd (pathLength R) ∧
      {v : V | v ∈ R} = F ∧ a ∈ (S i).1 ∧ b ∈ (S i).2.2 ∧
      (∀ (k : Fin n) (w : V), w ∈ stripVertices (T k) → (Gx.Adj r w ↔ Gx.Adj a w)) ∧
      (∀ (k : Fin n) (w : V), w ∈ stripVertices (T k) → (Gx.Adj s w ↔ Gx.Adj b w)) ∧
      (∀ k : Fin n, Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k))) := by
  classical
  have hQall' : ∀ v ∈ Q, ∃ f ∈ F, Gx.Adj v f := fun v hv => (hQall v hv).2
  -- the rung of `S i` through an attachment
  obtain ⟨u, huX, huS⟩ := hi
  obtain ⟨P₀, hP₀, huP⟩ := exists_rung_through (hL.1 i) huS
  obtain ⟨a, b, hP₀ab, -, -, -, -, -⟩ := id hP₀
  have hab : a ∈ (S i).1 ∧ b ∈ (S i).2.2 := srung_ends hP₀ hP₀ab
  have huXF : ∃ f ∈ F, Gx.Adj u f := huX.2
  -- a second antistrip, and one of its antirungs
  have hn2 : 2 ≤ n := hL.2.2.2.2.2.2.2.2.1
  obtain ⟨j', hjj'⟩ : ∃ j' : Fin n, j ≠ j' := by
    by_cases hj : (j : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have : (j : ℕ) = 1 := congrArg Fin.val h
      omega
    · exact ⟨⟨0, by omega⟩, fun h => hj (congrArg Fin.val h)⟩
  obtain ⟨Qb', hQb'⟩ := exists_rung (hL.2.1 j' : IsStrip Gxᶜ (T j'))
  -- the first application of 9.3
  obtain ⟨R, r, s, hR, hodd, hRset, hcr, hcs, hint⟩ :=
    Thm95Claim3Step.claim3_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq hone
      hjj' hP₀ hP₀ab huP huXF hQ hQb' hQall'
  have hmemF : ∀ v : V, v ∈ F ↔ v ∈ R := by
    intro v; rw [← hRset]; exact Iff.rfl
  have hFsplit : ∀ v ∈ F, v = r ∨ v = s ∨ v ∈ SPGT.interior R := by
    intro v hv
    by_cases h1 : v = r
    · exact Or.inl h1
    · by_cases h2 : v = s
      · exact Or.inr (Or.inl h2)
      · exact Or.inr (Or.inr
          ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨(hmemF v).mp hv, h1, h2⟩))
  have hrF : r ∈ F := (hmemF r).mpr (PathBasics.head_mem hR.2.1)
  have hsF : s ∈ F := (hmemF s).mpr (PathBasics.getLast_mem hR.2.2)
  -- one step of the propagation
  have propagate : ∀ (jb : Fin n) (Qb : List V), IsSRung Gxᶜ (T jb) Qb →
      (∀ v ∈ Qb, ∃ f ∈ F, Gx.Adj v f) →
      (∀ w ∈ Qb, (Gx.Adj r w ↔ Gx.Adj a w)) →
      (∀ w ∈ Qb, (Gx.Adj s w ↔ Gx.Adj b w)) →
      (∀ v ∈ SPGT.interior R, ∀ w ∈ Qb, ¬ Gx.Adj v w) →
      ∀ (k : Fin n), jb ≠ k → ∀ (Qk : List V), IsSRung Gxᶜ (T k) Qk →
      (∀ w ∈ Qk, (Gx.Adj r w ↔ Gx.Adj a w)) ∧ (∀ w ∈ Qk, (Gx.Adj s w ↔ Gx.Adj b w)) ∧
        (∀ v ∈ SPGT.interior R, ∀ w ∈ Qk, ¬ Gx.Adj v w) := by
    intro jb Qb hQb hQball hrb hsb hintb k hbk Qk hQk
    obtain ⟨z, hzQ, z', hz'Q, haz, hbz, hbz', haz'⟩ :=
      anchor (hL.2.2.2.2.2.2.2.2.2.2.2.1 i jb) hab.1 hab.2 hQb
    -- `r` is the only vertex of `F` adjacent to `z`, and `s` the only one adjacent to `z'`
    have uniqr : ∀ f ∈ F, Gx.Adj f z → f = r := by
      intro f hf hadj
      rcases hFsplit f hf with h | h | h
      · exact h
      · exact absurd ((hsb z hzQ).mp (h ▸ hadj)) hbz
      · exact absurd hadj (hintb f h z hzQ)
    have uniqs : ∀ f ∈ F, Gx.Adj f z' → f = s := by
      intro f hf hadj
      rcases hFsplit f hf with h | h | h
      · exact absurd ((hrb z' hz'Q).mp (h ▸ hadj)) haz'
      · exact h
      · exact absurd hadj (hintb f h z' hz'Q)
    obtain ⟨R₂, r₂, s₂, hR₂, hodd₂, hRset₂, hcr₂, hcs₂, hint₂⟩ :=
      Thm95Claim3Step.claim3_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq hone
        hbk hP₀ hP₀ab huP huXF hQb hQk hQball
    have hr₂F : r₂ ∈ F := by rw [← hRset₂]; exact PathBasics.head_mem hR₂.2.1
    have hs₂F : s₂ ∈ F := by rw [← hRset₂]; exact PathBasics.getLast_mem hR₂.2.2
    have hr₂r : r₂ = r := uniqr r₂ hr₂F ((hcr₂ z (Or.inl hzQ)).mpr haz)
    have hs₂s : s₂ = s := uniqs s₂ hs₂F ((hcs₂ z' (Or.inl hz'Q)).mpr hbz')
    have hIeq : ∀ v : V, v ∈ SPGT.interior R → v ∈ SPGT.interior R₂ := by
      intro v hv
      have hvF : v ∈ F := by
        rw [← hRset]; exact PathBasics.interior_subset hv
      have hvne := (PathBasics.mem_interior_iff_of_pathFrom hR).mp hv
      refine (PathBasics.mem_interior_iff_of_pathFrom hR₂).mpr ⟨?_, ?_, ?_⟩
      · have : v ∈ {w : V | w ∈ R₂} := by rw [hRset₂]; exact hvF
        exact this
      · rw [hr₂r]; exact hvne.2.1
      · rw [hs₂s]; exact hvne.2.2
    refine ⟨fun w hw => ?_, fun w hw => ?_, fun v hv w hw => ?_⟩
    · rw [← hr₂r]; exact hcr₂ w (Or.inr hw)
    · rw [← hs₂s]; exact hcs₂ w (Or.inr hw)
    · exact hint₂ v (hIeq v hv) w (Or.inr hw)
  -- the base data on the two antirungs already treated
  have hbaseQ : (∀ w ∈ Q, (Gx.Adj r w ↔ Gx.Adj a w)) ∧ (∀ w ∈ Q, (Gx.Adj s w ↔ Gx.Adj b w)) ∧
      (∀ v ∈ SPGT.interior R, ∀ w ∈ Q, ¬ Gx.Adj v w) :=
    ⟨fun w hw => hcr w (Or.inl hw), fun w hw => hcs w (Or.inl hw),
      fun v hv w hw => hint v hv w (Or.inl hw)⟩
  have hbaseQ' : (∀ w ∈ Qb', (Gx.Adj r w ↔ Gx.Adj a w)) ∧
      (∀ w ∈ Qb', (Gx.Adj s w ↔ Gx.Adj b w)) ∧
      (∀ v ∈ SPGT.interior R, ∀ w ∈ Qb', ¬ Gx.Adj v w) :=
    ⟨fun w hw => hcr w (Or.inr hw), fun w hw => hcs w (Or.inr hw),
      fun v hv w hw => hint v hv w (Or.inr hw)⟩
  -- every vertex of the second antistrip is an attachment, so it too can serve as a base
  have hQb'all : ∀ v ∈ Qb', ∃ f ∈ F, Gx.Adj v f := by
    intro v hv
    rcases cover_strip (hL.2.2.2.2.2.2.2.2.2.2.2.1 i j') hab.1 hab.2 v
        (KnotFromTwist.mem_stripVertices_of_isSRung hQb' hv) with h | h
    · exact ⟨r, hrF, ((hbaseQ'.1 v hv).mpr h).symm⟩
    · exact ⟨s, hsF, ((hbaseQ'.2.1 v hv).mpr h).symm⟩
  -- the propagation, on every antirung of every antistrip
  have hall : ∀ (k : Fin n) (Qk : List V), IsSRung Gxᶜ (T k) Qk →
      (∀ w ∈ Qk, (Gx.Adj r w ↔ Gx.Adj a w)) ∧ (∀ w ∈ Qk, (Gx.Adj s w ↔ Gx.Adj b w)) ∧
        (∀ v ∈ SPGT.interior R, ∀ w ∈ Qk, ¬ Gx.Adj v w) := by
    intro k Qk hQk
    by_cases hkj : k = j
    · subst k
      exact propagate j' Qb' hQb' hQb'all hbaseQ'.1 hbaseQ'.2.1 hbaseQ'.2.2 j hjj'.symm Qk hQk
    · exact propagate j Q hQ hQall' hbaseQ.1 hbaseQ.2.1 hbaseQ.2.2 k (Ne.symm hkj) Qk hQk
  refine ⟨R, r, s, a, b, hR, hodd, hRset, hab.1, hab.2, ?_, ?_, ?_⟩
  · intro k w hw
    obtain ⟨Qk, hQk, hwQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hw
    exact (hall k Qk hQk).1 w hwQ
  · intro k w hw
    obtain ⟨Qk, hQk, hwQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hw
    exact (hall k Qk hQk).2.1 w hwQ
  · intro k v hv w hw
    obtain ⟨Qk, hQk, hwQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hw
    exact (hall k Qk hQk).2.2 v hv w hwQ

end Workspace.ProofLemmas.Thm95Claim3Propagate
