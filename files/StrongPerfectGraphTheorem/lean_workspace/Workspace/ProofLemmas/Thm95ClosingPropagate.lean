import Workspace.ProofLemmas.Thm95ClosingStep

/-!
# Repeating 9.3.2 over every antirung, in the closing paragraph of 9.5

PAPER (9.5, printed p. 53): *"For any other choice of `Qⱼ` the same happens, and `f₁, f_k`
cannot become exchanged since `f₁` has neighbours in `Q₁` and `f_k` has none.  We deduce that
`f₁` is complete to `Xⱼ ∪ Zⱼ` and anticomplete to `Yⱼ`; and `{f₂,…,f_k}` is anticomplete to
`V(Tⱼ)`.  In particular there is a vertex of `X ∩ V(S₁)` and a vertex of `X ∩ V(Tⱼ)` that are
nonadjacent, and so by exchanging `T₁` and `Tⱼ` in the above argument, we deduce that `f₁` is
complete to `X₁ ∪ Z₁` and anticomplete to `Y₁`; and `{f₂,…,f_k}` is anticomplete to `V(T₁)`.
Since this holds for all `j`, it follows that `a₁, f₁` have the same neighbours in
`V(T₁) ∪ ⋯ ∪ V(T_n)`, and there are no edges between `{f₂,…,f_k}` and
`V(T₁) ∪ ⋯ ∪ V(T_n)`."*

The sentence *"`f₁, f_k` cannot become exchanged"* is here the statement that `f₁` is the only
vertex of `F` with a neighbour on the base antirung, so the end produced by a second use of
9.3.2 has to be `f₁` again; and then the copied rung end has to be the same one, because the
two ends of the rung differ at the vertex `Thm95GapBasics.rung_anchor` provides.

The *"in particular"* sentence, which is what lets `T₁` itself be treated, is the pair
consisting of the neighbour of `f_k` on `P₁ \ a₁` and the anchor vertex on `Qⱼ`: the anchor is
adjacent to no vertex of `P₁` other than `a₁`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95ClosingPropagate

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (closing paragraph of 9.5):** everything before the final maximality contradiction. -/
theorem closing_global {Gx : SimpleGraph V} {m n : ℕ}
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
    (hanti : ∀ (k : Fin n) (Qx : List V), IsSRung Gxᶜ (T k) Qx →
      ∃ v ∈ Qx, ¬ ∃ f ∈ F, Gx.Adj v f)
    {i : Fin m} {j : Fin n} {u w : V}
    (huX : ∃ f ∈ F, Gx.Adj u f) (hwX : ∃ f ∈ F, Gx.Adj w f)
    (huS : u ∈ stripVertices (S i)) (hwT : w ∈ stripVertices (T j))
    (huw : ¬ Gx.Adj u w) :
    ∃ (S₀ : Set V × Set V × Set V) (P R : List V) (a b r s : V),
      (S₀ = S i ∨ S₀ = reverseStrip (S i)) ∧ IsSRung Gx S₀ P ∧
      IsPathFrom Gx P a b ∧ IsPathFrom Gx R r s ∧ {v : V | v ∈ R} = F ∧
      (∃ v ∈ ({v : V | v ∈ P} \ {a} : Set V), Gx.Adj s v) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {s}) ({v : V | v ∈ P} \ {a}) ∧
      (∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ↔ Gx.Adj a z)) ∧
      (∀ k : Fin n, Anticomplete Gx ({v : V | v ∈ R} \ {r}) (stripVertices (T k))) := by
  classical
  obtain ⟨P₀, hP₀, huP⟩ := exists_rung_through (hL.1 i) huS
  obtain ⟨Q₀, hQ₀, hwQ⟩ := exists_rung_through (hL.2.1 j : IsStrip Gxᶜ (T j)) hwT
  obtain ⟨a₀, b₀, hP₀ab, -, -, -, -, -⟩ := id hP₀
  have hends := srung_ends hP₀ hP₀ab
  have hab₀ : a₀ ≠ b₀ := fun h =>
    Set.disjoint_left.mp (strip_ends_disjoint (hL.1 i)) hends.1 (h ▸ hends.2)
  have hn2 : 2 ≤ n := hL.2.2.2.2.2.2.2.2.1
  obtain ⟨j', hjj'⟩ : ∃ j' : Fin n, j ≠ j' := by
    by_cases hj : (j : ℕ) = 0
    · refine ⟨⟨1, by omega⟩, fun h => ?_⟩
      have : (j : ℕ) = 1 := congrArg Fin.val h
      omega
    · exact ⟨⟨0, by omega⟩, fun h => hj (congrArg Fin.val h)⟩
  obtain ⟨Q₁, hQ₁⟩ := exists_rung (hL.2.1 j' : IsStrip Gxᶜ (T j'))
  obtain ⟨c, R, r, s, hcab, hR, hRset, hcopy, hantic, hwit, hantic2⟩ :=
    Thm95ClosingStep.closing_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq hone
      hanti hjj' hP₀ hP₀ab hQ₀ hQ₁ huP huX hwQ hwX huw
  have hrF : r ∈ F := by rw [← hRset]; exact PathBasics.head_mem hR.2.1
  have hsF : s ∈ F := by rw [← hRset]; exact PathBasics.getLast_mem hR.2.2
  -- `r` is the only vertex of `F` with a neighbour on an antirung it is anticomplete to
  have uniq : ∀ (Qb : List V), Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Qb} →
      ∀ f ∈ F, ∀ z ∈ Qb, Gx.Adj f z → f = r := by
    intro Qb hant f hf z hz hadj
    by_contra hne
    have hfR : f ∈ {v : V | v ∈ R} := by rw [hRset]; exact hf
    exact hant f ⟨hfR, hne⟩ z hz hadj
  -- one propagation step
  have propagate : ∀ (jb : Fin n) (Qb : List V), IsSRung Gxᶜ (T jb) Qb →
      (∀ z ∈ Qb, (Gx.Adj r z ↔ Gx.Adj c z)) →
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Qb} →
      (∃ u' ∈ P₀, ∃ w' ∈ Qb, (∃ f ∈ F, Gx.Adj u' f) ∧ (∃ f ∈ F, Gx.Adj w' f) ∧
        ¬ Gx.Adj u' w') →
      ∀ (k : Fin n), jb ≠ k → ∀ (Qk : List V), IsSRung Gxᶜ (T k) Qk →
        (∀ z ∈ Qk, (Gx.Adj r z ↔ Gx.Adj c z)) ∧
        Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Qk} := by
    rintro jb Qb hQb hrb hantb ⟨u', hu'P, w', hw'Q, hu'X, hw'X, hu'w'⟩ k hbk Qk hQk
    obtain ⟨za, hzaQ, zb, hzbQ, ⟨haza, honlya⟩, ⟨hbzb, honlyb⟩⟩ :=
      rung_anchor (hL.2.2.2.2.2.2.2.2.2.2.2.1 i jb) hP₀ hP₀ab hQb
    obtain ⟨c₂, R₂, r₂, s₂, hcab₂, hR₂, hRset₂, hcopy₂, hantic₂, -, -⟩ :=
      Thm95ClosingStep.closing_step hG hnoenl hnoover hnoovercompl hL hFsub hFconn hminEq
        hone hanti hbk hP₀ hP₀ab hQb hQk hu'P hu'X hw'Q hw'X hu'w'
    have hr₂F : r₂ ∈ F := by rw [← hRset₂]; exact PathBasics.head_mem hR₂.2.1
    -- the second use of 9.3.2 produces the same end of `F`
    have hr₂r : r₂ = r := by
      rcases hcab₂ with h | h
      · exact uniq Qb hantb r₂ hr₂F za hzaQ ((hcopy₂ za (Or.inl hzaQ)).mpr (h ▸ haza))
      · exact uniq Qb hantb r₂ hr₂F zb hzbQ ((hcopy₂ zb (Or.inl hzbQ)).mpr (h ▸ hbzb))
    -- and the same end of the rung
    have hc₂c : c₂ = c := by
      have hza : Gx.Adj r za ↔ Gx.Adj c za := hrb za hzaQ
      have hza₂ : Gx.Adj r za ↔ Gx.Adj c₂ za := by
        rw [← hr₂r]; exact hcopy₂ za (Or.inl hzaQ)
      have hnb : ¬ Gx.Adj b₀ za := honlya b₀ (PathBasics.getLast_mem hP₀ab.2.2) hab₀.symm
      rcases hcab with h | h <;> rcases hcab₂ with h2 | h2
      · rw [h, h2]
      · exact absurd (hza₂.mp (hza.mpr (h ▸ haza))) (h2 ▸ hnb)
      · exact absurd (hza.mp (hza₂.mpr (h2 ▸ haza))) (h ▸ hnb)
      · rw [h, h2]
    refine ⟨fun z hz => ?_, fun v hv z hz => ?_⟩
    · rw [← hc₂c, ← hr₂r]; exact hcopy₂ z (Or.inr hz)
    · refine hantic₂ v ⟨?_, ?_⟩ z (Or.inr hz)
      · have : v ∈ {y : V | y ∈ R₂} := by rw [hRset₂, ← hRset]; exact hv.1
        exact this
      · rw [hr₂r]; exact hv.2
  -- the base data
  have hbase₀ : (∀ z ∈ Q₀, (Gx.Adj r z ↔ Gx.Adj c z)) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Q₀} :=
    ⟨fun z hz => hcopy z (Or.inl hz), fun v hv z hz => hantic v hv z (Or.inl hz)⟩
  have hbase₁ : (∀ z ∈ Q₁, (Gx.Adj r z ↔ Gx.Adj c z)) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Q₁} :=
    ⟨fun z hz => hcopy z (Or.inr hz), fun v hv z hz => hantic v hv z (Or.inr hz)⟩
  -- the nonadjacent pair on the second antistrip, from the neighbour of `s` on the rung
  obtain ⟨p, ⟨hpP, hpc⟩, hsp⟩ := hwit
  have hpair₁ : ∃ u' ∈ P₀, ∃ w' ∈ Q₁, (∃ f ∈ F, Gx.Adj u' f) ∧ (∃ f ∈ F, Gx.Adj w' f) ∧
      ¬ Gx.Adj u' w' := by
    obtain ⟨za, hzaQ, zb, hzbQ, ⟨haza, honlya⟩, ⟨hbzb, honlyb⟩⟩ :=
      rung_anchor (hL.2.2.2.2.2.2.2.2.2.2.2.1 i j') hP₀ hP₀ab hQ₁
    rcases hcab with h | h
    · exact ⟨p, hpP, za, hzaQ, ⟨s, hsF, hsp.symm⟩,
        ⟨r, hrF, ((hbase₁.1 za hzaQ).mpr (h ▸ haza)).symm⟩,
        fun hadj => honlya p hpP (h ▸ hpc) hadj⟩
    · exact ⟨p, hpP, zb, hzbQ, ⟨s, hsF, hsp.symm⟩,
        ⟨r, hrF, ((hbase₁.1 zb hzbQ).mpr (h ▸ hbzb)).symm⟩,
        fun hadj => honlyb p hpP (h ▸ hpc) hadj⟩
  have hpair₀ : ∃ u' ∈ P₀, ∃ w' ∈ Q₀, (∃ f ∈ F, Gx.Adj u' f) ∧ (∃ f ∈ F, Gx.Adj w' f) ∧
      ¬ Gx.Adj u' w' := ⟨u, huP, w, hwQ, huX, hwX, huw⟩
  have hall : ∀ (k : Fin n) (Qk : List V), IsSRung Gxᶜ (T k) Qk →
      (∀ z ∈ Qk, (Gx.Adj r z ↔ Gx.Adj c z)) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) {v : V | v ∈ Qk} := by
    intro k Qk hQk
    by_cases hkj : k = j
    · subst k
      exact propagate j' Q₁ hQ₁ hbase₁.1 hbase₁.2 hpair₁ j hjj'.symm Qk hQk
    · exact propagate j Q₀ hQ₀ hbase₀.1 hbase₀.2 hpair₀ k (Ne.symm hkj) Qk hQk
  have hcopyT : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) →
      (Gx.Adj r z ↔ Gx.Adj c z) := by
    intro k z hz
    obtain ⟨Qk, hQk, hzQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hz
    exact (hall k Qk hQk).1 z hzQ
  have hantiT : ∀ k : Fin n,
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) (stripVertices (T k)) := by
    intro k v hv z hz
    obtain ⟨Qk, hQk, hzQ⟩ := exists_rung_through (hL.2.1 k : IsStrip Gxᶜ (T k)) hz
    exact (hall k Qk hQk).2 v hv z hzQ
  -- assemble, reversing the strip if the copied end is the far one
  rcases hcab with h | h
  · subst c
    exact ⟨S i, P₀, R, a₀, b₀, r, s, Or.inl rfl, hP₀, hP₀ab, hR, hRset,
      ⟨p, ⟨hpP, hpc⟩, hsp⟩, hantic2, hcopyT, hantiT⟩
  · subst c
    have hPrev : ({v : V | v ∈ P₀.reverse} : Set V) = {v : V | v ∈ P₀} := by
      ext z; exact List.mem_reverse
    refine ⟨reverseStrip (S i), P₀.reverse, R, b₀, a₀, r, s, Or.inr rfl,
      KnotFromTwist.isSRung_reverse hP₀, PathBasics.isPathFrom_reverse hP₀ab, hR, hRset,
      ?_, ?_, hcopyT, hantiT⟩
    · rw [hPrev]; exact ⟨p, ⟨hpP, hpc⟩, hsp⟩
    · rw [hPrev]; exact hantic2

end Workspace.ProofLemmas.Thm95ClosingPropagate
