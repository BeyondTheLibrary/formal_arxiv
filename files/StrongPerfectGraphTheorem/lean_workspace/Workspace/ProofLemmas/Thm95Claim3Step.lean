import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.KnotFromTwist
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.Thm94ClosingStriation
import Workspace.ProofLemmas.Thm95GapBasics
import Workspace.Statements.S09.Thm_9_3

/-!
# One application of 9.3 inside claim (3) of 9.5

PAPER (9.5(3), printed p. 53): *"Let `Qⱼ` be an `xⱼ-Tⱼ-yⱼ`-antirung, let `a₁-P₁-b₁` be an
`S₁`-rung such that `X` meets `P₁`, and let `aᵢ-Pᵢ-bᵢ` be an `Sᵢ`-rung.  Hence
`(P₁, Pᵢ, Q₁, Qⱼ)` is a knot.  Let us apply 9.3.  By (2) and the minimality of `F` it follows
that 9.3.3 holds.  This has several consequences.  First, from the minimality of `F`, `G|F` is
an odd path `f₁-⋯-f_k` such that `f₁, a₁` have the same neighbours in `V(Q₁ ∪ Qⱼ)`, and so do
`f_k, b₁`."*

This file proves exactly that sentence, for one pair of antirungs.  The repetition over all
antirungs is `Thm95Claim3Propagate`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95Claim3Step

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(3)):** one application of 9.3 to the knot `(P₁, Pᵢ, Q₁, Qⱼ)`.

`a` and `b` are the two ends of the chosen `Sᵢ`-rung `P₀`, `u` is the vertex of `P₀` that has
a neighbour in `F` (*"`X` meets `P₁`"*), `Q` is an antirung of `T j` all of whose vertices are
attachments of `F`, and `Q'` is any antirung of another antistrip.  The conclusion is the
paper's *"`G|F` is an odd path `f₁-⋯-f_k` such that `f₁, a₁` have the same neighbours in
`V(Q₁ ∪ Qⱼ)`, and so do `f_k, b₁`"*, together with the third consequence *"`{f₂,…,f_{k-1}}`
is anticomplete to `V(T₁) ∪ ⋯ ∪ V(T_n)`"* for these two antirungs. -/
theorem claim3_step {Gx : SimpleGraph V} {m n : ℕ}
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
    {i : Fin m} {j j' : Fin n} (hjj' : j ≠ j')
    {P₀ Q Q' : List V} {a b u : V}
    (hP₀ : IsSRung Gx (S i) P₀) (hP₀ab : IsPathFrom Gx P₀ a b)
    (huP : u ∈ P₀) (huX : ∃ f ∈ F, Gx.Adj u f)
    (hQ : IsSRung Gxᶜ (T j) Q) (hQ' : IsSRung Gxᶜ (T j') Q')
    (hQall : ∀ v ∈ Q, ∃ f ∈ F, Gx.Adj v f) :
    ∃ (R : List V) (r s : V), IsPathFrom Gx R r s ∧ Odd (pathLength R) ∧
      {v : V | v ∈ R} = F ∧
      (∀ w ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V), (Gx.Adj r w ↔ Gx.Adj a w)) ∧
      (∀ w ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V), (Gx.Adj s w ↔ Gx.Adj b w)) ∧
      Anticomplete Gx {v : V | v ∈ SPGT.interior R}
        ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'}) := by
  classical
  obtain ⟨i', hii', htw⟩ := Thm94ClosingStriation.exists_twist_with_fixed_strip hL i hjj'
  obtain ⟨P₀', hP₀'⟩ := exists_rung (hL.1 i')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hjj' htw hP₀ hP₀' hQ hQ'
  have mP₁ := mem_iff_of_rev eP₁
  have mP₂ := mem_iff_of_rev eP₂
  have mQ₁ := mem_iff_of_rev eQ₁
  have mQ₂ := mem_iff_of_rev eQ₂
  have hVP₁ : ∀ v ∈ P₁, v ∈ stripVertices (S i) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)
  have hVP₂ : ∀ v ∈ P₂, v ∈ stripVertices (S i') := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ v).mp hv)
  have hVQ₁ : ∀ v ∈ Q₁, v ∈ stripVertices (T j) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hQ ((mQ₁ v).mp hv)
  have hVQ₂ : ∀ v ∈ Q₂, v ∈ stripVertices (T j') := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hQ' ((mQ₂ v).mp hv)
  have hLP₁ : ∀ v ∈ P₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hVP₁ v hv⟩)
  have hLP₂ : ∀ v ∈ P₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i', hVP₂ v hv⟩)
  have hLQ₁ : ∀ v ∈ Q₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j, hVQ₁ v hv⟩)
  have hLQ₂ : ∀ v ∈ Q₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨j', hVQ₂ v hv⟩)
  -- the two strips of the knot cannot both carry attachments of `F`
  have attS : ∀ (k : Fin m) (v : V), v ∈ stripVertices (S k) → (∃ f ∈ F, Gx.Adj v f) →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S k)).Nonempty := by
    rintro k v hv ⟨f, hf, hadj⟩
    exact ⟨v, ⟨Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hv⟩), f, hf, hadj⟩, hv⟩
  have key2 : ∀ v ∈ P₁, ∀ w ∈ P₂, (∃ f ∈ F, Gx.Adj v f) → (∃ f ∈ F, Gx.Adj w f) → False := by
    intro v hv w hw h1 h2
    exact hii' (hone i i' (attS i v (hVP₁ v hv) h1) (attS i' w (hVP₂ w hw) h2))
  set K : Set V :=
    {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} with hKdef
  have hFK : F ⊆ Kᶜ := by
    intro f hf hfK
    refine hFsub hf ?_
    rcases hfK with ((hv | hv) | hv) | hv
    · exact hLP₁ f hv
    · exact hLP₂ f hv
    · exact hLQ₁ f hv
    · exact hLQ₂ f hv
  have hQ₁att : ∀ v ∈ Q₁, v ∈ attachments Gx F K := by
    intro v hv
    obtain ⟨f, hf, hadj⟩ := hQall v ((mQ₁ v).mp hv)
    exact ⟨Or.inl (Or.inr hv), f, hf, hadj⟩
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂ (attachments Gx F K) := by
    rintro ⟨-, hnQ₁, -, -⟩
    exact hnQ₁ hQ₁att
  obtain ⟨a₁, b₁, a₂, b₂, x₁, y₁, x₂, y₂, hp₁, hp₂, hq₁, hq₂,
    d12, d1q1, d1q2, d2q1, d2q2, dqq, l1, l2, l3, l4, hantiP, hcompQ,
    E11, E12, E21, E22, N11, N12, N21, N22⟩ := id hknot
  obtain ⟨ha₁P, hb₁P⟩ := PathBasics.isPathFrom_ends_mem hp₁
  obtain ⟨ha₂P, hb₂P⟩ := PathBasics.isPathFrom_ends_mem hp₂
  obtain ⟨hx₁Q, hy₁Q⟩ := PathBasics.isPathFrom_ends_mem hq₁
  obtain ⟨hx₂Q, hy₂Q⟩ := PathBasics.isPathFrom_ends_mem hq₂
  have hab₁ : a₁ ≠ b₁ := PathBasics.isPathFrom_ends_ne hp₁ l1
  have hab₂ : a₂ ≠ b₂ := PathBasics.isPathFrom_ends_ne hp₂ l2
  have hxy₁ : x₁ ≠ y₁ := PathBasics.isPathFrom_ends_ne hq₁ l3
  have hxy₂ : x₂ ≠ y₂ := PathBasics.isPathFrom_ends_ne hq₂ l4
  have ax1a1 : Gx.Adj x₁ a₁ := adj_end hab₁ hxy₁ hx₁Q N11
  have ay1b1 : Gx.Adj y₁ b₁ := adj_end hab₁.symm hxy₁.symm hy₁Q (swap_N N11)
  have ax1a2 : Gx.Adj x₁ a₂ := adj_end hab₂ hxy₁ hx₁Q N21
  have ay1b2 : Gx.Adj y₁ b₂ := adj_end hab₂.symm hxy₁.symm hy₁Q (swap_N N21)
  have ax2a1 : Gx.Adj x₂ a₁ := adj_end hab₁ hxy₂ hx₂Q N12
  have ay2b1 : Gx.Adj y₂ b₁ := adj_end hab₁.symm hxy₂.symm hy₂Q (swap_N N12)
  have ay2a2 : Gx.Adj y₂ a₂ := adj_end hab₂ hxy₂.symm hy₂Q N22
  have ax2b2 : Gx.Adj x₂ b₂ := adj_end hab₂.symm hxy₂ hx₂Q (swap_N N22)
  -- the ends of the knot's first path are the ends of the chosen rung
  have hends : (a₁ = a ∧ b₁ = b) ∨ (a₁ = b ∧ b₁ = a) := by
    rcases eP₁ with rfl | rfl
    · exact Or.inl (end_eq_of_same_path hp₁ hP₀ab)
    · exact Or.inr (end_eq_of_same_path hp₁ (PathBasics.isPathFrom_reverse hP₀ab))
  -- outcome 9.3.2 is impossible: this is the `X ⊇ V(Q₁)` argument of the paper
  have out2 : ∀ (c d e : V) (P P' R : List V) (r₁ r₂ : V),
      e ∈ P → c ∈ Q₁ → d ∈ Q₁ → Gx.Adj e c → ¬ Gx.Adj e d →
      (∀ z ∈ P, z ≠ e → ¬ Gx.Adj z c) →
      (∀ z ∈ P, z ∈ ⋃ k : Fin m, stripVertices (S k)) →
      IsPathFrom Gx R r₁ r₂ → (∀ z ∈ R, z ∈ F) →
      (∀ z ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (Gx.Adj r₁ z ↔ Gx.Adj e z)) →
      Anticomplete Gx ({v : V | v ∈ R} \ {r₁})
        ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) →
      (∃ z ∈ ({v : V | v ∈ P} \ {e} : Set V), Gx.Adj r₂ z) → False := by
    intro c d e P P' R r₁ r₂ heP hcQ hdQ hec hned honly hPS hR hRF hcopy hantic hwit
    obtain ⟨w, ⟨hwP, hwe⟩, hr₂w⟩ := hwit
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have hRcand : ConnectedSet Gx {z : V | z ∈ R} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1
    have hcatt : c ∈ attachments Gx {z : V | z ∈ R} (striationVertices S T) :=
      ⟨hLQ₁ c hcQ, r₁, hr₁R, ((hcopy c (Or.inl (Or.inr hcQ))).mpr hec).symm⟩
    have hwatt : w ∈ attachments Gx {z : V | z ∈ R} (striationVertices S T) :=
      ⟨Set.mem_union_left _ (hPS w hwP), r₂, hr₂R, hr₂w.symm⟩
    have heq : {z : V | z ∈ R} = F := by
      refine hminEq _ hRF hRcand ?_
      rintro ⟨-, -, hcomplete⟩
      exact honly w hwP hwe
        (hcomplete w ⟨hwatt, hPS w hwP⟩ c ⟨hcatt, Set.mem_iUnion.mpr ⟨j, hVQ₁ c hcQ⟩⟩)
    obtain ⟨f, hfF, hdf⟩ := hQall d ((mQ₁ d).mp hdQ)
    have hfR : f ∈ R := by
      have : f ∈ {z : V | z ∈ R} := by rw [heq]; exact hfF
      exact this
    have hfr₁ : f = r₁ := by
      by_contra hne
      exact hantic f ⟨hfR, hne⟩ d (Or.inl (Or.inr hdQ)) hdf.symm
    exact hned ((hcopy d (Or.inl (Or.inr hdQ))).mp (hfr₁ ▸ hdf.symm))
  have h93 := Workspace.Statements.S09.SPGT.thm_9_3 Gx hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂ K rfl hnoenl hnoover
    hnoovercompl F hFK hFconn hnl
  rcases h93 with h1 | h2 | h3 | h4
  · obtain ⟨f, hfF, -, ⟨v, ⟨hfv, -⟩, hvP⟩, ⟨w, ⟨hfw, -⟩, hwP⟩, -⟩ := h1
    exact (key2 v hvP w hwP ⟨f, hfF, hfv.symm⟩ ⟨f, hfF, hfw.symm⟩).elim
  · exfalso
    obtain ⟨e, P, P', hcase, R, r₁, r₂, hR, hRF, hcopy, hantic, hwit, -⟩ := h2
    have hPS₁ : ∀ z ∈ P₁, z ∈ ⋃ k : Fin m, stripVertices (S k) := fun z hz =>
      Set.mem_iUnion.mpr ⟨i, hVP₁ z hz⟩
    have hPS₂ : ∀ z ∈ P₂, z ∈ ⋃ k : Fin m, stripVertices (S k) := fun z hz =>
      Set.mem_iUnion.mpr ⟨i', hVP₂ z hz⟩
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact out2 x₁ y₁ e P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact ha₁P) hx₁Q hy₁Q
        (by rw [h.1]; exact ax1a1.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N11 y₁ hy₁Q a₁ (Set.mem_insert _ _)).mpr (Or.inl ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E11)
        (by rw [h.2.1]; exact hPS₁) hR hRF hcopy hantic hwit
    · exact out2 y₁ x₁ e P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact hb₁P) hy₁Q hx₁Q
        (by rw [h.1]; exact ay1b1.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N11 x₁ hx₁Q b₁ (Set.mem_insert_of_mem _ rfl)).mpr (Or.inr ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E11))
        (by rw [h.2.1]; exact hPS₁) hR hRF hcopy hantic hwit
    · exact out2 x₁ y₁ e P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact ha₂P) hx₁Q hy₁Q
        (by rw [h.1]; exact ax1a2.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N21 y₁ hy₁Q a₂ (Set.mem_insert _ _)).mpr (Or.inl ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁ E21)
        (by rw [h.2.1]; exact hPS₂) hR hRF hcopy hantic hwit
    · exact out2 y₁ x₁ e P P' R r₁ r₂
        (by rw [h.1, h.2.1]; exact hb₂P) hy₁Q hx₁Q
        (by rw [h.1]; exact ay1b2.symm)
        (by rw [h.1]; exact fun hadj =>
          ((N21 x₁ hx₁Q b₂ (Set.mem_insert_of_mem _ rfl)).mpr (Or.inr ⟨rfl, rfl⟩)) hadj.symm)
        (by rw [h.1, h.2.1]; exact edge_end hxy₁.symm (swap_E E21))
        (by rw [h.2.1]; exact hPS₂) hR hRF hcopy hantic hwit
  · -- 9.3.3, the good outcome
    obtain ⟨c, d, P, P', hcase, R, r₁, r₂, hR, hRF, hodd, hcopy₁, hcopy₂, hantiI, -⟩ := h3
    have hcover : ∀ z ∈ Q₁, Gx.Adj z c ∨ Gx.Adj z d := by
      rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
      · rw [h.1, h.2.1]; exact cover_ends hab₁ hxy₁ N11
      · rw [h.1, h.2.1]; exact cover_ends hab₁.symm hxy₁.symm (swap_N N11)
      · rw [h.1, h.2.1]; exact cover_ends hab₂ hxy₁ N21
      · rw [h.1, h.2.1]; exact cover_ends hab₂.symm hxy₁.symm (swap_N N21)
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have memQQ : ∀ (Pz : List V) (z : V),
        z ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V) →
        z ∈ ({v : V | v ∈ Pz} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
      intro Pz z hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr ((mQ₁ z).mpr hz))
      · exact Or.inr ((mQ₂ z).mpr hz)
    -- minimality: the path already has vertex set `F`
    have hRsetF : {z : V | z ∈ R} = F := by
      refine hminEq _ hRF
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1) ?_
      intro hloc
      obtain ⟨z, hzQ, hznot⟩ := hloc.2.1 j Q hQ
      refine hznot ⟨hLQ₁ z ((mQ₁ z).mpr hzQ), ?_⟩
      rcases hcover z ((mQ₁ z).mpr hzQ) with hadj | hadj
      · exact ⟨r₁, hr₁R, ((hcopy₁ z (Or.inl (Or.inr ((mQ₁ z).mpr hzQ)))).mpr hadj.symm).symm⟩
      · exact ⟨r₂, hr₂R, ((hcopy₂ z (Or.inl (Or.inr ((mQ₁ z).mpr hzQ)))).mpr hadj.symm).symm⟩
    -- the two cases with `P = P₂` contradict the fact that `u ∈ P₁` has a neighbour in `F`
    have hbadP₂ : ∀ e ∈ P₂, (∀ z ∈ P₁, Gx.Adj e z → False) := by
      intro e he z hz hadj
      exact hantiP z hz e he hadj.symm
    have finish : ∀ (c' d' : V) (R' : List V) (r s : V), IsPathFrom Gx R' r s →
        Odd (pathLength R') → {z : V | z ∈ R'} = F →
        (∀ z ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V),
          (Gx.Adj r z ↔ Gx.Adj c' z)) →
        (∀ z ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V),
          (Gx.Adj s z ↔ Gx.Adj d' z)) →
        Anticomplete Gx {v : V | v ∈ SPGT.interior R'}
          ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'}) →
        ((c' = a ∧ d' = b) ∨ (c' = b ∧ d' = a)) →
        ∃ (R₀ : List V) (r₀ s₀ : V), IsPathFrom Gx R₀ r₀ s₀ ∧ Odd (pathLength R₀) ∧
          {v : V | v ∈ R₀} = F ∧
          (∀ w ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V),
            (Gx.Adj r₀ w ↔ Gx.Adj a w)) ∧
          (∀ w ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V),
            (Gx.Adj s₀ w ↔ Gx.Adj b w)) ∧
          Anticomplete Gx {v : V | v ∈ SPGT.interior R₀}
            ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'}) := by
      rintro c' d' R' r s hR' hodd' hset hc hd hint (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨R', r, s, hR', hodd', hset, hc, hd, hint⟩
      · refine ⟨R'.reverse, s, r, PathBasics.isPathFrom_reverse hR', ?_, ?_, hd, hc, ?_⟩
        · rwa [PathBasics.pathLength_reverse]
        · rw [← hset]; ext z; exact List.mem_reverse
        · intro z hz
          exact hint z (PathBasics.mem_interior_reverse.mp hz)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · obtain ⟨e1, e2, e3, e4⟩ := h
      refine finish c d R r₁ r₂ hR hodd hRsetF
        (fun z hz => hcopy₁ z (memQQ P' z hz))
        (fun z hz => hcopy₂ z (memQQ P' z hz))
        (fun z hz w hw => hantiI z hz w (memQQ P' w hw)) ?_
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨e1.trans h1, e2.trans h2⟩
      · exact Or.inr ⟨e1.trans h1, e2.trans h2⟩
    · obtain ⟨e1, e2, e3, e4⟩ := h
      refine finish c d R r₁ r₂ hR hodd hRsetF
        (fun z hz => hcopy₁ z (memQQ P' z hz))
        (fun z hz => hcopy₂ z (memQQ P' z hz))
        (fun z hz w hw => hantiI z hz w (memQQ P' w hw)) ?_
      rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inr ⟨e1.trans h2, e2.trans h1⟩
      · exact Or.inl ⟨e1.trans h2, e2.trans h1⟩
    · exfalso
      obtain ⟨e1, e2, e3, e4⟩ := h
      rw [e4] at hcopy₁ hcopy₂ hantiI
      obtain ⟨f, hfF, huf⟩ := huX
      have hfR : f ∈ R := by
        have hmem : f ∈ {z : V | z ∈ R} := by rw [hRsetF]; exact hfF
        exact hmem
      have huP₁ : u ∈ P₁ := (mP₁ u).mpr huP
      have hcP₂ : c ∈ P₂ := e1 ▸ ha₂P
      have hdP₂ : d ∈ P₂ := e2 ▸ hb₂P
      by_cases hf1 : f = r₁
      · subst f
        exact hbadP₂ c hcP₂ u huP₁ ((hcopy₁ u (Or.inl (Or.inl huP₁))).mp huf.symm)
      · by_cases hf2 : f = r₂
        · subst f
          exact hbadP₂ d hdP₂ u huP₁ ((hcopy₂ u (Or.inl (Or.inl huP₁))).mp huf.symm)
        · exact hantiI f ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hfR, hf1, hf2⟩)
            u (Or.inl (Or.inl huP₁)) huf.symm
    · exfalso
      obtain ⟨e1, e2, e3, e4⟩ := h
      rw [e4] at hcopy₁ hcopy₂ hantiI
      obtain ⟨f, hfF, huf⟩ := huX
      have hfR : f ∈ R := by
        have hmem : f ∈ {z : V | z ∈ R} := by rw [hRsetF]; exact hfF
        exact hmem
      have huP₁ : u ∈ P₁ := (mP₁ u).mpr huP
      have hcP₂ : c ∈ P₂ := e1 ▸ hb₂P
      have hdP₂ : d ∈ P₂ := e2 ▸ ha₂P
      by_cases hf1 : f = r₁
      · subst f
        exact hbadP₂ c hcP₂ u huP₁ ((hcopy₁ u (Or.inl (Or.inl huP₁))).mp huf.symm)
      · by_cases hf2 : f = r₂
        · subst f
          exact hbadP₂ d hdP₂ u huP₁ ((hcopy₂ u (Or.inl (Or.inl huP₁))).mp huf.symm)
        · exact hantiI f ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hfR, hf1, hf2⟩)
            u (Or.inl (Or.inl huP₁)) huf.symm
  · exfalso
    obtain ⟨x, y, Qo, hcase, f, hfF, hcopy, -⟩ := h4
    have step : ∀ v ∈ P₁, ∀ w ∈ P₂, Gx.Adj x v → Gx.Adj x w → False := by
      intro v hv w hw hxv hxw
      exact key2 v hv w hw
        ⟨f, hfF, ((hcopy v (Or.inl (Or.inl hv))).mpr hxv).symm⟩
        ⟨f, hfF, ((hcopy w (Or.inl (Or.inr hw))).mpr hxw).symm⟩
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact step a₁ ha₁P a₂ ha₂P (by rw [h.1]; exact ax1a1) (by rw [h.1]; exact ax1a2)
    · exact step b₁ hb₁P b₂ hb₂P (by rw [h.1]; exact ay1b1) (by rw [h.1]; exact ay1b2)
    · exact step a₁ ha₁P b₂ hb₂P (by rw [h.1]; exact ax2a1) (by rw [h.1]; exact ax2b2)
    · exact step b₁ hb₁P a₂ ha₂P (by rw [h.1]; exact ay2b1) (by rw [h.1]; exact ay2a2)

end Workspace.ProofLemmas.Thm95Claim3Step
