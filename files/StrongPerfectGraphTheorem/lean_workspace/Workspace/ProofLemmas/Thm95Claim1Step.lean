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
# One application of 9.3 inside claim (1) of 9.5

PAPER (9.5(1), printed p. 52): *"Let `2 ≤ j ≤ n`, and let `xⱼ-Qⱼ-yⱼ` be a `Tⱼ`-antirung.  Then
we can choose some `Sᵢ, Sᵢ'` to make a twist, and if we choose an `Sᵢ`-rung and `Sᵢ'`-rung and
apply 9.3 to the resultant knot, we deduce (since no vertices of `Sᵢ` and `Sᵢ'` are in `X`)
that 9.3.3 holds.  This has several consequences.  First, it implies that there is an odd path
in `F` with vertices `f₁, …, f_k` say, which is either parallel or co-parallel to `Q₁`, and
either parallel or co-parallel to `Qⱼ`; and there are no edges between `{f₂,…,f_{k-1}}` and
`Q₁ ∪ Qⱼ`.  Hence the set of attachments of `{f₁,…,f_k}` is not local with respect to `L`, and
so `F = {f₁,…,f_k}` from the minimality of `F`."*

The paper's *"either parallel or co-parallel"* is here the strip `Sx` returned below: it is one
of the two strips of the twist, possibly reversed, and the two ends `c, d` of one of its rungs
are exactly what the two ends of `F` copy on the two antirungs.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95Claim1Step

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.5(1)):** 9.3 applied to the knot made from a twist and two antirungs, when `F`
has no neighbour on any strip.  Only 9.3.3 survives, and minimality turns its path into `F`. -/
theorem claim1_step {Gx : SimpleGraph V} {m n : ℕ}
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
    (i : Fin m) {jb jt : Fin n} (hbt : jb ≠ jt)
    {Qb Qt : List V} (hQb : IsSRung Gxᶜ (T jb) Qb) (hQt : IsSRung Gxᶜ (T jt) Qt)
    (hQball : ∀ v ∈ Qb, ∃ f ∈ F, Gx.Adj v f) :
    ∃ (Sx : Set V × Set V × Set V) (c d : V) (R : List V) (r₁ r₂ : V),
      c ∈ Sx.1 ∧ d ∈ Sx.2.2 ∧
      (∀ kk : Fin n, ParallelStripAntistrip Gx Sx (T kk) ∨ CoParallel Gx Sx (T kk)) ∧
      IsPathFrom Gx R r₁ r₂ ∧ Odd (pathLength R) ∧ {v : V | v ∈ R} = F ∧
      (∀ z ∈ ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt} : Set V), (Gx.Adj r₁ z ↔ Gx.Adj c z)) ∧
      (∀ z ∈ ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt} : Set V), (Gx.Adj r₂ z ↔ Gx.Adj d z)) ∧
      Anticomplete Gx {v : V | v ∈ SPGT.interior R}
        ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt}) := by
  classical
  obtain ⟨i', hii', htw⟩ := Thm94ClosingStriation.exists_twist_with_fixed_strip hL i hbt
  obtain ⟨P₀, hP₀⟩ := exists_rung (hL.1 i)
  obtain ⟨P₀', hP₀'⟩ := exists_rung (hL.1 i')
  obtain ⟨P₁, P₂, Q₁, Q₂, eP₁, eP₂, eQ₁, eQ₂, hknot⟩ :=
    KnotFromTwist.exists_knot_of_twist hL hii' hbt htw hP₀ hP₀' hQb hQt
  have mP₁ := mem_iff_of_rev eP₁
  have mP₂ := mem_iff_of_rev eP₂
  have mQ₁ := mem_iff_of_rev eQ₁
  have mQ₂ := mem_iff_of_rev eQ₂
  have hVP₁ : ∀ v ∈ P₁, v ∈ stripVertices (S i) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀ ((mP₁ v).mp hv)
  have hVP₂ : ∀ v ∈ P₂, v ∈ stripVertices (S i') := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hP₀' ((mP₂ v).mp hv)
  have hVQ₁ : ∀ v ∈ Q₁, v ∈ stripVertices (T jb) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hQb ((mQ₁ v).mp hv)
  have hVQ₂ : ∀ v ∈ Q₂, v ∈ stripVertices (T jt) := fun v hv =>
    KnotFromTwist.mem_stripVertices_of_isSRung hQt ((mQ₂ v).mp hv)
  have hLP₁ : ∀ v ∈ P₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i, hVP₁ v hv⟩)
  have hLP₂ : ∀ v ∈ P₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨i', hVP₂ v hv⟩)
  have hLQ₁ : ∀ v ∈ Q₁, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨jb, hVQ₁ v hv⟩)
  have hLQ₂ : ∀ v ∈ Q₂, v ∈ striationVertices S T := fun v hv =>
    Set.mem_union_right _ (Set.mem_iUnion.mpr ⟨jt, hVQ₂ v hv⟩)
  have hnoP₁ : ∀ v ∈ P₁, ∀ f ∈ F, ¬ Gx.Adj v f := fun v hv f hf hadj =>
    hno i f hf v (hVP₁ v hv) hadj.symm
  have hnoP₂ : ∀ v ∈ P₂, ∀ f ∈ F, ¬ Gx.Adj v f := fun v hv f hf hadj =>
    hno i' f hf v (hVP₂ v hv) hadj.symm
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
  -- the knot's attachment set is not local: the whole of `Q₁` attaches to `F` by 9.1
  have hQ₁cov : ∀ z ∈ Q₁, Gx.Adj z a₁ ∨ Gx.Adj z b₁ := cover_ends hab₁ hxy₁ N11
  -- the strip carrying a given end of a knot path, up to reversal
  have mkStrip : ∀ (i₀ : Fin m) (Pb Pz : List V) (c d : V), IsSRung Gx (S i₀) Pb →
      (Pz = Pb ∨ Pz = Pb.reverse) → IsPathFrom Gx Pz c d →
      ∃ Sx : Set V × Set V × Set V, c ∈ Sx.1 ∧ d ∈ Sx.2.2 ∧
        ∀ kk : Fin n, ParallelStripAntistrip Gx Sx (T kk) ∨ CoParallel Gx Sx (T kk) := by
    intro i₀ Pb Pz c d hPb hrev hcd
    rcases hrev with rfl | rfl
    · exact ⟨S i₀, (srung_ends hPb hcd).1, (srung_ends hPb hcd).2,
        fun kk => hL.2.2.2.2.2.2.2.2.2.2.2.1 i₀ kk⟩
    · have h2 := KnotFromTwist.isSRung_reverse hPb
      refine ⟨reverseStrip (S i₀), (srung_ends h2 hcd).1, (srung_ends h2 hcd).2, fun kk => ?_⟩
      rcases hL.2.2.2.2.2.2.2.2.2.2.2.1 i₀ kk with h | h
      · exact Or.inr ((KnotFromTwist.coParallel_reverseStrip_left _ _).mpr h)
      · exact Or.inl ((KnotFromTwist.parallel_reverseStrip_left _ _).mpr h)
  have revcase : ∀ (Pb Pz : List V), (Pz = Pb ∨ Pz = Pb.reverse) →
      (Pz.reverse = Pb ∨ Pz.reverse = Pb.reverse) := by
    rintro Pb Pz (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (List.reverse_reverse Pb)
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂ (attachments Gx F K) := by
    rintro ⟨-, hnQ₁, -, -⟩
    refine hnQ₁ (fun z hz => ?_)
    obtain ⟨f, hf, hadj⟩ := hQball z ((mQ₁ z).mp hz)
    exact ⟨Or.inl (Or.inr hz), f, hf, hadj⟩
  have h93 := Workspace.Statements.S09.SPGT.thm_9_3 Gx hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂ K rfl hnoenl hnoover
    hnoovercompl F hFK hFconn hnl
  rcases h93 with h1 | h2 | h3 | h4
  · exfalso
    obtain ⟨f, hfF, -, ⟨v, ⟨hfv, -⟩, hvP⟩, -, -⟩ := h1
    exact hnoP₁ v hvP f hfF hfv.symm
  · exfalso
    obtain ⟨e, P, P', hcase, R, r₁, r₂, hR, hRF, -, -, hwit, -⟩ := h2
    obtain ⟨z, ⟨hzP, -⟩, hr₂z⟩ := hwit
    have hr₂F : r₂ ∈ F := hRF r₂ (PathBasics.getLast_mem hR.2.2)
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨e1, e2, e3⟩ := h
    · exact hnoP₁ z (by rw [← e2]; exact hzP) r₂ hr₂F hr₂z.symm
    · exact hnoP₁ z (by rw [← e2]; exact hzP) r₂ hr₂F hr₂z.symm
    · exact hnoP₂ z (by rw [← e2]; exact hzP) r₂ hr₂F hr₂z.symm
    · exact hnoP₂ z (by rw [← e2]; exact hzP) r₂ hr₂F hr₂z.symm
  · -- 9.3.3, the only surviving outcome
    obtain ⟨c, d, P, P', hcase, R, r₁, r₂, hR, hRF, hodd, hcopy₁, hcopy₂, hantiI, -⟩ := h3
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have hcover : ∀ z ∈ Q₁, Gx.Adj z c ∨ Gx.Adj z d := by
      rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
      · rw [h.1, h.2.1]; exact cover_ends hab₁ hxy₁ N11
      · rw [h.1, h.2.1]; exact cover_ends hab₁.symm hxy₁.symm (swap_N N11)
      · rw [h.1, h.2.1]; exact cover_ends hab₂ hxy₁ N21
      · rw [h.1, h.2.1]; exact cover_ends hab₂.symm hxy₁.symm (swap_N N21)
    have hRsetF : {z : V | z ∈ R} = F := by
      refine hminEq _ hRF
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1) ?_
      intro hloc
      obtain ⟨z, hzQ, hznot⟩ := hloc.2.1 jb Qb hQb
      refine hznot ⟨hLQ₁ z ((mQ₁ z).mpr hzQ), ?_⟩
      rcases hcover z ((mQ₁ z).mpr hzQ) with hadj | hadj
      · exact ⟨r₁, hr₁R, ((hcopy₁ z (Or.inl (Or.inr ((mQ₁ z).mpr hzQ)))).mpr hadj.symm).symm⟩
      · exact ⟨r₂, hr₂R, ((hcopy₂ z (Or.inl (Or.inr ((mQ₁ z).mpr hzQ)))).mpr hadj.symm).symm⟩
    have memQQ : ∀ (Pz : List V) (z : V),
        z ∈ ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt} : Set V) →
        z ∈ ({v : V | v ∈ Pz} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
      intro Pz z hz
      rcases hz with hz | hz
      · exact Or.inl (Or.inr ((mQ₁ z).mpr hz))
      · exact Or.inr ((mQ₂ z).mpr hz)
    have hfinish : ∀ Sx : Set V × Set V × Set V, c ∈ Sx.1 → d ∈ Sx.2.2 →
        (∀ kk : Fin n, ParallelStripAntistrip Gx Sx (T kk) ∨ CoParallel Gx Sx (T kk)) →
        ∃ (Sy : Set V × Set V × Set V) (c' d' : V) (R' : List V) (r' s' : V),
          c' ∈ Sy.1 ∧ d' ∈ Sy.2.2 ∧
          (∀ kk : Fin n, ParallelStripAntistrip Gx Sy (T kk) ∨ CoParallel Gx Sy (T kk)) ∧
          IsPathFrom Gx R' r' s' ∧ Odd (pathLength R') ∧ {v : V | v ∈ R'} = F ∧
          (∀ z ∈ ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt} : Set V),
            (Gx.Adj r' z ↔ Gx.Adj c' z)) ∧
          (∀ z ∈ ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt} : Set V),
            (Gx.Adj s' z ↔ Gx.Adj d' z)) ∧
          Anticomplete Gx {v : V | v ∈ SPGT.interior R'}
            ({v : V | v ∈ Qb} ∪ {v : V | v ∈ Qt}) := by
      intro Sx hc hd hpar
      exact ⟨Sx, c, d, R, r₁, r₂, hc, hd, hpar, hR, hodd, hRsetF,
        fun z hz => hcopy₁ z (memQQ P' z hz), fun z hz => hcopy₂ z (memQQ P' z hz),
        fun v hv z hz => hantiI v hv z (memQQ P' z hz)⟩
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨e1, e2, e3, e4⟩ := h
    · obtain ⟨Sx, hc, hd, hpar⟩ := mkStrip i P₀ P₁ a₁ b₁ hP₀ eP₁ hp₁
      exact hfinish Sx (by rw [e1]; exact hc) (by rw [e2]; exact hd) hpar
    · obtain ⟨Sx, hc, hd, hpar⟩ :=
        mkStrip i P₀ P₁.reverse b₁ a₁ hP₀ (revcase P₀ P₁ eP₁)
          (PathBasics.isPathFrom_reverse hp₁)
      exact hfinish Sx (by rw [e1]; exact hc) (by rw [e2]; exact hd) hpar
    · obtain ⟨Sx, hc, hd, hpar⟩ := mkStrip i' P₀' P₂ a₂ b₂ hP₀' eP₂ hp₂
      exact hfinish Sx (by rw [e1]; exact hc) (by rw [e2]; exact hd) hpar
    · obtain ⟨Sx, hc, hd, hpar⟩ :=
        mkStrip i' P₀' P₂.reverse b₂ a₂ hP₀' (revcase P₀' P₂ eP₂)
          (PathBasics.isPathFrom_reverse hp₂)
      exact hfinish Sx (by rw [e1]; exact hc) (by rw [e2]; exact hd) hpar
  · exfalso
    obtain ⟨x, y, Qo, hcase, f, hfF, hcopy, -⟩ := h4
    have step : ∀ v ∈ P₁, Gx.Adj x v → False := fun v hv hxv =>
      hnoP₁ v hv f hfF ((hcopy v (Or.inl (Or.inl hv))).mpr hxv).symm
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
    · exact step a₁ ha₁P (by rw [h.1]; exact ax1a1)
    · exact step b₁ hb₁P (by rw [h.1]; exact ay1b1)
    · exact step a₁ ha₁P (by rw [h.1]; exact ax2a1)
    · exact step b₁ hb₁P (by rw [h.1]; exact ay2b1)

end Workspace.ProofLemmas.Thm95Claim1Step
