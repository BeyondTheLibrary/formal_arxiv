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
# One application of 9.3 in the closing paragraph of 9.5

PAPER (9.5, printed p. 53): *"Let `2 ≤ j ≤ n`, and choose `i` with `2 ≤ i ≤ m` such that
`(S₁, Sᵢ, T₁, Tⱼ)` is a twist.  Let `Pᵢ` be an `Sᵢ`-rung, and let `Qⱼ` be a `Tⱼ`-antirung.  So
`(P₁, Pᵢ, Q₁, Qⱼ)` is a knot `K` say, and `X ∩ V(K)` is not local with respect to `K`.  Let us
apply 9.3; we deduce that one of the outcomes of 9.3 holds.  The first and fourth outcomes
contradict (2), and the third contradicts (3), so there is a path with vertex set in `F`
satisfying 9.3.2.  From the minimality of `F`, it follows that this path has vertex set `F`."*

The repetition over all antirungs is `Thm95ClosingPropagate`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm95ClosingStep

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95GapBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (closing paragraph of 9.5):** one application of 9.3 to the knot
`(P₁, Pᵢ, Q₁, Qⱼ)`.

`a, b` are the ends of the chosen `S i`-rung `P₀`; `u ∈ P₀` and `w ∈ Q` are nonadjacent
attachments of `F`, which is what makes `X ∩ V(K)` non-local.  The conclusion is 9.3.2 with
its path already identified with `F`: one end `c` of the rung is copied on both antirungs by
one end of `F`, and the other end of `F` has a neighbour on the rung. -/
theorem closing_step {Gx : SimpleGraph V} {m n : ℕ}
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
    {i : Fin m} {j j' : Fin n} (hjj' : j ≠ j')
    {P₀ Q Q' : List V} {a b u w : V}
    (hP₀ : IsSRung Gx (S i) P₀) (hP₀ab : IsPathFrom Gx P₀ a b)
    (hQ : IsSRung Gxᶜ (T j) Q) (hQ' : IsSRung Gxᶜ (T j') Q')
    (huP : u ∈ P₀) (huX : ∃ f ∈ F, Gx.Adj u f)
    (hwQ : w ∈ Q) (hwX : ∃ f ∈ F, Gx.Adj w f) (huw : ¬ Gx.Adj u w) :
    ∃ (c : V) (R : List V) (r s : V), (c = a ∨ c = b) ∧
      IsPathFrom Gx R r s ∧ {v : V | v ∈ R} = F ∧
      (∀ z ∈ ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'} : Set V), (Gx.Adj r z ↔ Gx.Adj c z)) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {r}) ({v : V | v ∈ Q} ∪ {v : V | v ∈ Q'}) ∧
      (∃ z ∈ ({v : V | v ∈ P₀} \ {c} : Set V), Gx.Adj s z) ∧
      Anticomplete Gx ({v : V | v ∈ R} \ {s}) ({v : V | v ∈ P₀} \ {c}) := by
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
  have attS : ∀ (k : Fin m) (v : V), v ∈ stripVertices (S k) → (∃ f ∈ F, Gx.Adj v f) →
      (attachments Gx F (striationVertices S T) ∩ stripVertices (S k)).Nonempty := by
    rintro k v hv ⟨f, hf, hadj⟩
    exact ⟨v, ⟨Set.mem_union_left _ (Set.mem_iUnion.mpr ⟨k, hv⟩), f, hf, hadj⟩, hv⟩
  have hnoP₂ : ∀ v ∈ P₂, ¬ ∃ f ∈ F, Gx.Adj v f := by
    intro v hv hex
    exact hii' (hone i i' (attS i u (hVP₁ u ((mP₁ u).mpr huP)) huX) (attS i' v (hVP₂ v hv) hex))
  -- the two antirungs are not swallowed by the attachment set
  have hnQ₁ : ∃ z ∈ Q₁, ¬ ∃ f ∈ F, Gx.Adj z f := by
    obtain ⟨z, hz, hzn⟩ := hanti j Q hQ
    exact ⟨z, (mQ₁ z).mpr hz, hzn⟩
  have hnQ₂ : ∃ z ∈ Q₂, ¬ ∃ f ∈ F, Gx.Adj z f := by
    obtain ⟨z, hz, hzn⟩ := hanti j' Q' hQ'
    exact ⟨z, (mQ₂ z).mpr hz, hzn⟩
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
  have huK : u ∈ attachments Gx F K := by
    obtain ⟨f, hf, hadj⟩ := huX
    exact ⟨Or.inl (Or.inl (Or.inl ((mP₁ u).mpr huP))), f, hf, hadj⟩
  have hwK : w ∈ attachments Gx F K := by
    obtain ⟨f, hf, hadj⟩ := hwX
    exact ⟨Or.inl (Or.inr ((mQ₁ w).mpr hwQ)), f, hf, hadj⟩
  have hnl : ¬ LocalForKnot Gx P₁ P₂ Q₁ Q₂ (attachments Gx F K) := by
    rintro ⟨-, -, -, hcomplete⟩
    exact huw (hcomplete u ⟨huK, Or.inl ((mP₁ u).mpr huP)⟩ w
      ⟨hwK, Or.inl ((mQ₁ w).mpr hwQ)⟩)
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
  have hends : (a₁ = a ∧ b₁ = b) ∨ (a₁ = b ∧ b₁ = a) := by
    rcases eP₁ with rfl | rfl
    · exact Or.inl (end_eq_of_same_path hp₁ hP₀ab)
    · exact Or.inr (end_eq_of_same_path hp₁ (PathBasics.isPathFrom_reverse hP₀ab))
  have hPset : ∀ v : V, v ∈ ({v : V | v ∈ P₁} : Set V) ↔ v ∈ ({v : V | v ∈ P₀} : Set V) :=
    fun v => mP₁ v
  have h93 := Workspace.Statements.S09.SPGT.thm_9_3 Gx hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hp₁ hp₂ hq₁ hq₂ K rfl hnoenl hnoover
    hnoovercompl F hFK hFconn hnl
  rcases h93 with h1 | h2 | h3 | h4
  · exfalso
    obtain ⟨f, hfF, hres⟩ := h1
    rcases hres.1 with hsub | hsub
    · obtain ⟨z, hz, hzn⟩ := hnQ₁
      exact hzn ⟨f, hfF, ((hsub hz).1 : Gx.Adj f z).symm⟩
    · obtain ⟨z, hz, hzn⟩ := hnQ₂
      exact hzn ⟨f, hfF, ((hsub hz).1 : Gx.Adj f z).symm⟩
  · -- 9.3.2, the good outcome
    obtain ⟨e, P, P', hcase, R, r₁, r₂, hR, hRF, hcopy, hantic, hwit, hantic2⟩ := h2
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have hbadP₂ : ∀ (ee : V), ee ∈ P₂ →
        (∃ zz ∈ ({v : V | v ∈ P₂} \ {ee} : Set V), Gx.Adj r₂ zz) → False := by
      rintro ee hee ⟨zz, ⟨hzz, -⟩, hadj⟩
      exact hnoP₂ zz hzz ⟨r₂, hRF r₂ hr₂R, hadj.symm⟩
    -- only `P = P₁` survives
    have hgood : ∃ c : V, (c = a₁ ∨ c = b₁) ∧
        (∀ z ∈ ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
          (Gx.Adj r₁ z ↔ Gx.Adj c z)) ∧
        Anticomplete Gx ({v : V | v ∈ R} \ {r₁})
          ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}) ∧
        (∃ z ∈ ({v : V | v ∈ P₁} \ {c} : Set V), Gx.Adj r₂ z) ∧
        Anticomplete Gx ({v : V | v ∈ R} \ {r₂}) ({v : V | v ∈ P₁} \ {c}) := by
      rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
        obtain ⟨e1, e2, e3⟩ := h
      · rw [e2] at hwit hantic2
        rw [e3] at hcopy hantic
        exact ⟨e, Or.inl e1, hcopy, hantic, hwit, hantic2⟩
      · rw [e2] at hwit hantic2
        rw [e3] at hcopy hantic
        exact ⟨e, Or.inr e1, hcopy, hantic, hwit, hantic2⟩
      · exact absurd (hbadP₂ e (e1 ▸ ha₂P) (by rw [← e2]; exact hwit)) not_false
      · exact absurd (hbadP₂ e (e1 ▸ hb₂P) (by rw [← e2]; exact hwit)) not_false
    obtain ⟨c, hcab, hcopy, hantic, hwit, hantic2⟩ := hgood
    -- minimality: the path already has vertex set `F`
    obtain ⟨p, ⟨hpP₁, hpc⟩, hr₂p⟩ := hwit
    obtain ⟨z, hzQ₁, hcz, honly⟩ : ∃ z ∈ Q₁, Gx.Adj c z ∧ ∀ v ∈ P₁, v ≠ c → ¬ Gx.Adj v z := by
      rcases hcab with h | h
      · rw [h]; exact ⟨x₁, hx₁Q, ax1a1.symm, edge_end hxy₁ E11⟩
      · rw [h]; exact ⟨y₁, hy₁Q, ay1b1.symm, edge_end hxy₁.symm (swap_E E11)⟩
    have hRsetF : {v : V | v ∈ R} = F := by
      refine hminEq _ hRF
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hR.1) ?_
      rintro ⟨-, -, hcomplete⟩
      have hzatt : z ∈ attachments Gx {v : V | v ∈ R} (striationVertices S T) :=
        ⟨hLQ₁ z hzQ₁, r₁, hr₁R, ((hcopy z (Or.inl (Or.inr hzQ₁))).mpr hcz).symm⟩
      have hpatt : p ∈ attachments Gx {v : V | v ∈ R} (striationVertices S T) :=
        ⟨hLP₁ p hpP₁, r₂, hr₂R, hr₂p.symm⟩
      exact honly p hpP₁ hpc
        (hcomplete p ⟨hpatt, Set.mem_iUnion.mpr ⟨i, hVP₁ p hpP₁⟩⟩ z
          ⟨hzatt, Set.mem_iUnion.mpr ⟨j, hVQ₁ z hzQ₁⟩⟩)
    have hcab' : c = a ∨ c = b := by
      rcases hcab with h | h <;> rcases hends with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h1)
      · exact Or.inr (h.trans h2)
      · exact Or.inl (h.trans h2)
    refine ⟨c, R, r₁, r₂, hcab', hR, hRsetF, ?_, ?_, ?_, ?_⟩
    · intro zz hzz
      refine hcopy zz ?_
      rcases hzz with hzz | hzz
      · exact Or.inl (Or.inr ((mQ₁ zz).mpr hzz))
      · exact Or.inr ((mQ₂ zz).mpr hzz)
    · intro v hv zz hzz
      refine hantic v hv zz ?_
      rcases hzz with hzz | hzz
      · exact Or.inl (Or.inr ((mQ₁ zz).mpr hzz))
      · exact Or.inr ((mQ₂ zz).mpr hzz)
    · exact ⟨p, ⟨(mP₁ p).mp hpP₁, hpc⟩, hr₂p⟩
    · intro v hv zz hzz
      exact hantic2 v hv zz ⟨(mP₁ zz).mpr hzz.1, hzz.2⟩
  · exfalso
    obtain ⟨c, d, P, P', hcase, R, r₁, r₂, hR, hRF, hodd, hcopy₁, hcopy₂, -, -⟩ := h3
    obtain ⟨hr₁R, hr₂R⟩ := PathBasics.isPathFrom_ends_mem hR
    have hcover : ∀ z ∈ Q₁, Gx.Adj z c ∨ Gx.Adj z d := by
      rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h
      · rw [h.1, h.2.1]; exact cover_ends hab₁ hxy₁ N11
      · rw [h.1, h.2.1]; exact cover_ends hab₁.symm hxy₁.symm (swap_N N11)
      · rw [h.1, h.2.1]; exact cover_ends hab₂ hxy₁ N21
      · rw [h.1, h.2.1]; exact cover_ends hab₂.symm hxy₁.symm (swap_N N21)
    obtain ⟨zz, hzzQ, hzzn⟩ := hnQ₁
    rcases hcover zz hzzQ with hadj | hadj
    · exact hzzn ⟨r₁, hRF r₁ hr₁R,
        ((hcopy₁ zz (Or.inl (Or.inr hzzQ))).mpr hadj.symm).symm⟩
    · exact hzzn ⟨r₂, hRF r₂ hr₂R,
        ((hcopy₂ zz (Or.inl (Or.inr hzzQ))).mpr hadj.symm).symm⟩
  · exfalso
    obtain ⟨x, y, Qo, hcase, f, hfF, hcopy, -⟩ := h4
    rcases hcase with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨e1, e2, e3⟩ := h
    · obtain ⟨zz, hzz, hzzn⟩ := hnQ₂
      exact hzzn ⟨f, hfF, ((hcopy zz (by rw [e3]; exact Or.inr hzz)).mpr
        (hcompQ x (e1 ▸ hx₁Q) zz hzz)).symm⟩
    · obtain ⟨zz, hzz, hzzn⟩ := hnQ₂
      exact hzzn ⟨f, hfF, ((hcopy zz (by rw [e3]; exact Or.inr hzz)).mpr
        (hcompQ x (e1 ▸ hy₁Q) zz hzz)).symm⟩
    · obtain ⟨zz, hzz, hzzn⟩ := hnQ₁
      exact hzzn ⟨f, hfF, ((hcopy zz (by rw [e3]; exact Or.inr hzz)).mpr
        (hcompQ zz hzz x (e1 ▸ hx₂Q)).symm).symm⟩
    · obtain ⟨zz, hzz, hzzn⟩ := hnQ₁
      exact hzzn ⟨f, hfF, ((hcopy zz (by rw [e3]; exact Or.inr hzz)).mpr
        (hcompQ zz hzz x (e1 ▸ hy₂Q)).symm).symm⟩

end Workspace.ProofLemmas.Thm95ClosingStep
