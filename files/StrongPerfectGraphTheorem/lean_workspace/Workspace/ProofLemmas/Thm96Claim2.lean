import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.Thm96Assembly
import Workspace.ProofLemmas.LooseSkewPartition
import Workspace.Statements.S09.Thm_9_5
import Workspace.Statements.S04.Thm_4_2

/-!
# Claim (2) of 9.6, after the *"by taking complements"* reduction

PAPER (9.6, printed p. 54):

> *"(2) If `M, N` are both nonempty then the theorem holds.*
>
> *For let `M₁` be a component of `M`, and `N₁` an anticomponent of `N`.  **By taking
> complements we may assume that there is a nonedge between `M₁` and `N₁`.**  Since the set of
> attachments of `M₁` in `V(L)` is local by 9.5, and since it has no attachments in
> `V(T₁) ∪ ⋯ ∪ V(T_n)`, we may assume that all its attachments are in `V(S₁)`.  Let
> `V' = V(G) \ (M₁ ∪ N₁ ∪ V(S₁))`.  Since every vertex of `S₁` is `N₁`-complete, it follows
> that `(M₁ ∪ V', N₁ ∪ V(S₁))` is a skew partition of `G`, and since there are `N₁`-complete
> vertices with no neighbours in `M₁` (for instance, any vertex of `V(S₂)`), the skew partition
> is loose, and by 4.2 `G` admits a balanced skew partition.  This proves (2)."*

This module carries the two seams of that paragraph.

* `attachments_in_one_strip` — *"Since the set of attachments of `M₁` in `V(L)` is local by
  9.5, and since it has no attachments in `V(T₁) ∪ ⋯ ∪ V(T_n)`, we may assume that all its
  attachments are in `V(S₁)`."*  Proved here: 9.5 says the attachment set is local, the first
  bullet of *local* says at most one `V(Sᵢ)` meets it, and the *"`M` is anticomplete to
  `V(T₁) ∪ ⋯ ∪ V(T_n)`"* half of `Thm96Body.Balanced` says none of the `V(Tⱼ)` does.  (The
  paper's *"we may assume … `V(S₁)`"* is a relabelling of the strips; here the index is
  produced rather than normalised to `1`.)

* `claim2_core` — claim (2) **after** its opening *"by taking complements we may assume that
  there is a nonedge between `M₁` and `N₁`"*, i.e. with that nonedge as a hypothesis.  The
  reduction itself is carried out in `Workspace.ProofLemmas.Thm96Body.claim2`, which runs this
  lemma at `Gᶜ` (with the strips and antistrips, and hence `M` and `N`, exchanged) when `M₁` is
  complete to `N₁`.

The hypotheses are spelled out rather than bundled as `Thm96Body.Setup`/`Thm96Body.Balanced`,
because `Thm96Body` imports this module.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm96Claim2

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.6, printed p. 54, inside claim (2)).**

*"Since the set of attachments of `M₁` in `V(L)` is local by 9.5, and since it has no
attachments in `V(T₁) ∪ ⋯ ∪ V(T_n)`, we may assume that all its attachments are in `V(S₁)`."*

The paper's *"we may assume … `V(S₁)`"* renames the strips so that the distinguished one is the
first; here the index `i₀` is produced instead. -/
theorem attachments_in_one_strip {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V}
    (hG : Berge Gx)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gx.induce K'),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gxᶜ.induce K'),
      IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ)
    (hmax : MaximalStriation Gx S T)
    (hpart : M ∪ N = (striationVertices S T)ᶜ)
    (hMloc : ∀ v ∈ M, LocalForStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T))
    (hbal2 : ∀ f ∈ M, ∀ u ∈ (⋃ j : Fin n, stripVertices (T j)), ¬ Gx.Adj f u)
    {M₁ : Set V} (hM₁ : IsComponent Gx M M₁) :
    ∃ i₀ : Fin m, attachments Gx M₁ (striationVertices S T) ⊆ stripVertices (S i₀) := by
  classical
  -- `M₁ ⊆ M ⊆ V(G) \ V(L)`
  have hsub : M₁ ⊆ (striationVertices S T)ᶜ := by
    intro v hv
    have : v ∈ M ∪ N := Set.mem_union_left _ (hM₁.1 hv)
    exact hpart ▸ this
  -- PAPER: *"the set of attachments of `M₁` in `V(L)` is local by 9.5"*
  have hloc : LocalForStriation Gx S T (attachments Gx M₁ (striationVertices S T)) :=
    _root_.Workspace.Statements.S09.SPGT.thm_9_5 Gx hG hnoenl hnoover hnoovercompl m n S T hmax
      M₁ hsub hM₁.2.1 (fun f hf => hMloc f (hM₁.1 hf))
  -- PAPER: *"it has no attachments in `V(T₁) ∪ ⋯ ∪ V(T_n)`"*
  have hinS : attachments Gx M₁ (striationVertices S T) ⊆ (⋃ i : Fin m, stripVertices (S i)) := by
    rintro v ⟨hvL, f, hf, hadj⟩
    rcases hvL with h | h
    · exact h
    · exact absurd hadj.symm (hbal2 f (hM₁.1 hf) v h)
  by_cases hex : ∃ i : Fin m,
      (attachments Gx M₁ (striationVertices S T) ∩ stripVertices (S i)).Nonempty
  · obtain ⟨i₀, hi₀⟩ := hex
    refine ⟨i₀, fun v hv => ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hinS hv)
    have : i = i₀ := hloc.1 i i₀ ⟨v, hv, hi⟩ hi₀
    exact this ▸ hi
  · push_neg at hex
    have hm2 : 2 ≤ m := hmax.1.2.2.2.2.2.2.2.1
    refine ⟨⟨0, by omega⟩, fun v hv => ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hinS hv)
    have hmem := Set.mem_inter hv hi
    rw [hex i] at hmem
    exact hmem.elim

/-- Bookkeeping: a strip is nonempty, because its `A`-side is (`IsStrip`, printed p. 50). -/
private theorem stripVertices_nonempty {Gy : SimpleGraph V} {S₀ : Set V × Set V × Set V}
    (h : IsStrip Gy S₀) : (stripVertices S₀).Nonempty := by
  obtain ⟨Aa, Cc, Bb⟩ := S₀
  obtain ⟨a, ha⟩ := h.2.2.2.1
  exact ⟨a, Or.inl (Or.inl ha)⟩

/-- **PAPER (9.6, printed p. 54), claim (2) after its complement reduction.**

*"For let `M₁` be a component of `M`, and `N₁` an anticomponent of `N`.  By taking complements
we may assume that there is a nonedge between `M₁` and `N₁`.  Since the set of attachments of
`M₁` in `V(L)` is local by 9.5, and since it has no attachments in `V(T₁) ∪ ⋯ ∪ V(T_n)`, we may
assume that all its attachments are in `V(S₁)`.  Let `V' = V(G) \ (M₁ ∪ N₁ ∪ V(S₁))`.  Since
every vertex of `S₁` is `N₁`-complete, it follows that `(M₁ ∪ V', N₁ ∪ V(S₁))` is a skew
partition of `G`, and since there are `N₁`-complete vertices with no neighbours in `M₁` (for
instance, any vertex of `V(S₂)`), the skew partition is loose, and by 4.2 `G` admits a balanced
skew partition.  This proves (2)."*

The opening *"by taking complements we may assume that there is a nonedge between `M₁` and
`N₁`"* is the hypothesis `hnonedge`; the reduction to it is performed by
`Workspace.ProofLemmas.Thm96Body.claim2`. -/
theorem claim2_core {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V}
    {M N : Set V}
    (hG : Berge Gx)
    (hnoenl : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gx J' ∨ Appears Gxᶜ J'))
    (hnoover : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gx.induce K'),
      IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gx H K' φ)
    (hnoovercompl : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gxᶜ.induce K'),
      IsAppearance Gxᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gxᶜ H K' φ)
    (hmax : MaximalStriation Gx S T)
    (hpart : M ∪ N = (striationVertices S T)ᶜ)
    (hdisj : Disjoint M N)
    (hMloc : ∀ v ∈ M, LocalForStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T))
    (hNres : ∀ v ∈ N, ResolvesStriation Gx S T (Gx.neighborSet v ∩ striationVertices S T))
    (hbal1 : ∀ f ∈ N, ∀ u ∈ (⋃ i : Fin m, stripVertices (S i)), Gx.Adj f u)
    (hbal2 : ∀ f ∈ M, ∀ u ∈ (⋃ j : Fin n, stripVertices (T j)), ¬ Gx.Adj f u)
    {M₁ N₁ : Set V} (hM₁ : IsComponent Gx M M₁) (hN₁ : IsAnticomponent Gx N N₁)
    (hnonedge : ∃ u ∈ M₁, ∃ f ∈ N₁, ¬ Gx.Adj u f) :
    Thm96Assembly.Concl Gx := by
  classical
  -- PAPER: *"For let `M₁` be a component of `M`, and `N₁` an anticomponent of `N`."*  Claim (2)
  -- assumes `M, N` both nonempty; the nonedge exhibits a vertex of each of `M₁`, `N₁`.
  obtain ⟨u₀, hu₀, f₀, hf₀, -⟩ := hnonedge
  have hM₁ne : M₁.Nonempty := ⟨u₀, hu₀⟩
  have hN₁ne : N₁.Nonempty := ⟨f₀, hf₀⟩
  -- PAPER: *"we may assume that all its attachments are in `V(S₁)`."*
  obtain ⟨i₀, hi₀⟩ :=
    attachments_in_one_strip hG hnoenl hnoover hnoovercompl hmax hpart hMloc hbal2 hM₁
  -- PAPER: *"any vertex of `V(S₂)`"* — a second strip exists because `m ≥ 2`.
  have hm2 : 2 ≤ m := hmax.1.2.2.2.2.2.2.2.1
  have h0 : (0 : ℕ) < m := by omega
  have h1 : (1 : ℕ) < m := by omega
  obtain ⟨i₁, hi₁⟩ : ∃ i₁ : Fin m, i₁ ≠ i₀ := by
    by_cases h : i₀ = ⟨0, h0⟩
    · exact ⟨⟨1, h1⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, h0⟩, fun he => h he.symm⟩
  ------------------------------------------------------------------
  -- bookkeeping about `M`, `N` and `V(L)`
  ------------------------------------------------------------------
  have hMnotL : ∀ v : V, v ∈ M → v ∉ striationVertices S T := by
    intro v hv
    have hmem : v ∈ M ∪ N := Set.mem_union_left _ hv
    rw [hpart] at hmem
    exact hmem
  have hNnotL : ∀ v : V, v ∈ N → v ∉ striationVertices S T := by
    intro v hv
    have hmem : v ∈ M ∪ N := Set.mem_union_right _ hv
    rw [hpart] at hmem
    exact hmem
  have hcover : ∀ v : V, v ∈ striationVertices S T ∨ v ∈ M ∨ v ∈ N := by
    intro v
    by_cases hv : v ∈ striationVertices S T
    · exact Or.inl hv
    · have hmem : v ∈ (striationVertices S T)ᶜ := hv
      rw [← hpart] at hmem
      exact Or.inr hmem
  have hSiU : ∀ (i : Fin m), ∀ x ∈ stripVertices (S i),
      x ∈ (⋃ i : Fin m, stripVertices (S i)) := by
    intro i x hx
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  have hSsubL : ∀ (i : Fin m), ∀ x ∈ stripVertices (S i), x ∈ striationVertices S T := by
    intro i x hx
    exact Set.mem_union_left _ (hSiU i x hx)
  have hSdisj : Disjoint (stripVertices (S i₁)) (stripVertices (S i₀)) :=
    hmax.1.2.2.1 i₁ i₀ hi₁
  obtain ⟨w, hw⟩ : (stripVertices (S i₁)).Nonempty := stripVertices_nonempty (hmax.1.1 i₁)
  obtain ⟨s₀, hs₀⟩ : (stripVertices (S i₀)).Nonempty := stripVertices_nonempty (hmax.1.1 i₀)
  -- PAPER: *"every vertex of `S₁` is `N₁`-complete"* — indeed every vertex of every `V(Sᵢ)` is,
  -- because after claim (1) `N` is complete to `V(S₁) ∪ ⋯ ∪ V(S_m)`.
  have hScompl : ∀ (i : Fin m), ∀ x ∈ stripVertices (S i), VertexComplete Gx x N₁ := by
    intro i x hx f hf
    exact (hbal1 f (hN₁.1 hf) x (hSiU i x hx)).symm
  -- PAPER: *"there are `N₁`-complete vertices with no neighbours in `M₁` (for instance, any
  -- vertex of `V(S₂)`)"* — no vertex of `V(S₂)` is an attachment of `M₁`.
  have hnoattach : ∀ x ∈ stripVertices (S i₁), ∀ y ∈ M₁, ¬ Gx.Adj x y := by
    intro x hx y hy hadj
    have hatt : x ∈ attachments Gx M₁ (striationVertices S T) := ⟨hSsubL i₁ x hx, y, hy, hadj⟩
    exact Set.disjoint_left.mp hSdisj hx (hi₀ hatt)
  ------------------------------------------------------------------
  -- the cutset.  PAPER (arXiv text of the same paragraph): *"Let `X` be the set of all
  -- `N₁`-complete vertices in `G`"*; the printed `B`-side is `N₁ ∪ V(S₁)`, and — exactly as in
  -- claim (1), where the `B`-side is `N₁ ∪ X'` with `X'` the vertices of `X` having neighbours
  -- in `U` — the `N₁`-complete vertices with a neighbour in `M₁` are put in it as well, so that
  -- `M₁` really has all of its neighbours inside the cutset.
  ------------------------------------------------------------------
  set Cut : Set V :=
    N₁ ∪ (stripVertices (S i₀) ∪
      {x : V | x ∉ M₁ ∧ VertexComplete Gx x N₁ ∧ ∃ y ∈ M₁, Gx.Adj x y}) with hCut
  have hmem : ∀ x : V, x ∈ Cut ↔
      (x ∈ N₁ ∨ x ∈ stripVertices (S i₀) ∨
        (x ∉ M₁ ∧ VertexComplete Gx x N₁ ∧ ∃ y ∈ M₁, Gx.Adj x y)) := by
    intro x
    rw [hCut]
    simp only [Set.mem_union, Set.mem_setOf_eq]
  -- every vertex of the cutset outside `N₁` is `N₁`-complete
  have hCutC : ∀ x : V, x ∈ Cut → x ∉ N₁ → VertexComplete Gx x N₁ := by
    intro x hx hxN₁
    rcases (hmem x).mp hx with h | h | h
    · exact absurd h hxN₁
    · exact hScompl i₀ x h
    · exact h.2.1
  have hN₁sub : N₁ ⊆ Cut := fun x hx => (hmem x).mpr (Or.inl hx)
  have hCutsplit : Cut = N₁ ∪ (Cut \ N₁) := (Set.union_diff_cancel hN₁sub).symm
  have hCutanti : Anticomplete Gxᶜ N₁ (Cut \ N₁) := by
    intro x hx y hy hadj
    exact ((SimpleGraph.compl_adj Gx x y).mp hadj).2 ((hCutC y hy.1 hy.2) x hx).symm
  have hs₀Cut : s₀ ∈ Cut \ N₁ :=
    ⟨(hmem s₀).mpr (Or.inr (Or.inl hs₀)),
      fun h => hNnotL s₀ (hN₁.1 h) (hSsubL i₀ s₀ hs₀)⟩
  -- PAPER: *"Since every vertex of `S₁` is `N₁`-complete"* — the `B`-side is not anticonnected.
  have hBnotanti : ¬ AnticonnectedSet Gx Cut :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split hCutsplit hN₁ne
      ⟨s₀, hs₀Cut⟩ (Set.disjoint_left.mpr fun a ha hb => hb.2 ha) hCutanti
  ------------------------------------------------------------------
  -- the `A`-side, `M₁ ∪ V'`
  ------------------------------------------------------------------
  have hM₁subA : M₁ ⊆ Cutᶜ := by
    intro x hx hxCut
    rcases (hmem x).mp hxCut with h | h | h
    · exact Set.disjoint_left.mp hdisj (hM₁.1 hx) (hN₁.1 h)
    · exact hMnotL x (hM₁.1 hx) (hSsubL i₀ x h)
    · exact h.1 hx
  have hwA : w ∈ Cutᶜ := by
    intro hwCut
    rcases (hmem w).mp hwCut with h | h | h
    · exact hNnotL w (hN₁.1 h) (hSsubL i₁ w hw)
    · exact Set.disjoint_left.mp hSdisj hw h
    · obtain ⟨y, hy, hadj⟩ := h.2.2
      exact hnoattach w hw y hy hadj
  have hwM₁ : w ∉ M₁ := fun h => hMnotL w (hM₁.1 h) (hSsubL i₁ w hw)
  have hAsplit : Cutᶜ = M₁ ∪ (Cutᶜ \ M₁) := (Set.union_diff_cancel hM₁subA).symm
  -- `M₁` has all of its neighbours inside the cutset
  have hantiA : Anticomplete Gx M₁ (Cutᶜ \ M₁) := by
    intro x hx y hy hadj
    have hyCut : y ∉ Cut := hy.1
    rcases hcover y with hyL | hyM | hyN
    · -- an attachment of `M₁` in `V(L)`: it lies in `V(S₁)`
      have hatt : y ∈ attachments Gx M₁ (striationVertices S T) := ⟨hyL, x, hx, hadj.symm⟩
      exact hyCut ((hmem y).mpr (Or.inr (Or.inl (hi₀ hatt))))
    · -- another component of `M`: no edges between distinct components
      obtain ⟨D, hD, hyD⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gx M hyM
      have hne : M₁ ≠ D := fun he => hy.2 (he ▸ hyD)
      exact ComponentsOfSetBasics.anticomplete_of_isComponent Gx hM₁ hD hne x hx y hyD hadj
    · -- a vertex of `N`: either it is in `N₁`, or it is `N₁`-complete, so in the cutset
      by_cases hyN₁ : y ∈ N₁
      · exact hyCut ((hmem y).mpr (Or.inl hyN₁))
      · exact hyCut ((hmem y).mpr (Or.inr (Or.inr
          ⟨hy.2, LooseSkewPartition.vertexComplete_of_notMem_anticomponent hN₁ hyN hyN₁,
            x, hx, hadj.symm⟩)))
  have hAnotconn : ¬ ConnectedSet Gx Cutᶜ :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split hAsplit hM₁ne
      ⟨w, hwA, hwM₁⟩ (Set.disjoint_left.mpr fun a ha hb => hb.2 ha) hantiA
  -- PAPER: *"it follows that `(M₁ ∪ V', N₁ ∪ V(S₁))` is a skew partition of `G`"*
  have hskew : IsSkewPartition Gx Cutᶜ Cut :=
    ⟨Set.compl_union_self Cut, disjoint_compl_left, hAnotconn, hBnotanti⟩
  -- `N₁` is an anticomponent of the `B`-side
  have hN₁anticomp : IsAnticomponent Gx Cut N₁ :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.isComponent_of_split
      (_root_.Workspace.Statements.S04.SPGT.Helpers42.isComponent_self hN₁.2.1) hN₁ne
      hCutsplit hCutanti
  -- PAPER: *"since there are `N₁`-complete vertices with no neighbours in `M₁` (for instance,
  -- any vertex of `V(S₂)`), the skew partition is loose"*
  have hloose : IsLooseSkewPartition Gx Cutᶜ Cut :=
    ⟨hskew, Or.inr ⟨w, hwA, N₁, hN₁anticomp, hScompl i₁ w hw⟩⟩
  -- PAPER: *"and by 4.2 `G` admits a balanced skew partition.  This proves (2)."*
  exact Or.inr (Or.inl (_root_.Workspace.Statements.S04.SPGT.thm_4_2 Gx hG
    ⟨Cutᶜ, Cut, hloose⟩))

end Workspace.ProofLemmas.Thm96Claim2
