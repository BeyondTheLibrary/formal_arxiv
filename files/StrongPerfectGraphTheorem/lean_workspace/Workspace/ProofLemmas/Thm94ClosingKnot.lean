import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Overshadowed
import Workspace.Types.Knots
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S09.Thm_9_3

/-!
# The singleton use of 9.3 in the closing paragraph of 9.4

The closing paragraph applies 9.3 with `F = {f}`.  The lemma below removes the three unwanted
outcomes and records the useful part of outcome 9.3.2.  It does not choose an orientation of the
first path: the copied end may be either end.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm94ClosingKnot

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **PAPER (9.4, printed pp. 51--52):** *"By 9.3, it follows that 9.3.2 holds."*

Here `F = {f}`.  A nonedge between two attachments, one on `P₁` and one on `Q₁`, makes the
attachment set non-local.  A nonneighbour of `f` on each antipath rules out 9.3.1 and 9.3.4,
while the absence of neighbours on `P₂` forces the path in 9.3.2 to be `P₁`. -/
theorem singleton_forces_end_copy {G : SimpleGraph V}
    (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ f : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance G H K' φ)
    (hnoovercompl : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (hfK : f ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪
      {v : V | v ∈ Q₂} : Set V))
    (hbad : ∃ p ∈ P₁, ∃ q ∈ Q₁, G.Adj f p ∧ G.Adj f q ∧ ¬ G.Adj p q)
    (hnoP₂ : ∀ p ∈ P₂, ¬ G.Adj f p)
    (hnoQ₁ : ∃ q ∈ Q₁, ¬ G.Adj f q)
    (hnoQ₂ : ∃ q ∈ Q₂, ¬ G.Adj f q) :
    ((∃ p ∈ ({v : V | v ∈ P₁} \ {a₁} : Set V), G.Adj f p) ∧
      ∀ q ∈ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (G.Adj f q ↔ G.Adj a₁ q)) ∨
    ((∃ p ∈ ({v : V | v ∈ P₁} \ {b₁} : Set V), G.Adj f p) ∧
      ∀ q ∈ ({v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
        (G.Adj f q ↔ G.Adj b₁ q)) := by
  let K : Set V :=
    {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂}
  have hK : KnotInduces P₁ P₂ Q₁ Q₂ K := rfl
  have hFsub : ({f} : Set V) ⊆ Kᶜ := by
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst z
    exact hfK
  have hFconn : ConnectedSet G ({f} : Set V) := by
    intro z w
    have hzw : z = w :=
      Subtype.ext ((Set.mem_singleton_iff.mp z.2).trans (Set.mem_singleton_iff.mp w.2).symm)
    subst w
    exact SimpleGraph.Reachable.refl z
  have hFattach : ¬ LocalForKnot G P₁ P₂ Q₁ Q₂ (attachments G ({f} : Set V) K) := by
    rintro ⟨-, -, -, hcomplete⟩
    obtain ⟨p, hpP, q, hqQ, hfp, hfq, hpq⟩ := hbad
    have hpA : p ∈ attachments G ({f} : Set V) K :=
      ⟨Or.inl (Or.inl (Or.inl hpP)), f, rfl, hfp.symm⟩
    have hqA : q ∈ attachments G ({f} : Set V) K :=
      ⟨Or.inl (Or.inr hqQ), f, rfl, hfq.symm⟩
    exact hpq (hcomplete p ⟨hpA, Or.inl hpP⟩ q ⟨hqA, Or.inl hqQ⟩)
  have h93 := Workspace.Statements.S09.SPGT.thm_9_3 G hG P₁ P₂ Q₁ Q₂
    a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK hnoenl hnoover
    hnoovercompl ({f} : Set V) hFsub hFconn hFattach
  have hx₁Q₁ : x₁ ∈ Q₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ₁).1
  have hy₁Q₁ : y₁ ∈ Q₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ₁).2
  have hx₂Q₂ : x₂ ∈ Q₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ₂).1
  have hy₂Q₂ : y₂ ∈ Q₂ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ₂).2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcompQQ,
    -, -, -, -, -, -, -, -⟩ := id hknot
  rcases h93 with h1 | h2 | h3 | h4
  · obtain ⟨g, hg, hres⟩ := h1
    rw [Set.mem_singleton_iff] at hg
    subst g
    rcases hres.1 with hsub | hsub
    · obtain ⟨q, hq, hnq⟩ := hnoQ₁
      exact (hnq (hsub hq).1).elim
    · obtain ⟨q, hq, hnq⟩ := hnoQ₂
      exact (hnq (hsub hq).1).elim
  · obtain ⟨a, P, P', hcase, R, r₁, r₂, hR, hRF, hsame, -, hnear, -⟩ := h2
    have hr₁ : r₁ = f := by
      exact Set.mem_singleton_iff.mp (hRF r₁ (Workspace.ProofLemmas.PathBasics.head_mem hR.2.1))
    have hr₂ : r₂ = f := by
      exact Set.mem_singleton_iff.mp
        (hRF r₂ (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hR).2)
    subst r₁
    subst r₂
    rcases hcase with hc | hc | hc | hc <;>
      simp only [Prod.mk.injEq] at hc <;> obtain ⟨rfl, rfl, rfl⟩ := hc
    · exact Or.inl ⟨hnear, fun q hq => hsame q (hq.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩
    · exact Or.inr ⟨hnear, fun q hq => hsame q (hq.elim (fun h => Or.inl (Or.inr h)) Or.inr)⟩
    · obtain ⟨p, hp, hadj⟩ := hnear
      exact absurd hadj (hnoP₂ p hp.1)
    · obtain ⟨p, hp, hadj⟩ := hnear
      exact absurd hadj (hnoP₂ p hp.1)
  · obtain ⟨a, b, P, P', -, R, r₁, r₂, hR, hRF, hodd, -⟩ := h3
    have hlen : R.length ≤ 1 := by
      by_contra hc
      push_neg at hc
      have h0 : R[0]'(by omega) = f :=
        Set.mem_singleton_iff.mp (hRF _ (List.getElem_mem (by omega)))
      have h1 : R[1]'(by omega) = f :=
        Set.mem_singleton_iff.mp (hRF _ (List.getElem_mem (by omega)))
      exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hR.1 (by omega) (by omega)
        (by omega : (0 : ℕ) ≠ 1) (h0.trans h1.symm)
    have hz : pathLength R = 0 := by
      simp only [pathLength]
      omega
    rw [hz] at hodd
    simp at hodd
  · obtain ⟨x, y, Q', hcase, g, hg, hsame, -⟩ := h4
    rw [Set.mem_singleton_iff] at hg
    subst g
    rcases hcase with hc | hc | hc | hc <;> simp only [Prod.mk.injEq] at hc
    · obtain ⟨hx, -, hQ'⟩ := hc
      obtain ⟨q, hq, hnq⟩ := hnoQ₂
      have hxQ : x ∈ Q₁ := by rw [hx]; exact hx₁Q₁
      exact (hnq ((hsame q (by rw [hQ']; exact Or.inr hq)).mpr (hcompQQ x hxQ q hq))).elim
    · obtain ⟨hx, -, hQ'⟩ := hc
      obtain ⟨q, hq, hnq⟩ := hnoQ₂
      have hxQ : x ∈ Q₁ := by rw [hx]; exact hy₁Q₁
      exact (hnq ((hsame q (by rw [hQ']; exact Or.inr hq)).mpr (hcompQQ x hxQ q hq))).elim
    · obtain ⟨hx, -, hQ'⟩ := hc
      obtain ⟨q, hq, hnq⟩ := hnoQ₁
      have hxQ : x ∈ Q₂ := by rw [hx]; exact hx₂Q₂
      exact (hnq ((hsame q (by rw [hQ']; exact Or.inr hq)).mpr (hcompQQ q hq x hxQ).symm)).elim
    · obtain ⟨hx, -, hQ'⟩ := hc
      obtain ⟨q, hq, hnq⟩ := hnoQ₁
      have hxQ : x ∈ Q₂ := by rw [hx]; exact hy₂Q₂
      exact (hnq ((hsame q (by rw [hQ']; exact Or.inr hq)).mpr (hcompQQ q hq x hxQ).symm)).elim

end Workspace.ProofLemmas.Thm94ClosingKnot
