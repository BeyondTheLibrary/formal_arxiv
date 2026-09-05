import Workspace.ProofLemmas.Thm95OffspringDefs

/-!
# Adding the path `F` to one strip of the striation

PAPER (9.5(1), printed p. 52, second bullet): *"we could add `f₁` to `Aᵢ`, `{f₂,…,f_{k-1}}` to
`Cᵢ`, and `f_k` to `Bᵢ`, contradicting the maximality of the striation"*.

The paper uses this construction to contradict maximality.  Here it is used positively: since
9.5(1) only has to produce *some* striation on `V(L) ∪ F`, the enlarged strip family is already
the answer whenever `f₁` and `f_k` copy the neighbourhoods of the two ends of `Sᵢ` on every
antistrip.  `Thm95StripExtension.two_end_absurd` does the same construction and then invokes
maximality; this file stops one step earlier and returns the striation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringMerge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} {G : SimpleGraph V}

/-- Replacing the `i`-th strip by a strip containing it and covered by it together with `F`,
where `F` is inside the new strip, adds exactly `F` to the vertex set of the striation. -/
theorem vertices_update {m n : ℕ} (S : Fin m → Set V × Set V × Set V)
    (T : Fin n → Set V × Set V × Set V) (i : Fin m) (U : Set V × Set V × Set V) {F : Set V}
    (hsub : stripVertices (S i) ⊆ stripVertices U)
    (hsupport : stripVertices U ⊆ stripVertices (S i) ∪ F)
    (hFU : F ⊆ stripVertices U) :
    striationVertices (Function.update S i U) T = striationVertices S T ∪ F := by
  classical
  refine Set.ext (fun v => ⟨?_, ?_⟩)
  · rintro (hv | hv)
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
      by_cases hki : k = i
      · subst k
        rcases hsupport (by simpa using hk) with h | h
        · exact Or.inl (Or.inl (Set.mem_iUnion_of_mem i h))
        · exact Or.inr h
      · exact Or.inl (Or.inl (Set.mem_iUnion_of_mem k (by
          simpa [Function.update_of_ne hki] using hk)))
    · exact Or.inl (Or.inr hv)
  · rintro ((hv | hv) | hv)
    · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
      by_cases hki : k = i
      · subst k
        exact Or.inl (Set.mem_iUnion_of_mem i (by simpa using hsub hk))
      · exact Or.inl (Set.mem_iUnion_of_mem k (by simpa [Function.update_of_ne hki] using hk))
    · exact Or.inr hv
    · exact Or.inl (Set.mem_iUnion_of_mem i (by simpa using hFU hv))

/-- **PAPER (9.5(1), p. 52, second bullet).**  If `f₁` and `f_k` have, on every antistrip of the
striation, the same neighbours as the two ends `a ∈ Aᵢ` and `b ∈ Bᵢ` of the strip `Sᵢ`, then
adding `f₁` to `Aᵢ`, the interior of `F` to `Cᵢ` and `f_k` to `Bᵢ` gives a striation on
`V(L) ∪ F`. -/
theorem merge_striation {m n : ℕ} {S : Fin m → Set V × Set V × Set V}
    {T : Fin n → Set V × Set V × Set V} (hG : Berge G) (hL : IsStriation G S T) {F : Set V}
    (hF : F ⊆ (striationVertices S T)ᶜ) (i : Fin m)
    (hantiS : ∀ k, Anticomplete G F (stripVertices (S k)))
    {R : List V} {r s a b : V} (hR : IsPathFrom G R r s) (hrs : r ≠ s)
    (hRset : {v : V | v ∈ R} = F) (ha : a ∈ (S i).1) (hb : b ∈ (S i).2.2)
    (hra : ∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj r w ↔ G.Adj a w))
    (hsb : ∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (G.Adj s w ↔ G.Adj b w))
    (hantiT : ∀ j : Fin n,
      Anticomplete G {v : V | v ∈ SPGT.interior R} (stripVertices (T j))) :
    ∃ (m' n' : ℕ) (S' : Fin m' → Set V × Set V × Set V)
      (T' : Fin n' → Set V × Set V × Set V), IsStriation G S' T' ∧
      striationVertices S' T' = striationVertices S T ∪ F := by
  classical
  have hRF : ∀ v ∈ R, v ∈ F := fun v hv => hRset ▸ hv
  rcases hSi : S i with ⟨A, C, B⟩
  have haA : a ∈ A := by simpa only [hSi] using ha
  have hbB : b ∈ B := by simpa only [hSi] using hb
  have hS : IsStrip G (A, C, B) := by simpa only [hSi] using hL.1 i
  have hout : ∀ v ∈ R, v ∉ A ∪ B ∪ C := by
    intro v hv hvS
    exact hF (hRF v hv)
      (StriationCompl.stripVertices_S_subset S T i (by simpa only [hSi] using hvS))
  let U : Set V × Set V × Set V := (insert r A, C ∪ {v | v ∈ SPGT.interior R}, insert s B)
  have hU : IsStrip G U := Thm95StripExtension.strip_add_two_ends hS hR hrs hout
  have hsub : stripVertices (S i) ⊆ stripVertices U := by
    rw [hSi]
    rintro v ((hv | hv) | hv)
    · exact Or.inl (Or.inl (Or.inr hv))
    · exact Or.inl (Or.inr (Or.inr hv))
    · exact Or.inr (Or.inl hv)
  have hsupport : stripVertices U ⊆ stripVertices (S i) ∪ F := by
    rw [hSi]
    rintro v (((hv | hv) | (hv | hv)) | (hv | hv))
    · exact Or.inr (hv ▸ hRF r (PathBasics.head_mem hR.2.1))
    · exact Or.inl (Or.inl (Or.inl hv))
    · exact Or.inr (hv ▸ hRF s (PathBasics.getLast_mem hR.2.2))
    · exact Or.inl (Or.inl (Or.inr hv))
    · exact Or.inl (Or.inr hv)
    · exact Or.inr (hRF v (PathBasics.interior_subset hv))
  have hFU : F ⊆ stripVertices U := by
    intro v hv
    have hvR : v ∈ R := by rw [← hRset] at hv; exact hv
    by_cases hvr : v = r
    · exact Or.inl (Or.inl (Or.inl hvr))
    by_cases hvs : v = s
    · exact Or.inl (Or.inr (Or.inl hvs))
    · exact Or.inr (Or.inr
        ((PathBasics.mem_interior_iff_of_pathFrom hR).mpr ⟨hvR, hvr, hvs⟩))
  have hdS : ∀ k, k ≠ i → Disjoint (stripVertices U) (stripVertices (S k)) := by
    intro k hki
    refine Set.disjoint_left.mpr (fun v hv hk => ?_)
    rcases hsupport hv with hi | hf
    · exact Set.disjoint_left.mp (hL.2.2.1 i k hki.symm) hi hk
    · exact hF hf (StriationCompl.stripVertices_S_subset S T k hk)
  have hdT : ∀ j, Disjoint (stripVertices U) (stripVertices (T j)) := by
    intro j
    refine Set.disjoint_left.mpr (fun v hv hj => ?_)
    rcases hsupport hv with hi | hf
    · exact Set.disjoint_left.mp (hL.2.2.2.2.1 i j) hi hj
    · exact hF hf (StriationCompl.stripVertices_T_subset S T j hj)
  have haSk : ∀ k, k ≠ i → Anticomplete G (stripVertices U) (stripVertices (S k)) := by
    intro k hki v hv w hw hadj
    rcases hsupport hv with hi | hf
    · rcases lt_or_gt_of_ne hki with hlt | hlt
      · exact hL.2.2.2.2.2.2.2.2.2.1 k i hlt w hw v hi hadj.symm
      · exact hL.2.2.2.2.2.2.2.2.2.1 i k hlt v hi w hw hadj
    · exact hantiS k v hf w hw hadj
  have hcopyA : ∀ j v, v ∈ U.1 →
      ∃ a' ∈ A, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj a' w := by
    rintro j v (rfl | hv)
    · exact ⟨a, haA, hra j⟩
    · exact ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyB : ∀ j v, v ∈ U.2.2 →
      ∃ b' ∈ B, ∀ w ∈ stripVertices (T j), G.Adj v w ↔ G.Adj b' w := by
    rintro j v (rfl | hv)
    · exact ⟨b, hbB, hsb j⟩
    · exact ⟨v, hv, fun _ _ => Iff.rfl⟩
  have hcopyC : ∀ j v, v ∈ U.2.1 → v ∈ C ∨ VertexAnticomplete G v (stripVertices (T j)) :=
    fun j v hv => hv.imp id (fun hv => hantiT j v hv)
  refine ⟨m, n, Function.update S i U, T,
    Thm95StripExtension.replace hG hL i U hU hdS hdT haSk ?_ ?_,
    vertices_update S T i U hsub hsupport hFU⟩
  · intro j hp
    rw [hSi] at hp
    exact Thm95StripExtension.parallel_enlarge hp (hcopyA j) (hcopyB j) (hcopyC j)
  · intro j hc
    rw [hSi] at hc
    exact Thm95StripExtension.coParallel_enlarge hc (hcopyA j) (hcopyB j) (hcopyC j)

end Workspace.ProofLemmas.Thm95OffspringMerge
