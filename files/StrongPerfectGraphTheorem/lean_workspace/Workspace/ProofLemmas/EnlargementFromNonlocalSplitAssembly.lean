import Workspace.ProofLemmas.EnlargementFromNonlocalSplitTransport
import Workspace.ProofLemmas.Thm82BranchDelta

/-!
# Promoting one or two internal attachment vertices to skeleton vertices

This finishes the track splitting asked for in the proofs of 7.5 and 8.5 (printed pp. 36–37
and 42).  Given a subdivision `H` of a 3-connected `J` and two vertices of `H` on no common
branch, cut each of the two tracks carrying an attachment vertex in its interior.  The refined
skeleton `B` is a subdivision of `J`, is subdivided by the same `H`, has the two attachment
vertices among its vertices, and every other vertex of `B` is a branch-vertex of `B`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.EnlargementFromNonlocalSplitAssembly

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.NoCrossTrackBranch
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.EnlargementFromNonlocalSplitCore
open Workspace.ProofLemmas.EnlargementFromNonlocalSplitTransport

variable {U W : Type*}

/-- The conclusion asked for by `Promotion`, written out. -/
def PromotionData (J : SimpleGraph U) (H : SimpleGraph W) (c₁ c₂ : W) : Prop :=
  ∃ (m : ℕ) (B : SimpleGraph (Fin m)) (a b : Fin m)
    (ι : Fin m → W) (T : Fin m → Fin m → List W),
    IsSubdivision J B ∧ SubData B H ι T ∧ ι a = c₁ ∧ ι b = c₂ ∧
    (∀ v, v ∈ branchVertices B ∨ v = a ∨ v = b) ∧
    (¬ ∃ q, IsBranch B q ∧ a ∈ q ∧ b ∈ q)

theorem promotionData_symm {J : SimpleGraph U} {H : SimpleGraph W} {c₁ c₂ : W}
    (h : PromotionData J H c₁ c₂) : PromotionData J H c₂ c₁ := by
  obtain ⟨m, B, a, b, ι, T, h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨m, B, b, a, ι, T, h1, h2, h4, h3, fun v => ?_, ?_⟩
  · rcases h5 v with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro ⟨q, hq, hb, ha⟩
    exact h6 ⟨q, hq, ha, hb⟩

/-- An attachment vertex which is not a vertex of the skeleton sits strictly inside one of the
tracks; this names that track and the position. -/
theorem exists_mark_data {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W}
    {T : U → U → List W} (hS : FullWitness J H ι T) (c : W) (hc : c ∉ Set.range ι) :
    ∃ (i j : U) (p : ℕ) (_ : J.Adj i j) (hp : p + 1 < (T i j).length),
      0 < p ∧ (T i j)[p]'(by omega) = c := by
  rcases hS.cover c with ⟨u, hu⟩ | ⟨i, j, hij, hw⟩
  · exact absurd ⟨u, hu.symm⟩ hc
  · obtain ⟨p, hp, h1, h2, h3⟩ := mem_interior_iff.mp hw
    exact ⟨i, j, p, hij, h2, h1, h3⟩

/-- **The refined skeleton has the required properties.**  Every vertex of the refined
skeleton other than the marks is a branch-vertex, because the refined skeleton is a subdivision
of the 3-connected `J`.  Marks on no common branch of the refined skeleton is exactly
nonadjacency there. -/
theorem promotionData_of_split [Fintype U] {J : SimpleGraph U} (hJ : IsKConnected J 3)
    {H : SimpleGraph W} {ι : U → W} {T : U → U → List W} (hS : FullWitness J H ι T)
    {k : ℕ} (D : SplitData J T k) (a b : U ⊕ Fin k)
    (hmark : ∀ t : Fin k, Sum.inr t = a ∨ Sum.inr t = b)
    (hnab : ¬ D.graph.Adj a b) (hne : D.emb ι a ≠ D.emb ι b) :
    PromotionData J H (D.emb ι a) (D.emb ι b) := by
  classical
  set Bg := D.graph.overFin (rfl : Fintype.card (U ⊕ Fin k) = Fintype.card (U ⊕ Fin k)) with hBg
  set ψ : D.graph ≃g Bg := D.graph.overFinIso rfl with hψ
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard := three_le_degree_of_three_connected J hJ
  have hskel := skelWitness D
  have hbr : Set.range (Sum.inl : U → U ⊕ Fin k) ⊆ branchVertices D.graph :=
    range_subset_branchVertices hskel.inj hskel.track hskel.len hskel.disj hskel.new hdeg
  have hcov : ∀ y : U ⊕ Fin k, y ∈ branchVertices D.graph ∨ y = a ∨ y = b := by
    rintro (i | t)
    · exact Or.inl (hbr ⟨i, rfl⟩)
    · rcases hmark t with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hcovB : ∀ v : Fin (Fintype.card (U ⊕ Fin k)),
      v ∈ branchVertices Bg ∨ v = ψ a ∨ v = ψ b := by
    intro v
    rcases hcov (ψ.symm v) with h | h | h
    · refine Or.inl ?_
      rw [branchVertices_image_of_iso ψ]
      exact ⟨ψ.symm v, h, by simp⟩
    · exact Or.inr (Or.inl (by rw [← h]; simp))
    · exact Or.inr (Or.inr (by rw [← h]; simp))
  refine ⟨Fintype.card (U ⊕ Fin k), Bg, ψ a, ψ b, fun u => D.emb ι (ψ.symm u),
    fun u v => D.tracks (ψ.symm u) (ψ.symm v), ?_, ?_, by simp, by simp, hcovB, ?_⟩
  · exact isSubdivision_of_iso ψ (isSubdivision_of_fullWitness hskel)
  · exact subData_of_iso ψ (splitWitness hS D)
  · rintro ⟨q, hq, ha, hb⟩
    have hab' : ψ a ≠ ψ b := fun h => hne (by rw [(EquivLike.injective ψ) h])
    exact hnab (ψ.map_rel_iff.mp (adj_of_common_branch hab' hcovB hq ha hb))

/-- **Cutting the tracks when the first attachment vertex is internal.**  If the second one is
a skeleton vertex only one track is cut, otherwise two different tracks are cut. -/
theorem promotionData_of_internal_first [Fintype U] [Finite W] {J : SimpleGraph U}
    (hJ : IsKConnected J 3) {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}
    (hS : FullWitness J H ι T) (c₁ c₂ : W) (hne : c₁ ≠ c₂)
    (hsep : ∀ i j : U, J.Adj i j → ¬ (c₁ ∈ T i j ∧ c₂ ∈ T i j))
    (hc₁ : c₁ ∉ Set.range ι) : PromotionData J H c₁ c₂ := by
  classical
  obtain ⟨i₁, j₁, p₁, hij₁, hp₁, hpos₁, hmk₁⟩ := exists_mark_data hS c₁ hc₁
  have hc₁mem : c₁ ∈ T i₁ j₁ := by rw [← hmk₁]; exact List.getElem_mem _
  by_cases hc₂ : c₂ ∈ Set.range ι
  · -- only the first track is cut
    obtain ⟨u₂, hu₂⟩ := hc₂
    let D : SplitData J T 1 :=
      { fst := fun _ => i₁, snd := fun _ => j₁, pos := fun _ => p₁
        adj := fun _ => hij₁, pos_pos := fun _ => hpos₁, pos_lt := fun _ => hp₁
        edge_inj := fun t t' _ => Subsingleton.elim t t' }
    have hembA : D.emb ι (Sum.inr 0) = c₁ := hmk₁
    have hembB : D.emb ι (Sum.inl u₂) = c₂ := hu₂
    have hres := promotionData_of_split hJ hS D (Sum.inr 0) (Sum.inl u₂)
      (fun t => Or.inl (congrArg Sum.inr (Subsingleton.elim t 0))) ?_ ?_
    · rwa [hembA, hembB] at hres
    · intro hadj
      have hor : u₂ = i₁ ∨ u₂ = j₁ := hadj
      refine hsep i₁ j₁ hij₁ ⟨hc₁mem, ?_⟩
      rcases hor with rfl | rfl
      · rw [← hu₂]
        exact List.mem_of_mem_head? (hS.track _ _ hij₁).2.1
      · rw [← hu₂]
        exact List.mem_of_getLast? (hS.track _ _ hij₁).2.2
    · rw [hembA, hembB]; exact hne
  · -- two different tracks are cut
    obtain ⟨i₂, j₂, p₂, hij₂, hp₂, hpos₂, hmk₂⟩ := exists_mark_data hS c₂ hc₂
    have hc₂mem : c₂ ∈ T i₂ j₂ := by rw [← hmk₂]; exact List.getElem_mem _
    have hedge : s(i₁, j₁) ≠ s(i₂, j₂) := by
      intro h
      refine hsep i₁ j₁ hij₁ ⟨hc₁mem, ?_⟩
      rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc₂mem
      · rw [hS.rev _ _ hij₁] at hc₂mem
        exact List.mem_reverse.mp hc₂mem
    let D : SplitData J T 2 :=
      { fst := ![i₁, i₂], snd := ![j₁, j₂], pos := ![p₁, p₂]
        adj := by
          intro t
          fin_cases t
          · exact hij₁
          · exact hij₂
        pos_pos := by
          intro t
          fin_cases t
          · exact hpos₁
          · exact hpos₂
        pos_lt := by
          intro t
          fin_cases t
          · exact hp₁
          · exact hp₂
        edge_inj := by
          intro t t' h
          fin_cases t <;> fin_cases t'
          · rfl
          · exact absurd h hedge
          · exact absurd h.symm hedge
          · rfl }
    have hembA : D.emb ι (Sum.inr 0) = c₁ := hmk₁
    have hembB : D.emb ι (Sum.inr 1) = c₂ := hmk₂
    have hres := promotionData_of_split hJ hS D (Sum.inr 0) (Sum.inr 1) ?_
      (D.not_adj_inr_inr) ?_
    · rwa [hembA, hembB] at hres
    · intro t
      fin_cases t
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [hembA, hembB]; exact hne

/-- **The two attachment vertices become skeleton vertices.**  This is the track-splitting
step asserted without proof in 7.5 and 8.5. -/
theorem promotionData_of_no_common_branch [Fintype U] [Fintype W] (J : SimpleGraph U)
    (hJ : IsKConnected J 3) (H : SimpleGraph W) (hsub : IsSubdivision J H) (c₁ c₂ : W)
    (hnb : ¬ ∃ q : List W, IsBranch H q ∧ c₁ ∈ q ∧ c₂ ∈ q)
    (hint : c₁ ∉ branchVertices H ∨ c₂ ∉ branchVertices H) :
    PromotionData J H c₁ c₂ := by
  classical
  obtain ⟨ι, T, hS⟩ := exists_fullWitness hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard := three_le_degree_of_three_connected J hJ
  have hbvLower : Set.range ι ⊆ branchVertices H :=
    range_subset_branchVertices hS.inj hS.track hS.len hS.disj hS.new hdeg
  have hbvUpper : branchVertices H ⊆ Set.range ι :=
    branchVertices_subset_range hS.track hS.rev hS.disj hS.cover hS.edges
  have hbranch : ∀ i j : U, J.Adj i j → IsBranch H (T i j) := by
    intro i j hij
    exact Workspace.ProofLemmas.Thm82BranchDelta.isBranch_of_ends_branch (hS.track i j hij)
      (fun h => hij.ne (hS.inj h))
      (fun w hw hwb => hS.new i j hij w hw (hbvUpper hwb))
      (hbvLower ⟨i, rfl⟩) (hbvLower ⟨j, rfl⟩)
  have hsep : ∀ i j : U, J.Adj i j → ¬ (c₁ ∈ T i j ∧ c₂ ∈ T i j) := by
    rintro i j hij ⟨h1, h2⟩
    exact hnb ⟨T i j, hbranch i j hij, h1, h2⟩
  have hne : c₁ ≠ c₂ := by
    intro heq
    subst heq
    rcases hS.cover c₁ with ⟨u, hu⟩ | ⟨i, j, hij, hw⟩
    · obtain ⟨v, huv⟩ := exists_adj_of_three_connected J hJ u
      refine hsep u v huv ⟨?_, ?_⟩ <;>
        · rw [hu]
          exact List.mem_of_mem_head? (hS.track u v huv).2.1
    · have hmem := Workspace.ProofLemmas.SubdivisionCompose.mem_of_mem_trackInterior hw
      exact hsep i j hij ⟨hmem, hmem⟩
  rcases hint with h | h
  · exact promotionData_of_internal_first hJ hS c₁ c₂ hne hsep (fun hc => h (hbvLower hc))
  · refine promotionData_symm (promotionData_of_internal_first hJ hS c₂ c₁ hne.symm ?_
      (fun hc => h (hbvLower hc)))
    rintro i j hij ⟨h1, h2⟩
    exact hsep i j hij ⟨h2, h1⟩

end Workspace.ProofLemmas.EnlargementFromNonlocalSplitAssembly

