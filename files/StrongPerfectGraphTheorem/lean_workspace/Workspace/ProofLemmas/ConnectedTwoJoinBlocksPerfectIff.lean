import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.MinimumAttachmentPathInternalVerticesAvoidAttachments
import Workspace.ProofLemmas.TwoJoinMarkerPathsHaveSameParity
import Workspace.ProofLemmas.PerfectMarkerBlockControlledPaletteColoring
import Workspace.ProofLemmas.TwoJoinPaletteRelabeling
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.PerfectInducedSubgraph
import Workspace.ProofLemmas.CliqueNumOfInducedSet

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core

namespace ConnectedTwoJoinBlocksPerfectIffAux

open Workspace.ProofLemmas.CliqueNumOfInducedSet

/-! ### §1 heredity -/

/-- Perfection passes to an induced subgraph on a subset of the ambient set. -/
theorem perfect_induce_subset {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y S : Set W) (hSY : S ⊆ Y)
    (h : SPGT.IsPerfect (K.induce Y)) : SPGT.IsPerfect (K.induce S) := by
  classical
  have h2 := Workspace.ProofLemmas.PerfectInducedSubgraph (K.induce Y)
    {y : ↥Y | (y : W) ∈ S} h
  let e : (K.induce Y).induce {y : ↥Y | (y : W) ∈ S} ≃g
      K.induce (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) :=
    { Equiv.Set.image (Subtype.val : ↥Y → W) {y : ↥Y | (y : W) ∈ S} Subtype.val_injective with
      map_rel_iff' := by
        intro a b
        rfl }
  have himg : (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSY hx⟩, hx, rfl⟩
  have hfin := Workspace.ProofLemmas.IsoTransport.isPerfect_of_iso e h2
  rwa [himg] at hfin

/-- A one-vertex clique shows a nonempty set has positive clique number. -/
theorem one_le_cliqueNum_of_mem {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) {Z : Set W} {x : W} (hx : x ∈ Z) :
    1 ≤ (K.induce Z).cliqueNum := by
  classical
  have := card_le_cliqueNum_induce K (K := ({x} : Finset W))
    (by simpa using hx) (by simpa using SimpleGraph.isClique_singleton (G := K) x)
  simpa using this

/-- The default side colouring, when no palette control is needed. -/
theorem side_coloring {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y T S : Set W) (hTY : T ⊆ Y) (hTS : T ⊆ S) (n : ℕ)
    (hblock : SPGT.IsPerfect (K.induce Y))
    (hn : (K.induce S).cliqueNum ≤ n) :
    Nonempty ((K.induce T).Coloring (Fin n)) := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have hp : SPGT.IsPerfect (K.induce T) := perfect_induce_subset K Y T hTY hblock
  have hc : (K.induce T).Colorable ((K.induce T).cliqueNum) :=
    colorable_cliqueNum_of_isPerfect _ hp
  exact hc.mono (le_trans (cliqueNum_induce_mono K hTS) hn)

/-! ### §5 the local attachment clique inequality -/

/-- Two complete-to-each-other attachment cliques on opposite sides combine. -/
theorem attach_sum_le {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (X₁ X₂ C₁ C₂ S : Set V) (hsides : Disjoint X₁ X₂)
    (hC₁ : C₁ ⊆ X₁) (hC₂ : C₂ ⊆ X₂)
    (hcomplete : ∀ u ∈ C₁, ∀ v ∈ C₂, F.Adj u v) :
    (F.induce (C₁ ∩ S)).cliqueNum + (F.induce (C₂ ∩ S)).cliqueNum
      ≤ (F.induce S).cliqueNum := by
  classical
  obtain ⟨K₁, hK₁sub, hK₁cl, hK₁card⟩ := exists_clique_card_eq_cliqueNum F (C₁ ∩ S)
  obtain ⟨K₂, hK₂sub, hK₂cl, hK₂card⟩ := exists_clique_card_eq_cliqueNum F (C₂ ∩ S)
  have hmem₁ : ∀ x ∈ K₁, x ∈ C₁ ∧ x ∈ S := fun x hx => hK₁sub (by simpa using hx)
  have hmem₂ : ∀ x ∈ K₂, x ∈ C₂ ∧ x ∈ S := fun x hx => hK₂sub (by simpa using hx)
  have hdisjK : Disjoint K₁ K₂ := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact Set.disjoint_left.mp hsides (hC₁ (hmem₁ x hx1).1) (hC₂ (hmem₂ x hx2).1)
  have hsub : (↑(K₁ ∪ K₂) : Set V) ⊆ S := by
    intro x hx
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hx
    rcases hx with hx | hx
    · exact (hmem₁ x hx).2
    · exact (hmem₂ x hx).2
  have hclique : F.IsClique (↑(K₁ ∪ K₂) : Set V) := by
    intro u hu v hv huv
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at hu hv
    rcases hu with hu | hu <;> rcases hv with hv | hv
    · exact hK₁cl (by simpa using hu) (by simpa using hv) huv
    · exact hcomplete u (hmem₁ u hu).1 v (hmem₂ v hv).1
    · exact (hcomplete v (hmem₁ v hv).1 u (hmem₂ u hu).1).symm
    · exact hK₂cl (by simpa using hu) (by simpa using hv) huv
  have hle := card_le_cliqueNum_induce F hsub hclique
  rw [Finset.card_union_of_disjoint hdisjK, hK₁card, hK₂card] at hle
  exact hle

/-! ### §9 the clique bound for one marker block -/

/-- A path contains no triangle. -/
theorem path_no_triangle {V : Type*} {F : SimpleGraph V} {Q : List V}
    (hQ : SPGT.IsPathList F Q) {x y z : V} (hx : x ∈ Q) (hy : y ∈ Q) (hz : z ∈ Q)
    (hxy : F.Adj x y) (hxz : F.Adj x z) (hyz : F.Adj y z) : False := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hy
  obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
  subst hix
  subst hjy
  subst hkz
  have h1 := (PathBasics.path_adj_iff hQ hi hj).mp hxy
  have h2 := (PathBasics.path_adj_iff hQ hi hk).mp hxz
  have h3 := (PathBasics.path_adj_iff hQ hj hk).mp hyz
  omega

/-- §9: the induced subgraph on one side's trace together with the opposite
marker path has clique number at most `ω`. -/
theorem block_cliqueNum_le {V : Type*} [Fintype V] [DecidableEq V] (F : SimpleGraph V)
    (X Y A B A' B' S : Set V) (n : ℕ)
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (hcross : ∀ u ∈ X, ∀ v ∈ Y, F.Adj u v ↔ (u ∈ A ∧ v ∈ A') ∨ (u ∈ B ∧ v ∈ B'))
    (Q : List V) (a' b' : V)
    (hQ : SPGT.IsPathFrom F Q a' b') (hQY : ∀ v ∈ Q, v ∈ Y)
    (hAmem : ∀ x ∈ Q, x ∈ A' ↔ x = a') (hBmem : ∀ x ∈ Q, x ∈ B' ↔ x = b')
    (hab' : a' ≠ b')
    (hαsum : (F.induce (A ∩ S)).cliqueNum + (F.induce (A' ∩ S)).cliqueNum ≤ n)
    (hβsum : (F.induce (B ∩ S)).cliqueNum + (F.induce (B' ∩ S)).cliqueNum ≤ n)
    (hα : 1 ≤ (F.induce (A ∩ S)).cliqueNum)
    (hα' : 1 ≤ (F.induce (A' ∩ S)).cliqueNum)
    (hβ' : 1 ≤ (F.induce (B' ∩ S)).cliqueNum)
    (hSn : (F.induce S).cliqueNum ≤ n) :
    (F.induce ((X ∩ S) ∪ {v : V | v ∈ Q})).cliqueNum ≤ n := by
  classical
  obtain ⟨C, hCsub, hCcl, hCcard⟩ :=
    exists_clique_card_eq_cliqueNum F ((X ∩ S) ∪ {v : V | v ∈ Q})
  rw [← hCcard]
  set M : Finset V := C.filter (fun x => x ∈ Q) with hM
  set D : Finset V := C.filter (fun x => ¬ (x ∈ Q)) with hD
  have hsplit : M.card + D.card = C.card := by
    rw [hM, hD]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  have hDmem : ∀ d ∈ D, d ∈ X ∧ d ∈ S ∧ d ∉ Q := by
    intro d hd
    rw [hD, Finset.mem_filter] at hd
    have hd' : d ∈ ((X ∩ S) ∪ {v : V | v ∈ Q} : Set V) := hCsub (by simpa using hd.1)
    rcases hd' with hd' | hd'
    · exact ⟨hd'.1, hd'.2, hd.2⟩
    · exact absurd hd' hd.2
  have hMmem : ∀ m ∈ M, m ∈ C ∧ m ∈ Q := by
    intro m hm
    rw [hM, Finset.mem_filter] at hm
    exact hm
  have hDC : (↑D : Set V) ⊆ (↑C : Set V) := by
    intro x hx
    have hx' : x ∈ D := by simpa using hx
    rw [hD, Finset.mem_filter] at hx'
    simpa using hx'.1
  have hDcl : F.IsClique (↑D : Set V) := hCcl.subset hDC
  -- (i) at most two marker vertices
  have hM2 : M.card ≤ 2 := by
    by_contra hcon
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq (show 3 ≤ M.card by omega)
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp hucard
    have hxM : x ∈ M := hu (by simp)
    have hyM : y ∈ M := hu (by simp)
    have hzM : z ∈ M := hu (by simp)
    exact path_no_triangle hQ.1 (hMmem x hxM).2 (hMmem y hyM).2 (hMmem z hzM).2
      (hCcl (by simpa using (hMmem x hxM).1) (by simpa using (hMmem y hyM).1) hxy)
      (hCcl (by simpa using (hMmem x hxM).1) (by simpa using (hMmem z hzM).1) hxz)
      (hCcl (by simpa using (hMmem y hyM).1) (by simpa using (hMmem z hzM).1) hyz)
  -- a side vertex adjacent to a marker vertex forces the marker endpoint
  have hlink : ∀ d ∈ D, ∀ m ∈ M, (m = a' ∧ d ∈ A) ∨ (m = b' ∧ d ∈ B) := by
    intro d hd m hm
    obtain ⟨hdX, hdS, hdQ⟩ := hDmem d hd
    obtain ⟨hmC, hmQ⟩ := hMmem m hm
    have hdC : d ∈ C := by
      rw [hD, Finset.mem_filter] at hd
      exact hd.1
    have hne : d ≠ m := fun h => hdQ (h ▸ hmQ)
    have hadj : F.Adj d m := hCcl (by simpa using hdC) (by simpa using hmC) hne
    have := (hcross d hdX m (hQY m hmQ)).mp hadj
    rcases this with ⟨hdA, hmA⟩ | ⟨hdB, hmB⟩
    · exact Or.inl ⟨(hAmem m hmQ).mp hmA, hdA⟩
    · exact Or.inr ⟨(hBmem m hmQ).mp hmB, hdB⟩
  have hcases : M.card = 0 ∨ M.card = 1 ∨ M.card = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · -- no marker vertex: the clique lives in `S`
    have hCS : (↑C : Set V) ⊆ S := by
      intro x hx
      have hxD : x ∈ D := by
        rw [hD, Finset.mem_filter]
        refine ⟨by simpa using hx, ?_⟩
        intro hxQ
        have : x ∈ M := by
          rw [hM, Finset.mem_filter]
          exact ⟨by simpa using hx, hxQ⟩
        rw [Finset.card_eq_zero] at h0
        rw [h0] at this
        exact absurd this (Finset.notMem_empty x)
      exact (hDmem x hxD).2.1
    exact le_trans (card_le_cliqueNum_induce F hCS hCcl) hSn
  · -- exactly one marker vertex
    obtain ⟨m, hMeq⟩ := Finset.card_eq_one.mp h1
    have hmM : m ∈ M := by rw [hMeq]; simp
    have hDsub : ∀ d ∈ D, (m = a' ∧ d ∈ A) ∨ (m = b' ∧ d ∈ B) := fun d hd => hlink d hd m hmM
    by_cases hDempty : D = ∅
    · rw [hDempty] at hsplit
      simp only [Finset.card_empty, add_zero] at hsplit
      omega
    · obtain ⟨d₀, hd₀⟩ := Finset.nonempty_iff_ne_empty.mpr hDempty
      rcases hDsub d₀ hd₀ with ⟨hma, -⟩ | ⟨hmb, -⟩
      · have hDA : (↑D : Set V) ⊆ A ∩ S := by
          intro d hd
          have hd' : d ∈ D := by simpa using hd
          rcases hDsub d hd' with ⟨-, hdA⟩ | ⟨hmb, -⟩
          · exact ⟨hdA, (hDmem d hd').2.1⟩
          · exact absurd (hma ▸ hmb : a' = b') hab'
        have := card_le_cliqueNum_induce F hDA hDcl
        omega
      · have hDB : (↑D : Set V) ⊆ B ∩ S := by
          intro d hd
          have hd' : d ∈ D := by simpa using hd
          rcases hDsub d hd' with ⟨hma, -⟩ | ⟨-, hdB⟩
          · exact absurd (hma ▸ hmb : a' = b') hab'
          · exact ⟨hdB, (hDmem d hd').2.1⟩
        have := card_le_cliqueNum_induce F hDB hDcl
        omega
  · -- two marker vertices: no side vertex can join them
    obtain ⟨m₁, m₂, hm12, hMeq⟩ := Finset.card_eq_two.mp h2
    have hm₁ : m₁ ∈ M := by rw [hMeq]; simp
    have hm₂ : m₂ ∈ M := by rw [hMeq]; simp
    have hDempty : D = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨d, hd⟩
      rcases hlink d hd m₁ hm₁ with ⟨h1a, hdA⟩ | ⟨h1b, hdB⟩ <;>
        rcases hlink d hd m₂ hm₂ with ⟨h2a, hdA'⟩ | ⟨h2b, hdB'⟩
      · exact hm12 (h1a.trans h2a.symm)
      · exact Set.disjoint_left.mp hAB hdA hdB'
      · exact Set.disjoint_left.mp hAB hdA' hdB
      · exact hm12 (h1b.trans h2b.symm)
    rw [hDempty] at hsplit
    simp only [Finset.card_empty, add_zero] at hsplit
    omega

/-! ### §11 gluing the two side colourings -/

theorem glue_colorings {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V) (X₁ X₂ A₁ B₁ A₂ B₂ S : Set V) (n : ℕ)
    (hpartition : X₁ ∪ X₂ = Set.univ)
    (hcross : ∀ u ∈ X₁, ∀ v ∈ X₂,
      F.Adj u v ↔ (u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂))
    (col₁ : (F.induce (X₁ ∩ S)).Coloring (Fin n))
    (col₂ : (F.induce (X₂ ∩ S)).Coloring (Fin n))
    (hA : Disjoint (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ A₁})
                   (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ A₂}))
    (hB : Disjoint (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ B₁})
                   (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ B₂})) :
    (F.induce S).Colorable n := by
  classical
  have hmem : ∀ x : V, x ∉ X₁ → x ∈ X₂ := by
    intro x hx
    have hu : x ∈ X₁ ∪ X₂ := by rw [hpartition]; trivial
    rcases hu with h | h
    · exact absurd h hx
    · exact h
  refine ⟨SimpleGraph.Coloring.mk
    (fun v : ↥S => if h : (v : V) ∈ X₁ then col₁ ⟨(v : V), ⟨h, v.2⟩⟩
      else col₂ ⟨(v : V), ⟨hmem (v : V) h, v.2⟩⟩) ?_⟩
  intro u v huv
  have hadj : F.Adj (u : V) (v : V) := huv
  by_cases hu : (u : V) ∈ X₁ <;> by_cases hv : (v : V) ∈ X₁
  · simp only [dif_pos hu, dif_pos hv]
    exact col₁.valid hadj
  · simp only [dif_pos hu, dif_neg hv]
    intro hcol
    rcases (hcross _ hu _ (hmem _ hv)).mp hadj with ⟨huA, hvA⟩ | ⟨huB, hvB⟩
    · exact Set.disjoint_left.mp hA ⟨⟨(u : V), ⟨hu, u.2⟩⟩, huA, rfl⟩
        ⟨⟨(v : V), ⟨hmem _ hv, v.2⟩⟩, hvA, hcol.symm⟩
    · exact Set.disjoint_left.mp hB ⟨⟨(u : V), ⟨hu, u.2⟩⟩, huB, rfl⟩
        ⟨⟨(v : V), ⟨hmem _ hv, v.2⟩⟩, hvB, hcol.symm⟩
  · simp only [dif_neg hu, dif_pos hv]
    intro hcol
    rcases (hcross _ hv _ (hmem _ hu)).mp hadj.symm with ⟨hvA, huA⟩ | ⟨hvB, huB⟩
    · exact Set.disjoint_left.mp hA ⟨⟨(v : V), ⟨hv, v.2⟩⟩, hvA, rfl⟩
        ⟨⟨(u : V), ⟨hmem _ hu, u.2⟩⟩, huA, hcol⟩
    · exact Set.disjoint_left.mp hB ⟨⟨(v : V), ⟨hv, v.2⟩⟩, hvB, rfl⟩
        ⟨⟨(u : V), ⟨hmem _ hu, u.2⟩⟩, huB, hcol⟩
  · simp only [dif_neg hu, dif_neg hv]
    exact col₂.valid hadj

/-- Post-composing a colouring with a permutation of the palette. -/
def recolor {V : Type*} {G : SimpleGraph V} {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c : G.Coloring (Fin n)) : G.Coloring (Fin n) :=
  SimpleGraph.Coloring.mk (fun v => σ (c v)) (by
    intro u v huv h
    exact c.valid huv (σ.injective h))

theorem recolor_image {V : Type*} {G : SimpleGraph V} {n : ℕ} (σ : Equiv.Perm (Fin n))
    (c : G.Coloring (Fin n)) (T : Set V) :
    (recolor σ c) '' T = Set.image σ (c '' T) := by
  rw [← Set.image_comp]
  rfl

/-- The empty-palette case of the disjointness input to `glue_colorings`. -/
theorem palette_empty {V : Type*} {F : SimpleGraph V} {n : ℕ} {X S C : Set V}
    (c : (F.induce (X ∩ S)).Coloring (Fin n)) (hC : C ∩ S = ∅) :
    (c '' {v : ↥(X ∩ S) | (v : V) ∈ C}) = ∅ := by
  rw [Set.image_eq_empty]
  rw [Set.eq_empty_iff_forall_notMem]
  rintro v hv
  have : (v : V) ∈ C ∩ S := ⟨hv, v.2.2⟩
  rw [hC] at this
  exact this

end ConnectedTwoJoinBlocksPerfectIffAux

open ConnectedTwoJoinBlocksPerfectIffAux
open Workspace.ProofLemmas.CliqueNumOfInducedSet

/-- The two marker-path blocks of a connected proper 2-join are perfect exactly
when the original finite graph is perfect. -/
theorem ConnectedTwoJoinBlocksPerfectIff
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : SimpleGraph V)
    (X₁ X₂ A₁ B₁ A₂ B₂ : Set V)
    (hpartition : X₁ ∪ X₂ = Set.univ)
    (hsides : Disjoint X₁ X₂)
    (hA₁ : A₁ ⊆ X₁) (hB₁ : B₁ ⊆ X₁)
    (hA₂ : A₂ ⊆ X₂) (hB₂ : B₂ ⊆ X₂)
    (hA₁ne : A₁.Nonempty) (hB₁ne : B₁.Nonempty)
    (hA₂ne : A₂.Nonempty) (hB₂ne : B₂.Nonempty)
    (hAB₁ : Disjoint A₁ B₁) (hAB₂ : Disjoint A₂ B₂)
    (hcross : ∀ u ∈ X₁, ∀ v ∈ X₂,
      F.Adj u v ↔ (u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂))
    (hcard₁ : 3 ≤ X₁.ncard) (hcard₂ : 3 ≤ X₂.ncard)
    (Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ : V)
    (ha₁ : a₁ ∈ A₁) (hb₁ : b₁ ∈ B₁)
    (ha₂ : a₂ ∈ A₂) (hb₂ : b₂ ∈ B₂)
    (hQ₁ : SPGT.IsPathFrom F Q₁ a₁ b₁)
    (hQ₂ : SPGT.IsPathFrom F Q₂ a₂ b₂)
    (hQ₁X₁ : ∀ v ∈ Q₁, v ∈ X₁)
    (hQ₂X₂ : ∀ v ∈ Q₂, v ∈ X₂)
    (hmin₁ : ∀ a ∈ A₁, ∀ b ∈ B₁, ∀ p : List V,
      SPGT.IsPathFrom F p a b → (∀ v ∈ p, v ∈ X₁) →
        SPGT.pathLength Q₁ ≤ SPGT.pathLength p)
    (hmin₂ : ∀ a ∈ A₂, ∀ b ∈ B₂, ∀ p : List V,
      SPGT.IsPathFrom F p a b → (∀ v ∈ p, v ∈ X₂) →
        SPGT.pathLength Q₂ ≤ SPGT.pathLength p) :
    SPGT.IsPerfect F ↔
      SPGT.IsPerfect (F.induce (X₁ ∪ {v : V | v ∈ Q₂})) ∧
        SPGT.IsPerfect (F.induce (X₂ ∪ {v : V | v ∈ Q₁})) := by
  classical
  constructor
  · intro hF
    exact ⟨PerfectInducedSubgraph F _ hF, PerfectInducedSubgraph F _ hF⟩
  · rintro ⟨hblock₁, hblock₂⟩ S
    -- §2: exact structure of the two minimum attachment paths
    obtain ⟨hab₁, hlen₁, hint₁, hAmem₁, hBmem₁⟩ :=
      MinimumAttachmentPathInternalVerticesAvoidAttachments F X₁ A₁ B₁ a₁ b₁ Q₁
        hA₁ hB₁ hAB₁ ha₁ hb₁ hQ₁ hQ₁X₁ hmin₁
    obtain ⟨hab₂, hlen₂, hint₂, hAmem₂, hBmem₂⟩ :=
      MinimumAttachmentPathInternalVerticesAvoidAttachments F X₂ A₂ B₂ a₂ b₂ Q₂
        hA₂ hB₂ hAB₂ ha₂ hb₂ hQ₂ hQ₂X₂ hmin₂
    -- §3
    have hparity := TwoJoinMarkerPathsHaveSameParity
      F X₁ X₂ A₁ B₁ A₂ B₂ hsides hA₁ hB₁ hA₂ hB₂ hAB₁ hAB₂ hcross
      Q₁ Q₂ a₁ b₁ a₂ b₂ ha₁ hb₁ ha₂ hb₂ hQ₁ hQ₂ hQ₁X₁ hQ₂X₂ hmin₁ hmin₂ hblock₁
    -- the mirrored cross-edge rule
    have hcross' : ∀ u ∈ X₂, ∀ v ∈ X₁,
        F.Adj u v ↔ (u ∈ A₂ ∧ v ∈ A₁) ∨ (u ∈ B₂ ∧ v ∈ B₁) := by
      intro u hu v hv
      rw [SimpleGraph.adj_comm, hcross v hv u hu]
      tauto
    apply le_antisymm
    · apply SimpleGraph.chromaticNumber_le_iff_colorable.mpr
      -- abbreviations
      set ω := (F.induce S).cliqueNum with hωdef
      set α₁ := (F.induce (A₁ ∩ S)).cliqueNum with hα₁def
      set β₁ := (F.induce (B₁ ∩ S)).cliqueNum with hβ₁def
      set α₂ := (F.induce (A₂ ∩ S)).cliqueNum with hα₂def
      set β₂ := (F.induce (B₂ ∩ S)).cliqueNum with hβ₂def
      -- §5
      have hαsum : α₁ + α₂ ≤ ω :=
        attach_sum_le F X₁ X₂ A₁ A₂ S hsides hA₁ hA₂
          (fun u hu v hv => (hcross u (hA₁ hu) v (hA₂ hv)).mpr (Or.inl ⟨hu, hv⟩))
      have hβsum : β₁ + β₂ ≤ ω :=
        attach_sum_le F X₁ X₂ B₁ B₂ S hsides hB₁ hB₂
          (fun u hu v hv => (hcross u (hB₁ hu) v (hB₂ hv)).mpr (Or.inr ⟨hu, hv⟩))
      have hS₁S : X₁ ∩ S ⊆ S := fun x hx => hx.2
      have hS₂S : X₂ ∩ S ⊆ S := fun x hx => hx.2
      have hS₁X : X₁ ∩ S ⊆ X₁ := fun x hx => hx.1
      have hS₂X : X₂ ∩ S ⊆ X₂ := fun x hx => hx.1
      have hS₁block : X₁ ∩ S ⊆ X₁ ∪ {v : V | v ∈ Q₂} := fun x hx => Or.inl hx.1
      have hS₂block : X₂ ∩ S ⊆ X₂ ∪ {v : V | v ∈ Q₁} := fun x hx => Or.inl hx.1
      have hωS₁ : (F.induce (X₁ ∩ S)).cliqueNum ≤ ω := cliqueNum_induce_mono F hS₁S
      have hωS₂ : (F.induce (X₂ ∩ S)).cliqueNum ≤ ω := cliqueNum_induce_mono F hS₂S
      -- the two marker-block interfaces
      have hPX₁ : Disjoint X₁ {v : V | v ∈ Q₂} := by
        rw [Set.disjoint_left]
        intro x hx hx2
        exact Set.disjoint_left.mp hsides hx (hQ₂X₂ x hx2)
      have hPX₂ : Disjoint X₂ {v : V | v ∈ Q₁} := by
        rw [Set.disjoint_left]
        intro x hx hx2
        exact Set.disjoint_left.mp hsides (hQ₁X₁ x hx2) hx
      have ha₂Q : a₂ ∈ Q₂ := PathBasics.head_mem hQ₂.2.1
      have hb₂Q : b₂ ∈ Q₂ := PathBasics.getLast_mem hQ₂.2.2
      have ha₁Q : a₁ ∈ Q₁ := PathBasics.head_mem hQ₁.2.1
      have hb₁Q : b₁ ∈ Q₁ := PathBasics.getLast_mem hQ₁.2.2
      have hpA₁ : ∀ x ∈ X₁, F.Adj a₂ x ↔ x ∈ A₁ := by
        intro x hx
        rw [SimpleGraph.adj_comm, hcross x hx a₂ (hQ₂X₂ a₂ ha₂Q)]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd ((hBmem₂ a₂ ha₂Q).mp h) hab₂
        · intro h
          exact Or.inl ⟨h, ha₂⟩
      have hpB₁ : ∀ x ∈ X₁, F.Adj b₂ x ↔ x ∈ B₁ := by
        intro x hx
        rw [SimpleGraph.adj_comm, hcross x hx b₂ (hQ₂X₂ b₂ hb₂Q)]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd ((hAmem₂ b₂ hb₂Q).mp h).symm hab₂
          · exact h
        · intro h
          exact Or.inr ⟨h, hb₂⟩
      have hpA₂ : ∀ x ∈ X₂, F.Adj a₁ x ↔ x ∈ A₂ := by
        intro x hx
        rw [SimpleGraph.adj_comm, hcross' x hx a₁ (hQ₁X₁ a₁ ha₁Q)]
        constructor
        · rintro (⟨h, -⟩ | ⟨-, h⟩)
          · exact h
          · exact absurd ((hBmem₁ a₁ ha₁Q).mp h) hab₁
        · intro h
          exact Or.inl ⟨h, ha₁⟩
      have hpB₂ : ∀ x ∈ X₂, F.Adj b₁ x ↔ x ∈ B₂ := by
        intro x hx
        rw [SimpleGraph.adj_comm, hcross' x hx b₁ (hQ₁X₁ b₁ hb₁Q)]
        constructor
        · rintro (⟨-, h⟩ | ⟨h, -⟩)
          · exact absurd ((hAmem₁ b₁ hb₁Q).mp h).symm hab₁
          · exact h
        · intro h
          exact Or.inr ⟨h, hb₁⟩
      have hinternal₁ : ∀ v ∈ SPGT.interior Q₂, ∀ x ∈ X₁, ¬ F.Adj v x := by
        intro v hv x hx hadj
        have hvQ : v ∈ Q₂ := PathBasics.interior_subset hv
        have := (hcross x hx v (hQ₂X₂ v hvQ)).mp hadj.symm
        rcases this with ⟨-, h⟩ | ⟨-, h⟩
        · exact hint₂ v hv (Or.inl h)
        · exact hint₂ v hv (Or.inr h)
      have hinternal₂ : ∀ v ∈ SPGT.interior Q₁, ∀ x ∈ X₂, ¬ F.Adj v x := by
        intro v hv x hx hadj
        have hvQ : v ∈ Q₁ := PathBasics.interior_subset hv
        have := (hcross' x hx v (hQ₁X₁ v hvQ)).mp hadj.symm
        rcases this with ⟨-, h⟩ | ⟨-, h⟩
        · exact hint₁ v hv (Or.inl h)
        · exact hint₁ v hv (Or.inr h)
      obtain ⟨hone₁, htwo₁⟩ :=
        PerfectMarkerBlockControlledPaletteColoring F X₁ A₁ B₁ hA₁ hB₁ hAB₁ Q₂ a₂ b₂
          hQ₂ hlen₂ hPX₁ hpA₁ hpB₁ hinternal₁ hblock₁ (X₁ ∩ S) hS₁X ω
      obtain ⟨hone₂, htwo₂⟩ :=
        PerfectMarkerBlockControlledPaletteColoring F X₂ A₂ B₂ hA₂ hB₂ hAB₂ Q₁ a₁ b₁
          hQ₁ hlen₁ hPX₂ hpA₂ hpB₂ hinternal₂ hblock₂ (X₂ ∩ S) hS₂X ω
      -- intersections of the attachments with the side traces
      have hA₁S : A₁ ∩ (X₁ ∩ S) = A₁ ∩ S := by
        ext x
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hA₁ h1, h2⟩
      have hB₁S : B₁ ∩ (X₁ ∩ S) = B₁ ∩ S := by
        ext x
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hB₁ h1, h2⟩
      have hA₂S : A₂ ∩ (X₂ ∩ S) = A₂ ∩ S := by
        ext x
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hA₂ h1, h2⟩
      have hB₂S : B₂ ∩ (X₂ ∩ S) = B₂ ∩ S := by
        ext x
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩; exact ⟨h1, hB₂ h1, h2⟩
      -- the "activity" dichotomy
      by_cases hact : (1 ≤ α₁ ∧ 1 ≤ α₂) ∧ (1 ≤ β₁ ∧ 1 ≤ β₂)
      · obtain ⟨⟨hα₁, hα₂⟩, hβ₁, hβ₂⟩ := hact
        have hbound₁ : (F.induce ((X₁ ∩ S) ∪ {v : V | v ∈ Q₂})).cliqueNum ≤ ω :=
          block_cliqueNum_le F X₁ X₂ A₁ B₁ A₂ B₂ S ω hA₁ hB₁ hAB₁ hcross Q₂ a₂ b₂
            hQ₂ hQ₂X₂ hAmem₂ hBmem₂ hab₂ hαsum hβsum hα₁ hα₂ hβ₂ le_rfl
        have hbound₂ : (F.induce ((X₂ ∩ S) ∪ {v : V | v ∈ Q₁})).cliqueNum ≤ ω :=
          block_cliqueNum_le F X₂ X₁ A₂ B₂ A₁ B₁ S ω hA₂ hB₂ hAB₂ hcross' Q₁ a₁ b₁
            hQ₁ hQ₁X₁ hAmem₁ hBmem₁ hab₁ (by omega) (by omega) hα₂ hα₁ hβ₁ le_rfl
        obtain ⟨col₁, hPA₁, hPB₁, hodd₁, heven₁⟩ := htwo₁ hbound₁
        obtain ⟨col₂, hPA₂, hPB₂, hodd₂, heven₂⟩ := htwo₂ hbound₂
        rw [hA₁S] at hPA₁ hodd₁ heven₁
        rw [hB₁S] at hPB₁ hodd₁ heven₁
        rw [hA₂S] at hPA₂ hodd₂ heven₂
        rw [hB₂S] at hPB₂ hodd₂ heven₂
        obtain ⟨hrel1, hrel2, -, -⟩ :=
          TwoJoinPaletteRelabeling ω
            (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ A₁})
            (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ B₁})
            (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ A₂})
            (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ B₂})
            α₁ β₁ α₂ β₂ hPA₁ hPB₁ hPA₂ hPB₂
        rcases Nat.even_or_odd (SPGT.pathLength Q₂) with hev | hod
        · have hev₁ : Even (SPGT.pathLength Q₁) := by
            rw [Nat.even_iff] at hev ⊢
            omega
          obtain ⟨σ₁, σ₂, hdA, hdB⟩ :=
            hrel2 hαsum hβsum (heven₁ hev) (heven₂ hev₁)
          refine glue_colorings F X₁ X₂ A₁ B₁ A₂ B₂ S ω hpartition hcross
            (recolor σ₁ col₁) (recolor σ₂ col₂) ?_ ?_
          · rw [recolor_image, recolor_image]; exact hdA
          · rw [recolor_image, recolor_image]; exact hdB
        · have hod₁ : Odd (SPGT.pathLength Q₁) := by
            rw [Nat.odd_iff] at hod ⊢
            omega
          obtain ⟨σ₁, σ₂, hdA, hdB⟩ :=
            hrel1 hαsum hβsum (hodd₁ hod) (hodd₂ hod₁)
          refine glue_colorings F X₁ X₂ A₁ B₁ A₂ B₂ S ω hpartition hcross
            (recolor σ₁ col₁) (recolor σ₂ col₂) ?_ ?_
          · rw [recolor_image, recolor_image]; exact hdA
          · rw [recolor_image, recolor_image]; exact hdB
      · -- at most one cross-edge type is active inside `S`
        have hAempty : ¬ (1 ≤ α₁ ∧ 1 ≤ α₂) → (A₁ ∩ S = ∅ ∨ A₂ ∩ S = ∅) := by
          intro h
          by_contra hcon
          push_neg at hcon
          obtain ⟨h1, h2⟩ := hcon
          obtain ⟨x, hx⟩ := h1
          obtain ⟨y, hy⟩ := h2
          exact h ⟨one_le_cliqueNum_of_mem F hx, one_le_cliqueNum_of_mem F hy⟩
        have hBempty : ¬ (1 ≤ β₁ ∧ 1 ≤ β₂) → (B₁ ∩ S = ∅ ∨ B₂ ∩ S = ∅) := by
          intro h
          by_contra hcon
          push_neg at hcon
          obtain ⟨h1, h2⟩ := hcon
          obtain ⟨x, hx⟩ := h1
          obtain ⟨y, hy⟩ := h2
          exact h ⟨one_le_cliqueNum_of_mem F hx, one_le_cliqueNum_of_mem F hy⟩
        by_cases hAa : 1 ≤ α₁ ∧ 1 ≤ α₂
        · -- only the `A` type can be active
          have hBoff : B₁ ∩ S = ∅ ∨ B₂ ∩ S = ∅ := hBempty (fun h => hact ⟨hAa, h⟩)
          obtain ⟨col₁, hPA₁⟩ := hone₁ A₁ (Or.inl rfl) (by rw [hA₁S]; omega) hωS₁
          obtain ⟨col₂, hPA₂⟩ := hone₂ A₂ (Or.inl rfl) (by rw [hA₂S]; omega) hωS₂
          rw [hA₁S] at hPA₁
          rw [hA₂S] at hPA₂
          obtain ⟨-, -, hrel3, -⟩ :=
            TwoJoinPaletteRelabeling ω
              (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ A₁})
              (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ B₁})
              (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ A₂})
              (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ B₂})
              α₁ _ α₂ _ hPA₁ rfl hPA₂ rfl
          obtain ⟨σ₁, σ₂, hdA⟩ := hrel3 hαsum
          refine glue_colorings F X₁ X₂ A₁ B₁ A₂ B₂ S ω hpartition hcross
            (recolor σ₁ col₁) (recolor σ₂ col₂) ?_ ?_
          · rw [recolor_image, recolor_image]; exact hdA
          · rcases hBoff with h | h
            · rw [recolor_image, palette_empty col₁ h]
              simp
            · rw [recolor_image (σ := σ₂), palette_empty col₂ h]
              simp
        · have hAoff : A₁ ∩ S = ∅ ∨ A₂ ∩ S = ∅ := hAempty hAa
          by_cases hBa : 1 ≤ β₁ ∧ 1 ≤ β₂
          · -- only the `B` type can be active
            obtain ⟨col₁, hPB₁⟩ := hone₁ B₁ (Or.inr rfl) (by rw [hB₁S]; omega) hωS₁
            obtain ⟨col₂, hPB₂⟩ := hone₂ B₂ (Or.inr rfl) (by rw [hB₂S]; omega) hωS₂
            rw [hB₁S] at hPB₁
            rw [hB₂S] at hPB₂
            obtain ⟨-, -, -, hrel4⟩ :=
              TwoJoinPaletteRelabeling ω
                (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ A₁})
                (col₁ '' {v : ↥(X₁ ∩ S) | (v : V) ∈ B₁})
                (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ A₂})
                (col₂ '' {v : ↥(X₂ ∩ S) | (v : V) ∈ B₂})
                _ β₁ _ β₂ rfl hPB₁ rfl hPB₂
            obtain ⟨σ₁, σ₂, hdB⟩ := hrel4 hβsum
            refine glue_colorings F X₁ X₂ A₁ B₁ A₂ B₂ S ω hpartition hcross
              (recolor σ₁ col₁) (recolor σ₂ col₂) ?_ ?_
            · rcases hAoff with h | h
              · rw [recolor_image, palette_empty col₁ h]
                simp
              · rw [recolor_image (σ := σ₂), palette_empty col₂ h]
                simp
            · rw [recolor_image, recolor_image]; exact hdB
          · -- no cross-edge type is active
            have hBoff : B₁ ∩ S = ∅ ∨ B₂ ∩ S = ∅ := hBempty hBa
            obtain ⟨col₁⟩ :=
              side_coloring F (X₁ ∪ {v : V | v ∈ Q₂}) (X₁ ∩ S) S hS₁block hS₁S ω
                hblock₁ le_rfl
            obtain ⟨col₂⟩ :=
              side_coloring F (X₂ ∪ {v : V | v ∈ Q₁}) (X₂ ∩ S) S hS₂block hS₂S ω
                hblock₂ le_rfl
            refine glue_colorings F X₁ X₂ A₁ B₁ A₂ B₂ S ω hpartition hcross
              col₁ col₂ ?_ ?_
            · rcases hAoff with h | h
              · rw [palette_empty col₁ h]
                simp
              · rw [palette_empty col₂ h]
                simp
            · rcases hBoff with h | h
              · rw [palette_empty col₁ h]
                simp
              · rw [palette_empty col₂ h]
                simp
    · exact SimpleGraph.cliqueNum_le_chromaticNumber

end Workspace.ProofLemmas
