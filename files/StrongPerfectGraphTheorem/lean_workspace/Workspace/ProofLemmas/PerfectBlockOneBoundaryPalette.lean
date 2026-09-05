import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.PerfectInducedSubgraph
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.PerfectCliqueBlowup

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas

open Workspace.Types.Core

namespace PerfectBlockOneBoundaryPaletteAux

/-- Perfection is inherited by an induced subgraph on a *subset* of the ambient
vertex set. -/
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

/-- Any proper colouring of `K[T]` uses at least `ω(K[C ∩ T])` colours on `C`. -/
theorem palette_ge {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (T C : Set W) (n : ℕ)
    (col : (K.induce T).Coloring (Fin n)) :
    (K.induce (C ∩ T)).cliqueNum ≤ (col '' {v : T | (v : W) ∈ C}).ncard := by
  classical
  obtain ⟨Q, hQsub, hQclique, hQcard⟩ :=
    Workspace.ProofLemmas.CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K (C ∩ T)
  set Q' : Finset ↥T :=
    Q.attach.map ⟨fun a => ⟨a.1, (hQsub (Finset.mem_coe.mpr a.2)).2⟩,
      by intro a b hab; exact Subtype.ext (by simpa using hab)⟩ with hQ'
  have hcard' : Q'.card = Q.card := by rw [hQ', Finset.card_map, Finset.card_attach]
  have hmem : ∀ a : ↥T, a ∈ (↑Q' : Set ↥T) → (a : W) ∈ (↑Q : Set W) := by
    intro a ha
    simp only [hQ', Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe, Finset.mem_attach] at ha
    obtain ⟨x, -, rfl⟩ := ha
    exact Finset.mem_coe.mpr x.2
  have hsub : (↑Q' : Set ↥T) ⊆ {v : T | (v : W) ∈ C} := by
    intro a ha
    exact (hQsub (hmem a ha)).1
  have hinj : Set.InjOn col (↑Q' : Set ↥T) := by
    intro a ha b hb hcol
    by_contra hne
    have hne' : (a : W) ≠ (b : W) := fun h => hne (Subtype.ext h)
    have hadj : (K.induce T).Adj a b := hQclique (hmem a ha) (hmem b hb) hne'
    exact col.valid hadj hcol
  calc (K.induce (C ∩ T)).cliqueNum = Q.card := hQcard.symm
    _ = Q'.card := hcard'.symm
    _ = (col '' (↑Q' : Set ↥T)).ncard := by
        rw [Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]
    _ ≤ (col '' {v : T | (v : W) ∈ C}).ncard :=
        Set.ncard_le_ncard (Set.image_mono hsub) (Set.toFinite _)

end PerfectBlockOneBoundaryPaletteAux

open PerfectBlockOneBoundaryPaletteAux

/-- **§6, one-boundary controlled coloring.**  In a perfect marker-path block, for
either boundary set `C ∈ {A, B}` there is a proper `n`-coloring of the side `K[T]`
whose palette on `C ∩ T` has cardinality exactly `ω(K[C ∩ T])`. -/
theorem PerfectBlockOneBoundaryPalette
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (X A B : Set W)
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (P : List W) (pA pB : W)
    (hP : SPGT.IsPathFrom K P pA pB)
    (hPpos : 1 ≤ SPGT.pathLength P)
    (hPX : Disjoint X {v : W | v ∈ P})
    (hpA : ∀ x ∈ X, K.Adj pA x ↔ x ∈ A)
    (hpB : ∀ x ∈ X, K.Adj pB x ↔ x ∈ B)
    (hinternal : ∀ v ∈ SPGT.interior P, ∀ x ∈ X, ¬ K.Adj v x)
    (hperfect : SPGT.IsPerfect (K.induce (X ∪ {v : W | v ∈ P})))
    (T : Set W) (hT : T ⊆ X) (n : ℕ)
    (C : Set W) (hC : C = A ∨ C = B)
    (hc : (K.induce (C ∩ T)).cliqueNum ≤ n)
    (hTn : (K.induce T).cliqueNum ≤ n) :
    ∃ col : (K.induce T).Coloring (Fin n),
      (col '' {v : T | (v : W) ∈ C}).ncard = (K.induce (C ∩ T)).cliqueNum := by
  classical
  -- the marker endpoint matching `C`
  obtain ⟨z, hzP, hzC⟩ : ∃ z : W, z ∈ P ∧ ∀ x ∈ T, K.Adj z x ↔ x ∈ C := by
    rcases hC with rfl | rfl
    · exact ⟨pA, (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP).1,
        fun x hx => hpA x (hT hx)⟩
    · exact ⟨pB, (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP).2,
        fun x hx => hpB x (hT hx)⟩
  have hzT : z ∉ T := fun h => (Set.disjoint_left.mp hPX (hT h)) hzP
  have hsubTz : T ∪ {z} ⊆ X ∪ {v : W | v ∈ P} := by
    intro x hx
    rcases hx with hx | hx
    · exact Or.inl (hT hx)
    · exact Or.inr (by simpa [Set.mem_singleton_iff] using hx ▸ hzP)
  have hperfTz : SPGT.IsPerfect (K.induce (T ∪ {z})) :=
    perfect_induce_subset K (X ∪ {v : W | v ∈ P}) (T ∪ {z}) hsubTz hperfect
  have hperfT : SPGT.IsPerfect (K.induce T) :=
    perfect_induce_subset K (X ∪ {v : W | v ∈ P}) T
      (fun x hx => Or.inl (hT hx)) hperfect
  set c : ℕ := (K.induce (C ∩ T)).cliqueNum with hcdef
  rcases eq_or_lt_of_le hc with hceq | hclt
  · -- degenerate branch `c = n`
    haveI : Fintype ↥T := Fintype.ofFinite ↥T
    obtain ⟨col⟩ : (K.induce T).Colorable n :=
      SimpleGraph.Colorable.mono hTn
        (Workspace.ProofLemmas.CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect
          (K.induce T) hperfT)
    refine ⟨col, le_antisymm ?_ (palette_ge K T C n col)⟩
    have hle : (col '' {v : T | (v : W) ∈ C}).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega
  · -- main branch `c < n`: blow `z` up into a clique of `n - c` twins
    have hzz : z ∈ T ∪ {z} := Or.inr rfl
    obtain ⟨W', hFin, hDec, K', Z, ζ, hinj, hdisj, hcover, hncard, hZclique,
      hζadj, hZadj, hperf⟩ :=
      Workspace.ProofLemmas.PerfectCliqueBlowup.exists_blowup
        (K.induce (T ∪ {z})) (⟨z, hzz⟩ : ↥(T ∪ {z})) (n := n - c) (by omega)
    letI : Fintype W' := hFin
    letI : DecidableEq W' := hDec
    -- `z ∉ T`, so the off-`Z` part of `K'` is a copy of `K[T]`
    have hne : ∀ t : ↥T, (⟨(t : W), Or.inl t.2⟩ : ↥(T ∪ {z})) ≠ ⟨z, hzz⟩ := by
      intro t h
      have h2 : (t : W) = z := congrArg Subtype.val h
      apply hzT
      rw [← h2]
      exact t.2
    set η : ↥T → W' := fun t => ζ ⟨⟨(t : W), Or.inl t.2⟩, hne t⟩ with hηdef
    have hηadj : ∀ s t : ↥T, K'.Adj (η s) (η t) ↔ K.Adj (s : W) (t : W) := by
      intro s t
      exact hζadj _ _
    have hηinj : Function.Injective η := by
      intro s t h
      have h0 := hinj h
      have h1 : (⟨(s : W), Or.inl s.2⟩ : ↥(T ∪ {z})) = ⟨(t : W), Or.inl t.2⟩ :=
        congrArg Subtype.val h0
      have h2 : (s : W) = (t : W) := congrArg (fun u : ↥(T ∪ {z}) => (u : W)) h1
      exact Subtype.ext h2
    have hηnotZ : ∀ t : ↥T, η t ∉ Z := by
      intro t
      exact Set.disjoint_left.mp hdisj ⟨_, rfl⟩
    have hηsurj : ∀ w : W', w ∉ Z → ∃ t : ↥T, η t = w := by
      intro w hw
      have hmem : w ∈ Set.range ζ ∪ Z := hcover ▸ Set.mem_univ w
      rcases hmem with ⟨a, rfl⟩ | h
      · have hne' : (a : ↥(T ∪ {z})).1 ≠ z := by
          intro h
          exact a.2 (Subtype.ext h)
        have hinT : ((a : ↥(T ∪ {z})) : W) ∈ T := by
          rcases (a : ↥(T ∪ {z})).2 with h | h
          · exact h
          · exact absurd h hne'
        refine ⟨⟨_, hinT⟩, ?_⟩
        exact congrArg ζ (Subtype.ext (Subtype.ext rfl))
      · exact absurd h hw
    have hZη : ∀ w ∈ Z, ∀ t : ↥T, (K'.Adj w (η t) ↔ (t : W) ∈ C) := by
      intro w hw t
      rw [hZadj w hw _]
      exact hzC (t : W) t.2
    -- `ω(K') ≤ n`
    have hZncard : Z.ncard = n - c := hncard
    have hK'ω : K'.cliqueNum ≤ n := by
      obtain ⟨Q, hQ⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := K')
      have hQclique : K'.IsClique (↑Q : Set W') := hQ.1
      have hQcard : Q.card = K'.cliqueNum := hQ.2
      set QZ : Finset W' := Q.filter (fun w => w ∈ Z) with hQZ
      set QT : Finset W' := Q.filter (fun w => w ∉ Z) with hQT
      have hsplit : QZ.card + QT.card = Q.card :=
        Finset.filter_card_add_filter_neg_card_eq_card _
      -- the `T`-part
      set TQ : Finset ↥T := Finset.univ.filter (fun t => η t ∈ Q) with hTQ
      have himg : TQ.image η = QT := by
        ext w
        simp only [hTQ, hQT, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨t, ht, rfl⟩
          exact ⟨ht, hηnotZ t⟩
        · rintro ⟨hwQ, hwZ⟩
          obtain ⟨t, rfl⟩ := hηsurj w hwZ
          exact ⟨t, hwQ, rfl⟩
      have hTQcard : TQ.card = QT.card := by
        rw [← himg, Finset.card_image_of_injective _ hηinj]
      set QW : Finset W := TQ.image (Subtype.val : ↥T → W) with hQW
      have hQWiff : ∀ x : W, x ∈ QW ↔ ∃ t : ↥T, t ∈ TQ ∧ (t : W) = x := by
        intro x
        rw [hQW, Finset.mem_image]
      have hQWcard : QW.card = TQ.card := by
        rw [hQW]
        exact Finset.card_image_of_injective TQ Subtype.val_injective
      have hQWmem : ∀ t : ↥T, t ∈ TQ → η t ∈ Q := by
        intro t ht
        rw [hTQ, Finset.mem_filter] at ht
        exact ht.2
      have hQWT : (↑QW : Set W) ⊆ T := by
        intro x hx
        obtain ⟨t, -, rfl⟩ := (hQWiff x).mp (Finset.mem_coe.mp hx)
        exact t.2
      have hQWclique : K.IsClique (↑QW : Set W) := by
        rintro x hx y hy hxy
        obtain ⟨s, hs, rfl⟩ := (hQWiff x).mp (Finset.mem_coe.mp hx)
        obtain ⟨t, ht, rfl⟩ := (hQWiff y).mp (Finset.mem_coe.mp hy)
        have hst : η s ≠ η t := fun h => hxy (congrArg Subtype.val (hηinj h))
        have := hQclique (Finset.mem_coe.mpr (hQWmem s hs))
          (Finset.mem_coe.mpr (hQWmem t ht)) hst
        exact (hηadj s t).mp this
      rcases Finset.eq_empty_or_nonempty QZ with hQZe | ⟨w0, hw0⟩
      · -- no vertex of `Z` in the clique
        have h1 : Q.card = QT.card := by rw [← hsplit, hQZe, Finset.card_empty]; omega
        have h2 : QW.card ≤ (K.induce T).cliqueNum :=
          Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce K hQWT hQWclique
        omega
      · -- the clique meets `Z`, so its `T`-part lies inside `C`
        rw [hQZ, Finset.mem_filter] at hw0
        have hw0Q : w0 ∈ Q := hw0.1
        have hw0Z : w0 ∈ Z := hw0.2
        have hQWC : (↑QW : Set W) ⊆ C ∩ T := by
          intro x hx
          refine ⟨?_, hQWT hx⟩
          obtain ⟨t, ht, rfl⟩ := (hQWiff x).mp (Finset.mem_coe.mp hx)
          have hnew : η t ≠ w0 := fun h => (hηnotZ t) (h ▸ hw0Z)
          have hadj : K'.Adj w0 (η t) :=
            hQclique (Finset.mem_coe.mpr hw0Q)
              (Finset.mem_coe.mpr (hQWmem t ht)) (fun h => hnew h.symm)
          exact (hZη w0 hw0Z t).mp hadj
        have h2 : QW.card ≤ c :=
          Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce K hQWC hQWclique
        have h3 : QZ.card ≤ n - c := by
          have hsub : (↑QZ : Set W') ⊆ Z := by
            intro x hx
            simpa [hQZ] using (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2
          have := Set.ncard_le_ncard hsub (Set.toFinite _)
          rwa [Set.ncard_coe_finset, hZncard] at this
        omega
    -- perfection of `K'` supplies an `n`-colouring
    have hK'perf : SPGT.IsPerfect K' := hperf hperfTz
    obtain ⟨col'⟩ : K'.Colorable n :=
      SimpleGraph.Colorable.mono hK'ω
        (Workspace.ProofLemmas.CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect K' hK'perf)
    refine ⟨SimpleGraph.Coloring.mk (fun t => col' (η t))
      (fun {s t} h => col'.valid ((hηadj s t).mpr h)), ?_⟩
    set col : (K.induce T).Coloring (Fin n) :=
      SimpleGraph.Coloring.mk (fun t => col' (η t))
        (fun {s t} h => col'.valid ((hηadj s t).mpr h)) with hcol
    refine le_antisymm ?_ (palette_ge K T C n col)
    -- the palette on `C` is disjoint from the `Z`-palette, which has `n - c` colours
    have hZCcard : (col' '' Z).ncard = n - c := by
      rw [Set.ncard_image_of_injOn, hZncard]
      intro a ha b hb hab
      by_contra hne'
      exact col'.valid (hZclique ha hb hne') hab
    have hdisj2 : Disjoint (col '' {v : T | (v : W) ∈ C}) (col' '' Z) := by
      rw [Set.disjoint_left]
      rintro x ⟨v, hv, rfl⟩ ⟨w, hw, hxw⟩
      have hadj : K'.Adj w (η v) := (hZη w hw v).mpr hv
      exact col'.valid hadj (by simpa [hcol] using hxw)
    have hun : (col '' {v : T | (v : W) ∈ C}).ncard + (col' '' Z).ncard
        = ((col '' {v : T | (v : W) ∈ C}) ∪ (col' '' Z)).ncard :=
      (Set.ncard_union_eq hdisj2 (Set.toFinite _) (Set.toFinite _)).symm
    have hle : ((col '' {v : T | (v : W) ∈ C}) ∪ (col' '' Z)).ncard
        ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
    omega

end Workspace.ProofLemmas
