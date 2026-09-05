import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.PerfectWeightedStableCover
import Workspace.ProofLemmas.ProperHomogeneousPairOuterGadgetPerfect

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Decompositions

/-- The weighted stable cover of the four-tag outer gadget projects to a
clique-number-sized family for the original graph, and its tag incidences
satisfy the three counting bounds needed by the homogeneous-pair assembly. -/
theorem ProperHomogeneousPairWeightedCliqueProjection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G)
    (A B : Set V) (hAB : SPGT.IsProperHomogeneousPair G A B)
    (H : SimpleGraph (↥((A ∪ B)ᶜ) ⊕ Fin 4))
    (hH : ∀ x y, H.Adj x y ↔
      match x, y with
      | Sum.inl c, Sum.inl d => G.Adj c.1 d.1
      | Sum.inl c, Sum.inr i =>
          (((i = 0 ∨ i = 1) ∧ SPGT.VertexComplete G c.1 A) ∨
            ((i = 2 ∨ i = 3) ∧ SPGT.VertexComplete G c.1 B))
      | Sum.inr i, Sum.inl c =>
          (((i = 0 ∨ i = 1) ∧ SPGT.VertexComplete G c.1 A) ∨
            ((i = 2 ∨ i = 3) ∧ SPGT.VertexComplete G c.1 B))
      | Sum.inr i, Sum.inr j =>
          (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
          (i = 3 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) :
    let p := (G.induce A).cliqueNum
    let q := (G.induce B).cliqueNum
    let r := (G.induce (A ∪ B)).cliqueNum
    let w : (↥((A ∪ B)ᶜ) ⊕ Fin 4) → ℕ := fun x =>
      match x with
      | Sum.inl _ => 1
      | Sum.inr i =>
          if i = 0 then p
          else if i = 1 then r - q
          else if i = 2 then q
          else r - p
    ∃ (k : ℕ)
        (cover : Fin k → Set (↥((A ∪ B)ᶜ) ⊕ Fin 4))
        (I0 I1 I2 I3 : Finset (Fin k)),
      (∀ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
          H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) →
            (∑ x ∈ Q, w x) ≤ k) ∧
      (∃ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
          H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) ∧
            (∑ x ∈ Q, w x) = k) ∧
      k ≤ G.cliqueNum ∧
      (∀ i : Fin k, H.IsIndepSet (cover i)) ∧
      (∀ x : ↥((A ∪ B)ᶜ) ⊕ Fin 4,
          ({i : Fin k | x ∈ cover i} : Set (Fin k)).ncard = w x) ∧
      (∀ c : ↥((A ∪ B)ᶜ),
          ({i : Fin k | Sum.inl c ∈ cover i} : Set (Fin k)).ncard = 1) ∧
      (∀ i : Fin k,
          i ∈ I0 ↔
            ¬ (Sum.inr (0 : Fin 4) ∈ cover i ∨
                Sum.inr (1 : Fin 4) ∈ cover i) ∧
            ¬ (Sum.inr (2 : Fin 4) ∈ cover i ∨
                Sum.inr (3 : Fin 4) ∈ cover i)) ∧
      (∀ i : Fin k,
          i ∈ I1 ↔
            (Sum.inr (0 : Fin 4) ∈ cover i ∨
              Sum.inr (1 : Fin 4) ∈ cover i) ∧
            ¬ (Sum.inr (2 : Fin 4) ∈ cover i ∨
                Sum.inr (3 : Fin 4) ∈ cover i)) ∧
      (∀ i : Fin k,
          i ∈ I2 ↔
            ¬ (Sum.inr (0 : Fin 4) ∈ cover i ∨
                Sum.inr (1 : Fin 4) ∈ cover i) ∧
            (Sum.inr (2 : Fin 4) ∈ cover i ∨
              Sum.inr (3 : Fin 4) ∈ cover i)) ∧
      (∀ i : Fin k,
          i ∈ I3 ↔
            (Sum.inr (0 : Fin 4) ∈ cover i ∨
              Sum.inr (1 : Fin 4) ∈ cover i) ∧
            (Sum.inr (2 : Fin 4) ∈ cover i ∨
              Sum.inr (3 : Fin 4) ∈ cover i)) ∧
      r ≤ I1.card + I2.card + I3.card ∧
      I2.card + p ≤ I1.card + I2.card + I3.card ∧
      I1.card + q ≤ I1.card + I2.card + I3.card := by
  classical
  let p := (G.induce A).cliqueNum
  let q := (G.induce B).cliqueNum
  let r := (G.induce (A ∪ B)).cliqueNum
  let w : (↥((A ∪ B)ᶜ) ⊕ Fin 4) → ℕ := fun x =>
    match x with
    | Sum.inl _ => 1
    | Sum.inr i =>
        if i = 0 then p
        else if i = 1 then r - q
        else if i = 2 then q
        else r - p
  change ∃ (k : ℕ)
      (cover : Fin k → Set (↥((A ∪ B)ᶜ) ⊕ Fin 4))
      (I0 I1 I2 I3 : Finset (Fin k)),
    (∀ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
        H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) →
          (∑ x ∈ Q, w x) ≤ k) ∧
    (∃ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
        H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) ∧
          (∑ x ∈ Q, w x) = k) ∧
    k ≤ G.cliqueNum ∧
    (∀ i : Fin k, H.IsIndepSet (cover i)) ∧
    (∀ x : ↥((A ∪ B)ᶜ) ⊕ Fin 4,
        ({i : Fin k | x ∈ cover i} : Set (Fin k)).ncard = w x) ∧
    (∀ c : ↥((A ∪ B)ᶜ),
        ({i : Fin k | Sum.inl c ∈ cover i} : Set (Fin k)).ncard = 1) ∧
    (∀ i : Fin k, i ∈ I0 ↔
      ¬ (Sum.inr (0 : Fin 4) ∈ cover i ∨ Sum.inr (1 : Fin 4) ∈ cover i) ∧
      ¬ (Sum.inr (2 : Fin 4) ∈ cover i ∨ Sum.inr (3 : Fin 4) ∈ cover i)) ∧
    (∀ i : Fin k, i ∈ I1 ↔
      (Sum.inr (0 : Fin 4) ∈ cover i ∨ Sum.inr (1 : Fin 4) ∈ cover i) ∧
      ¬ (Sum.inr (2 : Fin 4) ∈ cover i ∨ Sum.inr (3 : Fin 4) ∈ cover i)) ∧
    (∀ i : Fin k, i ∈ I2 ↔
      ¬ (Sum.inr (0 : Fin 4) ∈ cover i ∨ Sum.inr (1 : Fin 4) ∈ cover i) ∧
      (Sum.inr (2 : Fin 4) ∈ cover i ∨ Sum.inr (3 : Fin 4) ∈ cover i)) ∧
    (∀ i : Fin k, i ∈ I3 ↔
      (Sum.inr (0 : Fin 4) ∈ cover i ∨ Sum.inr (1 : Fin 4) ∈ cover i) ∧
      (Sum.inr (2 : Fin 4) ∈ cover i ∨ Sum.inr (3 : Fin 4) ∈ cover i)) ∧
    r ≤ I1.card + I2.card + I3.card ∧
    I2.card + p ≤ I1.card + I2.card + I3.card ∧
    I1.card + q ≤ I1.card + I2.card + I3.card
  rcases hAB with
    ⟨hABdisj, hAne, hBne, hAcover, hBcover, hCC, hCA, hAC, hAA⟩
  have hp_le_r : p ≤ r := by
    exact CliqueNumOfInducedSet.cliqueNum_induce_mono G Set.subset_union_left
  have hq_le_r : q ≤ r := by
    exact CliqueNumOfInducedSet.cliqueNum_induce_mono G Set.subset_union_right
  obtain ⟨RAB, hRABsub, hRABclique, hRABcard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G (A ∪ B)
  obtain ⟨RA, hRAsub, hRAclique, hRAcard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G A
  obtain ⟨RB, hRBsub, hRBclique, hRBcard⟩ :=
    CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum G B
  have hr_le_pq : r ≤ p + q := by
    let RA' := RAB.filter (fun x ↦ x ∈ A)
    let RB' := RAB.filter (fun x ↦ x ∈ B)
    have hRA'sub : (↑RA' : Set V) ⊆ A := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hRB'sub : (↑RB' : Set V) ⊆ B := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2
    have hRA'clique : G.IsClique (↑RA' : Set V) :=
      hRABclique.subset (by intro x hx; exact (Finset.mem_filter.mp hx).1)
    have hRB'clique : G.IsClique (↑RB' : Set V) :=
      hRABclique.subset (by intro x hx; exact (Finset.mem_filter.mp hx).1)
    have hRA'le : RA'.card ≤ p := by
      simpa [p] using CliqueNumOfInducedSet.card_le_cliqueNum_induce
        G hRA'sub hRA'clique
    have hRB'le : RB'.card ≤ q := by
      simpa [q] using CliqueNumOfInducedSet.card_le_cliqueNum_induce
        G hRB'sub hRB'clique
    have hdisj : Disjoint RA' RB' := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact Set.disjoint_left.mp hABdisj
        (Finset.mem_filter.mp hxA).2 (Finset.mem_filter.mp hxB).2
    have hunion : RA' ∪ RB' = RAB := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_filter.mp hx).1
        · exact (Finset.mem_filter.mp hx).1
      · intro hx
        rcases hRABsub hx with hxA | hxB
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, hxA⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, hxB⟩)
    dsimp [r, p, q]
    rw [← hRABcard, ← hunion, Finset.card_union_of_disjoint hdisj]
    omega
  let cliqueWeights : Finset ℕ :=
    (@Finset.filter (Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4))
      (fun Q ↦ H.IsClique (Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)))
      (fun _ ↦ Classical.propDecidable _)
      Finset.univ.powerset).image (fun Q ↦ ∑ z ∈ Q, w z)
  let hnonempty : cliqueWeights.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [cliqueWeights, Finset.mem_image]
    refine ⟨∅, ?_, by simp⟩
    simp
  let k := cliqueWeights.max' hnonempty
  have hweight_le_k : ∀ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
      H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) →
        (∑ x ∈ Q, w x) ≤ k := by
    intro Q hQ
    apply Finset.le_max' cliqueWeights
    refine Finset.mem_image.mpr ⟨Q, ?_, rfl⟩
    simpa [cliqueWeights] using hQ
  have hmax_exists : ∃ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
      H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) ∧
        (∑ x ∈ Q, w x) = k := by
    have hm := Finset.max'_mem cliqueWeights hnonempty
    rcases Finset.mem_image.mp hm with ⟨Q, hQ, hQweight⟩
    refine ⟨Q, ?_, ?_⟩
    · have hQ' : Q ∈ Finset.univ.powerset ∧
          H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) := by
        simpa only [Finset.mem_filter] using hQ
      exact hQ'.2
    · exact hQweight
  have hproject_all : ∀ Q : Finset (↥((A ∪ B)ᶜ) ⊕ Fin 4),
      H.IsClique (↑Q : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4)) →
        (∑ x ∈ Q, w x) ≤ G.cliqueNum := by
    intro Q hQ
    let Csub : Finset ↥((A ∪ B)ᶜ) :=
      Finset.univ.filter (fun c ↦ Sum.inl c ∈ Q)
    let valEmb : ↥((A ∪ B)ᶜ) ↪ V :=
      ⟨Subtype.val, Subtype.val_injective⟩
    let Cold : Finset V := Csub.map valEmb
    have hcQ : ∀ {c : ↥((A ∪ B)ᶜ)}, c ∈ Csub → Sum.inl c ∈ Q := by
      intro c hc
      simpa [Csub] using hc
    have hColdcard : Cold.card = Csub.card := by
      simp [Cold]
    have hColdclique : G.IsClique (↑Cold : Set V) := by
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨c, hc, rfl⟩
      rcases Finset.mem_map.mp hy with ⟨d, hd, rfl⟩
      change G.Adj c.1 d.1
      apply (hH (Sum.inl c) (Sum.inl d)).mp
      exact hQ (hcQ hc) (hcQ hd) (by simpa using hxy)
    have hproject (R : Finset V)
        (hRsub : (↑R : Set V) ⊆ A ∪ B)
        (hRclique : G.IsClique (↑R : Set V))
        (hcross : ∀ c ∈ Csub, ∀ a ∈ R, G.Adj c.1 a) :
        Csub.card + R.card ≤ G.cliqueNum := by
      have hdisj : Disjoint Cold R := by
        rw [Finset.disjoint_left]
        intro x hxCold hxR
        rcases Finset.mem_map.mp hxCold with ⟨c, hc, rfl⟩
        exact c.2 (hRsub hxR)
      have hunionClique : G.IsClique (↑(Cold ∪ R) : Set V) := by
        intro x hx y hy hxy
        rcases Finset.mem_union.mp hx with hxC | hxR <;>
          rcases Finset.mem_union.mp hy with hyC | hyR
        · exact hColdclique hxC hyC hxy
        · rcases Finset.mem_map.mp hxC with ⟨c, hc, rfl⟩
          exact hcross c hc y hyR
        · rcases Finset.mem_map.mp hyC with ⟨c, hc, rfl⟩
          exact (hcross c hc x hxR).symm
        · exact hRclique hxR hyR hxy
      have hle := hunionClique.card_le_cliqueNum
      rw [Finset.card_union_of_disjoint hdisj, hColdcard] at hle
      exact hle
    have hcompA :
        (Sum.inr (0 : Fin 4) ∈ Q ∨ Sum.inr (1 : Fin 4) ∈ Q) →
        ∀ c ∈ Csub, SPGT.VertexComplete G c.1 A := by
      intro ht c hc
      rcases ht with h0 | h1
      · have hadj := hQ (hcQ hc) h0 (by simp)
        have hm := (hH (Sum.inl c) (Sum.inr 0)).mp hadj
        simpa using hm
      · have hadj := hQ (hcQ hc) h1 (by simp)
        have hm := (hH (Sum.inl c) (Sum.inr 1)).mp hadj
        simpa using hm
    have hcompB :
        (Sum.inr (2 : Fin 4) ∈ Q ∨ Sum.inr (3 : Fin 4) ∈ Q) →
        ∀ c ∈ Csub, SPGT.VertexComplete G c.1 B := by
      intro ht c hc
      rcases ht with h2 | h3
      · have hadj := hQ (hcQ hc) h2 (by simp)
        have hm := (hH (Sum.inl c) (Sum.inr 2)).mp hadj
        simpa using hm
      · have hadj := hQ (hcQ hc) h3 (by simp)
        have hm := (hH (Sum.inl c) (Sum.inr 3)).mp hadj
        simpa using hm
    have hboundA (ht : Sum.inr (0 : Fin 4) ∈ Q ∨
        Sum.inr (1 : Fin 4) ∈ Q) :
        Csub.card + p ≤ G.cliqueNum := by
      simpa [p, hRAcard] using
        (hproject RA (hRAsub.trans Set.subset_union_left) hRAclique
          (by intro c hc a ha; exact hcompA ht c hc a (hRAsub ha)))
    have hboundB (ht : Sum.inr (2 : Fin 4) ∈ Q ∨
        Sum.inr (3 : Fin 4) ∈ Q) :
        Csub.card + q ≤ G.cliqueNum := by
      simpa [q, hRBcard] using
        (hproject RB (hRBsub.trans Set.subset_union_right) hRBclique
          (by intro c hc b hb; exact hcompB ht c hc b (hRBsub hb)))
    have hboundAB
        (htA : Sum.inr (0 : Fin 4) ∈ Q ∨ Sum.inr (1 : Fin 4) ∈ Q)
        (htB : Sum.inr (2 : Fin 4) ∈ Q ∨ Sum.inr (3 : Fin 4) ∈ Q) :
        Csub.card + r ≤ G.cliqueNum := by
      simpa [r, hRABcard] using (hproject RAB hRABsub hRABclique (by
          intro c hc a ha
          rcases hRABsub ha with haA | haB
          · exact hcompA htA c hc a haA
          · exact hcompB htB c hc a haB))
    have hboundOld : Csub.card ≤ G.cliqueNum := by
      have h := hproject ∅ (by simp) (by simp) (by simp)
      simpa using h
    have hw0 : w (Sum.inr (0 : Fin 4)) = p := by simp [w]
    have hw1 : w (Sum.inr (1 : Fin 4)) = r - q := by simp [w]
    have hw2 : w (Sum.inr (2 : Fin 4)) = q := by simp [w]
    have hw3 : w (Sum.inr (3 : Fin 4)) = r - p := by simp [w]
    have hsum : (∑ x ∈ Q, w x) =
        Csub.card + (if Sum.inr (0 : Fin 4) ∈ Q then p else 0) +
          (if Sum.inr (1 : Fin 4) ∈ Q then r - q else 0) +
          (if Sum.inr (2 : Fin 4) ∈ Q then q else 0) +
          (if Sum.inr (3 : Fin 4) ∈ Q then r - p else 0) := by
      calc
        (∑ x ∈ Q, w x) = ∑ x, if x ∈ Q then w x else 0 := by simp
        _ = Csub.card + (if Sum.inr (0 : Fin 4) ∈ Q then p else 0) +
            (if Sum.inr (1 : Fin 4) ∈ Q then r - q else 0) +
            (if Sum.inr (2 : Fin 4) ∈ Q then q else 0) +
            (if Sum.inr (3 : Fin 4) ∈ Q then r - p else 0) := by
          rw [Fintype.sum_sum_type]
          have hleft : (∑ c : ↥((A ∪ B)ᶜ),
              if Sum.inl c ∈ Q then w (Sum.inl c) else 0) = Csub.card := by
            simp [Csub, w]
          rw [hleft, Fin.sum_univ_four]
          rw [hw0, hw1, hw2, hw3]
          ac_rfl
    have h01 : ¬ (Sum.inr (0 : Fin 4) ∈ Q ∧ Sum.inr (1 : Fin 4) ∈ Q) := by
      rintro ⟨h0, h1⟩
      have hadj := hQ h0 h1 (by simp)
      rw [hH] at hadj
      omega
    have h02 : ¬ (Sum.inr (0 : Fin 4) ∈ Q ∧ Sum.inr (2 : Fin 4) ∈ Q) := by
      rintro ⟨h0, h2⟩
      have hadj := hQ h0 h2 (by simp)
      rw [hH] at hadj
      omega
    have h23 : ¬ (Sum.inr (2 : Fin 4) ∈ Q ∧ Sum.inr (3 : Fin 4) ∈ Q) := by
      rintro ⟨h2, h3⟩
      have hadj := hQ h2 h3 (by simp)
      rw [hH] at hadj
      omega
    by_cases h0 : Sum.inr (0 : Fin 4) ∈ Q
    · have h1 : Sum.inr (1 : Fin 4) ∉ Q := fun h1 ↦ h01 ⟨h0, h1⟩
      have h2 : Sum.inr (2 : Fin 4) ∉ Q := fun h2 ↦ h02 ⟨h0, h2⟩
      by_cases h3 : Sum.inr (3 : Fin 4) ∈ Q
      · have hb := hboundAB (Or.inl h0) (Or.inr h3)
        rw [hsum, if_pos h0, if_neg h1, if_neg h2, if_pos h3]
        omega
      · have hb := hboundA (Or.inl h0)
        rw [hsum, if_pos h0, if_neg h1, if_neg h2, if_neg h3]
        omega
    · by_cases h1 : Sum.inr (1 : Fin 4) ∈ Q
      · by_cases h2 : Sum.inr (2 : Fin 4) ∈ Q
        · have h3 : Sum.inr (3 : Fin 4) ∉ Q := fun h3 ↦ h23 ⟨h2, h3⟩
          have hb := hboundAB (Or.inr h1) (Or.inl h2)
          rw [hsum, if_neg h0, if_pos h1, if_pos h2, if_neg h3]
          omega
        · by_cases h3 : Sum.inr (3 : Fin 4) ∈ Q
          · have hb := hboundAB (Or.inr h1) (Or.inr h3)
            rw [hsum, if_neg h0, if_pos h1, if_neg h2, if_pos h3]
            omega
          · have hb := hboundA (Or.inr h1)
            rw [hsum, if_neg h0, if_pos h1, if_neg h2, if_neg h3]
            omega
      · by_cases h2 : Sum.inr (2 : Fin 4) ∈ Q
        · have h3 : Sum.inr (3 : Fin 4) ∉ Q := fun h3 ↦ h23 ⟨h2, h3⟩
          have hb := hboundB (Or.inl h2)
          rw [hsum, if_neg h0, if_neg h1, if_pos h2, if_neg h3]
          omega
        · by_cases h3 : Sum.inr (3 : Fin 4) ∈ Q
          · have hb := hboundB (Or.inr h3)
            rw [hsum, if_neg h0, if_neg h1, if_neg h2, if_pos h3]
            omega
          · rw [hsum, if_neg h0, if_neg h1, if_neg h2, if_neg h3]
            simpa using hboundOld
  obtain ⟨Qmax, hQmaxClique, hQmaxWeight⟩ := hmax_exists
  have hk_le : k ≤ G.cliqueNum := by
    rw [← hQmaxWeight]
    exact hproject_all Qmax hQmaxClique
  have hHperfect := ProperHomogeneousPairOuterGadgetPerfect G hG A B
    ⟨hABdisj, hAne, hBne, hAcover, hBcover, hCC, hCA, hAC, hAA⟩ H hH
  have hcover := PerfectWeightedStableCover H w hHperfect
  change ∃ cover : Fin k → Set (↥((A ∪ B)ᶜ) ⊕ Fin 4),
      (∀ i, Set.Pairwise (cover i) (fun x y ↦ ¬ H.Adj x y)) ∧
      ∀ x, {i | x ∈ cover i}.ncard = w x at hcover
  rcases hcover with ⟨cover, hstable, hocc⟩
  let first : Fin k → Prop := fun i ↦
    Sum.inr (0 : Fin 4) ∈ cover i ∨ Sum.inr (1 : Fin 4) ∈ cover i
  let second : Fin k → Prop := fun i ↦
    Sum.inr (2 : Fin 4) ∈ cover i ∨ Sum.inr (3 : Fin 4) ∈ cover i
  let I0 := Finset.univ.filter (fun i ↦ ¬ first i ∧ ¬ second i)
  let I1 := Finset.univ.filter (fun i ↦ first i ∧ ¬ second i)
  let I2 := Finset.univ.filter (fun i ↦ ¬ first i ∧ second i)
  let I3 := Finset.univ.filter (fun i ↦ first i ∧ second i)
  have hI0 (i : Fin k) : i ∈ I0 ↔ ¬ first i ∧ ¬ second i := by simp [I0]
  have hI1 (i : Fin k) : i ∈ I1 ↔ first i ∧ ¬ second i := by simp [I1]
  have hI2 (i : Fin k) : i ∈ I2 ↔ ¬ first i ∧ second i := by simp [I2]
  have hI3 (i : Fin k) : i ∈ I3 ↔ first i ∧ second i := by simp [I3]
  have hI13 : Disjoint I1 I3 := by
    rw [Finset.disjoint_left]
    intro i hi1 hi3
    exact (hI1 i).mp hi1 |>.2 ((hI3 i).mp hi3).2
  have hI23 : Disjoint I2 I3 := by
    rw [Finset.disjoint_left]
    intro i hi2 hi3
    exact (hI2 i).mp hi2 |>.1 ((hI3 i).mp hi3).1
  let T0 := Finset.univ.filter
    (fun i : Fin k ↦ Sum.inr (0 : Fin 4) ∈ cover i)
  let T2 := Finset.univ.filter
    (fun i : Fin k ↦ Sum.inr (2 : Fin 4) ∈ cover i)
  let T3 := Finset.univ.filter
    (fun i : Fin k ↦ Sum.inr (3 : Fin 4) ∈ cover i)
  have hT0card : T0.card = p := by
    have h := hocc (Sum.inr (0 : Fin 4))
    simpa [T0, w, Set.ncard_eq_toFinset_card'] using h
  have hT2card : T2.card = q := by
    have h := hocc (Sum.inr (2 : Fin 4))
    simpa [T2, w, Set.ncard_eq_toFinset_card'] using h
  have hT3card : T3.card = r - p := by
    have h := hocc (Sum.inr (3 : Fin 4))
    simpa [T3, w, Set.ncard_eq_toFinset_card'] using h
  have hT0sub : T0 ⊆ I1 ∪ I3 := by
    intro i hi
    have hi0 : Sum.inr (0 : Fin 4) ∈ cover i := by simpa [T0] using hi
    have hfirst : first i := Or.inl hi0
    by_cases hs : second i
    · exact Finset.mem_union_right _ ((hI3 i).mpr ⟨hfirst, hs⟩)
    · exact Finset.mem_union_left _ ((hI1 i).mpr ⟨hfirst, hs⟩)
  have hT2sub : T2 ⊆ I2 ∪ I3 := by
    intro i hi
    have hi2 : Sum.inr (2 : Fin 4) ∈ cover i := by simpa [T2] using hi
    have hsecond : second i := Or.inl hi2
    by_cases hf : first i
    · exact Finset.mem_union_right _ ((hI3 i).mpr ⟨hf, hsecond⟩)
    · exact Finset.mem_union_left _ ((hI2 i).mpr ⟨hf, hsecond⟩)
  have hT3sub : T3 ⊆ I2 := by
    intro i hi
    have hi3 : Sum.inr (3 : Fin 4) ∈ cover i := by simpa [T3] using hi
    have hnfirst : ¬ first i := by
      rintro (hi0 | hi1)
      · have hn := hstable i hi3 hi0 (by simp)
        exact hn ((hH _ _).mpr (by simp))
      · have hn := hstable i hi3 hi1 (by simp)
        exact hn ((hH _ _).mpr (by simp))
    exact (hI2 i).mpr ⟨hnfirst, Or.inr hi3⟩
  have hp_count : p ≤ I1.card + I3.card := by
    have hc := Finset.card_le_card hT0sub
    rw [hT0card, Finset.card_union_of_disjoint hI13] at hc
    exact hc
  have hq_count : q ≤ I2.card + I3.card := by
    have hc := Finset.card_le_card hT2sub
    rw [hT2card, Finset.card_union_of_disjoint hI23] at hc
    exact hc
  have hrp_count : r - p ≤ I2.card := by
    have hc := Finset.card_le_card hT3sub
    rwa [hT3card] at hc
  refine ⟨k, cover, I0, I1, I2, I3, hweight_le_k,
    ⟨Qmax, hQmaxClique, hQmaxWeight⟩, hk_le, hstable, hocc,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c
    simpa [w] using hocc (Sum.inl c)
  · intro i
    simpa [first, second] using hI0 i
  · intro i
    simpa [first, second] using hI1 i
  · intro i
    simpa [first, second] using hI2 i
  · intro i
    simpa [first, second] using hI3 i
  · omega
  · omega
  · omega

end Workspace.ProofLemmas
