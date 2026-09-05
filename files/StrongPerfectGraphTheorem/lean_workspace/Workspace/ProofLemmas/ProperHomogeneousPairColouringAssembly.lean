import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.ProperHomogeneousPairInnerGadgetPerfect
import Workspace.ProofLemmas.PerfectWeightedStableCover
import Workspace.ProofLemmas.ProperHomogeneousPairWeightedCliqueProjection
import Workspace.ProofLemmas.MinimumImperfectNotCliqueNumColorable

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Decompositions

private def innerRel {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    (↥(A ∪ B) ⊕ Fin 2) → (↥(A ∪ B) ⊕ Fin 2) → Prop
  | Sum.inl a, Sum.inl b => G.Adj a.1 b.1
  | Sum.inl a, Sum.inr i =>
      (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
  | Sum.inr i, Sum.inl a =>
      (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
  | Sum.inr i, Sum.inr j =>
      (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)

private lemma innerRel_symm {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    Symmetric (innerRel G A B) := by
  rintro (a | i) (b | j)
  · intro h
    exact G.symm h
  · exact id
  · exact id
  · intro h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩

private lemma innerRel_irrefl {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    Std.Irrefl (innerRel G A B) := by
  constructor
  rintro (a | i)
  · exact G.irrefl
  · fin_cases i <;> simp [innerRel]

private def innerGraph {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    SimpleGraph (↥(A ∪ B) ⊕ Fin 2) where
  Adj := innerRel G A B
  symm := innerRel_symm G A B
  loopless := innerRel_irrefl G A B

private def outerRel {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    (↥((A ∪ B)ᶜ) ⊕ Fin 4) → (↥((A ∪ B)ᶜ) ⊕ Fin 4) → Prop
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
      (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)

private lemma outerRel_symm {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    Symmetric (outerRel G A B) := by
  rintro (c | i) (d | j)
  · intro h
    exact G.symm h
  · exact id
  · exact id
  · intro h
    rcases h with h | h | h | h | h | h
    · exact Or.inr (Or.inl ⟨h.2, h.1⟩)
    · exact Or.inl ⟨h.2, h.1⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.2, h.1⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.2, h.1⟩))))

private lemma outerRel_irrefl {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    Std.Irrefl (outerRel G A B) := by
  constructor
  rintro (c | i)
  · exact G.irrefl
  · fin_cases i <;> simp [outerRel]

private def outerGraph {V : Type*} (G : SimpleGraph V) (A B : Set V) :
    SimpleGraph (↥((A ∪ B)ᶜ) ⊕ Fin 4) where
  Adj := outerRel G A B
  symm := outerRel_symm G A B
  loopless := outerRel_irrefl G A B

private lemma subtypeFinset_card_le_induce_cliqueNum
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y X : Set V) (R : Finset ↥Y)
    (hX : ∀ z ∈ R, z.1 ∈ X)
    (hclique : ∀ z ∈ R, ∀ t ∈ R, z ≠ t → G.Adj z.1 t.1) :
    R.card ≤ (G.induce X).cliqueNum := by
  let f : ↥R → ↥X := fun z => ⟨z.1.1, hX z.1 z.2⟩
  let T : Finset ↥X := Finset.univ.image f
  have hf : Function.Injective f := by
    intro z t h
    apply Subtype.ext
    apply Subtype.ext
    change (f z).1 = (f t).1
    exact congrArg Subtype.val h
  have hcard : T.card = R.card := by
    rw [Finset.card_image_of_injective _ hf]
    simp [T]
  have hT : (G.induce X).IsClique (T : Set ↥X) := by
    intro z hz t ht hzt
    simp only [T, Finset.mem_coe, Finset.mem_image, Finset.mem_univ, true_and] at hz ht
    rcases hz with ⟨z', rfl⟩
    rcases ht with ⟨t', rfl⟩
    exact hclique z'.1 z'.2 t'.1 t'.2
      (fun h => hzt (congrArg f (Subtype.ext h)))
  rw [← hcard]
  exact hT.card_le_cliqueNum

/-- A minimum imperfect graph cannot contain a specified proper homogeneous
pair: the inner- and outer-gadget stable covers assemble into a clique-number
colouring of the original graph. -/
theorem ProperHomogeneousPairColouringAssembly
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G)
    (A B : Set V) (hAB : SPGT.IsProperHomogeneousPair G A B) :
    False := by
  classical
  let F := innerGraph G A B
  let H := outerGraph G A B
  have hF : ∀ x y, F.Adj x y ↔
      match x, y with
      | Sum.inl a, Sum.inl b => G.Adj a.1 b.1
      | Sum.inl a, Sum.inr i =>
          (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
      | Sum.inr i, Sum.inl a =>
          (i = 0 ∧ a.1 ∈ A) ∨ (i = 1 ∧ a.1 ∈ B)
      | Sum.inr i, Sum.inr j =>
          (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
    intro x y
    rfl
  have hH : ∀ x y, H.Adj x y ↔
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
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
    intro x y
    rfl
  have hFperfect := ProperHomogeneousPairInnerGadgetPerfect G hG A B hAB F hF
  rcases ProperHomogeneousPairWeightedCliqueProjection G hG A B hAB H hH with
    ⟨k, C, I0, I1, I2, I3, hCQ, hCmax, hk, hCstable, hCocc,
      hCold, hI0, hI1, hI2, hI3, hJr, hJp, hJq⟩
  let p := (G.induce A).cliqueNum
  let q := (G.induce B).cliqueNum
  let r := (G.induce (A ∪ B)).cliqueNum
  let J := I1.card + I2.card + I3.card
  let wF : (↥(A ∪ B) ⊕ Fin 2) → ℕ := fun x =>
    match x with
    | Sum.inl _ => 1
    | Sum.inr i => if i = 0 then I2.card else I1.card
  let cliqueWeightsF : Finset ℕ :=
    (@Finset.filter (Finset (↥(A ∪ B) ⊕ Fin 2))
      (fun Q ↦ F.IsClique (Q : Set (↥(A ∪ B) ⊕ Fin 2)))
      (fun _ ↦ Classical.propDecidable _)
      Finset.univ.powerset).image (fun Q ↦ ∑ z ∈ Q, wF z)
  have hcwF : cliqueWeightsF.Nonempty := by
    refine ⟨0, ?_⟩
    simp only [cliqueWeightsF, Finset.mem_image]
    refine ⟨∅, ?_, by simp⟩
    simp
  let omegaF := cliqueWeightsF.max' hcwF
  have hweight_bound : ∀ Q : Finset (↥(A ∪ B) ⊕ Fin 2),
      F.IsClique (Q : Set (↥(A ∪ B) ⊕ Fin 2)) →
      (∑ z ∈ Q, wF z) ≤ J := by
    intro Q hQ
    let R : Finset ↥(A ∪ B) := Finset.univ.filter fun a => Sum.inl a ∈ Q
    have hRclique : ∀ z ∈ R, ∀ t ∈ R, z ≠ t → G.Adj z.1 t.1 := by
      intro z hz t ht hzt
      have hzQ : Sum.inl z ∈ Q := by simpa [R] using hz
      have htQ : Sum.inl t ∈ Q := by simpa [R] using ht
      exact (hF _ _).mp (hQ hzQ htQ (by simpa using hzt))
    have hsum : (∑ z ∈ Q, wF z) =
        R.card + (if Sum.inr (0 : Fin 2) ∈ Q then I2.card else 0) +
          (if Sum.inr (1 : Fin 2) ∈ Q then I1.card else 0) := by
      classical
      calc
        (∑ z ∈ Q, wF z) =
            ∑ z, if z ∈ Q then wF z else 0 := by simp
        _ = R.card + (if Sum.inr (0 : Fin 2) ∈ Q then I2.card else 0) +
            (if Sum.inr (1 : Fin 2) ∈ Q then I1.card else 0) := by
          rw [Fintype.sum_sum_type]
          simp [R, wF, Fin.sum_univ_two, add_assoc, add_comm, add_left_comm]
    by_cases h0 : Sum.inr (0 : Fin 2) ∈ Q
    · have hRA : ∀ z ∈ R, z.1 ∈ A := by
        intro z hz
        have hzQ : Sum.inl z ∈ Q := by simpa [R] using hz
        have hadj := hQ hzQ h0 (by simp)
        simpa [hF] using hadj
      by_cases h1 : Sum.inr (1 : Fin 2) ∈ Q
      · have hRB : ∀ z ∈ R, z.1 ∈ B := by
          intro z hz
          have hzQ : Sum.inl z ∈ Q := by simpa [R] using hz
          have hadj := hQ hzQ h1 (by simp)
          simpa [hF] using hadj
        have hRempty : R = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro z hz
          exact Set.disjoint_left.mp hAB.1 (hRA z hz) (hRB z hz)
        rw [hsum, if_pos h0, if_pos h1, hRempty]
        simp only [Finset.card_empty, zero_add]
        dsimp [J]
        omega
      · have hRp : R.card ≤ p :=
          subtypeFinset_card_le_induce_cliqueNum G (A ∪ B) A R hRA hRclique
        rw [hsum, if_pos h0, if_neg h1]
        dsimp [J] at hJp ⊢
        omega
    · by_cases h1 : Sum.inr (1 : Fin 2) ∈ Q
      · have hRB : ∀ z ∈ R, z.1 ∈ B := by
          intro z hz
          have hzQ : Sum.inl z ∈ Q := by simpa [R] using hz
          have hadj := hQ hzQ h1 (by simp)
          simpa [hF] using hadj
        have hRq : R.card ≤ q :=
          subtypeFinset_card_le_induce_cliqueNum G (A ∪ B) B R hRB hRclique
        rw [hsum, if_neg h0, if_pos h1]
        dsimp [J] at hJq ⊢
        omega
      · have hRr : R.card ≤ r :=
          subtypeFinset_card_le_induce_cliqueNum G (A ∪ B) (A ∪ B) R
            (by intro z hz; exact z.2) hRclique
        rw [hsum, if_neg h0, if_neg h1]
        dsimp [J] at hJr ⊢
        omega
  have homegaF : omegaF ≤ J := by
    have hm := Finset.max'_mem cliqueWeightsF hcwF
    rcases Finset.mem_image.mp hm with ⟨Q, hQ, hEq⟩
    have hQ' : F.IsClique (Q : Set (↥(A ∪ B) ⊕ Fin 2)) := by
      have ht : Q ∈ Finset.univ.powerset ∧
          F.IsClique (Q : Set (↥(A ∪ B) ⊕ Fin 2)) := by
        simpa only [Finset.mem_filter] using hQ
      exact ht.2
    change cliqueWeightsF.max' hcwF ≤ J
    rw [← hEq]
    exact hweight_bound Q hQ'
  have hcoverF := PerfectWeightedStableCover F wF hFperfect
  change ∃ S : Fin omegaF → Set (↥(A ∪ B) ⊕ Fin 2),
      (∀ i, Set.Pairwise (S i) (fun x y ↦ ¬ F.Adj x y)) ∧
      ∀ z, {i | z ∈ S i}.ncard = wF z at hcoverF
  rcases hcoverF with ⟨S, hSstable, hSocc⟩
  let T1 : Set (Fin omegaF) := {i | Sum.inr (1 : Fin 2) ∈ S i}
  let T2 : Set (Fin omegaF) := {i | Sum.inr (0 : Fin 2) ∈ S i}
  let T3 : Set (Fin omegaF) := (T1 ∪ T2)ᶜ
  have hT1 : T1.ncard = I1.card := by
    simpa [T1, wF] using hSocc (Sum.inr (1 : Fin 2))
  have hT2 : T2.ncard = I2.card := by
    simpa [T2, wF] using hSocc (Sum.inr (0 : Fin 2))
  have hT12 : Disjoint T1 T2 := by
    refine Set.disjoint_left.mpr ?_
    intro i hi1 hi2
    have hnot := hSstable i hi1 hi2 (by simp)
    exact hnot ((hF _ _).mpr (by simp))
  have hT3 : T3.ncard ≤ I3.card := by
    have hparts := Set.ncard_add_ncard_compl (T1 ∪ T2)
    rw [Set.ncard_union_eq hT12, hT1, hT2] at hparts
    simp only [Nat.card_fin] at hparts
    change (T1 ∪ T2)ᶜ.ncard ≤ I3.card
    dsimp [J] at homegaF
    omega
  let U1 : Set (Fin k) := (I1 : Set (Fin k))
  let U2 : Set (Fin k) := (I2 : Set (Fin k))
  let U3 : Set (Fin k) := (I3 : Set (Fin k))
  have he1card : Fintype.card ↥T1 ≤ Fintype.card ↥U1 := by
    simpa [Set.ncard_eq_toFinset_card', U1] using hT1.le
  have he2card : Fintype.card ↥T2 ≤ Fintype.card ↥U2 := by
    simpa [Set.ncard_eq_toFinset_card', U2] using hT2.le
  have he3card : Fintype.card ↥T3 ≤ Fintype.card ↥U3 := by
    simpa [Set.ncard_eq_toFinset_card', U3] using hT3
  let e1 : ↥T1 ↪ ↥U1 := (Fintype.equivFin T1).toEmbedding.trans
    ((Fin.castLEEmb he1card).trans (Fintype.equivFin U1).symm.toEmbedding)
  let e2 : ↥T2 ↪ ↥U2 := (Fintype.equivFin T2).toEmbedding.trans
    ((Fin.castLEEmb he2card).trans (Fintype.equivFin U2).symm.toEmbedding)
  let e3 : ↥T3 ↪ ↥U3 := (Fintype.equivFin T3).toEmbedding.trans
    ((Fin.castLEEmb he3card).trans (Fintype.equivFin U3).symm.toEmbedding)
  have hCold_one : ∀ c : ↥((A ∪ B)ᶜ), ∃ i : Fin k,
      {j : Fin k | Sum.inl c ∈ C j} = {i} := by
    intro c
    exact Set.ncard_eq_one.mp (hCold c)
  choose cIndex hcIndex using hCold_one
  have hSold_one : ∀ a : ↥(A ∪ B), ∃ i : Fin omegaF,
      {j : Fin omegaF | Sum.inl a ∈ S j} = {i} := by
    intro a
    apply Set.ncard_eq_one.mp
    simpa [wF] using hSocc (Sum.inl a)
  choose sIndex hsIndex using hSold_one
  have hc_mem (c : ↥((A ∪ B)ᶜ)) : Sum.inl c ∈ C (cIndex c) := by
    have : cIndex c ∈ ({j : Fin k | Sum.inl c ∈ C j} : Set (Fin k)) := by
      rw [hcIndex c]
      simp
    exact this
  have hc_unique (c : ↥((A ∪ B)ᶜ)) (i : Fin k)
      (hi : Sum.inl c ∈ C i) : i = cIndex c := by
    have : i ∈ ({j : Fin k | Sum.inl c ∈ C j} : Set (Fin k)) := hi
    rw [hcIndex c] at this
    simpa using this
  have hs_mem (a : ↥(A ∪ B)) : Sum.inl a ∈ S (sIndex a) := by
    have : sIndex a ∈ ({j : Fin omegaF | Sum.inl a ∈ S j} : Set (Fin omegaF)) := by
      rw [hsIndex a]
      simp
    exact this
  have hs_unique (a : ↥(A ∪ B)) (i : Fin omegaF)
      (hi : Sum.inl a ∈ S i) : i = sIndex a := by
    have : i ∈ ({j : Fin omegaF | Sum.inl a ∈ S j} : Set (Fin omegaF)) := hi
    rw [hsIndex a] at this
    simpa using this
  let insideColor : ↥(A ∪ B) → Fin k := fun a =>
    if h1 : sIndex a ∈ T1 then (e1 ⟨sIndex a, h1⟩).1
    else if h2 : sIndex a ∈ T2 then (e2 ⟨sIndex a, h2⟩).1
    else (e3 ⟨sIndex a, by simp [T3, h1, h2]⟩).1
  have inside_mem (a : ↥(A ∪ B)) :
      (insideColor a ∈ I1 ∧ sIndex a ∈ T1) ∨
      (insideColor a ∈ I2 ∧ sIndex a ∈ T2) ∨
      (insideColor a ∈ I3 ∧ sIndex a ∈ T3) := by
    by_cases h1 : sIndex a ∈ T1
    · left
      exact ⟨by simpa [insideColor, h1, U1] using (e1 ⟨sIndex a, h1⟩).2, h1⟩
    · by_cases h2 : sIndex a ∈ T2
      · right; left
        exact ⟨by simpa [insideColor, h1, h2, U2] using (e2 ⟨sIndex a, h2⟩).2, h2⟩
      · right; right
        exact ⟨by simpa [insideColor, h1, h2, U3] using
          (e3 ⟨sIndex a, by simp [T3, h1, h2]⟩).2, by simp [T3, h1, h2]⟩
  have hI12 : Disjoint (I1 : Set (Fin k)) (I2 : Set (Fin k)) := by
    refine Set.disjoint_left.mpr ?_
    intro i hi1 hi2
    have h1 := (hI1 i).mp hi1
    have h2 := (hI2 i).mp hi2
    exact h2.1 h1.1
  have hI13 : Disjoint (I1 : Set (Fin k)) (I3 : Set (Fin k)) := by
    refine Set.disjoint_left.mpr ?_
    intro i hi1 hi3
    have h1 := (hI1 i).mp hi1
    have h3 := (hI3 i).mp hi3
    exact h1.2 h3.2
  have hI23 : Disjoint (I2 : Set (Fin k)) (I3 : Set (Fin k)) := by
    refine Set.disjoint_left.mpr ?_
    intro i hi2 hi3
    have h2 := (hI2 i).mp hi2
    have h3 := (hI3 i).mp hi3
    exact h2.1 h3.1
  have inside_injective_on_class {a b : ↥(A ∪ B)}
      (hcol : insideColor a = insideColor b) : sIndex a = sIndex b := by
    rcases inside_mem a with ha | ha | ha <;>
      rcases inside_mem b with hb | hb | hb
    · have hcol' : (e1 ⟨sIndex a, ha.2⟩).1 = (e1 ⟨sIndex b, hb.2⟩).1 := by
        simpa [insideColor, ha.2, hb.2] using hcol
      have hh := e1.injective (Subtype.ext hcol' :
          e1 ⟨sIndex a, ha.2⟩ = e1 ⟨sIndex b, hb.2⟩)
      exact congrArg Subtype.val hh
    · exfalso
      exact Set.disjoint_left.mp hI12 ha.1 (hcol ▸ hb.1)
    · exfalso
      exact Set.disjoint_left.mp hI13 ha.1 (hcol ▸ hb.1)
    · exfalso
      exact Set.disjoint_left.mp hI12 (hcol ▸ hb.1) ha.1
    · have hna : sIndex a ∉ T1 := fun h => Set.disjoint_left.mp hT12 h ha.2
      have hnb : sIndex b ∉ T1 := fun h => Set.disjoint_left.mp hT12 h hb.2
      have hcol' : (e2 ⟨sIndex a, ha.2⟩).1 = (e2 ⟨sIndex b, hb.2⟩).1 := by
        simpa [insideColor, hna, hnb, ha.2, hb.2] using hcol
      have hh := e2.injective (Subtype.ext hcol' :
          e2 ⟨sIndex a, ha.2⟩ = e2 ⟨sIndex b, hb.2⟩)
      exact congrArg Subtype.val hh
    · exfalso
      exact Set.disjoint_left.mp hI23 ha.1 (hcol ▸ hb.1)
    · exfalso
      exact Set.disjoint_left.mp hI13 (hcol ▸ hb.1) ha.1
    · exfalso
      exact Set.disjoint_left.mp hI23 (hcol ▸ hb.1) ha.1
    · have hna : sIndex a ∉ T1 ∧ sIndex a ∉ T2 := by simpa [T3] using ha.2
      have hnb : sIndex b ∉ T1 ∧ sIndex b ∉ T2 := by simpa [T3] using hb.2
      have hcol' : (e3 ⟨sIndex a, ha.2⟩).1 = (e3 ⟨sIndex b, hb.2⟩).1 := by
        simpa [insideColor, hna.1, hna.2, hnb.1, hnb.2] using hcol
      have hh := e3.injective (Subtype.ext hcol' :
          e3 ⟨sIndex a, ha.2⟩ = e3 ⟨sIndex b, hb.2⟩)
      exact congrArg Subtype.val hh
  have hcross {v w : V} (hv : v ∈ A ∪ B) (hw : w ∈ (A ∪ B)ᶜ)
      (hvw : G.Adj v w) (hci : cIndex ⟨w, hw⟩ = insideColor ⟨v, hv⟩) : False := by
        rcases inside_mem ⟨v, hv⟩ with hi | hi | hi
        · have hclass := (hI1 (insideColor ⟨v, hv⟩)).mp hi.1
          have htags := hclass.1
          have hc := hc_mem ⟨w, hw⟩
          rcases htags with ht | ht
          · have hnot := hCstable (insideColor ⟨v, hv⟩)
                (hci ▸ hc) ht (by simp)
            have hncomp : ¬ SPGT.VertexComplete G w A := by
              intro hh
              exact hnot ((hH _ _).mpr (Or.inl ⟨Or.inl rfl, hh⟩))
            have hunif : SPGT.VertexAnticomplete G w A := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x A} ∪
                    {x : V | x ∉ A ∧ SPGT.VertexAnticomplete G x A} := by
                rw [hAB.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hncomp hm).elim
              · exact hm.2
            rcases hv with hvA | hvB
            · exact hunif v hvA hvw.symm
            · have hsTag : Sum.inr (1 : Fin 2) ∈ S (sIndex ⟨v, Or.inr hvB⟩) := hi.2
              have hnotF := hSstable _ (hs_mem ⟨v, Or.inr hvB⟩) hsTag (by simp)
              exact hnotF ((hF _ _).mpr (by simp [hvB]))
          · have hnot := hCstable (insideColor ⟨v, hv⟩)
                (hci ▸ hc) ht (by simp)
            have hncomp : ¬ SPGT.VertexComplete G w A := by
              intro hh
              exact hnot ((hH _ _).mpr (Or.inl ⟨Or.inr rfl, hh⟩))
            have hunif : SPGT.VertexAnticomplete G w A := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x A} ∪
                    {x : V | x ∉ A ∧ SPGT.VertexAnticomplete G x A} := by
                rw [hAB.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hncomp hm).elim
              · exact hm.2
            rcases hv with hvA | hvB
            · exact hunif v hvA hvw.symm
            · have hsTag : Sum.inr (1 : Fin 2) ∈ S (sIndex ⟨v, Or.inr hvB⟩) := hi.2
              have hnotF := hSstable _ (hs_mem ⟨v, Or.inr hvB⟩) hsTag (by simp)
              exact hnotF ((hF _ _).mpr (by simp [hvB]))
        · have hclass := (hI2 (insideColor ⟨v, hv⟩)).mp hi.1
          have htags := hclass.2
          have hc := hc_mem ⟨w, hw⟩
          rcases htags with ht | ht
          · have hnot := hCstable (insideColor ⟨v, hv⟩)
                (hci ▸ hc) ht (by simp)
            have hncomp : ¬ SPGT.VertexComplete G w B := by
              intro hh
              exact hnot ((hH _ _).mpr (Or.inr ⟨Or.inl rfl, hh⟩))
            have hunif : SPGT.VertexAnticomplete G w B := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x B} ∪
                    {x : V | x ∉ B ∧ SPGT.VertexAnticomplete G x B} := by
                rw [hAB.2.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hncomp hm).elim
              · exact hm.2
            rcases hv with hvA | hvB
            · have hsTag : Sum.inr (0 : Fin 2) ∈ S (sIndex ⟨v, Or.inl hvA⟩) := hi.2
              have hnotF := hSstable _ (hs_mem ⟨v, Or.inl hvA⟩) hsTag (by simp)
              exact hnotF ((hF _ _).mpr (by simp [hvA]))
            · exact hunif v hvB hvw.symm
          · have hnot := hCstable (insideColor ⟨v, hv⟩)
                (hci ▸ hc) ht (by simp)
            have hncomp : ¬ SPGT.VertexComplete G w B := by
              intro hh
              exact hnot ((hH _ _).mpr (Or.inr ⟨Or.inr rfl, hh⟩))
            have hunif : SPGT.VertexAnticomplete G w B := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x B} ∪
                    {x : V | x ∉ B ∧ SPGT.VertexAnticomplete G x B} := by
                rw [hAB.2.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hncomp hm).elim
              · exact hm.2
            rcases hv with hvA | hvB
            · have hsTag : Sum.inr (0 : Fin 2) ∈ S (sIndex ⟨v, Or.inl hvA⟩) := hi.2
              have hnotF := hSstable _ (hs_mem ⟨v, Or.inl hvA⟩) hsTag (by simp)
              exact hnotF ((hF _ _).mpr (by simp [hvA]))
            · exact hunif v hvB hvw.symm
        · have hclass := (hI3 (insideColor ⟨v, hv⟩)).mp hi.1
          have hc := hc_mem ⟨w, hw⟩
          rcases hclass.1 with htA | htA <;> rcases hclass.2 with htB | htB
          all_goals
            have hnotA := hCstable (insideColor ⟨v, hv⟩) (hci ▸ hc) htA (by simp)
            have hnotB := hCstable (insideColor ⟨v, hv⟩) (hci ▸ hc) htB (by simp)
            have hnA : ¬ SPGT.VertexComplete G w A := by
              intro hh
              apply hnotA
              apply (hH _ _).mpr
              first | exact Or.inl ⟨Or.inl rfl, hh⟩ | exact Or.inl ⟨Or.inr rfl, hh⟩
            have hnB : ¬ SPGT.VertexComplete G w B := by
              intro hh
              apply hnotB
              apply (hH _ _).mpr
              first | exact Or.inr ⟨Or.inl rfl, hh⟩ | exact Or.inr ⟨Or.inr rfl, hh⟩
            have haAnti : SPGT.VertexAnticomplete G w A := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x A} ∪
                    {x : V | x ∉ A ∧ SPGT.VertexAnticomplete G x A} := by
                rw [hAB.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hnA hm).elim
              · exact hm.2
            have hbAnti : SPGT.VertexAnticomplete G w B := by
              have hm : w ∈ {x : V | SPGT.VertexComplete G x B} ∪
                    {x : V | x ∉ B ∧ SPGT.VertexAnticomplete G x B} := by
                rw [hAB.2.2.2.2.1]
                exact hw
              rcases hm with hm | hm
              · exact (hnB hm).elim
              · exact hm.2
            rcases hv with hvA | hvB
            · exact haAnti v hvA hvw.symm
            · exact hbAnti v hvB hvw.symm
  let color : V → Fin k := fun v =>
    if hv : v ∈ A ∪ B then insideColor ⟨v, hv⟩ else cIndex ⟨v, hv⟩
  have hcolor_valid {v w : V} (hvw : G.Adj v w) : color v ≠ color w := by
    intro heq
    by_cases hv : v ∈ A ∪ B
    · by_cases hw : w ∈ A ∪ B
      · have hinside : insideColor ⟨v, hv⟩ = insideColor ⟨w, hw⟩ := by
          dsimp only [color] at heq
          rw [dif_pos hv, dif_pos hw] at heq
          exact heq
        have hsidx := inside_injective_on_class hinside
        have hne : (⟨v, hv⟩ : ↥(A ∪ B)) ≠ ⟨w, hw⟩ := by
          intro h
          exact G.ne_of_adj hvw (congrArg Subtype.val h)
        have hnot := hSstable (sIndex ⟨v, hv⟩)
          (hs_mem ⟨v, hv⟩) (hsidx ▸ hs_mem ⟨w, hw⟩) (by simpa using hne)
        exact hnot ((hF _ _).mpr hvw)
      · apply hcross hv hw hvw
        dsimp only [color] at heq
        rw [dif_pos hv, dif_neg hw] at heq
        exact heq.symm
    · by_cases hw : w ∈ A ∪ B
      · apply hcross hw hv hvw.symm
        dsimp only [color] at heq
        rw [dif_neg hv, dif_pos hw] at heq
        exact heq
      · have hci : cIndex ⟨v, hv⟩ = cIndex ⟨w, hw⟩ := by
          dsimp only [color] at heq
          rw [dif_neg hv, dif_neg hw] at heq
          exact heq
        have hne : (⟨v, hv⟩ : ↥((A ∪ B)ᶜ)) ≠ ⟨w, hw⟩ := by
          intro h
          exact G.ne_of_adj hvw (congrArg Subtype.val h)
        have hnot := hCstable (cIndex ⟨v, hv⟩)
          (hc_mem ⟨v, hv⟩) (hci ▸ hc_mem ⟨w, hw⟩) (by simpa using hne)
        exact hnot ((hH _ _).mpr hvw)
  apply MinimumImperfectNotCliqueNumColorable.not_colorable_cliqueNum hG
  have hcolk : G.Colorable k := ⟨SimpleGraph.Coloring.mk color hcolor_valid⟩
  exact ⟨G.recolorOfCardLE (by simpa using hk) hcolk.some⟩

end Workspace.ProofLemmas

