import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Prisms.SPGT

private def ninePrismAdj (p q : Fin 3 × Fin 3) : Prop :=
  if p.1 = q.1 then ((p.2 : ℕ) + 1 = (q.2 : ℕ) ∨ (q.2 : ℕ) + 1 = (p.2 : ℕ))
  else (((p.2 : ℕ) = 0 ∧ (q.2 : ℕ) = 0) ∨ ((p.2 : ℕ) = 2 ∧ (q.2 : ℕ) = 2))

private instance : DecidableRel ninePrismAdj := fun p q => by
  unfold ninePrismAdj
  infer_instance

private def ninePrism : SimpleGraph (Fin 3 × Fin 3) where
  Adj := ninePrismAdj
  symm := by
    intro p q h
    unfold ninePrismAdj at h ⊢
    split_ifs at h ⊢ with h1 h2
    · omega
    · exact absurd h1.symm h2
    · tauto
    · tauto
  loopless := ⟨by decide⟩

private instance : DecidableRel ninePrism.Adj := inferInstanceAs (DecidableRel ninePrismAdj)

private theorem ninePrismBounds (U : Set (Fin 3 × Fin 3)) (hU : U.ncard = 8) :
    ({w : U |
      letI : Fintype (((ninePrism : SimpleGraph (Fin 3 × Fin 3)).induce U).neighborSet w) :=
        Fintype.ofFinite _
      ((ninePrism : SimpleGraph (Fin 3 × Fin 3)).induce U).degree w = 3}).ncard ≤ 4 ∧
    ∀ w : U,
      letI : Fintype ((((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).induce U).neighborSet w) :=
        Fintype.ofFinite _
      4 ≤ (((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).induce U).degree w := by
  classical
  have hcomp : Uᶜ.ncard = 1 := by
    rw [Set.ncard_compl, hU, Nat.card_eq_fintype_card]
    norm_num
  obtain ⟨z, hz⟩ := Set.ncard_eq_one.mp hcomp
  have hUeq : U = {x : Fin 3 × Fin 3 | x ≠ z} := by
    ext x
    have hx := Set.ext_iff.mp (congrArg (fun S : Set (Fin 3 × Fin 3) => Sᶜ) hz) x
    simpa using hx
  cases hUeq
  letI : Fintype {x : Fin 3 × Fin 3 | x ≠ z} :=
    Fintype.ofFinset (Finset.univ.erase z) (by
      intro x
      simp)
  let J : SimpleGraph {x : Fin 3 × Fin 3 | x ≠ z} :=
    (ninePrism : SimpleGraph (Fin 3 × Fin 3)).induce {x : Fin 3 × Fin 3 | x ≠ z}
  let F : Finset {x : Fin 3 × Fin 3 | x ≠ z} := Finset.univ.filter fun q =>
    (J.neighborFinset q).card = 3
  have hF : F.card ≤ 4 := by
    rcases z with ⟨i, j⟩
    fin_cases i <;> fin_cases j <;> decide
  have hFset :
      ({w : {x : Fin 3 × Fin 3 | x ≠ z} |
        letI : Fintype (J.neighborSet w) := Fintype.ofFinite _
        J.degree w = 3}) = ↑F := by
    ext w
    change (@SimpleGraph.degree _ J w (Fintype.ofFinite _) = 3) ↔ w ∈ F
    let F' : Fintype (J.neighborSet w) := inferInstance
    rw [show @SimpleGraph.degree _ J w (Fintype.ofFinite _) = @SimpleGraph.degree _ J w F' by
      calc
        @SimpleGraph.degree _ J w (Fintype.ofFinite _) = @Fintype.card (J.neighborSet w) (Fintype.ofFinite _) :=
          (@SimpleGraph.card_neighborSet_eq_degree _ J w (Fintype.ofFinite _)).symm
        _ = @Fintype.card (J.neighborSet w) F' :=
          @Fintype.card_congr (J.neighborSet w) (J.neighborSet w) (Fintype.ofFinite _) F' (Equiv.refl _)
        _ = @SimpleGraph.degree _ J w F' := @SimpleGraph.card_neighborSet_eq_degree _ J w F']
    change (@SimpleGraph.degree _ J w F' = 3) ↔ w ∈ F
    change (@SimpleGraph.degree _ J w F' = 3) ↔ w ∈ Finset.univ.filter (fun q => (J.neighborFinset q).card = 3)
    rw [← @SimpleGraph.card_neighborFinset_eq_degree _ J w F']
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rw [hFset, Set.ncard_coe_finset]
    exact hF
  · intro w
    let JC : SimpleGraph {x : Fin 3 × Fin 3 | x ≠ z} :=
      ((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).induce {x : Fin 3 × Fin 3 | x ≠ z}
    let K : Finset {x : Fin 3 × Fin 3 | x ≠ z} := Finset.univ.filter fun q =>
      4 ≤ (JC.neighborFinset q).card
    have hK : K = Finset.univ := by
      rcases z with ⟨i, j⟩
      fin_cases i <;> fin_cases j <;> decide
    let F' : Fintype (JC.neighborSet w) := inferInstance
    have hneigh : 4 ≤ (@SimpleGraph.neighborFinset _ JC w F').card := by
      have hmem : w ∈ K := by
        rw [hK]
        exact Finset.mem_univ w
      change w ∈ Finset.univ.filter (fun q => 4 ≤ (JC.neighborFinset q).card) at hmem
      exact (Finset.mem_filter.mp hmem).2
    have hdegree : 4 ≤ @SimpleGraph.degree _ JC w F' := by
      simpa only [← @SimpleGraph.card_neighborFinset_eq_degree _ JC w F'] using hneigh
    rw [show (((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).induce {x : Fin 3 × Fin 3 | x ≠ z}) = JC from rfl]
    rw [show @SimpleGraph.degree _ JC w (Fintype.ofFinite _) = @SimpleGraph.degree _ JC w F' by
      calc
        @SimpleGraph.degree _ JC w (Fintype.ofFinite _) = @Fintype.card (JC.neighborSet w) (Fintype.ofFinite _) :=
          (@SimpleGraph.card_neighborSet_eq_degree _ JC w (Fintype.ofFinite _)).symm
        _ = @Fintype.card (JC.neighborSet w) F' :=
          @Fintype.card_congr (JC.neighborSet w) (JC.neighborSet w) (Fintype.ofFinite _) F' (Equiv.refl _)
        _ = @SimpleGraph.degree _ JC w F' := @SimpleGraph.card_neighborSet_eq_degree _ JC w F']
    exact hdegree

theorem SpanningNineVertexEvenPrismHasInducedDegreeBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V)
    (hcard : Fintype.card V = 9)
    (hprism : ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V),
      IsEvenPrism H a b P₁ P₂ P₃ ∧
        {v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ P₃} = Set.univ) :
    ∀ W : Set V, W.ncard = 8 →
      ({w : W |
        letI : Fintype ((H.induce W).neighborSet w) := Fintype.ofFinite _
        (H.induce W).degree w = 3}).ncard ≤ 4 ∧
      ∀ w : W,
        letI : Fintype (((Hᶜ).induce W).neighborSet w) := Fintype.ofFinite _
        4 ≤ ((Hᶜ).induce W).degree w := by
  classical
  rcases hprism with ⟨a, b, P₁, P₂, P₃, heven, hcover⟩
  rcases heven with ⟨hform, hev1, hev2, hev3⟩
  have hform0 := hform
  rcases hform with ⟨hAA, hBB, hAB, hp1, hp2, hp3, e12, e13, e23⟩
  have flipc : ∀ (P Q : List V) (x y z t : V),
      (∀ u ∈ P, ∀ v ∈ Q, (H.Adj u v ↔ (u = x ∧ v = y) ∨ (u = z ∧ v = t))) →
      ∀ u ∈ Q, ∀ v ∈ P, (H.Adj u v ↔ (u = y ∧ v = x) ∨ (u = t ∧ v = z)) := by
    intro P Q x y z t e u hu v hv
    rw [SimpleGraph.adj_comm, e v hv u hu]
    tauto
  obtain ⟨R, hR0, hR1, hR2⟩ : ∃ R : Fin 3 → List V, R 0 = P₁ ∧ R 1 = P₂ ∧ R 2 = P₃ :=
    ⟨![P₁, P₂, P₃], by simp, by simp, by simp⟩
  have hpath : ∀ i : Fin 3, Workspace.Types.Core.SPGT.IsPathFrom H (R i) (a i) (b i) := by
    intro i
    fin_cases i
    · simpa [hR0] using HyperprismFromPrism.formPrism_path (R := ![P₁, P₂, P₃]) hform0 (0 : Fin 3)
    · simpa [hR1] using HyperprismFromPrism.formPrism_path (R := ![P₁, P₂, P₃]) hform0 (1 : Fin 3)
    · simpa [hR2] using HyperprismFromPrism.formPrism_path (R := ![P₁, P₂, P₃]) hform0 (2 : Fin 3)
  have hev : ∀ i : Fin 3, Even (Workspace.Types.Core.SPGT.pathLength (R i)) := by
    intro i
    fin_cases i
    · simpa [hR0] using hev1
    · simpa [hR1] using hev2
    · simpa [hR2] using hev3
  have hcross : ∀ i j : Fin 3, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j,
      (H.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [hR0, hR1] using e12
    · simpa [hR0, hR2] using e13
    · simpa [hR0, hR1] using flipc P₁ P₂ (a 0) (a 1) (b 0) (b 1) e12
    · exact absurd rfl hij
    · simpa [hR1, hR2] using e23
    · simpa [hR0, hR2] using flipc P₁ P₃ (a 0) (a 2) (b 0) (b 2) e13
    · simpa [hR1, hR2] using flipc P₂ P₃ (a 1) (a 2) (b 1) (b 2) e23
    · exact absurd rfl hij
  have hcov : ∀ v : V, ∃ i : Fin 3, v ∈ R i := by
    intro v
    have hmem : v ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ P₃} : Set V) := by
      rw [hcover]
      trivial
    rcases hmem with (hm | hm) | hm
    · exact ⟨0, by rw [hR0]; exact hm⟩
    · exact ⟨1, by rw [hR1]; exact hm⟩
    · exact ⟨2, by rw [hR2]; exact hm⟩
  have hne2 : ∀ i : Fin 3, 2 ≤ (R i).length := by
    intro i
    by_contra hc
    have hpos : 0 < (R i).length := PathBasics.path_length_pos (hpath i).1
    have hl1 : (R i).length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
    have h2 := (hpath i).2.1
    have h3 := (hpath i).2.2
    rw [hx] at h2 h3
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h2 h3
    exact hAB i i (h2.symm.trans h3)
  have hdisj : ∀ (i j : Fin 3), i ≠ j → ∀ u ∈ R i, u ∉ R j := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [hR0, hR1] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (0 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    · simpa [hR0, hR2] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    · simpa [hR0, hR1] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (1 : Fin 3)) (j := (0 : Fin 3)) (by decide)
    · exact absurd rfl hij
    · simpa [hR1, hR2] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (1 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    · simpa [hR0, hR2] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (2 : Fin 3)) (j := (0 : Fin 3)) (by decide)
    · simpa [hR1, hR2] using HyperprismFromPrism.formPrism_disjoint (R := ![P₁, P₂, P₃]) hform0 (i := (2 : Fin 3)) (j := (1 : Fin 3)) (by decide)
    · exact absurd rfl hij
  have hge3 : ∀ i : Fin 3, 3 ≤ (R i).length := by
    intro i
    have h2 := hne2 i
    have hE := hev i
    rw [PathBasics.pathLength_eq, Nat.even_iff] at hE
    omega
  have hnodupL : (R 0 ++ R 1 ++ R 2).Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨(hpath 0).1.2.1, (hpath 1).1.2.1, ?_⟩, (hpath 2).1.2.1, ?_⟩
    · intro x hx y hy hxy
      exact hdisj 0 1 (by decide) x hx (hxy ▸ hy)
    · intro x hx y hy hxy
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hdisj 0 2 (by decide) x hx' (hxy ▸ hy)
      · exact hdisj 1 2 (by decide) x hx' (hxy ▸ hy)
  have hmemL : ∀ v : V, v ∈ R 0 ++ R 1 ++ R 2 := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    fin_cases i
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (by simpa using hi))))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (by simpa using hi))))
    · exact List.mem_append.mpr (Or.inr (by simpa using hi))
  have hlenL : (R 0 ++ R 1 ++ R 2).length = 9 := by
    have hu : (R 0 ++ R 1 ++ R 2).toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (hmemL v)
    have hc := List.toFinset_card_of_nodup hnodupL
    rw [hu, Finset.card_univ, hcard] at hc
    omega
  have hsum : (R 0).length + (R 1).length + (R 2).length = 9 := by
    simp only [List.length_append] at hlenL
    omega
  have hL0 : (R 0).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hL1 : (R 1).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hL2 : (R 2).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hlen3 : ∀ i : Fin 3, (R i).length = 3 := by
    intro i
    fin_cases i
    · simpa using hL0
    · simpa using hL1
    · simpa using hL2
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 × Fin 3 → V,
      ∀ (i k : Fin 3), w (i, k) = (R i)[(k : ℕ)]'(by rw [hlen3]; exact k.isLt) :=
    ⟨fun p => (R p.1).getD (p.2 : ℕ) (a 0), by
      intro i k
      exact List.getD_eq_getElem _ _ _⟩
  have hend0 : ∀ i : Fin 3, (R i)[(0 : ℕ)]'(by rw [hlen3]; omega) = a i := fun i =>
    PathBasics.getElem_zero_of_head? (hpath i).2.1 _
  have hend2 : ∀ i : Fin 3, (R i)[(2 : ℕ)]'(by rw [hlen3]; omega) = b i := by
    intro i
    have ht := PathBasics.getElem_last_of_getLast? (hpath i).2.2 (by rw [hlen3]; omega)
    have hl : (R i).length - 1 = 2 := by rw [hlen3]
    simpa [hl] using ht
  have hinj : Function.Injective w := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hkl
    rw [hw, hw] at hkl
    by_cases hij : i = j
    · subst hij
      have hkl' : (k : ℕ) = (l : ℕ) := by
        by_contra hne
        exact PathBasics.path_ne_of_ne_index (hpath i).1 _ _ hne hkl
      simp [Fin.ext_iff, hkl']
    · exfalso
      have hmi : (R i)[(k : ℕ)]'(by rw [hlen3]; exact k.isLt) ∈ R i := List.getElem_mem _
      have hmj : (R j)[(l : ℕ)]'(by rw [hlen3]; exact l.isLt) ∈ R j := List.getElem_mem _
      rw [hkl] at hmi
      exact hdisj j i (Ne.symm hij) _ hmj hmi
  have hsurj : Function.Surjective w := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hi
    have hk3 : k < 3 := by rw [← hlen3 i]; exact hk
    refine ⟨(i, ⟨k, hk3⟩), ?_⟩
    rw [hw]
    exact hkv
  have hadj : ∀ p q : Fin 3 × Fin 3, H.Adj (w p) (w q) ↔ ninePrismAdj p q := by
    rintro ⟨i, k⟩ ⟨j, l⟩
    rw [hw, hw]
    unfold ninePrismAdj
    by_cases hij : i = j
    · subst hij
      simp only [if_pos rfl]
      exact PathBasics.path_adj_iff (hpath i).1 _ _
    · rw [if_neg hij]
      rw [hcross i j hij _ (List.getElem_mem _) _ (List.getElem_mem _)]
      have hA : ∀ (m : Fin 3) (n : Fin 3),
          ((R m)[(n : ℕ)]'(by rw [hlen3]; exact n.isLt) = a m) ↔ (n : ℕ) = 0 := by
        intro m n
        constructor
        · intro hn
          by_contra hne
          exact PathBasics.path_ne_of_ne_index (hpath m).1 _ _ hne (hn.trans (hend0 m).symm)
        · intro hn
          rw [← hend0 m]
          congr 1
      have hB : ∀ (m : Fin 3) (n : Fin 3),
          ((R m)[(n : ℕ)]'(by rw [hlen3]; exact n.isLt) = b m) ↔ (n : ℕ) = 2 := by
        intro m n
        constructor
        · intro hn
          by_contra hne
          exact PathBasics.path_ne_of_ne_index (hpath m).1 _ _ hne (hn.trans (hend2 m).symm)
        · intro hn
          rw [← hend2 m]
          congr 1
      rw [hA i k, hA j l, hB i k, hB j l]
  have hiso : ninePrism ≃g H :=
    ⟨Equiv.ofBijective w ⟨hinj, hsurj⟩, fun {p q} => hadj p q⟩
  intro W hW
  let U : Set (Fin 3 × Fin 3) := hiso ⁻¹' W
  have hBij : Set.BijOn (hiso : Fin 3 × Fin 3 → V) U W := by
    refine ⟨?_, hiso.toEquiv.injective.injOn, ?_⟩
    · intro x hx
      exact hx
    · intro y hy
      refine ⟨hiso.symm y, ?_, hiso.apply_symm_apply y⟩
      change hiso (hiso.symm y) ∈ W
      simpa using hy
  have hUcard : U.ncard = 8 := hBij.ncard_eq.trans hW
  have hBounds := ninePrismBounds U hUcard
  let J : SimpleGraph U := ninePrism.induce U
  let K : SimpleGraph W := H.induce W
  let eW : J ≃g K :=
    { toEquiv := hBij.equiv hiso
      map_rel_iff' := by
        intro x y
        change H.Adj (hiso x) (hiso y) ↔ ninePrism.Adj x y
        exact hiso.map_rel_iff }
  have hdeg (u : U) :
      @SimpleGraph.degree _ K (eW u) (Fintype.ofFinite _) =
        @SimpleGraph.degree _ J u (Fintype.ofFinite _) := by
    calc
      @SimpleGraph.degree _ K (eW u) (Fintype.ofFinite _) =
          @Fintype.card (K.neighborSet (eW u)) (Fintype.ofFinite _) :=
        (@SimpleGraph.card_neighborSet_eq_degree _ K (eW u) (Fintype.ofFinite _)).symm
      _ = @Fintype.card (J.neighborSet u) (Fintype.ofFinite _) :=
        @Fintype.card_congr (K.neighborSet (eW u)) (J.neighborSet u)
          (Fintype.ofFinite _) (Fintype.ofFinite _) (eW.mapNeighborSet u).symm
      _ = @SimpleGraph.degree _ J u (Fintype.ofFinite _) :=
        @SimpleGraph.card_neighborSet_eq_degree _ J u (Fintype.ofFinite _)
  let S : Set U := {u : U |
    letI : Fintype (J.neighborSet u) := Fintype.ofFinite _
    J.degree u = 3}
  let T : Set W := {v : W |
    letI : Fintype (K.neighborSet v) := Fintype.ofFinite _
    K.degree v = 3}
  have hS : S.ncard ≤ 4 := by
    simpa only [S, J, U] using hBounds.1
  have hSbij : Set.BijOn eW S T := by
    refine ⟨?_, eW.toEquiv.injective.injOn, ?_⟩
    · intro u hu
      change @SimpleGraph.degree _ K (eW u) (Fintype.ofFinite _) = 3
      change @SimpleGraph.degree _ J u (Fintype.ofFinite _) = 3 at hu
      rw [hdeg u]
      exact hu
    · intro v hv
      refine ⟨eW.symm v, ?_, eW.apply_symm_apply v⟩
      change @SimpleGraph.degree _ J (eW.symm v) (Fintype.ofFinite _) = 3
      change @SimpleGraph.degree _ K v (Fintype.ofFinite _) = 3 at hv
      have hh := hdeg (eW.symm v)
      rw [eW.apply_symm_apply] at hh
      rw [← hh]
      exact hv
  let JC : SimpleGraph U := ((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).induce U
  let KC : SimpleGraph W := (Hᶜ).induce W
  let eC : (ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ ≃g Hᶜ :=
    { toEquiv := hiso.toEquiv
      map_rel_iff' := by
        intro x y
        simp only [SimpleGraph.compl_adj]
        constructor
        · rintro ⟨hne, hnot⟩
          refine ⟨?_, ?_⟩
          · intro hxy
            exact hne (congrArg hiso hxy)
          · intro hJ
            exact hnot ((hiso.map_rel_iff).mpr hJ)
        · rintro ⟨hne, hnot⟩
          refine ⟨?_, ?_⟩
          · intro hxy
            exact hne (hiso.toEquiv.injective hxy)
          · intro hH
            exact hnot ((hiso.map_rel_iff).mp hH) }
  have hBijC : Set.BijOn (eC : Fin 3 × Fin 3 → V) U W := by
    simpa only [eC] using hBij
  let eCW : JC ≃g KC :=
    { toEquiv := hBijC.equiv eC
      map_rel_iff' := by
        intro x y
        change Hᶜ.Adj (eC x) (eC y) ↔ ((ninePrism : SimpleGraph (Fin 3 × Fin 3))ᶜ).Adj x y
        exact eC.map_rel_iff }
  have hLower : ∀ u : U,
      letI : Fintype (JC.neighborSet u) := Fintype.ofFinite _
      4 ≤ JC.degree u := by
    simpa only [JC, U] using hBounds.2
  have hdegC (u : U) :
      @SimpleGraph.degree _ KC (eCW u) (Fintype.ofFinite _) =
        @SimpleGraph.degree _ JC u (Fintype.ofFinite _) := by
    calc
      @SimpleGraph.degree _ KC (eCW u) (Fintype.ofFinite _) =
          @Fintype.card (KC.neighborSet (eCW u)) (Fintype.ofFinite _) :=
        (@SimpleGraph.card_neighborSet_eq_degree _ KC (eCW u) (Fintype.ofFinite _)).symm
      _ = @Fintype.card (JC.neighborSet u) (Fintype.ofFinite _) :=
        @Fintype.card_congr (KC.neighborSet (eCW u)) (JC.neighborSet u)
          (Fintype.ofFinite _) (Fintype.ofFinite _) (eCW.mapNeighborSet u).symm
      _ = @SimpleGraph.degree _ JC u (Fintype.ofFinite _) :=
        @SimpleGraph.card_neighborSet_eq_degree _ JC u (Fintype.ofFinite _)
  constructor
  · change T.ncard ≤ 4
    rw [← hSbij.ncard_eq]
    exact hS
  · intro v
    change 4 ≤ @SimpleGraph.degree _ KC v (Fintype.ofFinite _)
    let u : U := eCW.symm v
    have hu := hLower u
    change 4 ≤ @SimpleGraph.degree _ JC u (Fintype.ofFinite _) at hu
    have hh := hdegC u
    rw [show eCW u = v from eCW.apply_symm_apply v] at hh
    rw [hh]
    exact hu

end Workspace.ProofLemmas
