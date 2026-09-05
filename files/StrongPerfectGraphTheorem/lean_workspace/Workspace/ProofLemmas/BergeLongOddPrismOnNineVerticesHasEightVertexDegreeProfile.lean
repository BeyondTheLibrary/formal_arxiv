import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Statements.S07.Thm_7_2
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.BergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

/-! The only possible long odd prism on at most nine vertices has rung vertex counts
`4, 2, 2`.  We use the following fixed labelled copy of that prism. -/

private def oddEightArm (p : Fin 8) : Fin 3 :=
  if (p : ℕ) < 4 then 0 else if (p : ℕ) < 6 then 1 else 2

private def oddEightPos (p : Fin 8) : ℕ :=
  if (p : ℕ) < 4 then p else if (p : ℕ) < 6 then p - 4 else p - 6

private def oddEightEnd (i : Fin 3) : ℕ :=
  if i = 0 then 3 else 1

private def oddEightLast (p : Fin 8) : ℕ := oddEightEnd (oddEightArm p)

private def oddEightAdj (p q : Fin 8) : Prop :=
  if oddEightArm p = oddEightArm q then
    oddEightPos p + 1 = oddEightPos q ∨ oddEightPos q + 1 = oddEightPos p
  else
    (oddEightPos p = 0 ∧ oddEightPos q = 0) ∨
      (oddEightPos p = oddEightLast p ∧ oddEightPos q = oddEightLast q)

private instance : DecidableRel oddEightAdj := fun p q => by
  unfold oddEightAdj oddEightArm oddEightPos oddEightLast
  infer_instance

private def oddEightPrism : SimpleGraph (Fin 8) where
  Adj := oddEightAdj
  symm := by
    intro p q h
    unfold oddEightAdj at h ⊢
    by_cases heq : oddEightArm p = oddEightArm q
    · rw [if_pos heq] at h
      rw [if_pos heq.symm]
      tauto
    · rw [if_neg heq] at h
      rw [if_neg fun hh => heq hh.symm]
      tauto
  loopless := ⟨by decide⟩

private instance : DecidableRel oddEightPrism.Adj := inferInstanceAs (DecidableRel oddEightAdj)

private theorem oddEightPrism_degree_profile :
    ({u : Fin 8 |
      letI : Fintype (oddEightPrism.neighborSet u) := Fintype.ofFinite _
      oddEightPrism.degree u = 3}).ncard = 6 ∧
    ({u : Fin 8 |
      letI : Fintype (oddEightPrism.neighborSet u) := Fintype.ofFinite _
      oddEightPrism.degree u = 2}).ncard = 2 := by
  classical
  let F₃ : Finset (Fin 8) := Finset.univ.filter fun u =>
    (oddEightPrism.neighborFinset u).card = 3
  let F₂ : Finset (Fin 8) := Finset.univ.filter fun u =>
    (oddEightPrism.neighborFinset u).card = 2
  have hF₃ : F₃.card = 6 := by decide
  have hF₂ : F₂.card = 2 := by decide
  have set_eq (d : ℕ) :
      {u : Fin 8 |
        letI : Fintype (oddEightPrism.neighborSet u) := Fintype.ofFinite _
        oddEightPrism.degree u = d} =
        ↑(Finset.univ.filter fun u => (oddEightPrism.neighborFinset u).card = d) := by
    ext u
    change (@SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) = d) ↔ _
    letI F' : Fintype (oddEightPrism.neighborSet u) := inferInstance
    rw [show @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) =
        @SimpleGraph.degree _ oddEightPrism u F' by
      calc
        @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) =
            @Fintype.card (oddEightPrism.neighborSet u) (Fintype.ofFinite _) :=
          (@SimpleGraph.card_neighborSet_eq_degree _ oddEightPrism u (Fintype.ofFinite _)).symm
        _ = @Fintype.card (oddEightPrism.neighborSet u) F' :=
          @Fintype.card_congr _ _ (Fintype.ofFinite _) F' (Equiv.refl _)
        _ = @SimpleGraph.degree _ oddEightPrism u F' :=
          @SimpleGraph.card_neighborSet_eq_degree _ oddEightPrism u F']
    rw [← @SimpleGraph.card_neighborFinset_eq_degree _ oddEightPrism u F']
    simp
  constructor
  · rw [set_eq 3, Set.ncard_coe_finset]
    exact hF₃
  · rw [set_eq 2, Set.ncard_coe_finset]
    exact hF₂

theorem bergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hcard : Fintype.card V = 9)
    (hprism : ∃ (s t : Fin 3 → V) (R₁ R₂ R₃ : List V),
      IsLongPrism G s t R₁ R₂ R₃ ∧ IsOddPrism G s t R₁ R₂ R₃) :
    ∃ W : Set V,
      W.ncard = 8 ∧
      {w : W |
        letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
        (G.induce W).degree w = 3}.ncard = 6 ∧
      {w : W |
        letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
        (G.induce W).degree w = 2}.ncard = 2 := by
  classical
  rcases hprism with ⟨s, t, R₀, R₁, R₂, ⟨hform, hlong⟩, ⟨_, hodd⟩⟩
  have hpar := Workspace.Statements.S07.SPGT.thm_7_2 G hG s t R₀ R₁ R₂ hform
  have hn₀ : ¬ Even (pathLength R₀) := by
    intro he
    exact hodd ⟨he, hpar.1.mp he, hpar.2.mp he⟩
  have hn₁ : ¬ Even (pathLength R₁) := by
    intro he
    have he₀ : Even (pathLength R₀) := hpar.1.mpr he
    exact hodd ⟨he₀, he, hpar.2.mp he₀⟩
  have hn₂ : ¬ Even (pathLength R₂) := by
    intro he
    have he₀ : Even (pathLength R₀) := hpar.2.mpr he
    exact hodd ⟨he₀, hpar.1.mp he₀, he⟩
  let R : Fin 3 → List V := ![R₀, R₁, R₂]
  have hformR : FormPrism G s t (R 0) (R 1) (R 2) := by simpa [R] using hform
  have hpath (i : Fin 3) : IsPathFrom G (R i) (s i) (t i) :=
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hformR i
  have htwo (i : Fin 3) : 2 ≤ (R i).length :=
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length hformR i
  have hdisj (i j : Fin 3) (hij : i ≠ j) : ∀ u ∈ R i, u ∉ R j :=
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hformR hij
  have hnodup : (R 0 ++ R 1 ++ R 2).Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨(hpath 0).1.2.1, (hpath 1).1.2.1, ?_⟩, (hpath 2).1.2.1, ?_⟩
    · intro x hx y hy hxy
      exact hdisj 0 1 (by decide) x hx (hxy ▸ hy)
    · intro x hx y hy hxy
      rcases List.mem_append.mp hx with hx | hx
      · exact hdisj 0 2 (by decide) x hx (hxy ▸ hy)
      · exact hdisj 1 2 (by decide) x hx (hxy ▸ hy)
  have hsum_le : (R 0).length + (R 1).length + (R 2).length ≤ 9 := by
    have hc : (R 0 ++ R 1 ++ R 2).toFinset.card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.subset_univ _)
    rw [List.toFinset_card_of_nodup hnodup, Finset.card_univ, hcard] at hc
    simpa only [List.length_append] using hc
  have odd_length_even_vertices (P : List V) (hP : IsPathList G P)
      (ho : Odd (pathLength P)) : Even P.length := by
    rcases ho with ⟨k, hk⟩
    refine ⟨k + 1, ?_⟩
    have hp := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hP
    omega
  have he₀ : Even R₀.length :=
    odd_length_even_vertices R₀ (by simpa [R] using (hpath 0).1)
      (Nat.not_even_iff_odd.mp hn₀)
  have he₁ : Even R₁.length :=
    odd_length_even_vertices R₁ (by simpa [R] using (hpath 1).1)
      (Nat.not_even_iff_odd.mp hn₁)
  have he₂ : Even R₂.length :=
    odd_length_even_vertices R₂ (by simpa [R] using (hpath 2).1)
      (Nat.not_even_iff_odd.mp hn₂)
  have htwo₀ : 2 ≤ R₀.length := by simpa [R] using htwo 0
  have htwo₁ : 2 ≤ R₁.length := by simpa [R] using htwo 1
  have htwo₂ : 2 ≤ R₂.length := by simpa [R] using htwo 2
  have hsum_le' : R₀.length + R₁.length + R₂.length ≤ 9 := by
    simpa [R] using hsum_le
  have long_vertices (P : List V) (hP : IsPathList G P) (he : Even P.length)
      (hl : 1 < pathLength P) :
      4 ≤ P.length := by
    rcases he with ⟨k, hk⟩
    have hp := Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hP
    omega
  have hlong' : 4 ≤ R₀.length ∨ 4 ≤ R₁.length ∨ 4 ≤ R₂.length := by
    rcases hlong with hl | hl | hl
    · exact Or.inl (long_vertices R₀ (by simpa [R] using (hpath 0).1) he₀ hl)
    · exact Or.inr (Or.inl (long_vertices R₁ (by simpa [R] using (hpath 1).1) he₁ hl))
    · exact Or.inr (Or.inr (long_vertices R₂ (by simpa [R] using (hpath 2).1) he₂ hl))

  have finish : ∀ (a b : Fin 3 → V) (P₀ P₁ P₂ : List V),
      FormPrism G a b P₀ P₁ P₂ → P₀.length = 4 → P₁.length = 2 → P₂.length = 2 →
      ∃ W : Set V,
        W.ncard = 8 ∧
        {w : W |
          letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
          (G.induce W).degree w = 3}.ncard = 6 ∧
        {w : W |
          letI : Fintype ((G.induce W).neighborSet w) := Fintype.ofFinite _
          (G.induce W).degree w = 2}.ncard = 2 := by
    intro a b P₀ P₁ P₂ hp hlen₀ hlen₁ hlen₂
    let Q : Fin 3 → List V := ![P₀, P₁, P₂]
    have hpQ : FormPrism G a b (Q 0) (Q 1) (Q 2) := by simpa [Q] using hp
    have hQpath (i : Fin 3) : IsPathFrom G (Q i) (a i) (b i) :=
      Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path hpQ i
    have hQdisj (i j : Fin 3) (hij : i ≠ j) : ∀ u ∈ Q i, u ∉ Q j :=
      Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint hpQ hij
    let arm : Fin 8 → Fin 3 := oddEightArm
    let pos : Fin 8 → ℕ := oddEightPos
    let last : Fin 3 → ℕ := oddEightEnd
    have hpos (u : Fin 8) : pos u < (Q (arm u)).length := by
      fin_cases u <;> simp [pos, arm, oddEightPos, oddEightArm, Q,
        hlen₀, hlen₁, hlen₂]
    have hlast (i : Fin 3) : last i < (Q i).length := by
      fin_cases i <;> simp [last, oddEightEnd, Q, hlen₀, hlen₁, hlen₂]
    have hzero (i : Fin 3) : 0 < (Q i).length :=
      Workspace.ProofLemmas.PathBasics.path_length_pos (hQpath i).1
    have hhead (i : Fin 3) : (Q i)[0]'(hzero i) = a i :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? (hQpath i).2.1 (hzero i)
    have hend (i : Fin 3) : (Q i)[last i]'(hlast i) = b i := by
      have hh := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast?
        (hQpath i).2.2 (hzero i)
      have hi : (Q i).length - 1 = last i := by
        fin_cases i <;> simp [last, oddEightEnd, Q, hlen₀, hlen₁, hlen₂]
      simpa only [hi] using hh
    let w : Fin 8 → V := fun u => (Q (arm u)).getD (pos u) (a 0)
    have hw (u : Fin 8) : w u = (Q (arm u))[pos u]'(hpos u) := by
      simp only [w]
      exact List.getD_eq_getElem _ _ (hpos u)
    have ha (u : Fin 8) : w u = a (arm u) ↔ pos u = 0 := by
      constructor
      · intro hu
        have heq : (Q (arm u))[pos u]'(hpos u) =
            (Q (arm u))[0]'(hzero (arm u)) := by
          exact (hw u).symm.trans (hu.trans (hhead (arm u)).symm)
        exact ((hQpath (arm u)).1.2.1.getElem_inj_iff).mp heq
      · intro hu
        rw [hw u]
        simpa only [hu] using hhead (arm u)
    have hb (u : Fin 8) : w u = b (arm u) ↔ pos u = last (arm u) := by
      constructor
      · intro hu
        have heq : (Q (arm u))[pos u]'(hpos u) =
            (Q (arm u))[last (arm u)]'(hlast (arm u)) := by
          exact (hw u).symm.trans (hu.trans (hend (arm u)).symm)
        exact ((hQpath (arm u)).1.2.1.getElem_inj_iff).mp heq
      · intro hu
        rw [hw u]
        simpa only [hu] using hend (arm u)
    have hcode : Function.Injective (fun u : Fin 8 => (arm u, pos u)) := by
      intro p q hpq
      fin_cases p <;> fin_cases q <;>
        simp_all [arm, pos, oddEightArm, oddEightPos]
    have hinj : Function.Injective w := by
      intro p q hpq
      by_cases har : arm p = arm q
      · have hpq' := hpq
        simp only [w] at hpq'
        rw [har] at hpq'
        rw [List.getD_eq_getElem _ _ (by simpa only [har] using hpos p),
          List.getD_eq_getElem _ _ (hpos q)] at hpq'
        have hposEq : pos p = pos q :=
          ((hQpath (arm q)).1.2.1.getElem_inj_iff).mp hpq'
        exact hcode (Prod.ext har hposEq)
      · apply False.elim
        apply hQdisj (arm p) (arm q) har (w p) (by
          rw [hw p]
          exact List.getElem_mem _)
        rw [hpq]
        rw [hw q]
        exact List.getElem_mem _
    have hadj (p q : Fin 8) : G.Adj (w p) (w q) ↔ oddEightAdj p q := by
      by_cases har : arm p = arm q
      · have hs : G.Adj (w p) (w q) ↔
            (pos p + 1 = pos q ∨ pos q + 1 = pos p) := by
          simp only [w]
          rw [har]
          rw [List.getD_eq_getElem _ _ (by simpa only [har] using hpos p),
            List.getD_eq_getElem _ _ (hpos q)]
          exact Workspace.ProofLemmas.PathBasics.path_adj_iff
            (hQpath (arm q)).1 _ _
        rw [hs]
        simp only [arm] at har
        unfold oddEightAdj
        rw [if_pos har]
      · rw [Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross hpQ har
          (w p) (by rw [hw p]; exact List.getElem_mem _)
          (w q) (by rw [hw q]; exact List.getElem_mem _),
          ha p, ha q, hb p, hb q]
        simp only [arm] at har
        unfold oddEightAdj
        rw [if_neg har]
        rfl
    let W : Set V := Set.range w
    have hWcard : W.ncard = 8 := by
      change (Set.range w).ncard = 8
      rw [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
      simp
    let wW : Fin 8 → W := fun u => ⟨w u, Set.mem_range_self u⟩
    have hwWinj : Function.Injective wW := fun p q he =>
      hinj (congrArg Subtype.val he)
    have hwWsurj : Function.Surjective wW := by
      rintro ⟨v, u, rfl⟩
      exact ⟨u, rfl⟩
    let K : SimpleGraph W := G.induce W
    let e : oddEightPrism ≃g K :=
      ⟨Equiv.ofBijective wW ⟨hwWinj, hwWsurj⟩, fun {p q} => by
        change G.Adj (w p) (w q) ↔ oddEightAdj p q
        exact hadj p q⟩
    have hdeg (u : Fin 8) :
        @SimpleGraph.degree _ K (e u) (Fintype.ofFinite _) =
          @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) := by
      calc
        @SimpleGraph.degree _ K (e u) (Fintype.ofFinite _) =
            @Fintype.card (K.neighborSet (e u)) (Fintype.ofFinite _) :=
          (@SimpleGraph.card_neighborSet_eq_degree _ K (e u) (Fintype.ofFinite _)).symm
        _ = @Fintype.card (oddEightPrism.neighborSet u) (Fintype.ofFinite _) :=
          @Fintype.card_congr (K.neighborSet (e u)) (oddEightPrism.neighborSet u)
            (Fintype.ofFinite _) (Fintype.ofFinite _) (e.mapNeighborSet u).symm
        _ = @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) :=
          @SimpleGraph.card_neighborSet_eq_degree _ oddEightPrism u (Fintype.ofFinite _)
    let S (d : ℕ) : Set (Fin 8) := {u : Fin 8 |
      @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) = d}
    let T (d : ℕ) : Set W := {v : W |
      @SimpleGraph.degree _ K v (Fintype.ofFinite _) = d}
    have hbij (d : ℕ) : Set.BijOn e (S d) (T d) := by
      refine ⟨?_, e.toEquiv.injective.injOn, ?_⟩
      · intro u hu
        change @SimpleGraph.degree _ K (e u) (Fintype.ofFinite _) = d
        change @SimpleGraph.degree _ oddEightPrism u (Fintype.ofFinite _) = d at hu
        rw [hdeg u]
        exact hu
      · intro v hv
        refine ⟨e.symm v, ?_, e.apply_symm_apply v⟩
        change @SimpleGraph.degree _ oddEightPrism (e.symm v) (Fintype.ofFinite _) = d
        change @SimpleGraph.degree _ K v (Fintype.ofFinite _) = d at hv
        have hh := hdeg (e.symm v)
        rw [e.apply_symm_apply] at hh
        rw [← hh]
        exact hv
    refine ⟨W, hWcard, ?_, ?_⟩
    · change (T 3).ncard = 6
      rw [← (hbij 3).ncard_eq]
      exact oddEightPrism_degree_profile.1
    · change (T 2).ncard = 2
      rw [← (hbij 2).ncard_eq]
      exact oddEightPrism_degree_profile.2

  rcases he₀ with ⟨k₀, hk₀⟩
  rcases he₁ with ⟨k₁, hk₁⟩
  rcases he₂ with ⟨k₂, hk₂⟩
  rcases hlong' with hl₀ | hl₁ | hl₂
  · have hlen₀ : R₀.length = 4 := by omega
    have hlen₁ : R₁.length = 2 := by omega
    have hlen₂ : R₂.length = 2 := by omega
    exact finish s t R₀ R₁ R₂ hform hlen₀ hlen₁ hlen₂
  · have hlen₀ : R₀.length = 2 := by omega
    have hlen₁ : R₁.length = 4 := by omega
    have hlen₂ : R₂.length = 2 := by omega
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 1
    have hp' := Workspace.ProofLemmas.PrismSymmetry.formPrism_perm
      (R := ![R₀, R₁, R₂]) hform σ
    refine finish (fun i => s (σ i)) (fun i => t (σ i))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 0))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 1))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 2)) hp' ?_ ?_ ?_
    all_goals simp [σ, Equiv.swap_apply_of_ne_of_ne, hlen₀, hlen₁, hlen₂]
  · have hlen₀ : R₀.length = 2 := by omega
    have hlen₁ : R₁.length = 2 := by omega
    have hlen₂ : R₂.length = 4 := by omega
    let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    have hp' := Workspace.ProofLemmas.PrismSymmetry.formPrism_perm
      (R := ![R₀, R₁, R₂]) hform σ
    refine finish (fun i => s (σ i)) (fun i => t (σ i))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 0))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 1))
      ((![R₀, R₁, R₂] : Fin 3 → List V) (σ 2)) hp' ?_ ?_ ?_
    all_goals simp [σ, Equiv.swap_apply_of_ne_of_ne, hlen₀, hlen₁, hlen₂]

end Workspace.ProofLemmas.BergeLongOddPrismOnNineVerticesHasEightVertexDegreeProfile
