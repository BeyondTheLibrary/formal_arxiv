import Mathlib
import Workspace.Types.Gamma
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover
import Workspace.Types.TwoElementAssignment
import Workspace.Types.EdgeColouring

open Set

open scoped Graph

open Workspace.Types.Gamma

namespace Workspace.Facts.Lemma21

variable {α β : Type*} {G H : Graph α β} {P : β → Set Gamma} {e f : β} {v : α}

/-! ## Private helper lemmas -/

private lemma restrict_loopless (h : G.IsLoopless) (F : Set β) :
    (G.restrict F).IsLoopless :=
  fun e x hl => h e x (hl.mono Graph.restrict_le)

private lemma restrict_incidenceSet_eq_palette (G : Graph α β) (P : β → Set Gamma)
    (v : α) (s : Gamma) :
    (G.restrict {f | s ∈ P f}).incidenceSet v = G.paletteIncidenceSet P v s := by
  ext e
  simp only [Graph.mem_incidenceSet, Graph.restrict_inc, Graph.mem_paletteIncidenceSet,
    Set.mem_setOf_eq]

private lemma restrict_degree_eq (h : G.IsLoopless) (F : Set β) (v : α) :
    (G.restrict F).degree v = ((G.restrict F).incidenceSet v).ncard :=
  (restrict_loopless h F).degree_eq_ncard_incidenceSet v

private lemma sub_loopless {K : Graph α β} (h : G.IsLoopless) (hle : K ≤ G) :
    K.IsLoopless :=
  fun e x hl => h e x (hl.mono hle)

/-- For a subgraph `K ≤ H`, the edges incident to `x` in `H` that belong to `K`
are exactly the edges incident to `x` in `K`. -/
private lemma incidenceSet_inter_edgeSet_of_le {K : Graph α β} (hle : K ≤ G) (x : α) :
    G.incidenceSet x ∩ E(K) = K.incidenceSet x := by
  ext e
  simp only [Set.mem_inter_iff, Graph.mem_incidenceSet]
  constructor
  · rintro ⟨hHe, heK⟩
    obtain ⟨a, b, hlink⟩ := Graph.exists_isLink_of_mem_edgeSet heK
    rcases hHe.eq_or_eq_of_isLink (hlink.mono hle) with rfl | rfl
    · exact hlink.inc_left
    · exact hlink.inc_right
  · intro hKe
    exact ⟨hKe.mono hle, hKe.edge_mem⟩

/-- Deleting the edges of a subgraph `C` from `G` removes exactly the `C`-edges from
each incidence set. -/
private lemma restrict_diff_incidenceSet (G C : Graph α β) (x : α) :
    (G.restrict (E(G) \ E(C))).incidenceSet x = G.incidenceSet x \ E(C) := by
  ext e
  simp only [Graph.mem_incidenceSet, Graph.restrict_inc, Set.mem_diff]
  constructor
  · rintro ⟨hinc, -, hnC⟩; exact ⟨hinc, hnC⟩
  · rintro ⟨hinc, hnC⟩; exact ⟨hinc, hinc.edge_mem, hnC⟩

private lemma encard_mem_iff_ncard {X : Type*} {S : Set X} (hS : S.Finite) :
    S.encard ∈ ({0, 2} : Set ℕ∞) ↔ (S.ncard = 0 ∨ S.ncard = 2) := by
  rw [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl ((Set.ncard_eq_zero hS).2 (Set.encard_eq_zero.1 h))
    · exact Or.inr (Set.ncard_eq_two.2 (Set.encard_eq_two.1 h))
  · rintro (h | h)
    · exact Or.inl (Set.encard_eq_zero.2 ((Set.ncard_eq_zero hS).1 h))
    · exact Or.inr (Set.encard_eq_two.2 (Set.ncard_eq_two.1 h))

private lemma edgeMultiplicity_add (D₁ D₂ : Multiset (Graph α β)) (e : β) :
    (D₁ + D₂).edgeMultiplicity e = D₁.edgeMultiplicity e + D₂.edgeMultiplicity e := by
  classical
  simp only [Multiset.edgeMultiplicity_def, Multiset.countP_add]

private lemma edgeMultiplicity_finsetSum {ι : Type*} (t : Finset ι)
    (D : ι → Multiset (Graph α β)) (e : β) :
    (∑ i ∈ t, D i).edgeMultiplicity e = ∑ i ∈ t, (D i).edgeMultiplicity e := by
  classical
  induction t using Finset.induction with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, edgeMultiplicity_add, ih]

/-! ## Facts used in the proof of Lemma 2.1 -/

theorem fact_2_1a (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (P : β → Set Gamma) :
    (∀ v ∈ V(G), ∀ s : Gamma, (G.paletteIncidenceSet P v s).encard ∈ ({0, 2} : Set ℕ∞)) ↔
      (∀ s : Gamma, ∀ v ∈ V(G), (G.restrict {f | s ∈ P f}).degree v = 0 ∨
        (G.restrict {f | s ∈ P f}).degree v = 2) := by
  have hkey : ∀ (s : Gamma) (v : α),
      (G.restrict {f | s ∈ P f}).degree v = (G.paletteIncidenceSet P v s).ncard := by
    intro s v
    rw [restrict_degree_eq hloop, restrict_incidenceSet_eq_palette]
  have hfin : ∀ (v : α) (s : Gamma), (G.paletteIncidenceSet P v s).Finite :=
    fun v s => hE.subset (G.paletteIncidenceSet_subset_edgeSet P v s)
  constructor
  · intro hL s v hv
    rw [hkey s v]
    exact (encard_mem_iff_ncard (hfin v s)).1 (hL v hv s)
  · intro hR v hv s
    rw [encard_mem_iff_ncard (hfin v s), ← hkey s v]
    exact hR s v hv

theorem fact_2_1b (hV : V(H).Finite) (hE : E(H).Finite) (hloop : H.IsLoopless)
    (hdeg : ∀ x ∈ V(H), H.degree x = 0 ∨ H.degree x = 2)
    (hv : v ∈ V(H)) (hvdeg : H.degree v = 2) :
    H.IsCycle (H.induce {x | H.Reachable v x}) := by
  -- X = component of v, C = induced subgraph
  have hXsub : {x | H.Reachable v x} ⊆ V(H) := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rcases eq_or_ne x v with rfl | hne
    · exact hv
    · exact hx.right_mem_of_ne (Ne.symm hne)
  have hCle : H.induce {x | H.Reachable v x} ≤ H := Graph.induce_le hXsub
  have hCloop : (H.induce {x | H.Reachable v x}).IsLoopless :=
    fun e y hl => hloop e y (hl.mono hCle)
  have hvX : v ∈ {x | H.Reachable v x} := Graph.Reachable.rfl
  -- degree of every vertex of the component is 2 in H
  have hdeg2 : ∀ x ∈ {x | H.Reachable v x}, H.degree x = 2 := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    rcases eq_or_ne x v with rfl | hne
    · exact hvdeg
    · have hxV : x ∈ V(H) := hx.right_mem_of_ne (Ne.symm hne)
      rcases hdeg x hxV with h0 | h2
      · exfalso
        obtain ⟨c, hadj, -⟩ := (hx.symm.cases_head).resolve_left hne
        obtain ⟨e, hlink⟩ := hadj
        have heinc : e ∈ H.incidenceSet x := (H.mem_incidenceSet x e).2 hlink.inc_left
        have hfin : (H.incidenceSet x).Finite := hE.subset (H.incidenceSet_subset_edgeSet x)
        rw [hloop.degree_eq_ncard_incidenceSet, Set.ncard_eq_zero hfin] at h0
        rw [h0] at heinc
        exact absurd heinc (Set.notMem_empty e)
      · exact h2
  -- the incidence set of a component vertex is the same in C and in H
  have hincid : ∀ x ∈ {x | H.Reachable v x},
      (H.induce {x | H.Reachable v x}).incidenceSet x = H.incidenceSet x := by
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    ext e
    rw [Graph.mem_incidenceSet, Graph.mem_incidenceSet]
    constructor
    · intro hCe; exact hCe.mono hCle
    · intro hHe
      obtain ⟨y, hlink⟩ := hHe
      have hyX : H.Reachable v y := hx.tail hlink.adj
      exact ⟨y, by rw [Graph.induce_isLink]; exact ⟨hlink, hx, hyX⟩⟩
  refine Graph.IsCycle.mk hCle ?_ ?_
  · -- connectivity of the component
    refine Graph.connected_of_forall_reachable (x := v)
      (by rw [Graph.vertexSet_induce]; exact hvX) ?_
    intro y hy
    rw [Graph.vertexSet_induce] at hy
    simp only [Set.mem_setOf_eq] at hy
    induction hy with
    | refl => exact Graph.Reachable.rfl
    | tail hvb hby ih =>
      obtain ⟨e, hlink⟩ := hby
      have hCadj : (H.induce {x | H.Reachable v x}).Adj _ _ :=
        ⟨e, by rw [Graph.induce_isLink]; exact ⟨hlink, hvb, hvb.tail hlink.adj⟩⟩
      exact ih.tail hCadj
  · -- two-regularity of the component
    intro x hx
    rw [Graph.vertexSet_induce] at hx
    rw [hCloop.degree_eq_ncard_incidenceSet, hincid x hx,
      ← hloop.degree_eq_ncard_incidenceSet]
    exact hdeg2 x hx

/-- Strong induction on the number of edges: a finite loopless graph with all
degrees `0` or `2` decomposes into cycles. -/
private lemma decomp_aux (n : ℕ) : ∀ (K : Graph α β), E(K).ncard = n →
    V(K).Finite → E(K).Finite → K.IsLoopless →
    (∀ x ∈ V(K), K.degree x = 0 ∨ K.degree x = 2) →
    ∃ D : Multiset (Graph α β), (∀ C ∈ D, K.IsCycle C) ∧
      ∀ e ∈ E(K), D.edgeMultiplicity e = 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro K hn hVfin hEfin hloop hdeg
    rcases Set.eq_empty_or_nonempty E(K) with hEmpty | hNe
    · -- no edges: the empty decomposition works
      refine ⟨0, fun C hC => absurd hC (Multiset.notMem_zero C), fun e he => ?_⟩
      rw [hEmpty] at he; exact absurd he (Set.notMem_empty e)
    · -- pick an edge, peel off the cycle through one of its ends
      obtain ⟨e₀, he₀⟩ := hNe
      obtain ⟨x₀, y₀, hlink₀⟩ := Graph.exists_isLink_of_mem_edgeSet he₀
      have hx₀mem : x₀ ∈ V(K) := hlink₀.left_mem
      have hx₀deg2 : K.degree x₀ = 2 := by
        rcases hdeg x₀ hx₀mem with h0 | h2
        · exfalso
          have heinc : e₀ ∈ K.incidenceSet x₀ := (K.mem_incidenceSet x₀ e₀).2 hlink₀.inc_left
          have hfin : (K.incidenceSet x₀).Finite := hEfin.subset (K.incidenceSet_subset_edgeSet x₀)
          rw [hloop.degree_eq_ncard_incidenceSet, Set.ncard_eq_zero hfin] at h0
          rw [h0] at heinc; exact absurd heinc (Set.notMem_empty e₀)
        · exact h2
      set C₀ : Graph α β := K.induce {x | K.Reachable x₀ x} with hC₀def
      have hcyc₀ : K.IsCycle C₀ := fact_2_1b hVfin hEfin hloop hdeg hx₀mem hx₀deg2
      have hC₀le : C₀ ≤ K := hcyc₀.le
      have hC₀loop : C₀.IsLoopless := sub_loopless hloop hC₀le
      -- the peeled graph
      set K' : Graph α β := K.restrict (E(K) \ E(C₀)) with hK'def
      have hK'le : K' ≤ K := Graph.restrict_le
      have hloop' : K'.IsLoopless := restrict_loopless hloop _
      have hEH' : E(K') = E(K) \ E(C₀) := by
        rw [hK'def, Graph.edgeSet_restrict, Set.inter_eq_right.2 Set.diff_subset]
      have hVH' : V(K') = V(K) := by rw [hK'def, Graph.vertexSet_restrict]
      have hE'fin : E(K').Finite := by rw [hEH']; exact hEfin.diff
      -- degrees stay in {0,2} after peeling the cycle
      have hdeg' : ∀ x ∈ V(K'), K'.degree x = 0 ∨ K'.degree x = 2 := by
        intro x hx'
        rw [hVH'] at hx'
        have hHfin : (K.incidenceSet x).Finite := hEfin.subset (K.incidenceSet_subset_edgeSet x)
        have hinter : K.incidenceSet x ∩ E(C₀) = C₀.incidenceSet x :=
          incidenceSet_inter_edgeSet_of_le hC₀le x
        have hC₀sub : C₀.incidenceSet x ⊆ K.incidenceSet x := by
          rw [← hinter]; exact Set.inter_subset_left
        have hdiff_eq : K.incidenceSet x \ E(C₀) = K.incidenceSet x \ C₀.incidenceSet x := by
          rw [← hinter, Set.diff_self_inter]
        have h1 : K'.degree x = (K.incidenceSet x).ncard - (C₀.incidenceSet x).ncard := by
          rw [hloop'.degree_eq_ncard_incidenceSet, hK'def, restrict_diff_incidenceSet,
            hdiff_eq, Set.ncard_diff hC₀sub (hHfin.subset hC₀sub)]
        rw [← hloop.degree_eq_ncard_incidenceSet, ← hC₀loop.degree_eq_ncard_incidenceSet] at h1
        have hC₀val : C₀.degree x = 0 ∨ C₀.degree x = 2 := by
          by_cases hxC₀ : x ∈ V(C₀)
          · exact Or.inr (hcyc₀.isTwoRegular x hxC₀)
          · exact Or.inl (Graph.degree_eq_zero_of_notMem hxC₀)
        have hle : C₀.degree x ≤ K.degree x := by
          rw [hloop.degree_eq_ncard_incidenceSet, hC₀loop.degree_eq_ncard_incidenceSet]
          exact Set.ncard_le_ncard hC₀sub hHfin
        rcases hdeg x hx' with hh | hh <;> rw [h1] <;> omega
      -- fewer edges, so induction applies
      have hlt : E(K').ncard < n := by
        rw [← hn, hEH']
        obtain ⟨e₁, he₁⟩ := hcyc₀.edgeSet_nonempty
        have he₁H : e₁ ∈ E(K) := Graph.IsSubgraph.edgeSet_mono hC₀le he₁
        refine Set.ncard_lt_ncard ⟨Set.diff_subset, ?_⟩ hEfin
        intro hsub; exact (hsub he₁H).2 he₁
      obtain ⟨D', hD'cyc, hD'cover⟩ :=
        ih (E(K').ncard) hlt K' rfl (by rw [hVH']; exact hVfin) hE'fin hloop' hdeg'
      refine ⟨C₀ ::ₘ D', ?_, ?_⟩
      · intro C hC
        rw [Multiset.mem_cons] at hC
        rcases hC with rfl | hC
        · exact hcyc₀
        · exact (hD'cyc C hC).mono hK'le
      · intro e he
        by_cases heC₀ : e ∈ E(C₀)
        · have hz : D'.edgeMultiplicity e = 0 := by
            rw [Multiset.edgeMultiplicity_eq_zero_iff]
            intro C hC heC
            have hmem : e ∈ E(K') := Graph.IsSubgraph.edgeSet_mono (hD'cyc C hC).le heC
            rw [hEH'] at hmem; exact hmem.2 heC₀
          rw [Multiset.edgeMultiplicity_cons_of_mem _ heC₀, hz]
        · rw [Multiset.edgeMultiplicity_cons_of_notMem _ heC₀]
          apply hD'cover
          rw [hEH']; exact ⟨he, heC₀⟩

theorem fact_2_1b_decomposition (hV : V(H).Finite) (hE : E(H).Finite)
    (hloop : H.IsLoopless) (hdeg : ∀ x ∈ V(H), H.degree x = 0 ∨ H.degree x = 2) :
    ∃ D : Multiset (Graph α β), (∀ C ∈ D, H.IsCycle C) ∧
      ∀ e ∈ E(H), D.edgeMultiplicity e = 1 :=
  decomp_aux (E(H).ncard) H rfl hV hE hloop hdeg

theorem fact_2_1c (hV : V(G).Finite) (hE : E(G).Finite)
    (hP : G.IsTwoElementAssignment P) (he : e ∈ E(G)) :
    {s : Gamma | e ∈ E(G.restrict {f | s ∈ P f})}.encard = 2 := by
  have hset : {s : Gamma | e ∈ E(G.restrict {f | s ∈ P f})} = P e := by
    ext s
    simp only [Set.mem_setOf_eq, Graph.edgeSet_restrict, Set.mem_inter_iff]
    exact ⟨fun h => h.2, fun h => ⟨he, h⟩⟩
  rw [hset]
  exact hP.encard_palette e he

theorem fact_2_1d (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (hP : G.IsTwoElementAssignment P)
    (D : Gamma → Multiset (Graph α β))
    (hcyc : ∀ s : Gamma, ∀ C ∈ D s, (G.restrict {f | s ∈ P f}).IsCycle C)
    (hcover : ∀ s : Gamma, ∀ e ∈ E(G.restrict {f | s ∈ P f}), (D s).edgeMultiplicity e = 1) :
    G.IsCycleDoubleCover (∑ s : Gamma, D s) := by
  classical
  refine ⟨fun C hC => ?_, fun e he => ?_⟩
  · -- every member of the sum is a cycle of some M_s, hence of G
    rw [Multiset.mem_sum] at hC
    obtain ⟨s, -, hCs⟩ := hC
    exact (hcyc s C hCs).mono Graph.restrict_le
  · -- multiplicity of e is 2
    rw [edgeMultiplicity_finsetSum]
    have hper : ∀ s : Gamma, (D s).edgeMultiplicity e =
        (if e ∈ E(G.restrict {f | s ∈ P f}) then (1 : ℕ) else 0) := by
      intro s
      by_cases hmem : e ∈ E(G.restrict {f | s ∈ P f})
      · rw [if_pos hmem]; exact hcover s e hmem
      · rw [if_neg hmem]
        rw [Multiset.edgeMultiplicity_eq_zero_iff]
        intro C hC heC
        exact hmem (Graph.IsSubgraph.edgeSet_mono (hcyc s C hC).le heC)
    simp_rw [hper]
    have hfc := fact_2_1c hV hE hP he
    obtain ⟨a, b, hab, hs⟩ := Set.encard_eq_two.1 hfc
    rw [Finset.sum_boole]
    have hfilter : (Finset.univ.filter (fun s => e ∈ E(G.restrict {f | s ∈ P f}))) = {a, b} := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      have hmem : s ∈ {s : Gamma | e ∈ E(G.restrict {f | s ∈ P f})} ↔ s ∈ ({a, b} : Set Gamma) := by
        rw [hs]
      simpa only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
    rw [hfilter]
    simp [Finset.card_pair hab]

/-! ## Remark 2.1e -/

theorem remark_2_1e (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (c : β → Fin 3) (hc : G.IsProper3EdgeColouring c)
    (e₁ e₂ : Gamma) (h₁ : e₁ ≠ 0) (h₂ : e₂ ≠ 0) (h₁₂ : e₁ ≠ e₂) :
    G.IsTwoElementAssignment
      (fun e ↦ if c e = 0 then {0, e₁} else if c e = 1 then {0, e₂} else {e₁, e₂}) := by
  set Q : β → Set Gamma :=
    fun e ↦ if c e = 0 then {0, e₁} else if c e = 1 then {0, e₂} else {e₁, e₂} with hQ
  refine ⟨?_, ?_⟩
  · -- each palette has exactly two elements
    intro e he
    show (Q e).encard = 2
    rw [hQ]
    by_cases hc0 : c e = 0
    · simp only [hc0, if_pos]
      exact Set.encard_pair (Ne.symm h₁)
    · by_cases hc1 : c e = 1
      · simp only [hc0, hc1, if_true, if_false, reduceIte]
        exact Set.encard_pair (Ne.symm h₂)
      · simp only [hc0, hc1, if_false, reduceIte]
        exact Set.encard_pair h₁₂
  · -- condition (1)
    intro v hv s
    have hdeg3 : G.degree v = 3 := hcubic v hv
    obtain ⟨a, ha_inc, ha_c⟩ := hc.exists_inc_colour hloop hv hdeg3 0
    obtain ⟨b, hb_inc, hb_c⟩ := hc.exists_inc_colour hloop hv hdeg3 1
    obtain ⟨d, hd_inc, hd_c⟩ := hc.exists_inc_colour hloop hv hdeg3 2
    have hab : a ≠ b := by rintro rfl; rw [ha_c] at hb_c; exact absurd hb_c (by decide)
    have had : a ≠ d := by rintro rfl; rw [ha_c] at hd_c; exact absurd hd_c (by decide)
    have hbd : b ≠ d := by rintro rfl; rw [hb_c] at hd_c; exact absurd hd_c (by decide)
    -- the three edges are exactly the incidence set
    have hincid_card : (G.incidenceSet v).ncard = 3 := by
      rw [← hloop.degree_eq_ncard_incidenceSet v, hdeg3]
    have hsub : ({a, b, d} : Set β) ⊆ G.incidenceSet v := by
      rw [Set.insert_subset_iff, Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨(G.mem_incidenceSet v a).2 ha_inc, (G.mem_incidenceSet v b).2 hb_inc,
        (G.mem_incidenceSet v d).2 hd_inc⟩
    have htriple_card : ({a, b, d} : Set β).ncard = 3 := by
      rw [Set.ncard_eq_three]; exact ⟨a, b, d, hab, had, hbd, rfl⟩
    have hincid_eq : G.incidenceSet v = ({a, b, d} : Set β) := by
      refine (Set.eq_of_subset_of_ncard_le hsub ?_
        (hE.subset (G.incidenceSet_subset_edgeSet v))).symm
      rw [hincid_card, htriple_card]
    -- palette values on the three edges
    have hPa : Q a = ({0, e₁} : Set Gamma) := by rw [hQ]; simp [ha_c]
    have hPb : Q b = ({0, e₂} : Set Gamma) := by rw [hQ]; simp [hb_c]
    have hPd : Q d = ({e₁, e₂} : Set Gamma) := by rw [hQ]; simp [hd_c]
    -- the palette-incidence set as a subset of {a,b,d}
    have hpalinc : G.paletteIncidenceSet Q v s = {x ∈ ({a, b, d} : Set β) | s ∈ Q x} := by
      ext x
      simp only [Graph.mem_paletteIncidenceSet, Set.mem_sep_iff]
      constructor
      · rintro ⟨hinc, hsx⟩
        have hx : x ∈ G.incidenceSet v := (G.mem_incidenceSet v x).2 hinc
        rw [hincid_eq] at hx
        exact ⟨hx, hsx⟩
      · rintro ⟨hx, hsx⟩
        have hx' : x ∈ G.incidenceSet v := by rw [hincid_eq]; exact hx
        exact ⟨(G.mem_incidenceSet v x).1 hx', hsx⟩
    rw [hpalinc]
    -- case analysis on which of 0, e₁, e₂ equals s
    by_cases hs0 : s = 0
    · have hset : {x ∈ ({a, b, d} : Set β) | s ∈ Q x} = ({a, b} : Set β) := by
        ext x
        simp only [Set.mem_sep_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨hx, hsx⟩
          rcases hx with h | h | h
          · exact Or.inl h
          · exact Or.inr h
          · exfalso
            rw [h, hPd, hs0] at hsx
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
            rcases hsx with hh | hh
            · exact h₁ hh.symm
            · exact h₂ hh.symm
        · rintro (h | h)
          · exact ⟨Or.inl h, by rw [h, hPa, hs0]; exact Set.mem_insert _ _⟩
          · exact ⟨Or.inr (Or.inl h), by rw [h, hPb, hs0]; exact Set.mem_insert _ _⟩
      rw [hset, Set.encard_pair hab]; exact Or.inr rfl
    · by_cases hse1 : s = e₁
      · have hset : {x ∈ ({a, b, d} : Set β) | s ∈ Q x} = ({a, d} : Set β) := by
          ext x
          simp only [Set.mem_sep_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          constructor
          · rintro ⟨hx, hsx⟩
            rcases hx with h | h | h
            · exact Or.inl h
            · exfalso
              rw [h, hPb, hse1] at hsx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
              rcases hsx with hh | hh
              · exact h₁ hh
              · exact h₁₂ hh
            · exact Or.inr h
          · rintro (h | h)
            · exact ⟨Or.inl h, by rw [h, hPa, hse1]; exact Set.mem_insert_of_mem _ rfl⟩
            · exact ⟨Or.inr (Or.inr h), by rw [h, hPd, hse1]; exact Set.mem_insert _ _⟩
        rw [hset, Set.encard_pair had]; exact Or.inr rfl
      · by_cases hse2 : s = e₂
        · have hset : {x ∈ ({a, b, d} : Set β) | s ∈ Q x} = ({b, d} : Set β) := by
            ext x
            simp only [Set.mem_sep_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
            constructor
            · rintro ⟨hx, hsx⟩
              rcases hx with h | h | h
              · exfalso
                rw [h, hPa, hse2] at hsx
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
                rcases hsx with hh | hh
                · exact h₂ hh
                · exact h₁₂ hh.symm
              · exact Or.inl h
              · exact Or.inr h
            · rintro (h | h)
              · exact ⟨Or.inr (Or.inl h), by rw [h, hPb, hse2]; exact Set.mem_insert_of_mem _ rfl⟩
              · exact ⟨Or.inr (Or.inr h), by rw [h, hPd, hse2]; exact Set.mem_insert_of_mem _ rfl⟩
          rw [hset, Set.encard_pair hbd]; exact Or.inr rfl
        · -- s ∉ {0, e₁, e₂}: the set is empty
          have hset : {x ∈ ({a, b, d} : Set β) | s ∈ Q x} = (∅ : Set β) := by
            ext x
            simp only [Set.mem_sep_iff, Set.mem_empty_iff_false, iff_false]
            rintro ⟨hx, hsx⟩
            rcases hx with h | h | h
            · rw [h, hPa] at hsx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
              rcases hsx with hh | hh
              · exact hs0 hh
              · exact hse1 hh
            · rw [h, hPb] at hsx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
              rcases hsx with hh | hh
              · exact hs0 hh
              · exact hse2 hh
            · rw [h, hPd] at hsx
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hsx
              rcases hsx with hh | hh
              · exact hse1 hh
              · exact hse2 hh
          rw [hset, Set.encard_empty]; exact Or.inl rfl

/-! ## Lemma 2.1 -/

theorem lemma_2_1 (hV : V(G).Finite) (hE : E(G).Finite) (hloop : G.IsLoopless)
    (hcubic : G.IsCubic) (hP : G.IsTwoElementAssignment P) :
    G.HasCycleDoubleCover := by
  have hdeg : ∀ s : Gamma, ∀ x ∈ V(G.restrict {f | s ∈ P f}),
      (G.restrict {f | s ∈ P f}).degree x = 0 ∨ (G.restrict {f | s ∈ P f}).degree x = 2 := by
    have hkey := (fact_2_1a hV hE hloop P).1 hP.encard_paletteIncidenceSet
    intro s x hx
    rw [Graph.vertexSet_restrict] at hx
    exact hkey s x hx
  have hdecomp : ∀ s : Gamma, ∃ D : Multiset (Graph α β),
      (∀ C ∈ D, (G.restrict {f | s ∈ P f}).IsCycle C) ∧
        ∀ e ∈ E(G.restrict {f | s ∈ P f}), D.edgeMultiplicity e = 1 := by
    intro s
    have hVs : V(G.restrict {f | s ∈ P f}).Finite := by
      rw [Graph.vertexSet_restrict]; exact hV
    have hEs : E(G.restrict {f | s ∈ P f}).Finite := by
      rw [Graph.edgeSet_restrict]; exact hE.subset Set.inter_subset_left
    exact fact_2_1b_decomposition hVs hEs (restrict_loopless hloop _) (hdeg s)
  choose D hD using hdecomp
  exact ⟨∑ s : Gamma, D s, fact_2_1d hV hE hloop hcubic hP D (fun s => (hD s).1)
    (fun s => (hD s).2)⟩

end Workspace.Facts.Lemma21
