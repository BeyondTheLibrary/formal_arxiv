import Mathlib
import Workspace.Types.MultigraphBasic
import Workspace.Types.Connectivity
import Workspace.Types.Bridge
import Workspace.Types.Cycle
import Workspace.Types.CycleDoubleCover
import Workspace.PriorWorkProofs.Jaeger.Moves
import Workspace.PriorWork.Fleischner
import Workspace.PriorWork.Veblen

/-!
# Jaeger's reduction — the CDC lift across the reroute

Lifts a cycle double cover of `reroute G v₁ v₂ e₁ e₂` back to `G`, serving both degree-2
suppression and the degree-≥4 Fleischner split with a single lemma `cdc_lift_reroute`.

For a CDC `D` of `G' = reroute G v₁ v₂ e₁ e₂` and each cycle `C ∈ D`, set

  `F C := E(C) ∪ (if e₁ ∈ E(C) then {e₂} else ∅)`,   `L C := G.restrict (F C)`.

The key degree identity

  `(L C).degree x = C.degree x + (if e₁ ∈ E(C) ∧ x = v then 2 else 0)`

makes every `L C` even, so Veblen's decomposition (`veblen_even_decomposition`) breaks it into
cycles of `G`; binding these over `D` gives a CDC of `G`.
-/

open Set
open scoped Graph
open scoped Classical

namespace Workspace.PriorWorkProofs.Jaeger

open Workspace.Types.Cycle Workspace.Types.CycleDoubleCover

variable {α β : Type*} {G : Graph α β} {v : α}

/-! ## Structural facts about a cycle of the reroute -/

/-- For an edge `f ≠ e₁` of a cycle `C` of the reroute, `G` and `C` see the same incidences
(the reroute only changes `e₁` and deletes `e₂`, and `e₂ ∉ E(C)`). -/
private theorem reroute_cycle_inc_iff {v1 v2 : α} {e1 e2 : β}
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {C : Graph α β} (hC : (reroute G v1 v2 e1 e2).IsCycle C)
    {f : β} (hfC : f ∈ E(C)) (hfe1 : f ≠ e1) (x : α) :
    (G.Inc f x ↔ C.Inc f x) := by
  have hCle : C ≤ reroute G v1 v2 e1 e2 := hC.le
  have hfe2 : f ≠ e2 := by
    intro h
    have hmem : f ∈ E(reroute G v1 v2 e1 e2) := Graph.IsSubgraph.edgeSet_mono hCle hfC
    rw [edgeSet_reroute he1 he2 hne] at hmem
    exact hmem.2 (by simpa using h)
  constructor
  · rintro ⟨y, hxy⟩
    obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet hfC
    have hGab : G.IsLink f a b := by
      have hr := hCle.isLink_mono hab
      rw [reroute_isLink] at hr
      rcases hr with ⟨rfl, -, -⟩ | ⟨-, -, hg⟩
      · exact absurd rfl hfe1
      · exact hg
    rcases hxy.eq_and_eq_or_eq_and_eq hGab with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨b, hab⟩
    · exact ⟨a, hab.symm⟩
  · rintro ⟨y, hxy⟩
    have hr := hCle.isLink_mono hxy
    rw [reroute_isLink] at hr
    rcases hr with ⟨rfl, -, -⟩ | ⟨-, -, hg⟩
    · exact absurd rfl hfe1
    · exact ⟨y, hg⟩

/-- In a cycle `C` of the reroute that uses `e₁`, the edge `e₁` joins `v₁`–`v₂` (as relabelled). -/
private theorem reroute_cycle_e1_link {v1 v2 : α} {e1 e2 : β}
    {C : Graph α β} (hC : (reroute G v1 v2 e1 e2).IsCycle C) (hfC : e1 ∈ E(C)) :
    C.IsLink e1 v1 v2 := by
  have hCle : C ≤ reroute G v1 v2 e1 e2 := hC.le
  obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet hfC
  have hr := hCle.isLink_mono hab
  rw [reroute_isLink] at hr
  rcases hr with ⟨-, -, hd⟩ | ⟨hfe1, -, -⟩
  · rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab
    · exact hab.symm
  · exact absurd rfl hfe1

/-- Only `e₁` can be a loop of a cycle `C` of the reroute (`G` is loopless, and every edge other
than `e₁` keeps its `G`-incidences), and `e₁` is a loop of `C` iff `v₁ = v₂` (at the vertex `v₁`). -/
private theorem reroute_cycle_isLoopAt_iff {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {C : Graph α β} (hC : (reroute G v1 v2 e1 e2).IsCycle C)
    {f : β} {x : α} (hloop : C.IsLoopAt f x) : f = e1 ∧ v1 = v2 ∧ x = v1 := by
  have hCle : C ≤ reroute G v1 v2 e1 e2 := hC.le
  have hfC : f ∈ E(C) := hloop.inc.edge_mem
  have hlink : C.IsLink f x x := hloop
  by_cases hfe1 : f = e1
  · have hce1 : C.IsLink e1 v1 v2 := reroute_cycle_e1_link hC (hfe1 ▸ hfC)
    have hlink' : C.IsLink e1 x x := hfe1 ▸ hlink
    -- both `C.IsLink e1 x x` and `C.IsLink e1 v1 v2`, so `{x} = {v1, v2}`
    rcases hlink'.eq_and_eq_or_eq_and_eq hce1 with ⟨rfl, hb⟩ | ⟨rfl, hb⟩
    · exact ⟨hfe1, hb, rfl⟩
    · exact ⟨hfe1, hb.symm, hb⟩
  · exfalso
    have hr := hCle.isLink_mono hlink
    rw [reroute_isLink] at hr
    rcases hr with ⟨heq, -, -⟩ | ⟨-, -, hg⟩
    · exact hfe1 heq
    · exact hll f x hg
/-- Peeling one element `e` from a finite set: its cardinality is that of `S \ {e}` plus the
`0/1` indicator of `e ∈ S`. -/
private lemma ncard_peel (S : Set β) (hS : S.Finite) (e : β) :
    S.ncard = (S \ {e}).ncard + (if e ∈ S then 1 else 0) := by
  by_cases h : e ∈ S
  · rw [if_pos h]
    have hins : insert e (S \ {e}) = S := by
      rw [Set.insert_diff_singleton, Set.insert_eq_of_mem h]
    have hnotin : e ∉ S \ {e} := by simp
    conv_lhs => rw [← hins]
    rw [Set.ncard_insert_of_notMem hnotin hS.diff]
  · rw [if_neg h, add_zero, Set.diff_singleton_eq_self h]

/-- `G.Inc e x` for a non-loop edge `e = a b` holds exactly at its two ends. -/
private lemma inc_iff_ends {a b x : α} {e : β} (he : G.IsLink e a b) :
    G.Inc e x ↔ (x = a ∨ x = b) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases hy.eq_and_eq_or_eq_and_eq he with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (rfl | rfl)
    · exact ⟨b, he⟩
    · exact ⟨a, he.symm⟩

/-- **The key degree identity.** The lifted subgraph `L C = G.restrict (F C)` has degree at `x`
equal to `C`'s degree, except `+2` at the suppressed vertex `v` when `C` uses `e₁`. Hence every
degree of `L C` is even (a cycle is `2`-regular). -/
private theorem lift_degree_eq {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (hEfin : E(G).Finite)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {C : Graph α β} (hC : (reroute G v1 v2 e1 e2).IsCycle C) (x : α) :
    (G.restrict (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅))).degree x
      = C.degree x + (if e1 ∈ E(C) ∧ x = v then 2 else 0) := by
  classical
  have hv1 : v ≠ v1 := fun h => hll e1 v (h ▸ he1)
  have hv2 : v ≠ v2 := fun h => hll e2 v (h ▸ he2)
  have hCle : C ≤ reroute G v1 v2 e1 e2 := hC.le
  have hEC : E(C) ⊆ E(G) := by
    refine (Graph.IsSubgraph.edgeSet_mono hCle).trans ?_
    rw [edgeSet_reroute he1 he2 hne]; exact Set.diff_subset
  have he2nC : e2 ∉ E(C) := by
    intro h
    have hm := Graph.IsSubgraph.edgeSet_mono hCle h
    rw [edgeSet_reroute he1 he2 hne] at hm; exact hm.2 rfl
  have hGe1 : G.Inc e1 x ↔ (x = v ∨ x = v1) := inc_iff_ends he1
  have hGe2 : G.Inc e2 x ↔ (x = v ∨ x = v2) := inc_iff_ends he2
  set F : Set β := E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅) with hFdef
  set L : Graph α β := G.restrict F with hLdef
  have hLloop : L.IsLoopless := fun e y hl => hll e y (hl.mono Graph.restrict_le)
  have hLincSubG : L.incidenceSet x ⊆ E(G) :=
    (L.incidenceSet_subset_edgeSet x).trans (Graph.IsSubgraph.edgeSet_mono Graph.restrict_le)
  have hLincFin : (L.incidenceSet x).Finite := hEfin.subset hLincSubG
  have hCincFin : (C.incidenceSet x).Finite :=
    hEfin.subset ((C.incidenceSet_subset_edgeSet x).trans hEC)
  have hCloopFin : (C.loopSet x).Finite :=
    hEfin.subset ((C.loopSet_subset_incidenceSet x).trans
      ((C.incidenceSet_subset_edgeSet x).trans hEC))
  have hmemL : ∀ f, f ∈ L.incidenceSet x ↔ (G.Inc f x ∧ f ∈ F) := by
    intro f; rw [Graph.mem_incidenceSet, hLdef, Graph.restrict_inc]
  -- membership facts as `↔` for rewriting the indicators
  have he1inL : (e1 ∈ L.incidenceSet x) ↔ (e1 ∈ F ∧ G.Inc e1 x) := (hmemL e1).trans And.comm
  have he2inL : (e2 ∈ L.incidenceSet x \ {e1}) ↔ (e2 ∈ F ∧ G.Inc e2 x) := by
    rw [Set.mem_diff, Set.mem_singleton_iff, hmemL]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨h2, h1⟩, hne.symm⟩
  have he1F : e1 ∈ F ↔ e1 ∈ E(C) := by
    rw [hFdef]; constructor
    · rintro (h | h)
      · exact h
      · split_ifs at h with hc
        · rw [Set.mem_singleton_iff] at h; exact absurd h hne
        · exact absurd h (Set.notMem_empty e1)
    · intro h; exact Or.inl h
  have he2F : e2 ∈ F ↔ e1 ∈ E(C) := by
    rw [hFdef]; constructor
    · rintro (h | h)
      · exact absurd h he2nC
      · split_ifs at h with hc
        · exact hc
        · exact absurd h (Set.notMem_empty e2)
    · intro h; exact Or.inr (by rw [if_pos h]; exact rfl)
  have hCe1inc : C.Inc e1 x ↔ (e1 ∈ E(C) ∧ (x = v1 ∨ x = v2)) := by
    constructor
    · intro h
      exact ⟨h.edge_mem, (inc_iff_ends (reroute_cycle_e1_link hC h.edge_mem)).mp h⟩
    · rintro ⟨hmem, hx⟩
      exact (inc_iff_ends (reroute_cycle_e1_link hC hmem)).mpr hx
  have hCe1loop : C.IsLoopAt e1 x ↔ (e1 ∈ E(C) ∧ v1 = v2 ∧ x = v1) := by
    constructor
    · intro h
      obtain ⟨-, hvv, hxv1⟩ := reroute_cycle_isLoopAt_iff hll he1 he2 hne hC h
      exact ⟨h.inc.edge_mem, hvv, hxv1⟩
    · rintro ⟨hmem, hvv, hxv1⟩
      have hlink := reroute_cycle_e1_link hC hmem
      rw [hxv1]; exact hvv.symm ▸ hlink
  -- the common `A = C.incidenceSet x \ {e1}` and the two peelings of `L`
  have hAeq : (L.incidenceSet x \ {e1}) \ {e2} = C.incidenceSet x \ {e1} := by
    ext f
    simp only [Set.mem_diff, Set.mem_singleton_iff, hmemL, Graph.mem_incidenceSet]
    constructor
    · rintro ⟨⟨⟨hInc, hfF⟩, hfe1⟩, hfe2⟩
      have hfC : f ∈ E(C) := by
        rw [hFdef] at hfF
        rcases hfF with h | h
        · exact h
        · split_ifs at h with hc
          · rw [Set.mem_singleton_iff] at h; exact absurd h hfe2
          · exact absurd h (Set.notMem_empty f)
      exact ⟨(reroute_cycle_inc_iff he1 he2 hne hC hfC hfe1 x).mp hInc, hfe1⟩
    · rintro ⟨hCInc, hfe1⟩
      have hfC : f ∈ E(C) := hCInc.edge_mem
      have hfe2 : f ≠ e2 := fun h => he2nC (h ▸ hfC)
      refine ⟨⟨⟨(reroute_cycle_inc_iff he1 he2 hne hC hfC hfe1 x).mpr hCInc, ?_⟩, hfe1⟩, hfe2⟩
      rw [hFdef]; exact Or.inl hfC
  have hCloopA : C.loopSet x \ {e1} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro f hf
    rw [Set.mem_diff, Graph.mem_loopSet, Set.mem_singleton_iff] at hf
    obtain ⟨hfe1, -, -⟩ := reroute_cycle_isLoopAt_iff hll he1 he2 hne hC hf.1
    exact hf.2 hfe1
  have hL1 := ncard_peel (L.incidenceSet x) hLincFin e1
  have hL2 := ncard_peel (L.incidenceSet x \ {e1}) hLincFin.diff e2
  rw [hAeq] at hL2
  have hCdeg : C.degree x = (C.incidenceSet x \ {e1}).ncard
      + (if e1 ∈ C.incidenceSet x then 1 else 0) + (if e1 ∈ C.loopSet x then 1 else 0) := by
    rw [Graph.degree_def, ncard_peel (C.incidenceSet x) hCincFin e1,
        ncard_peel (C.loopSet x) hCloopFin e1, hCloopA, Set.ncard_empty]
    ring
  -- assemble and reduce to an arithmetic identity in the indicators
  rw [hLloop.degree_eq_ncard_incidenceSet, hL1, hL2, hCdeg, he1inL, he2inL, he1F, he2F,
    Graph.mem_incidenceSet, Graph.mem_loopSet, hCe1inc, hCe1loop]
  simp only [hGe1, hGe2]
  clear hmemL he1inL he2inL he1F he2F hCe1inc hCe1loop hL1 hL2 hCdeg hGe1 hGe2 hAeq hCloopA
    hLloop hLincFin hLincSubG hCincFin hCloopFin hEC he2nC hCle hFdef hLdef
  by_cases he1C : e1 ∈ E(C) <;> by_cases hxv : x = v <;> by_cases hxv1 : x = v1 <;>
    by_cases hxv2 : x = v2 <;> by_cases hvv : v1 = v2 <;> simp_all <;> omega

/-- Veblen-decompose the lift `L C` of a cycle `C` of the reroute: a multiset of cycles of `G`
covering each edge of `F C` exactly once (and no other edge). -/
private theorem exists_decomp {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (hVfin : V(G).Finite) (hEfin : E(G).Finite)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {C : Graph α β} (hC : (reroute G v1 v2 e1 e2).IsCycle C) :
    ∃ DC : Multiset (Graph α β), (∀ Ci ∈ DC, G.IsCycle Ci) ∧
      ∀ f, DC.edgeMultiplicity f
        = if f ∈ (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅)) then 1 else 0 := by
  classical
  have hEC : E(C) ⊆ E(G) :=
    (Graph.IsSubgraph.edgeSet_mono hC.le).trans
      (by rw [edgeSet_reroute he1 he2 hne]; exact Set.diff_subset)
  set F : Set β := E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅) with hFdef
  have hFsubG : F ⊆ E(G) := by
    intro f hf
    rw [hFdef, Set.mem_union] at hf
    rcases hf with h | h
    · exact hEC h
    · split_ifs at h with hc
      · rw [Set.mem_singleton_iff] at h; exact h ▸ he2.edge_mem
      · exact absurd h (Set.notMem_empty f)
  have hLle : G.restrict F ≤ G := Graph.restrict_le
  have hLloop : (G.restrict F).IsLoopless := fun e y hl => hll e y (hl.mono hLle)
  have hVL : V(G.restrict F).Finite := by rw [Graph.vertexSet_restrict]; exact hVfin
  have hEL : E(G.restrict F).Finite := hEfin.subset (Graph.IsSubgraph.edgeSet_mono hLle)
  have hELeq : E(G.restrict F) = F := by
    rw [Graph.edgeSet_restrict, Set.inter_eq_right.mpr hFsubG]
  have hEven : ∀ x ∈ V(G.restrict F), Even ((G.restrict F).degree x) := by
    intro x _
    have hkey := lift_degree_eq hll hEfin he1 he2 hne hC x
    rw [← hFdef] at hkey
    rw [hkey]
    have hCe : Even (C.degree x) := by
      by_cases hx : x ∈ V(C)
      · rw [hC.degree_eq hx]; exact even_two
      · rw [Graph.degree_eq_zero_of_notMem hx]; exact ⟨0, rfl⟩
    by_cases hcond : e1 ∈ E(C) ∧ x = v
    · rw [if_pos hcond]; obtain ⟨k, hk⟩ := hCe; exact ⟨k + 1, by omega⟩
    · rw [if_neg hcond, add_zero]; exact hCe
  obtain ⟨DC, hcyc, hcover⟩ := Workspace.PriorWork.veblen_even_decomposition (G.restrict F) hVL hEL hLloop hEven
  refine ⟨DC, fun Ci hCi => (hcyc Ci hCi).mono hLle, fun f => ?_⟩
  by_cases hf : f ∈ F
  · rw [if_pos hf]; exact hcover f (by rw [hELeq]; exact hf)
  · rw [if_neg hf, Multiset.edgeMultiplicity_eq_zero_iff]
    intro Ci hCi hfCi
    have hmem : f ∈ E(G.restrict F) := Graph.IsSubgraph.edgeSet_mono (hcyc Ci hCi).le hfCi
    rw [hELeq] at hmem; exact hf hmem

/-- Multiplicity in a bind is the sum of the members' multiplicities. -/
private lemma edgeMultiplicity_bind (D : Multiset (Graph α β))
    (g : Graph α β → Multiset (Graph α β)) (f : β) :
    (D.bind g).edgeMultiplicity f = (D.map (fun C => (g C).edgeMultiplicity f)).sum := by
  classical
  induction D using Multiset.induction with
  | empty => simp [Multiset.edgeMultiplicity_def]
  | cons C D ih =>
    rw [Multiset.cons_bind, Multiset.map_cons, Multiset.sum_cons, ← ih,
      Multiset.edgeMultiplicity_def, Multiset.edgeMultiplicity_def, Multiset.edgeMultiplicity_def,
      Multiset.countP_add]

/-- Sum of `0/1` indicators over a multiset equals `countP`. -/
private lemma sum_map_indicator (D : Multiset (Graph α β)) (p : Graph α β → Prop)
    [DecidablePred p] : (D.map (fun C => if p C then (1 : ℕ) else 0)).sum = D.countP p := by
  induction D using Multiset.induction with
  | empty => simp
  | cons C D ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, ih, Multiset.countP_cons, add_comm]

/-- **The unified reroute CDC lift.** -/
theorem cdc_lift_reroute {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (hVfin : V(G).Finite) (hEfin : E(G).Finite)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {D : Multiset (Graph α β)} (hD : (reroute G v1 v2 e1 e2).IsCycleDoubleCover D) :
    G.HasCycleDoubleCover := by
  classical
  -- for each cycle `C` of the reroute, its Veblen-decomposed lift
  let gg : Graph α β → Multiset (Graph α β) := fun C =>
    if hCc : (reroute G v1 v2 e1 e2).IsCycle C
    then (exists_decomp hll hVfin hEfin he1 he2 hne hCc).choose else 0
  have hggspec : ∀ C, (reroute G v1 v2 e1 e2).IsCycle C →
      (∀ Ci ∈ gg C, G.IsCycle Ci) ∧
        ∀ f, (gg C).edgeMultiplicity f
          = if f ∈ (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅)) then 1 else 0 := by
    intro C hCc
    have hgg : gg C = (exists_decomp hll hVfin hEfin he1 he2 hne hCc).choose := dif_pos hCc
    rw [hgg]; exact (exists_decomp hll hVfin hEfin he1 he2 hne hCc).choose_spec
  refine ⟨D.bind gg, ?_, ?_⟩
  · -- every member is a cycle of `G`
    intro Ci hCi
    rw [Multiset.mem_bind] at hCi
    obtain ⟨C, hCD, hCigg⟩ := hCi
    exact (hggspec C (hD.isCycle_of_mem hCD)).1 Ci hCigg
  · -- every edge of `G` has multiplicity `2`
    intro f hf
    rw [edgeMultiplicity_bind]
    have hmapeq : D.map (fun C => (gg C).edgeMultiplicity f)
        = D.map (fun C => if f ∈ (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅)) then 1 else 0) := by
      apply Multiset.map_congr rfl
      intro C hCD
      exact (hggspec C (hD.isCycle_of_mem hCD)).2 f
    rw [hmapeq, sum_map_indicator]
    by_cases hfe2 : f = e2
    · have hpred : ∀ C ∈ D, (f ∈ (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅))) ↔ (e1 ∈ E(C)) := by
        intro C hCD
        have hCc := hD.isCycle_of_mem hCD
        have he2nC : e2 ∉ E(C) := by
          intro h
          have hm := Graph.IsSubgraph.edgeSet_mono hCc.le h
          rw [edgeSet_reroute he1 he2 hne] at hm; exact hm.2 rfl
        rw [hfe2, Set.mem_union]
        constructor
        · rintro (h | h)
          · exact absurd h he2nC
          · split_ifs at h with hc
            · exact hc
            · exact absurd h (Set.notMem_empty e2)
        · intro h; exact Or.inr (by rw [if_pos h]; exact rfl)
      rw [Multiset.countP_congr rfl (by intro C hCD; exact propext (hpred C hCD)),
        ← Multiset.edgeMultiplicity_def]
      have he1G' : e1 ∈ E(reroute G v1 v2 e1 e2) := by
        rw [edgeSet_reroute he1 he2 hne]; exact ⟨he1.edge_mem, by simpa using hne⟩
      exact hD.edgeMultiplicity_eq he1G'
    · have hpred : ∀ C ∈ D, (f ∈ (E(C) ∪ (if e1 ∈ E(C) then {e2} else ∅))) ↔ (f ∈ E(C)) := by
        intro C hCD
        rw [Set.mem_union]
        constructor
        · rintro (h | h)
          · exact h
          · split_ifs at h with hc
            · rw [Set.mem_singleton_iff] at h; exact absurd h hfe2
            · exact absurd h (Set.notMem_empty f)
        · intro h; exact Or.inl h
      rw [Multiset.countP_congr rfl (by intro C hCD; exact propext (hpred C hCD)),
        ← Multiset.edgeMultiplicity_def]
      have hfG' : f ∈ E(reroute G v1 v2 e1 e2) := by
        rw [edgeSet_reroute he1 he2 hne]; exact ⟨hf, by simpa using hfe2⟩
      exact hD.edgeMultiplicity_eq hfG'

/-- **Move D2 — the CDC lift (degree-2 suppression).** -/
theorem cdc_lift_reroute_degree_two {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (hVfin : V(G).Finite) (hEfin : E(G).Finite) (hdeg : G.degree v = 2)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {D : Multiset (Graph α β)} (hD : (reroute G v1 v2 e1 e2).IsCycleDoubleCover D) :
    G.HasCycleDoubleCover :=
  cdc_lift_reroute hll hVfin hEfin he1 he2 hne hD

/-- **Move SP — the CDC lift (degree-≥4 split, uses Veblen).** -/
theorem cdc_lift_reroute_split {v1 v2 : α} {e1 e2 : β}
    (hll : G.IsLoopless) (hVfin : V(G).Finite) (hEfin : E(G).Finite)
    (he1 : G.IsLink e1 v v1) (he2 : G.IsLink e2 v v2) (hne : e1 ≠ e2)
    {D : Multiset (Graph α β)} (hD : (reroute G v1 v2 e1 e2).IsCycleDoubleCover D) :
    G.HasCycleDoubleCover :=
  cdc_lift_reroute hll hVfin hEfin he1 he2 hne hD

end Workspace.PriorWorkProofs.Jaeger
