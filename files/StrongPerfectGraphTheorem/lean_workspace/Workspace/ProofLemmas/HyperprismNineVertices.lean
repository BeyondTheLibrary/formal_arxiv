import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismFromPrism

/-!
# 10.6, the tail of step (4): a fully degenerate hyperprism *is* an even prism

This module is the last two sentences of the printed proof of **10.6** (published version,
printed p. 62):

> *"Let `X` be the union of `S₁` and all components of `V(G) \ V(H)` whose attachment set is a
> subset of `S₁`, and let `Y = V(G) \ X`.  Then `|Y| ≥ 4`, and so either `(X,Y)` is a proper
> 2-join in `G`, or both `A₁, B₁` have one element and `X` is the vertex set of a path between
> these two vertices.  **We may assume the latter, and the same for `S₂` and `S₃`; and so `G`
> is an even prism.  Then either it admits a proper 2-join, or `|V(G)| = 9`.**"*

`thm_10_6_all_degenerate` is the bold part: the *degenerate* branch of that trichotomy, taken
for all three of `S₁, S₂, S₃` at once, yields exactly the first two disjuncts of 10.6's
conclusion.

## How the printed sentences map onto the Lean proof

* *"both `Aᵢ, Bᵢ` have one element"* is `hA : ∀ i, A i = {a i}` and `hB : ∀ i, B i = {b i}`;
  *"`Xᵢ` is the vertex set of a path between these two vertices"* is
  `hP : ∀ i, IsPathFrom G (P i) (a i) (b i)` together with `hcover`, which says the three
  vertex sets `V(Pᵢ)` exhaust `V(G)` (each `Xᵢ` contains `Sᵢ`, and by claim (2) every
  component of `V(G) \ V(H)` lands in one of them).
* *"and so `G` is an even prism"* splits into two halves that the paper runs together.
  - **A prism.**  The three triangle edges come from the hyperprism's *"`Aᵢ` is complete to
    `Aⱼ`"*, and the cross-condition from its *"there are no other edges between `Sᵢ` and
    `Sⱼ`"* — once `hout` has pushed an edge between `V(Pᵢ)` and `V(Pⱼ)` back into `Sᵢ × Sⱼ`.
    Since `|Aᵢ| = |Bᵢ| = 1`, *"`u ∈ Aᵢ`"* becomes *"`u = aᵢ`"*, which is what `FormPrism`
    wants.  Vertex-disjointness of the three paths is then automatic
    (`HyperprismFromPrism.formPrism_disjoint`), so it is not assumed.
  - **Even.**  This is where claim (1) of the printed proof is used: `Pᵢ` need not be a rung
    (its interior may contain whole components of `V(G) \ V(H)`), so instead glue `Pᵢ` to an
    honest `j`-rung `R` for some `j ≠ i`.  `Pᵢ ++ R.reverse` is a hole, so `|Pᵢ| + |R|` is
    even, and `R` is even by claim (1) (`HyperprismBasics.rung_even`); hence so is `Pᵢ`.
* *"Then either it admits a proper 2-join, or `|V(G)| = 9`."*  All three lengths are even and
  `≥ 2`, so `|V(G)| = |P₁| + |P₂| + |P₃|` is `9` exactly when all three lengths are `2`.
  Otherwise some `Pᵢ` has length `≥ 4`, and `proper2Join_of_long` cuts it: with
  `p = Pᵢ = p₀-p₁-⋯-p_m`,
  ```
  X₁ = {p₀, p₁, p₂, p₃},   A₁ = {p₀} = {aᵢ},   B₁ = {p₃},
  X₂ = V(G) \ X₁,          A₂ = {aⱼ, a_k},     B₂ = {p₄}
  ```
  is a proper 2-join.  The only edges leaving `X₁` are `aᵢaⱼ`, `aᵢa_k` and `p₃p₄`; the fourth
  bullet of `IsProper2Join` is satisfied on the `X₁` side because `G|X₁` is a path of length
  exactly `3`, which is odd and `≥ 3`, and holds vacuously on the `X₂` side because
  `|A₂| = 2`.  **The cut is at `p₃`, not at the middle of `Pᵢ`**: cutting off the interior of
  `Pᵢ` (or splitting the prism into "one path" and "two paths") leaves an *even* path on one
  side and so fails that fourth bullet — those 2-joins are exactly the improper ones.
-/

set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismNineVertices

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

private theorem dl {X Y : Set V} (h : Disjoint X Y) {x : V} (hx : x ∈ X) : x ∉ Y :=
  Set.disjoint_left.mp h hx

/-- Three pairwise distinct indices exhaust `Fin 3`. -/
private theorem fin3_triple : ∀ i j k l : Fin 3, i ≠ j → i ≠ k → j ≠ k →
    (l = i ∨ l = j ∨ l = k) := by decide

/-! ### Cutting a long path of the prism: the proper 2-join -/

/-- **A prism one of whose paths has length `≥ 4` admits a proper 2-join.**

`X₁` is the first four vertices `p₀-p₁-p₂-p₃` of that path, `X₂` everything else.  The only
edges between them are `p₀aⱼ`, `p₀a_k` (the triangle edges at `p₀ = aᵢ`) and `p₃p₄`, so
`A₁ = {p₀}`, `A₂ = {aⱼ, a_k}`, `B₁ = {p₃}`, `B₂ = {p₄}`.  `G|X₁` is a path of length `3`,
which is odd and `≥ 3`, and `|A₂| = 2`, so the last bullet of `IsProper2Join` holds on both
sides. -/
private theorem proper2Join_of_long [Fintype V] [DecidableEq V]
    {a b : Fin 3 → V} {P : Fin 3 → List V}
    (hP : ∀ l, IsPathFrom G (P l) (a l) (b l))
    (hpc : ∀ l m : Fin 3, l ≠ m → ∀ u ∈ P l, ∀ v ∈ P m,
        (G.Adj u v ↔ (u = a l ∧ v = a m) ∨ (u = b l ∧ v = b m)))
    (hdisj : ∀ l m : Fin 3, l ≠ m → ∀ u ∈ P l, u ∉ P m)
    (hcov : ∀ v : V, ∃ l : Fin 3, v ∈ P l)
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h5 : 5 ≤ (P i).length) :
    AdmitsProper2Join G := by
  ------------------------------------------------------------------
  -- Notation for the four vertices that matter on `Pᵢ`.
  ------------------------------------------------------------------
  have hnd : (P i).Nodup := PathBasics.path_nodup (hP i).1
  have hpos : 0 < (P i).length := by omega
  have h0 : (P i)[0]'hpos = a i := PathBasics.getElem_zero_of_head? (hP i).2.1 hpos
  have hlastget : (P i)[(P i).length - 1]'(by omega) = b i :=
    PathBasics.getElem_last_of_getLast? (hP i).2.2 hpos
  obtain ⟨p3, h3lt, hp3⟩ : ∃ (z : V) (h : 3 < (P i).length), (P i)[3]'h = z :=
    ⟨_, by omega, rfl⟩
  obtain ⟨p4, h4lt, hp4⟩ : ∃ (z : V) (h : 4 < (P i).length), (P i)[4]'h = z :=
    ⟨_, by omega, rfl⟩
  ------------------------------------------------------------------
  -- Splitting `Pᵢ` after its fourth vertex.
  ------------------------------------------------------------------
  have hsplit : (P i).take 4 ++ (P i).drop 4 = P i := List.take_append_drop 4 (P i)
  have hndsplit : ((P i).take 4 ++ (P i).drop 4).Nodup := by rw [hsplit]; exact hnd
  obtain ⟨hndT, hndD, hTD⟩ := List.nodup_append.mp hndsplit
  have hmemsplit : ∀ v : V, v ∈ P i ↔ v ∈ (P i).take 4 ∨ v ∈ (P i).drop 4 := by
    intro v
    constructor
    · intro hv
      exact List.mem_append.mp (show v ∈ (P i).take 4 ++ (P i).drop 4 by rw [hsplit]; exact hv)
    · intro hv
      rw [← hsplit]
      exact List.mem_append.mpr hv
  have hTsub : ∀ v ∈ (P i).take 4, v ∈ P i := fun v hv => (hmemsplit v).mpr (Or.inl hv)
  have hDsub : ∀ v ∈ (P i).drop 4, v ∈ P i := fun v hv => (hmemsplit v).mpr (Or.inr hv)
  -- membership in the first block, by index
  have hT4 : (P i).take 4 = ((P i).drop 0).take (3 - 0 + 1) := by simp
  have hmemT : ∀ v : V, v ∈ (P i).take 4 ↔
      ∃ (s : ℕ) (hs : s < (P i).length), s ≤ 3 ∧ (P i)[s]'hs = v := by
    intro v
    rw [hT4, PathBasics.mem_slice_iff (P i) (show (0 : ℕ) ≤ 3 by omega) (by omega)]
    constructor
    · rintro ⟨s, hs, -, h2, h3⟩
      exact ⟨s, hs, h2, h3⟩
    · rintro ⟨s, hs, h2, h3⟩
      exact ⟨s, hs, Nat.zero_le _, h2, h3⟩
  have hlenT : ((P i).take 4).length = 4 := by
    rw [List.length_take]; omega
  -- the four named vertices, placed
  have haiT : a i ∈ (P i).take 4 := (hmemT (a i)).mpr ⟨0, hpos, by omega, h0⟩
  have hp3T : p3 ∈ (P i).take 4 := (hmemT p3).mpr ⟨3, h3lt, by omega, hp3⟩
  have hnotT : ∀ (s : ℕ) (hs : s < (P i).length), 4 ≤ s → (P i)[s]'hs ∉ (P i).take 4 := by
    intro s hs hs4 hmem
    obtain ⟨t, ht, ht3, hteq⟩ := (hmemT _).mp hmem
    exact absurd (hnd.getElem_inj_iff.mp hteq) (by omega)
  have hp4nT : p4 ∉ (P i).take 4 := by rw [← hp4]; exact hnotT 4 h4lt le_rfl
  have hp4D : p4 ∈ (P i).drop 4 :=
    ((hmemsplit p4).mp (by rw [← hp4]; exact List.getElem_mem h4lt)).resolve_left hp4nT
  have hbinT : b i ∉ (P i).take 4 := by
    rw [← hlastget]; exact hnotT _ (by omega) (by omega)
  have hbiD : b i ∈ (P i).drop 4 :=
    ((hmemsplit (b i)).mp (PathBasics.getLast_mem (hP i).2.2)).resolve_left hbinT
  -- the ends of the other two paths
  have hajP : a j ∈ P j := PathBasics.head_mem (hP j).2.1
  have hakP : a k ∈ P k := PathBasics.head_mem (hP k).2.1
  have hbjP : b j ∈ P j := PathBasics.getLast_mem (hP j).2.2
  have hajak : G.Adj (a j) (a k) :=
    (hpc j k hjk (a j) hajP (a k) hakP).mpr (Or.inl ⟨rfl, rfl⟩)
  have hbibj : G.Adj (b i) (b j) :=
    (hpc i j hij (b i) (PathBasics.getLast_mem (hP i).2.2) (b j) hbjP).mpr
      (Or.inr ⟨rfl, rfl⟩)
  ------------------------------------------------------------------
  -- The two sides of the 2-join.
  ------------------------------------------------------------------
  have hX1X2 : Disjoint ({v : V | v ∈ (P i).take 4})
      ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) := by
    refine Set.disjoint_left.mpr ?_
    rintro v hv ((h | h) | h)
    · exact hTD v hv v h rfl
    · exact hdisj i j hij v (hTsub v hv) h
    · exact hdisj i k hik v (hTsub v hv) h
  have hcover2 : ({v : V | v ∈ (P i).take 4}) ∪
      ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) = Set.univ := by
    ext v
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨l, hl⟩ := hcov v
    rcases fin3_triple i j k l hij hik hjk with rfl | rfl | rfl
    · rcases (hmemsplit v).mp hl with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (Or.inl h))
    · exact Or.inr (Or.inl (Or.inr hl))
    · exact Or.inr (Or.inr hl)
  ------------------------------------------------------------------
  -- Connectivity of the two sides.
  ------------------------------------------------------------------
  have hX1conn : ConnectedSet G {v : V | v ∈ (P i).take 4} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (PathBasics.isPathList_take (hP i).1 (by omega))
  have hX2conn : ConnectedSet G
      ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) := by
    refine ConnectedSetUnionAttach.connectedSet_union
      (ConnectedSetUnionAttach.connectedSet_union
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
          (PathBasics.isPathList_drop (hP i).1 (by omega)))
        (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList (hP j).1)
        (Or.inr ⟨b i, hbiD, b j, hbjP, hbibj⟩))
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList (hP k).1)
      (Or.inr ⟨a j, Or.inr hajP, a k, hakP, hajak⟩)
  ------------------------------------------------------------------
  -- The edges between the two sides.
  ------------------------------------------------------------------
  have hcross : ∀ u ∈ ({v : V | v ∈ (P i).take 4}),
      ∀ v ∈ ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}),
      (G.Adj u v ↔
        ((u ∈ ({a i} : Set V) ∧ v ∈ ({a j, a k} : Set V)) ∨
         (u ∈ ({p3} : Set V) ∧ v ∈ ({p4} : Set V)))) := by
    intro u hu v hv
    have huP : u ∈ P i := hTsub u hu
    obtain ⟨s, hs, hs3, hsu⟩ := (hmemT u).mp hu
    constructor
    · intro hadj
      rcases hv with (h | h) | h
      · -- `v` is further along `Pᵢ`
        have hvnT : v ∉ (P i).take 4 := fun hc => hTD v hc v h rfl
        obtain ⟨t, ht, htv⟩ := List.getElem_of_mem (hDsub v h)
        have ht4 : 4 ≤ t := by
          by_contra hc
          exact hvnT ((hmemT v).mpr ⟨t, ht, by omega, htv⟩)
        have hadj' : G.Adj ((P i)[s]'hs) ((P i)[t]'ht) := by rw [hsu, htv]; exact hadj
        have hidx := (PathBasics.path_adj_iff (hP i).1 hs ht).mp hadj'
        have hst : s = 3 ∧ t = 4 := by omega
        refine Or.inr ⟨?_, ?_⟩
        · rw [← hsu, ← hp3]
          exact hnd.getElem_inj_iff.mpr hst.1
        · rw [← htv, ← hp4]
          exact hnd.getElem_inj_iff.mpr hst.2
      · -- `v` lies on `Pⱼ`
        rcases (hpc i j hij u huP v h).mp hadj with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, Or.inl e2⟩
        · exact absurd (e1 ▸ hu) hbinT
      · -- `v` lies on `P_k`
        rcases (hpc i k hik u huP v h).mp hadj with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact Or.inl ⟨e1, Or.inr e2⟩
        · exact absurd (e1 ▸ hu) hbinT
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · have hu1 : u = a i := h1
        have huP' : a i ∈ P i := by rw [← hu1]; exact huP
        rcases h2 with h2 | h2
        · rw [hu1, show v = a j from h2]
          exact (hpc i j hij (a i) huP' (a j) hajP).mpr (Or.inl ⟨rfl, rfl⟩)
        · rw [hu1, show v = a k from h2]
          exact (hpc i k hik (a i) huP' (a k) hakP).mpr (Or.inl ⟨rfl, rfl⟩)
      · rw [show u = p3 from h1, show v = p4 from h2, ← hp3, ← hp4]
        exact PathBasics.path_adj_succ (hP i).1 (show 3 + 1 < (P i).length by omega)
  ------------------------------------------------------------------
  -- Assembling `IsProper2Join`.
  ------------------------------------------------------------------
  have hajX2 : a j ∈ ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) :=
    Or.inl (Or.inr hajP)
  have hakX2 : a k ∈ ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) :=
    Or.inr hakP
  have hp4X2 : p4 ∈ ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) :=
    Or.inl (Or.inl hp4D)
  have hp4Pi : p4 ∈ P i := by rw [← hp4]; exact List.getElem_mem h4lt
  refine ⟨{v : V | v ∈ (P i).take 4},
    {v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k},
    hcover2, hX1X2, ({a i} : Set V), ({p3} : Set V), ({a j, a k} : Set V), ({p4} : Set V),
    ?_, ?_, ?_, ?_, ⟨a i, rfl⟩, ⟨p3, rfl⟩, ⟨a j, Or.inl rfl⟩, ⟨p4, rfl⟩, ?_, ?_,
    hcross, ?_, ?_, ?_, ?_⟩
  · -- `A₁ ⊆ X₁`
    rintro z rfl; exact haiT
  · -- `B₁ ⊆ X₁`
    rintro z rfl; exact hp3T
  · -- `A₂ ⊆ X₂`
    rintro z (rfl | rfl)
    · exact hajX2
    · exact hakX2
  · -- `B₂ ⊆ X₂`
    rintro z rfl; exact hp4X2
  · -- `Disjoint A₁ B₁`
    refine Set.disjoint_left.mpr ?_
    rintro z hz1 hz2
    have hzai : z = a i := hz1
    have hzp3 : z = p3 := hz2
    have heq : a i = p3 := hzai.symm.trans hzp3
    rw [← h0, ← hp3] at heq
    have h03 := hnd.getElem_inj_iff.mp heq
    omega
  · -- `Disjoint A₂ B₂`
    refine Set.disjoint_left.mpr ?_
    rintro z hz1 hz2
    have hzp4 : z ∈ P i := by rw [show z = p4 from hz2]; exact hp4Pi
    rcases hz1 with hz1 | hz1
    · exact hdisj j i (Ne.symm hij) (a j) hajP (by rw [← show z = a j from hz1]; exact hzp4)
    · exact hdisj k i (Ne.symm hik) (a k) hakP (by rw [← show z = a k from hz1]; exact hzp4)
  · -- every component of `G|X₁` meets `A₁` and `B₁`
    intro D hD
    have hDeq : {v : V | v ∈ (P i).take 4} = D := hD.2.2 _ hD.1 (subset_refl _) hX1conn
    have haiD : a i ∈ D := by rw [← hDeq]; exact haiT
    have hp3D : p3 ∈ D := by rw [← hDeq]; exact hp3T
    exact ⟨⟨a i, haiD, rfl⟩, ⟨p3, hp3D, rfl⟩⟩
  · -- every component of `G|X₂` meets `A₂` and `B₂`
    intro D hD
    have hDeq : ({v : V | v ∈ (P i).drop 4} ∪ {v : V | v ∈ P j} ∪ {v : V | v ∈ P k}) = D :=
      hD.2.2 _ hD.1 (subset_refl _) hX2conn
    have hajD : a j ∈ D := by rw [← hDeq]; exact hajX2
    have hp4D' : p4 ∈ D := by rw [← hDeq]; exact hp4X2
    exact ⟨⟨a j, hajD, Or.inl rfl⟩, ⟨p4, hp4D', rfl⟩⟩
  · -- the fourth bullet on the `X₁` side: `G|X₁` is a path of length exactly `3`
    intro a' b' ha' hb' q hq hqset
    have hqmem : ∀ v : V, v ∈ q ↔ v ∈ (P i).take 4 := fun v => Set.ext_iff.mp hqset v
    have hfin : q.toFinset = ((P i).take 4).toFinset := by
      ext v
      simp only [List.mem_toFinset]
      exact hqmem v
    have hc1 := List.toFinset_card_of_nodup (PathBasics.path_nodup hq.1)
    have hc2 := List.toFinset_card_of_nodup hndT
    rw [hfin, hc2, hlenT] at hc1
    rw [PathBasics.pathLength_eq, ← hc1]
    exact ⟨by decide, by omega⟩
  · -- the fourth bullet on the `X₂` side: `|A₂| = 2`, so the hypothesis is unsatisfiable
    intro a' b' ha' hb' q hq hqset
    exfalso
    have h1 : a j = a' := by
      have hm : a j ∈ ({a j, a k} : Set V) := Or.inl rfl
      rw [ha'] at hm
      exact hm
    have h2 : a k = a' := by
      have hm : a k ∈ ({a j, a k} : Set V) := Or.inr rfl
      rw [ha'] at hm
      exact hm
    exact hajak.ne (h1.trans h2.symm)

/-! ### The tail of step (4) -/

/-- **The last two sentences of the printed proof of 10.6** (printed p. 62).

PAPER: *"We may assume the latter, and the same for `S₂` and `S₃`; and so `G` is an even
prism.  Then either it admits a proper 2-join, or `|V(G)| = 9`."*

The hypotheses are the degenerate branch of the trichotomy, taken for all three `Sᵢ`: each
`Aᵢ`, `Bᵢ` is a single vertex, and the paper's `Xᵢ` — which contains `Sᵢ` (`hSP`), receives all
the edges leaving it (`hout`), and together with the other two exhausts `V(G)` (`hcover`) — is
the vertex set of a path `Pᵢ` between them.  The conclusion is the disjunction of the first two
alternatives of `Workspace.Statements.S10.SPGT.thm_10_6`. -/
theorem thm_10_6_all_degenerate [Fintype V] [DecidableEq V]
    (hG : Berge G) (hH : IsHyperprism G A B C)
    (a b : Fin 3 → V) (hA : ∀ i, A i = {a i}) (hB : ∀ i, B i = {b i})
    (P : Fin 3 → List V)
    (hP : ∀ i, IsPathFrom G (P i) (a i) (b i))
    (hSP : ∀ i, A i ∪ B i ∪ C i ⊆ {v : V | v ∈ P i})
    (hout : ∀ i j : Fin 3, i ≠ j → ∀ u ∈ P i, ∀ v ∈ P j, G.Adj u v →
        u ∈ A i ∪ B i ∪ C i ∧ v ∈ A j ∪ B j ∪ C j)
    (hcover : {v : V | v ∈ P 0} ∪ {v : V | v ∈ P 1} ∪ {v : V | v ∈ P 2} = Set.univ) :
    ((∃ (a' b' : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a' b' R₁ R₂ R₃ ∧
        {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
      Fintype.card V = 9) ∨
    AdmitsProper2Join G := by
  have hmemA : ∀ (l : Fin 3), a l ∈ A l := fun l => by rw [hA l]; rfl
  have hmemB : ∀ (l : Fin 3), b l ∈ B l := fun l => by rw [hB l]; rfl
  ------------------------------------------------------------------
  -- *"and so `G` is an even prism"*, first half: the three paths form a prism.
  ------------------------------------------------------------------
  have hpc : ∀ l m : Fin 3, l ≠ m → ∀ u ∈ P l, ∀ v ∈ P m,
      (G.Adj u v ↔ (u = a l ∧ v = a m) ∨ (u = b l ∧ v = b m)) := by
    intro l m hlm u hu v hv
    constructor
    · intro hadj
      obtain ⟨huS, hvS⟩ := hout l m hlm u hu v hv hadj
      rcases cross hH hlm huS hvS hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [hA l] at h1; rw [hA m] at h2
        exact Or.inl ⟨h1, h2⟩
      · rw [hB l] at h1; rw [hB m] at h2
        exact Or.inr ⟨h1, h2⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact complete_A hH hlm _ (hmemA l) _ (hmemA m)
      · exact complete_B hH hlm _ (hmemB l) _ (hmemB m)
  have hanb : ∀ l m : Fin 3, a l ≠ b m := by
    intro l m h
    exact dl (hH.2.1 l m) (hmemA l) (by rw [hB m]; exact h)
  have hform : FormPrism G a b (P 0) (P 1) (P 2) :=
    ⟨fun l m hlm => complete_A hH hlm _ (hmemA l) _ (hmemA m),
      fun l m hlm => complete_B hH hlm _ (hmemB l) _ (hmemB m), hanb,
      hP 0, hP 1, hP 2,
      hpc 0 1 (by decide), hpc 0 2 (by decide), hpc 1 2 (by decide)⟩
  -- vertex-disjointness of the three paths is a consequence, not an assumption
  have hdisj : ∀ l m : Fin 3, l ≠ m → ∀ u ∈ P l, u ∉ P m := by
    intro l m hlm u hu
    exact HyperprismFromPrism.formPrism_disjoint (R := P) hform hlm u hu
  ------------------------------------------------------------------
  -- *"and so `G` is an even prism"*, second half: each `Pᵢ` is even (claim (1)).
  ------------------------------------------------------------------
  have hlen2 : ∀ l : Fin 3, 2 ≤ (P l).length := fun l =>
    two_le_length_of_ends_ne (hP l) (hanb l l)
  have heven : ∀ l : Fin 3, Even (SPGT.pathLength (P l)) := by
    intro l
    obtain ⟨m, hlm⟩ : ∃ m : Fin 3, l ≠ m := by
      rcases fin3_cases l with rfl | rfl | rfl
      exacts [⟨1, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩]
    obtain ⟨R, x, y, hR⟩ := exists_rung hH m
    have hxa : x = a m := by have h := hR.1; rw [hA m] at h; exact h
    have hyb : y = b m := by have h := hR.2.1; rw [hB m] at h; exact h
    have hRsub : ∀ u ∈ R, u ∈ P m := fun u hu => hSP m (rung_mem_S hR u hu)
    -- `Pₗ ++ R.reverse` is a hole
    have hhole : IsHoleList G (P l ++ R.reverse) := by
      refine PathGlue.glue_hole (hP l) (PathBasics.isPathFrom_reverse hR.2.2.1) ?_ ?_ ?_
      · intro u hu hcon
        exact hdisj l m hlm u hu (hRsub u (List.mem_reverse.mp hcon))
      · intro u hu v hv
        rw [hpc l m hlm u hu v (hRsub v (List.mem_reverse.mp hv)), hxa, hyb]
        exact or_comm
      · have := hlen2 l
        have := rung_two_le_length hH hR
        simp only [List.length_reverse]
        omega
    have hev : Even ((P l ++ R.reverse).length) := hG.1 _ hhole
    simp only [List.length_append, List.length_reverse] at hev
    have hRev : Even (SPGT.pathLength R) := rung_even hG hH hR
    have e1 : (P l).length = SPGT.pathLength (P l) + 1 :=
      PathBasics.length_eq_pathLength_add_one (hP l).1
    have e2 : R.length = SPGT.pathLength R + 1 :=
      PathBasics.length_eq_pathLength_add_one hR.2.2.1.1
    rw [e1, e2] at hev
    rw [Nat.even_iff] at hev hRev ⊢
    omega
  -- an even path with distinct ends has at least three vertices
  have hlen3 : ∀ l : Fin 3, 3 ≤ (P l).length := by
    intro l
    have h2 := hlen2 l
    have hE := heven l
    rw [PathBasics.pathLength_eq, Nat.even_iff] at hE
    omega
  ------------------------------------------------------------------
  -- *"Then either it admits a proper 2-join, or `|V(G)| = 9`."*
  ------------------------------------------------------------------
  have hcov : ∀ v : V, ∃ l : Fin 3, v ∈ P l := by
    intro v
    have hv : v ∈ ({v : V | v ∈ P 0} ∪ {v : V | v ∈ P 1} ∪ {v : V | v ∈ P 2}) := by
      rw [hcover]; trivial
    rcases hv with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  by_cases hall : ∀ l : Fin 3, (P l).length = 3
  · -- all three paths have length `2`: the prism has nine vertices
    left
    refine ⟨⟨a, b, P 0, P 1, P 2, ⟨hform, heven 0, heven 1, heven 2⟩, hcover⟩, ?_⟩
    have hnodupL : (P 0 ++ P 1 ++ P 2).Nodup := by
      rw [List.nodup_append, List.nodup_append]
      refine ⟨⟨(hP 0).1.2.1, (hP 1).1.2.1, ?_⟩, (hP 2).1.2.1, ?_⟩
      · intro x hx y hy hxy
        exact hdisj 0 1 (by decide) x hx (hxy ▸ hy)
      · intro x hx y hy hxy
        rcases List.mem_append.mp hx with hx' | hx'
        · exact hdisj 0 2 (by decide) x hx' (hxy ▸ hy)
        · exact hdisj 1 2 (by decide) x hx' (hxy ▸ hy)
    have hmemL : ∀ v : V, v ∈ P 0 ++ P 1 ++ P 2 := by
      intro v
      obtain ⟨l, hl⟩ := hcov v
      rcases fin3_cases l with rfl | rfl | rfl
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hl)))
      · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hl)))
      · exact List.mem_append.mpr (Or.inr hl)
    have hu : (P 0 ++ P 1 ++ P 2).toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (hmemL v)
    have hc := List.toFinset_card_of_nodup hnodupL
    rw [hu, Finset.card_univ] at hc
    simp only [List.length_append] at hc
    rw [hall 0, hall 1, hall 2] at hc
    omega
  · -- some path is longer: cut it
    right
    push Not at hall
    obtain ⟨l, hl⟩ := hall
    have h5 : 5 ≤ (P l).length := by
      have h3 := hlen3 l
      have hE := heven l
      rw [PathBasics.pathLength_eq, Nat.even_iff] at hE
      omega
    rcases fin3_cases l with rfl | rfl | rfl
    · exact proper2Join_of_long (i := 0) (j := 1) (k := 2) hP hpc hdisj hcov
        (by decide) (by decide) (by decide) h5
    · exact proper2Join_of_long (i := 1) (j := 0) (k := 2) hP hpc hdisj hcov
        (by decide) (by decide) (by decide) h5
    · exact proper2Join_of_long (i := 2) (j := 0) (k := 1) hP hpc hdisj hcov
        (by decide) (by decide) (by decide) h5

end Workspace.ProofLemmas.HyperprismNineVertices
