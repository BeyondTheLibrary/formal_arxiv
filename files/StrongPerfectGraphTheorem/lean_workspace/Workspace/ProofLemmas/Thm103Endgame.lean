/-  Helper leaf for the printed proof of **10.3** (Chudnovsky–Robertson–Seymour–Thomas,
    *The Strong Perfect Graph Theorem*, printed p. 58).

    The last step of the printed proof reads:

      *"So `f₁-⋯-fₙ` satisfies 10.1.4, and therefore we may assume that for some `i` with
       `1 ≤ i ≤ 3`, `f₁` is adjacent to the two vertices in `A \ {aᵢ}`, and `fₙ` has at
       least one neighbour in `Rᵢ \ aᵢ`, and there are no other edges between
       `{f₁,…,fₙ}` and `V(K) \ {aᵢ}`.  Suppose first that `i > 1`, `i = 2` say.  Then both
       `f₁, fₙ` have neighbours in `V(R₂) ∪ V(R₃)`, and so from the minimality of `F` it
       follows that `n = 1` and `f₁ = v₁`.  But then `f₁` can be linked onto the triangle
       `B`, via the path between `f₁` and `b₁` with interior in
       `{v₂,…,v_m} ∪ V(R₁ \ a₁)`, the path between `f₁` and `b₂` with interior in
       `V(R₂ \ a₂)`, and the path `f₁-a₃-R₃-b₃`, contrary to 2.4.  Hence `i = 1` …"*

    This module is exactly that *"Suppose first that `i > 1` … contrary to 2.4"* paragraph.

    Encoding.  The paper's `R₁,R₂,R₃` are `R 0, R 1, R 2`; the paper's distinguished rung
    (the one whose interior contains `x₁`) is `R 0`, so the paper's *"`i > 1`"* is `i ≠ 0`.
    The paper's *"up to the symmetry between `A` and `B`"* is the pair `(c, d)`, which is
    either `(a, b)` or `(b, a)`: `c` is the triangle two of whose vertices `v₁` sees, and
    `d` is the triangle that `v₁` gets linked onto.  `j` and `k` are the two indices other
    than `i`, so `{c j, c k} = C \ {c i}`; one of them is `0`.  `v₁` is the single vertex
    `f₁ = fₙ` (`n = 1`); the last hypothesis is the 10.1.4 clause *"there are no other
    edges between `{f₁,…,fₙ}` and `V(K) \ {cᵢ}`"* specialised to that one vertex.

    Proof sketch (the paper's): `v₁` is linked onto the triangle `{d 0, d 1, d 2}` by the
    three paths listed above (the first uses `F` connected, `x₁` an attachment, and the
    minimality of `F`), so 2.4 makes `v₁` adjacent to two of `d 0, d 1, d 2`.  But by the
    last hypothesis the only neighbour of `v₁` in `{d 0, d 1, d 2}` is `d i` (the two others
    lie outside `{c j, c k} ∪ V(R i)`, since the three paths of a prism are pairwise
    disjoint and `a p ≠ b q` for all `p, q`) — a contradiction.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Statements.S02.Thm_2_4
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm101LinkOntoTriangle
import Workspace.ProofLemmas.Thm103UniqueAttach

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm103Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!  We first prove the one oriented case used in the printed paragraph:
`c = a`, `d = b`, and the exceptional rung is `R 1`.  The three linking sectors are

* a path in `F ∪ (R 0).tail`, with its initial vertex `v` removed;
* `(R 1).tail`;
* `R 2`.

Thus the first two sectors omit their `a`-ends and the third is the only one that retains
one.  The prism cross-edge axiom consequently leaves only the three edges of the `b`-triangle.
The uniqueness lemma for the nonzero-rung attachment makes every vertex of `F \ {v}`
anticomplete to the other two sectors. -/

private theorem oriented_one (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {z : V | z ∈ R 0} ∪ {z : V | z ∈ R 1} ∪ {z : V | z ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (x₁ : V) (hx₁ : IsAttachment G F K x₁) (hx₁R : x₁ ∈ SPGT.interior (R 0))
    (hFmin : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
      (∃ z, IsAttachment G F' K z ∧ z ∉ R 0) → F' = F)
    (v : V) (hv : v ∈ F)
    (_hva0 : G.Adj v (a 0)) (hva2 : G.Adj v (a 2))
    (y : V) (hy : y ∈ R 1) (hyne : y ≠ a 1) (hvy : G.Adj v y)
    (hother : ∀ m ∈ K, m ≠ a 1 → G.Adj v m →
      m = a 0 ∨ m = a 2 ∨ m ∈ R 1) : False := by
  classical
  let hp : ∀ t : Fin 3, IsPathFrom G (R t) (a t) (b t) :=
    fun t => HyperprismFromPrism.formPrism_path hprism t
  have hlen : ∀ t : Fin 3, 2 ≤ (R t).length :=
    fun t => HyperprismFromPrism.formPrism_two_le_length hprism t
  have htailPath : ∀ t : Fin 3, IsPathList G (R t).tail := by
    intro t
    exact HyperprismRungStructure.isPathList_tail (hp t).1 (hlen t)
  have htailLast : ∀ t : Fin 3, (R t).tail.getLast? = some (b t) := by
    intro t
    rw [← List.drop_one, List.getLast?_drop, if_neg (by have := hlen t; omega)]
    exact (hp t).2.2
  have hRmemK : ∀ t : Fin 3, ∀ z ∈ R t, z ∈ K := by
    intro t z hz
    rw [hK]
    rcases HyperprismBasics.fin3_cases t with rfl | rfl | rfl
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr hz)
    · exact Or.inr hz
  have hFnotR : ∀ z ∈ F, ∀ t : Fin 3, z ∉ R t := by
    intro z hz t hzt
    exact hFK hz (hRmemK t z hzt)
  have htailMem : ∀ t : Fin 3, ∀ {z : V}, z ∈ (R t).tail ↔ z ∈ R t ∧ z ≠ a t := by
    intro t z
    exact HyperprismRungStructure.mem_tail_iff_of_pathFrom (hp t)
  have hx₁tail : x₁ ∈ (R 0).tail := by
    apply (htailMem 0).2
    have h := (PathBasics.mem_interior_iff_of_pathFrom (hp 0)).mp hx₁R
    exact ⟨h.1, h.2.1⟩
  have hb0tail : b 0 ∈ (R 0).tail := by
    exact (htailMem 0).2 ⟨PathBasics.getLast_mem (hp 0).2.2, (hprism.2.2.1 0 0).symm⟩
  have htail0conn : ConnectedSet G {z : V | z ∈ (R 0).tail} :=
    InducedPathExtraction.connectedSet_setOf_mem_of_isPathList (htailPath 0)
  have hSconn : ConnectedSet G (F ∪ {z : V | z ∈ (R 0).tail}) := by
    apply ConnectedSetUnionAttach.connectedSet_union hFconn htail0conn
    right
    obtain ⟨f, hf, hxf⟩ := hx₁.2
    exact ⟨f, hf, x₁, hx₁tail, hxf.symm⟩
  have hvneB0 : v ≠ b 0 := by
    intro heq
    exact hFK hv (heq ▸ hRmemK 0 (b 0) (PathBasics.getLast_mem (hp 0).2.2))
  obtain ⟨q, hq, hqS⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hSconn (Or.inl hv) (Or.inr hb0tail)
  have hqlen : 2 ≤ q.length :=
    HyperprismBasics.two_le_length_of_ends_ne hq hvneB0
  have hqtailPath : IsPathList G q.tail :=
    HyperprismRungStructure.isPathList_tail hq.1 hqlen
  have hqtailLast : q.tail.getLast? = some (b 0) := by
    rw [← List.drop_one, List.getLast?_drop, if_neg (by omega)]
    exact hq.2.2
  have hqtailSub : ∀ z ∈ q.tail,
      z ∈ (F \ {v}) ∪ {z : V | z ∈ (R 0).tail} := by
    intro z hz
    have hzq : z ∈ q := (HyperprismRungStructure.mem_tail_iff_of_pathFrom hq).mp hz |>.1
    have hzv : z ≠ v := (HyperprismRungStructure.mem_tail_iff_of_pathFrom hq).mp hz |>.2
    rcases hqS z hzq with hzF | hzR
    · exact Or.inl ⟨hzF, by simpa using hzv⟩
    · exact Or.inr hzR
  have hqNeighbor : ∃ z ∈ q.tail, G.Adj v z := by
    have h1 : 1 < q.length := by omega
    have h0 : 0 < q.length := by omega
    let z := q[1]'h1
    have hzq : z ∈ q := List.getElem_mem h1
    have hzv : z ≠ v := by
      rw [← PathBasics.getElem_zero_of_head? hq.2.1 h0]
      exact PathBasics.path_ne_of_ne_index hq.1 h1 h0 (by omega)
    have hzt : z ∈ q.tail :=
      (HyperprismRungStructure.mem_tail_iff_of_pathFrom hq).2 ⟨hzq, hzv⟩
    refine ⟨z, hzt, ?_⟩
    have hadj := PathBasics.path_adj_succ hq.1 (show 0 + 1 < q.length by omega)
    rw [PathBasics.getElem_zero_of_head? hq.2.1 h0] at hadj
    exact hadj

  let p : Fin 3 → List V := ![q.tail, (R 1).tail, R 2]
  let S : Fin 3 → Set V :=
    ![(F \ {v}) ∪ {z : V | z ∈ (R 0).tail},
      {z : V | z ∈ (R 1).tail}, {z : V | z ∈ R 2}]
  have hdisj01 : ∀ z ∈ S 0, z ∉ S 1 := by
    intro z hz0 hz1
    change z ∈ (F \ {v}) ∪ {z : V | z ∈ (R 0).tail} at hz0
    change z ∈ (R 1).tail at hz1
    have hz1R : z ∈ R 1 := (htailMem 1).mp hz1 |>.1
    rcases hz0 with hzF | hzR0
    · exact hFnotR z hzF.1 1 hz1R
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 0) (j := 1)
        (by decide) z ((htailMem 0).mp hzR0 |>.1) hz1R
  have hdisj02 : ∀ z ∈ S 0, z ∉ S 2 := by
    intro z hz0 hz2
    change z ∈ (F \ {v}) ∪ {z : V | z ∈ (R 0).tail} at hz0
    change z ∈ R 2 at hz2
    rcases hz0 with hzF | hzR0
    · exact hFnotR z hzF.1 2 hz2
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 0) (j := 2)
        (by decide) z ((htailMem 0).mp hzR0 |>.1) hz2
  have hdisj12 : ∀ z ∈ S 1, z ∉ S 2 := by
    intro z hz1 hz2
    change z ∈ (R 1).tail at hz1
    change z ∈ R 2 at hz2
    exact HyperprismFromPrism.formPrism_disjoint hprism (i := 1) (j := 2)
      (by decide) z ((htailMem 1).mp hz1 |>.1) hz2

  have huniq := Thm103UniqueAttach.thm103_unique_attach G a b R K F hprism hK hFK hFconn
    x₁ hx₁ hx₁R hFmin
  have hcross01 : ∀ x ∈ S 0, ∀ z ∈ S 1, G.Adj x z → x = b 0 ∧ z = b 1 := by
    intro x hx z hz hxz
    change x ∈ (F \ {v}) ∪ {w : V | w ∈ (R 0).tail} at hx
    change z ∈ (R 1).tail at hz
    have hzR : z ∈ R 1 := (htailMem 1).mp hz |>.1
    rcases hx with hxF | hxR
    · have hxv : x = v := huniq x hxF.1 v hv
          ⟨z, Or.inl hzR, hxz⟩ ⟨y, Or.inl hy, hvy⟩
      exact False.elim (hxF.2 (by simpa [hxv]))
    · rcases (HyperprismFromPrism.formPrism_cross hprism (i := 0) (j := 1)
          (by decide) x ((htailMem 0).mp hxR |>.1) z hzR).mp hxz with ha | hb
      · exact False.elim (((htailMem 0).mp hxR).2 ha.1)
      · exact hb
  have hcross02 : ∀ x ∈ S 0, ∀ z ∈ S 2, G.Adj x z → x = b 0 ∧ z = b 2 := by
    intro x hx z hz hxz
    change x ∈ (F \ {v}) ∪ {w : V | w ∈ (R 0).tail} at hx
    change z ∈ R 2 at hz
    rcases hx with hxF | hxR
    · have hxv : x = v := huniq x hxF.1 v hv
          ⟨z, Or.inr hz, hxz⟩ ⟨y, Or.inl hy, hvy⟩
      exact False.elim (hxF.2 (by simpa [hxv]))
    · rcases (HyperprismFromPrism.formPrism_cross hprism (i := 0) (j := 2)
          (by decide) x ((htailMem 0).mp hxR |>.1) z hz).mp hxz with ha | hb
      · exact False.elim (((htailMem 0).mp hxR).2 ha.1)
      · exact hb
  have hcross12 : ∀ x ∈ S 1, ∀ z ∈ S 2, G.Adj x z → x = b 1 ∧ z = b 2 := by
    intro x hx z hz hxz
    change x ∈ (R 1).tail at hx
    change z ∈ R 2 at hz
    rcases (HyperprismFromPrism.formPrism_cross hprism (i := 1) (j := 2)
        (by decide) x ((htailMem 1).mp hx |>.1) z hz).mp hxz with ha | hb
    · exact False.elim (((htailMem 1).mp hx).2 ha.1)
    · exact hb

  have hlink : VertexCanBeLinkedOntoTriangle G v (b 0) (b 1) (b 2) := by
    apply Thm101LinkOntoTriangle.canBeLinkedOntoTriangle_of_sectors G v b p S
    · exact hprism.2.1
    · intro t
      fin_cases t
      · exact hqtailPath
      · exact htailPath 1
      · exact (hp 2).1
    · intro t
      fin_cases t
      · exact Or.inr hqtailLast
      · exact Or.inr (htailLast 1)
      · exact Or.inr (hp 2).2.2
    · intro t z hz
      fin_cases t
      · exact hqtailSub z hz
      · exact hz
      · exact hz
    · intro t u htu z hzt hzu
      fin_cases t <;> fin_cases u
      · exact htu rfl
      · exact hdisj01 z hzt hzu
      · exact hdisj02 z hzt hzu
      · exact hdisj01 z hzu hzt
      · exact htu rfl
      · exact hdisj12 z hzt hzu
      · exact hdisj02 z hzu hzt
      · exact hdisj12 z hzu hzt
      · exact htu rfl
    · intro t u htu x hx z hz hxz
      fin_cases t <;> fin_cases u
      · exact False.elim (htu rfl)
      · exact hcross01 x hx z hz hxz
      · exact hcross02 x hx z hz hxz
      · have h := hcross01 z hz x hx hxz.symm
        exact ⟨h.2, h.1⟩
      · exact False.elim (htu rfl)
      · exact hcross12 x hx z hz hxz
      · have h := hcross02 z hz x hx hxz.symm
        exact ⟨h.2, h.1⟩
      · have h := hcross12 z hz x hx hxz.symm
        exact ⟨h.2, h.1⟩
      · exact False.elim (htu rfl)
    · intro t
      fin_cases t
      · exact hqNeighbor
      · exact ⟨y, (htailMem 1).2 ⟨hy, hyne⟩, hvy⟩
      · exact ⟨a 2, PathBasics.head_mem (hp 2).2.1, hva2⟩

  have hnb0 : ¬ G.Adj v (b 0) := by
    intro hvb
    have hb0K := hRmemK 0 (b 0) (PathBasics.getLast_mem (hp 0).2.2)
    rcases hother (b 0) hb0K (hprism.2.2.1 1 0).symm hvb with h | h | h
    · exact (hprism.2.2.1 0 0) h.symm
    · exact (hprism.2.2.1 2 0) h.symm
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 0) (j := 1)
        (by decide) (b 0) (PathBasics.getLast_mem (hp 0).2.2) h
  have hnb2 : ¬ G.Adj v (b 2) := by
    intro hvb
    have hb2K := hRmemK 2 (b 2) (PathBasics.getLast_mem (hp 2).2.2)
    rcases hother (b 2) hb2K (hprism.2.2.1 1 2).symm hvb with h | h | h
    · exact (hprism.2.2.1 0 2) h.symm
    · exact (hprism.2.2.1 2 2) h.symm
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 2) (j := 1)
        (by decide) (b 2) (PathBasics.getLast_mem (hp 2).2.2) h
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG v (b 0) (b 1) (b 2) hlink with h | h | h
  · exact hnb0 h.1
  · exact hnb0 h.1
  · exact hnb2 h.2

private theorem oriented (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {z : V | z ∈ R 0} ∪ {z : V | z ∈ R 1} ∪ {z : V | z ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (x₁ : V) (hx₁ : IsAttachment G F K x₁) (hx₁R : x₁ ∈ SPGT.interior (R 0))
    (hFmin : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
      (∃ z, IsAttachment G F' K z ∧ z ∉ R 0) → F' = F)
    (i j k : Fin 3) (hi : i ≠ 0) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v : V) (hv : v ∈ F) (hvaj : G.Adj v (a j)) (hvak : G.Adj v (a k))
    (y : V) (hy : y ∈ R i) (hyne : y ≠ a i) (hvy : G.Adj v y)
    (hother : ∀ m ∈ K, m ≠ a i → G.Adj v m →
      m = a j ∨ m = a k ∨ m ∈ R i) : False := by
  classical
  have hcases :
      (i = 1 ∧ j = 0 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨
      (i = 2 ∧ j = 0 ∧ k = 1) ∨ (i = 2 ∧ j = 1 ∧ k = 0) := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp_all
  rcases hcases with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact oriented_one G hG a b R K F hprism hK hFK hFconn x₁ hx₁ hx₁R hFmin
      v hv hvaj hvak y hy hyne hvy hother
  · apply oriented_one G hG a b R K F hprism hK hFK hFconn x₁ hx₁ hx₁R hFmin
      v hv hvak hvaj y hy hyne hvy
    intro m hm hne hadj
    rcases hother m hm hne hadj with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  · let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have hp' := PrismSymmetry.formPrism_perm hprism σ
    have hs0 : σ 0 = 0 := by decide
    have hs1 : σ 1 = 2 := by decide
    have hs2 : σ 2 = 1 := by decide
    have hK' : K = {z : V | z ∈ R (σ 0)} ∪ {z : V | z ∈ R (σ 1)} ∪
        {z : V | z ∈ R (σ 2)} := by
      simpa [hs0, hs1, hs2, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hK
    have hx₁R' : x₁ ∈ SPGT.interior (R (σ 0)) := by simpa [hs0] using hx₁R
    have hFmin' : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
        (∃ z, IsAttachment G F' K z ∧ z ∉ R (σ 0)) → F' = F := by
      simpa [hs0] using hFmin
    have hva0' : G.Adj v (a (σ 0)) := by simpa [hs0] using hvaj
    have hva2' : G.Adj v (a (σ 2)) := by simpa [hs2] using hvak
    have hy' : y ∈ R (σ 1) := by simpa [hs1] using hy
    have hyne' : y ≠ a (σ 1) := by simpa [hs1] using hyne
    have hother' : ∀ m ∈ K, m ≠ a (σ 1) → G.Adj v m →
        m = a (σ 0) ∨ m = a (σ 2) ∨ m ∈ R (σ 1) := by
      simpa [hs0, hs1, hs2] using hother
    exact oriented_one G hG (fun t => a (σ t)) (fun t => b (σ t)) (fun t => R (σ t))
      K F hp' hK' hFK hFconn x₁ hx₁ hx₁R' hFmin' v hv hva0' hva2' y hy' hyne' hvy hother'
  · let σ : Equiv.Perm (Fin 3) := Equiv.swap 1 2
    have hp' := PrismSymmetry.formPrism_perm hprism σ
    have hs0 : σ 0 = 0 := by decide
    have hs1 : σ 1 = 2 := by decide
    have hs2 : σ 2 = 1 := by decide
    have hK' : K = {z : V | z ∈ R (σ 0)} ∪ {z : V | z ∈ R (σ 1)} ∪
        {z : V | z ∈ R (σ 2)} := by
      simpa [hs0, hs1, hs2, Set.union_assoc, Set.union_left_comm, Set.union_comm] using hK
    have hx₁R' : x₁ ∈ SPGT.interior (R (σ 0)) := by simpa [hs0] using hx₁R
    have hFmin' : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
        (∃ z, IsAttachment G F' K z ∧ z ∉ R (σ 0)) → F' = F := by
      simpa [hs0] using hFmin
    have hva0' : G.Adj v (a (σ 0)) := by simpa [hs0] using hvak
    have hva2' : G.Adj v (a (σ 2)) := by simpa [hs2] using hvaj
    have hy' : y ∈ R (σ 1) := by simpa [hs1] using hy
    have hyne' : y ≠ a (σ 1) := by simpa [hs1] using hyne
    have hother' : ∀ m ∈ K, m ≠ a (σ 1) → G.Adj v m →
        m = a (σ 0) ∨ m = a (σ 2) ∨ m ∈ R (σ 1) := by
      intro m hm hne hadj
      rcases hother m hm (by simpa [hs1] using hne) hadj with h | h | h
      · exact Or.inr (Or.inl (by simpa [hs2] using h))
      · exact Or.inl (by simpa [hs0] using h)
      · exact Or.inr (Or.inr (by simpa [hs1] using h))
    exact oriented_one G hG (fun t => a (σ t)) (fun t => b (σ t)) (fun t => R (σ t))
      K F hp' hK' hFK hFconn x₁ hx₁ hx₁R' hFmin' v hv hva0' hva2' y hy' hyne' hvy hother'

/-- **"Suppose first that `i > 1` … contrary to 2.4"** (printed p. 58, in the proof of
10.3). -/
theorem thm103_endgame (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hFmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (x₁ : V) (hx₁ : IsAttachment G F K x₁) (hx₁R : x₁ ∈ SPGT.interior (R 0))
    (hFmin : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
      (∃ z, IsAttachment G F' K z ∧ z ∉ R 0) → F' = F)
    (c d : Fin 3 → V) (hcd : (c = a ∧ d = b) ∨ (c = b ∧ d = a))
    (i j k : Fin 3) (hi : i ≠ 0) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (v₁ : V) (hv₁ : v₁ ∈ F)
    (hadjj : G.Adj v₁ (c j)) (hadjk : G.Adj v₁ (c k))
    (y : V) (hy : y ∈ R i) (hyne : y ≠ c i) (hadjy : G.Adj v₁ y)
    (hother : ∀ m ∈ K, m ≠ c i → G.Adj v₁ m → m = c j ∨ m = c k ∨ m ∈ R i) :
    False := by
  classical
  rcases hcd with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · subst c
    subst d
    exact oriented G hG a b R K F hprism hK hFK hFconn x₁ hx₁ hx₁R hFmin
      i j k hi hij hik hjk v₁ hv₁ hadjj hadjk y hy hyne hadjy hother
  · subst c
    subst d
    let R' : Fin 3 → List V := fun t => (R t).reverse
    have hp' : FormPrism G b a (R' 0) (R' 1) (R' 2) :=
      PrismSymmetry.formPrism_swap hprism
    have hK' : K = {z : V | z ∈ R' 0} ∪ {z : V | z ∈ R' 1} ∪
        {z : V | z ∈ R' 2} := by simpa [R'] using hK
    have hx₁R' : x₁ ∈ SPGT.interior (R' 0) := by
      change x₁ ∈ SPGT.interior (R 0).reverse
      exact (PathBasics.mem_interior_reverse (p := R 0)).2 hx₁R
    have hFmin' : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
        (∃ z, IsAttachment G F' K z ∧ z ∉ R' 0) → F' = F := by
      simpa [R'] using hFmin
    have hy' : y ∈ R' i := by simpa [R'] using hy
    have hother' : ∀ m ∈ K, m ≠ b i → G.Adj v₁ m →
        m = b j ∨ m = b k ∨ m ∈ R' i := by simpa [R'] using hother
    exact oriented G hG b a R' K F hp' hK' hFK hFconn x₁ hx₁ hx₁R' hFmin'
      i j k hi hij hik hjk v₁ hv₁ hadjj hadjk y hy' hyne hadjy hother'

end Workspace.ProofLemmas.Thm103Endgame
