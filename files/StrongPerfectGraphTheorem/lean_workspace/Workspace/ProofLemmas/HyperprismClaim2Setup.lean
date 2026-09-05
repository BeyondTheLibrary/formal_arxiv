import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ExtremalChoice
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.HyperprismBasics
import Workspace.ProofLemmas.HyperprismRungStructure
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.Thm106Assembly

/-!
# Claim (2) of 10.6 — the shared vocabulary (P3/P5/P6 foundation)

The printed proof of claim (2) (pp. 60–62) opens

> *"For suppose not.  Choose `F` minimal, and let `X` be the set of attachments of `F` in
> `H`."*

and then runs three blocks, each ending *"contrary to the maximality of the hyperprism"*.
Following the project convention, each block is stated **positively** — *produce a strictly
larger hyperprism* — so that it carries no maximality hypothesis, and maximality is discharged
once, here, by `Set.ncard_lt_ncard`.

This module fixes the vocabulary the three blocks share:

* `BadSet` / `MinimalBad` — *"a connected `F ⊆ V(G) \ V(H)` whose attachment set is not
  local"*, and the minimal such.  `MinimalBad.local_of_ssubset` is the workhorse: **every
  proper connected subset of a minimal bad set has a local attachment set**, which is how the
  paper turns *"from the minimality of `F`"* into information about the neighbours of
  individual `fᵢ`.
* `BiggerHyperprism` — the positive form of *"contrary to the maximality of `V(H)`"*.
* `claim2_of_bigger` — the reduction: if every minimal bad set yields a strictly larger
  hyperprism, then `Thm106Assembly.Claim2` holds.
* the transports of all of this along `isHyperprism_perm` and `isHyperprism_swap`, so that the
  printed *"we may assume"*s cost two lines each.
* `no_edge_A_B` — inside one strip there are **no** edges from `Aᵢ` to `Bᵢ`, because such an
  edge would be an `i`-rung of length `1`, and claim (1) says every rung is even.  The printed
  proof uses this silently in every *"… is an odd hole"*.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.HyperprismClaim2Setup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.Thm106Assembly

variable {V : Type*} {G : SimpleGraph V} {A B C : Fin 3 → Set V}

/-! ### Three-fold unions -/

/-- Membership in `f 0 ∪ f 1 ∪ f 2`. -/
theorem mem_union3 {f : Fin 3 → Set V} {x : V} :
    x ∈ f 0 ∪ f 1 ∪ f 2 ↔ ∃ i : Fin 3, x ∈ f i := by
  constructor
  · rintro ((h | h) | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
    · exact ⟨2, h⟩
  · rintro ⟨i, hi⟩
    rcases fin3_cases i with rfl | rfl | rfl
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
    · exact Or.inr hi

theorem mem_union3_of {f : Fin 3 → Set V} {x : V} (i : Fin 3) (h : x ∈ f i) :
    x ∈ f 0 ∪ f 1 ∪ f 2 := mem_union3.mpr ⟨i, h⟩

/-- A three-fold union is invariant under relabelling the index. -/
theorem union3_perm (f : Fin 3 → Set V) (σ : Equiv.Perm (Fin 3)) :
    f (σ 0) ∪ f (σ 1) ∪ f (σ 2) = f 0 ∪ f 1 ∪ f 2 := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_union3 (f := fun i => f (σ i)).mp hx
    exact mem_union3_of (σ i) hi
  · intro hx
    obtain ⟨i, hi⟩ := mem_union3.mp hx
    refine mem_union3 (f := fun i => f (σ i)) |>.mpr ⟨σ.symm i, ?_⟩
    simpa using hi

/-! ### No edges between the two ends of one strip -/

/-- **Inside one strip there are no edges from `Aᵢ` to `Bᵢ`.**  Such an edge would be an
`i`-rung of length `1`, contradicting claim (1) (`HyperprismBasics.rung_even`).  The printed
proof relies on this in every *"… is an odd hole"* of claim (2). -/
theorem no_edge_A_B (hG : Berge G) (hH : IsHyperprism G A B C) (i : Fin 3) {a b : V}
    (ha : a ∈ A i) (hb : b ∈ B i) : ¬ G.Adj a b := by
  intro hadj
  have hpath : IsPathFrom G [a, b] a b :=
    ⟨PathBasics.isPathList_pair hadj, rfl, rfl⟩
  have hrung : IsRungFrom G A B C i [a, b] a b := by
    refine ⟨ha, hb, hpath, ?_⟩
    intro w hw
    simp [SPGT.interior] at hw
  have := rung_even hG hH hrung
  rw [PathBasics.pathLength_pair] at this
  exact (Nat.not_even_iff_odd.mpr ⟨0, rfl⟩) this

/-! ### Attachments -/

theorem mem_attachments {F K : Set V} {v : V} :
    v ∈ attachments G F K ↔ v ∈ K ∧ ∃ f ∈ F, G.Adj v f := Iff.rfl

theorem attachments_mono {F F' K : Set V} (h : F' ⊆ F) :
    attachments G F' K ⊆ attachments G F K := by
  rintro v ⟨hvK, f, hf, hadj⟩
  exact ⟨hvK, f, h hf, hadj⟩

theorem attachments_subset {F K : Set V} : attachments G F K ⊆ K := fun _ h => h.1

/-! ### `LocalForHyperprism`, in the form the proof uses -/

theorem localForHyperprism_iff {X : Set V} :
    LocalForHyperprism A B C X ↔
      (∃ i : Fin 3, X ⊆ A i ∪ B i ∪ C i) ∨ X ⊆ A 0 ∪ A 1 ∪ A 2 ∨ X ⊆ B 0 ∪ B 1 ∪ B 2 := by
  constructor
  · rintro (h | h | h | h | h)
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inl ⟨2, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (⟨i, hi⟩ | h | h)
    · rcases fin3_cases i with rfl | rfl | rfl
      · exact Or.inl hi
      · exact Or.inr (Or.inl hi)
      · exact Or.inr (Or.inr (Or.inl hi))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))

theorem localForHyperprism_perm {X : Set V} (σ : Equiv.Perm (Fin 3)) :
    LocalForHyperprism (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i)) X ↔
      LocalForHyperprism A B C X := by
  rw [localForHyperprism_iff, localForHyperprism_iff, union3_perm A σ, union3_perm B σ]
  constructor
  · rintro (⟨i, hi⟩ | h)
    · exact Or.inl ⟨σ i, hi⟩
    · exact Or.inr h
  · rintro (⟨i, hi⟩ | h)
    · refine Or.inl ⟨σ.symm i, ?_⟩
      simpa using hi
    · exact Or.inr h

theorem localForHyperprism_swap {X : Set V} :
    LocalForHyperprism B A C X ↔ LocalForHyperprism A B C X := by
  have hS : ∀ i : Fin 3, B i ∪ A i ∪ C i = A i ∪ B i ∪ C i := by
    intro i
    ext x
    constructor
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
    · rintro ((h | h) | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h
  rw [localForHyperprism_iff, localForHyperprism_iff]
  simp only [hS]
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)

/-- `hyperVerts` is symmetric in its first two arguments (an instance-free copy of
`Thm106Assembly.hyperVerts_swap`, which carries `[Fintype V] [DecidableEq V]`). -/
theorem hyperVerts_swap' (A B C : Fin 3 → Set V) :
    hyperVerts B A C = hyperVerts A B C := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    refine mem_hyperVerts_iff.mpr ⟨i, ?_⟩
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    refine mem_hyperVerts_iff.mpr ⟨i, ?_⟩
    rcases hi with (h | h) | h
    · exact Or.inl (Or.inr h)
    · exact Or.inl (Or.inl h)
    · exact Or.inr h

theorem hyperVerts_perm (A B C : Fin 3 → Set V) (σ : Equiv.Perm (Fin 3)) :
    hyperVerts (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i)) = hyperVerts A B C := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    exact mem_hyperVerts_iff.mpr ⟨σ i, hi⟩
  · intro hx
    obtain ⟨i, hi⟩ := mem_hyperVerts_iff.mp hx
    refine mem_hyperVerts_iff.mpr ⟨σ.symm i, ?_⟩
    simpa using hi

/-! ### Bad sets and the minimal one -/

/-- *"a connected subset `F` of `V(G) \ V(H)` whose set of attachments in `H` is not local"* —
the object the printed proof supposes to exist. -/
def BadSet (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V) : Prop :=
  ConnectedSet G F ∧ F ⊆ (hyperVerts A B C)ᶜ ∧
    ¬ LocalForHyperprism A B C (attachments G F (hyperVerts A B C))

/-- *"Choose `F` minimal"*.  Minimality is by cardinality, which for finite `V` implies
minimality under inclusion (`local_of_ssubset` below). -/
def MinimalBad (G : SimpleGraph V) (A B C : Fin 3 → Set V) (F : Set V) : Prop :=
  BadSet G A B C F ∧ ∀ F' : Set V, BadSet G A B C F' → F.ncard ≤ F'.ncard

theorem exists_minimalBad {F : Set V} (h : BadSet G A B C F) :
    ∃ F₀ : Set V, MinimalBad G A B C F₀ :=
  ExtremalChoice.exists_min_nat (BadSet G A B C) Set.ncard ⟨F, h⟩

/-- A bad set is nonempty: the empty set has no attachments, and `∅` is local. -/
theorem BadSet.nonempty {F : Set V} (h : BadSet G A B C F) : F.Nonempty := by
  rcases Set.eq_empty_or_nonempty F with rfl | hne
  · exact absurd (localForHyperprism_iff.mpr (Or.inr (Or.inl (by
      rintro v ⟨-, f, hf, -⟩; exact absurd hf (Set.notMem_empty f))))) h.2.2
  · exact hne

/-- **The engine of every *"from the minimality of `F`"* in the printed proof.**  A proper
connected subset of a minimal bad set has a *local* attachment set. -/
theorem MinimalBad.local_of_ssubset [Fintype V] {F F' : Set V} (h : MinimalBad G A B C F)
    (hsub : F' ⊆ F) (hne : F' ≠ F) (hconn : ConnectedSet G F') :
    LocalForHyperprism A B C (attachments G F' (hyperVerts A B C)) := by
  by_contra hnl
  have hbad : BadSet G A B C F' := ⟨hconn, hsub.trans h.1.2.1, hnl⟩
  exact hne (Set.eq_of_subset_of_ncard_le hsub (h.2 F' hbad) (Set.toFinite F))

/-! ### The positive form of *"contrary to the maximality of the hyperprism"* -/

/-- *"contrary to the maximality of `V(H)`"*, stated positively: a hyperprism with a strictly
larger vertex set.  Stating the three blocks of claim (2) this way keeps the maximality
hypothesis out of them entirely. -/
def BiggerHyperprism (G : SimpleGraph V) (A B C : Fin 3 → Set V) : Prop :=
  ∃ A' B' C' : Fin 3 → Set V,
    IsHyperprism G A' B' C' ∧ hyperVerts A B C ⊂ hyperVerts A' B' C'

theorem biggerHyperprism_perm {σ : Equiv.Perm (Fin 3)}
    (h : BiggerHyperprism G (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i))) :
    BiggerHyperprism G A B C := by
  obtain ⟨A', B', C', hH, hlt⟩ := h
  exact ⟨A', B', C', hH, by rwa [hyperVerts_perm] at hlt⟩

theorem biggerHyperprism_swap (h : BiggerHyperprism G B A C) : BiggerHyperprism G A B C := by
  obtain ⟨A', B', C', hH, hlt⟩ := h
  exact ⟨A', B', C', hH, by rwa [hyperVerts_swap'] at hlt⟩

theorem badSet_perm {F : Set V} (σ : Equiv.Perm (Fin 3)) :
    BadSet G (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i)) F ↔ BadSet G A B C F := by
  unfold BadSet
  rw [hyperVerts_perm, localForHyperprism_perm]

theorem badSet_swap {F : Set V} : BadSet G B A C F ↔ BadSet G A B C F := by
  unfold BadSet
  rw [hyperVerts_swap', localForHyperprism_swap]

theorem minimalBad_perm {F : Set V} (σ : Equiv.Perm (Fin 3))
    (h : MinimalBad G A B C F) :
    MinimalBad G (fun i => A (σ i)) (fun i => B (σ i)) (fun i => C (σ i)) F :=
  ⟨(badSet_perm σ).mpr h.1, fun F' hF' => h.2 F' ((badSet_perm σ).mp hF')⟩

theorem minimalBad_swap {F : Set V} (h : MinimalBad G A B C F) : MinimalBad G B A C F :=
  ⟨badSet_swap.mpr h.1, fun F' hF' => h.2 F' (badSet_swap.mp hF')⟩

/-! ### The reduction of `Claim2` -/

/-- **Claim (2) from the three blocks, in positive form.**  The printed proof of claim (2) is
*"for suppose not; choose `F` minimal; … contrary to the maximality of the hyperprism"*.  Once
every block is stated as *"a strictly larger hyperprism exists"*, that outer shell is this
lemma: the `by_cases` on `AdmitsBalancedSkewPartition G` is the paper's two appeals to **10.5**
(*"By 10.5 we may assume …"*), and `Set.ncard_lt_ncard` is *"contrary to the maximality"*. -/
theorem claim2_of_bigger [Fintype V]
    (hbig : ∀ A B C : Fin 3 → Set V, Berge G → NoK4 G → ¬ AdmitsBalancedSkewPartition G →
      IsHyperprism G A B C → ∀ F : Set V, MinimalBad G A B C F → BiggerHyperprism G A B C) :
    Claim2 G := by
  intro hG hK4 A B C hH hmax
  by_cases hbal : AdmitsBalancedSkewPartition G
  · exact Or.inl hbal
  refine Or.inr ?_
  by_contra hcon
  push_neg at hcon
  obtain ⟨F, hFconn, hFsub, hFnl⟩ := hcon
  obtain ⟨F₀, hF₀⟩ := exists_minimalBad (F := F) ⟨hFconn, hFsub, hFnl⟩
  obtain ⟨A', B', C', hH', hlt⟩ := hbig A B C hG hK4 hbal hH F₀ hF₀
  exact absurd (hmax A' B' C' hH') (not_le.mpr (Set.ncard_lt_ncard hlt (Set.toFinite _)))

end Workspace.ProofLemmas.HyperprismClaim2Setup
