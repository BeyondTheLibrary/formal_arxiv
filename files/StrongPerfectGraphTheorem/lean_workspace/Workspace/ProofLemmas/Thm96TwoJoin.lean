import Mathlib
import Workspace.Types.Core
import Workspace.Types.Knots
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.Thm96StriationTools

/-!
# The proper 2-join built from one strip in 9.6

This is the common construction in claim (3) and the closing paragraph.  The chosen side is
one strip together with every component outside the striation whose attachments lie in that
strip.  When the middle sets of all antistrips are empty, the striation relations give exactly
the two allowed kinds of crossing edge.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm96TwoJoin

open scoped Classical

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm96StriationTools

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The side belonging to `S i`: the strip and all outside components attached only there. -/
def sideSet (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M : Set V) (i : Fin m) : Set V :=
  stripVertices (S i) ∪
    {v : V | ∃ F : Set V, IsComponent G M F ∧ v ∈ F ∧
      (attachments G F (striationVertices S T)).Nonempty ∧
      attachments G F (striationVertices S T) ⊆ stripVertices (S i)}

/-- The antistrip vertices joined to the left end-set of `S i`. -/
noncomputable def farLeft (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (i : Fin m) : Set V :=
  ⋃ j : Fin n, if ParallelStripAntistrip G (S i) (T j)
    then leftPart (T j) else rightPart (T j)

/-- The antistrip vertices joined to the right end-set of `S i`. -/
noncomputable def farRight (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (i : Fin m) : Set V :=
  ⋃ j : Fin n, if ParallelStripAntistrip G (S i) (T j)
    then rightPart (T j) else leftPart (T j)

private theorem component_swallow {G : SimpleGraph V} {X D Z : Set V}
    (hD : IsComponent G X D) (hZ : ConnectedSet G Z) (hZX : Z ⊆ X)
    (hmeet : (D ∩ Z).Nonempty) : Z ⊆ D := by
  obtain ⟨w, hwD, hwZ⟩ := hmeet
  have hcon : ConnectedSet G (D ∪ Z) :=
    ConnectedSetUnionAttach.connectedSet_union hD.2.1 hZ (Or.inl ⟨w, hwD, hwZ⟩)
  have heq : D ∪ Z = D :=
    hD.2.2 (D ∪ Z) Set.subset_union_left (Set.union_subset hD.1 hZX) hcon
  intro z hz
  rw [← heq]
  exact Or.inr hz

private theorem component_add_adjacent {G : SimpleGraph V} {X D : Set V}
    (hD : IsComponent G X D) {x y : V} (hx : x ∈ D) (hy : y ∈ X) (hxy : G.Adj x y) :
    y ∈ D := by
  have hcon : ConnectedSet G (D ∪ {y}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hD.2.1 ⟨x, hx, hxy.symm⟩
  have heq := hD.2.2 (D ∪ {y}) Set.subset_union_left
    (Set.union_subset hD.1 (Set.singleton_subset_iff.mpr hy)) hcon
  have : y ∈ D ∪ {y} := Or.inr rfl
  rwa [heq] at this

/-- A connected subset of an induced path which contains both ends contains the whole path. -/
private theorem path_subset_of_connected {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) {C : Set V} (hCsub : C ⊆ {v : V | v ∈ p})
    (hC : ConnectedSet G C) (ha : a ∈ C) (hb : b ∈ C) :
    {v : V | v ∈ p} ⊆ C := by
  have hlen : 0 < p.length := Workspace.ProofLemmas.PathBasics.path_length_pos hp.1
  have hzero : p[0]'hlen = a :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 hlen
  have hlast : p[p.length - 1]'(by omega) = b :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 hlen
  intro x hx
  by_contra hxC
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  subst hxi
  have hi0 : 0 < i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · exact absurd (hzero ▸ ha) hxC
    · exact h
  have hilast : i < p.length - 1 := by
    rcases Nat.lt_or_ge i (p.length - 1) with h | h
    · exact h
    · have : i = p.length - 1 := by omega
      subst this
      exact absurd (hlast ▸ hb) hxC
  set P : Set V := {v : V | ∃ j, ∃ _ : j < p.length, j < i ∧ v = p[j]} with hP
  set Q : Set V := {v : V | ∃ j, ∃ _ : j < p.length, i < j ∧ v = p[j]} with hQ
  have hPQ : Anticomplete G P Q := by
    rintro u ⟨j, hj, hji, rfl⟩ v ⟨k, hk, hik, rfl⟩
    exact Workspace.ProofLemmas.PathBasics.path_not_adj_of_gap hp.1 hj hk (by omega) (by omega)
  have hsub : C ⊆ P ∪ Q := by
    intro c hc
    obtain ⟨j, hj, hcj⟩ := List.mem_iff_getElem.mp (hCsub hc)
    have hji : j ≠ i := by
      rintro rfl
      exact hxC (hcj ▸ hc)
    rcases Nat.lt_or_ge j i with h | h
    · exact Or.inl ⟨j, hj, h, hcj.symm⟩
    · exact Or.inr ⟨j, hj, by omega, hcj.symm⟩
  have hreach : ∀ {u v : ↥C}, (G.induce C).Reachable u v → (u : V) ∈ P → (v : V) ∈ P := by
    intro u v hr huP
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact huP
    | @cons x y _ hadj _ ih =>
        apply ih
        rcases hsub y.2 with hyP | hyQ
        · exact hyP
        · exact absurd (show G.Adj (x : V) (y : V) from hadj) (hPQ (x : V) huP (y : V) hyQ)
  have haP : a ∈ P := ⟨0, hlen, hi0, hzero.symm⟩
  have hbP : b ∈ P := hreach (hC ⟨a, ha⟩ ⟨b, hb⟩) haP
  obtain ⟨k, hk, hki, hbk⟩ := hbP
  have heq : p[k]'hk = p[p.length - 1]'(by omega) := by rw [← hbk, hlast]
  have := (Workspace.ProofLemmas.PathBasics.path_nodup hp.1).getElem_inj_iff.mp heq
  omega

private theorem eq_pair_of_pathLength_one {G : SimpleGraph V} {p : List V} {a b : V}
    (hp : IsPathFrom G p a b) (hlen : pathLength p = 1) : p = [a, b] := by
  have hlen2 : p.length = 2 := by
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq] at hlen
    omega
  obtain ⟨x, y, hxy⟩ := Workspace.ProofLemmas.PrismBasics.length_eq_two hlen2
  rw [hxy] at hp ⊢
  have hx : x = a := by simpa using hp.2.1
  have hy : y = b := by simpa using hp.2.2
  rw [hx, hy]

/-- With empty antistrip middle, the striation relation gives the two crossing pairs. -/
private theorem strip_antistrip_cross {G : SimpleGraph V}
    {S₀ T₀ : Set V × Set V × Set V}
    (hS : IsStrip G S₀) (hT : IsAntistrip G T₀)
    (hpc : ParallelStripAntistrip G S₀ T₀ ∨ CoParallel G S₀ T₀)
    (hmid : middlePart T₀ = ∅) {u v : V}
    (hu : u ∈ stripVertices S₀) (hv : v ∈ stripVertices T₀) (hadj : G.Adj u v) :
    (u ∈ leftPart S₀ ∧
        (if ParallelStripAntistrip G S₀ T₀ then v ∈ leftPart T₀ else v ∈ rightPart T₀)) ∨
      (u ∈ rightPart S₀ ∧
        (if ParallelStripAntistrip G S₀ T₀ then v ∈ rightPart T₀ else v ∈ leftPart T₀)) := by
  classical
  obtain ⟨A, C, B⟩ := S₀
  obtain ⟨X, Z, Y⟩ := T₀
  simp only [stripVertices, leftPart, middlePart, rightPart] at hu hv hmid ⊢
  have hz : Z = ∅ := hmid
  subst Z
  simp only [Set.union_empty, Set.mem_union, Set.notMem_empty, if_pos, if_neg] at hv
  rcases hpc with hp | hc
  · simp only [if_pos hp]
    simp only [ParallelStripAntistrip] at hp
    rcases hu with (huA | huB) | huC <;> rcases hv with hvX | hvY
    · exact Or.inl ⟨huA, hvX⟩
    · exact absurd hadj.symm (hp.2.2 v hvY u (Or.inl huA))
    · exact absurd hadj.symm (hp.2.1 v hvX u (Or.inl huB))
    · exact Or.inr ⟨huB, hvY⟩
    · exact absurd hadj.symm (hp.2.1 v hvX u (Or.inr huC))
    · exact absurd hadj.symm (hp.2.2 v hvY u (Or.inr huC))
  · have hnp : ¬ ParallelStripAntistrip G (A, C, B) (X, ∅, Y) := by
      intro hp
      exact Workspace.ProofLemmas.StriationCompl.not_parallel_and_coParallel
        hS hT ⟨hp, hc⟩
    simp only [if_neg hnp]
    simp only [CoParallel, reverseStrip, ParallelStripAntistrip] at hc
    rcases hu with (huA | huB) | huC <;> rcases hv with hvX | hvY
    · exact absurd hadj.symm (hc.2.2 v hvX u (Or.inl huA))
    · exact Or.inl ⟨huA, hvY⟩
    · exact Or.inr ⟨huB, hvX⟩
    · exact absurd hadj.symm (hc.2.1 v hvY u (Or.inl huB))
    · exact absurd hadj.symm (hc.2.2 v hvX u (Or.inr huC))
    · exact absurd hadj.symm (hc.2.1 v hvY u (Or.inr huC))

/-- **PAPER (9.6, claim (3) and the closing paragraph).**

Choose one strip and add every outside component attached only to it.  If no outside
component is attachment-free and every antistrip has empty middle, this side and its
complement form a proper 2-join, except for the forbidden two-vertex side. -/
theorem proper2Join_of_side
    (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hL : IsStriation G S T) (M : Set V)
    (hpart : M = (striationVertices S T)ᶜ)
    (hassign : ∀ F : Set V, IsComponent G M F →
      ∃ k : Fin m, attachments G F (striationVertices S T) ⊆ stripVertices (S k))
    (hne : ∀ F : Set V, IsComponent G M F → F.Nonempty →
      (attachments G F (striationVertices S T)).Nonempty)
    (hmid : ∀ j : Fin n, middlePart (T j) = ∅)
    (i : Fin m)
    (hnondeg : 2 < (stripVertices (S i)).ncard ∨
      ∃ v ∈ sideSet G S T M i, v ∉ stripVertices (S i)) :
    AdmitsProper2Join G := by
  classical
  obtain ⟨hS, hT, hSS, hTT, hST, hoddS, hoddT, hm, hn,
    hSanti, hTcomp, hpc, htwS, htwT⟩ := hL
  let X := sideSet G S T M i
  let Y := Xᶜ
  let A₁ := leftPart (S i)
  let B₁ := rightPart (S i)
  let A₂ := farLeft G S T i
  let B₂ := farRight G S T i
  have hLmemS : ∀ k : Fin m, stripVertices (S k) ⊆ striationVertices S T := by
    intro k v hv
    exact Or.inl (Set.mem_iUnion.mpr ⟨k, hv⟩)
  have hLmemT : ∀ j : Fin n, stripVertices (T j) ⊆ striationVertices S T := by
    intro j v hv
    exact Or.inr (Set.mem_iUnion.mpr ⟨j, hv⟩)
  have hMoff : M ⊆ (striationVertices S T)ᶜ := by rw [hpart]
  have hSX : stripVertices (S i) ⊆ X := fun _ hv => Or.inl hv
  have hFside : ∀ {F : Set V}, IsComponent G M F → F.Nonempty →
      attachments G F (striationVertices S T) ⊆ stripVertices (S i) → F ⊆ X := by
    intro F hF hFne hsub v hv
    exact Or.inr ⟨F, hF, hv, hne F hF hFne, hsub⟩
  have hTY : ∀ j : Fin n, stripVertices (T j) ⊆ Y := by
    intro j v hv
    show v ∈ Xᶜ
    intro hvX
    rcases hvX with hvS | ⟨F, hF, hvF, -, -⟩
    · exact Set.disjoint_left.mp (hST i j) hvS hv
    · exact hMoff (hF.1 hvF) (hLmemT j hv)
  have hSY : ∀ k : Fin m, k ≠ i → stripVertices (S k) ⊆ Y := by
    intro k hki v hv
    show v ∈ Xᶜ
    intro hvX
    rcases hvX with hvS | ⟨F, hF, hvF, -, -⟩
    · exact Set.disjoint_left.mp (hSS k i hki) hv hvS
    · exact hMoff (hF.1 hvF) (hLmemS k hv)
  have hTsplit : ∀ j : Fin n,
      stripVertices (T j) = leftPart (T j) ∪ rightPart (T j) := by
    intro j
    rw [stripVertices_eq, hmid j, Set.union_empty]
  have hA₂Y : A₂ ⊆ Y := by
    intro v hv
    rcases Set.mem_iUnion.mp hv with ⟨j, hvj⟩
    apply hTY j
    by_cases hp : ParallelStripAntistrip G (S i) (T j)
    · rw [if_pos hp] at hvj
      exact left_subset_stripVertices _ hvj
    · rw [if_neg hp] at hvj
      exact right_subset_stripVertices _ hvj
  have hB₂Y : B₂ ⊆ Y := by
    intro v hv
    rcases Set.mem_iUnion.mp hv with ⟨j, hvj⟩
    apply hTY j
    by_cases hp : ParallelStripAntistrip G (S i) (T j)
    · rw [if_pos hp] at hvj
      exact right_subset_stripVertices _ hvj
    · rw [if_neg hp] at hvj
      exact left_subset_stripVertices _ hvj
  have hA₁ne : A₁.Nonempty := left_nonempty (hS i)
  have hB₁ne : B₁.Nonempty := right_nonempty (hS i)
  have hn0 : 0 < n := by omega
  let j₀ : Fin n := ⟨0, hn0⟩
  obtain ⟨x₀, hx₀⟩ := left_nonempty (hT j₀)
  obtain ⟨y₀, hy₀⟩ := right_nonempty (hT j₀)
  have hA₂ne : A₂.Nonempty := by
    by_cases hp : ParallelStripAntistrip G (S i) (T j₀)
    · exact ⟨x₀, Set.mem_iUnion.mpr ⟨j₀, by rw [if_pos hp]; exact hx₀⟩⟩
    · exact ⟨y₀, Set.mem_iUnion.mpr ⟨j₀, by rw [if_neg hp]; exact hy₀⟩⟩
  have hB₂ne : B₂.Nonempty := by
    by_cases hp : ParallelStripAntistrip G (S i) (T j₀)
    · exact ⟨y₀, Set.mem_iUnion.mpr ⟨j₀, by rw [if_pos hp]; exact hy₀⟩⟩
    · exact ⟨x₀, Set.mem_iUnion.mpr ⟨j₀, by rw [if_neg hp]; exact hx₀⟩⟩
  have hA₂B₂ : Disjoint A₂ B₂ := by
    refine Set.disjoint_left.mpr ?_
    intro v hvA hvB
    rcases Set.mem_iUnion.mp hvA with ⟨j, hvAj⟩
    rcases Set.mem_iUnion.mp hvB with ⟨k, hvBk⟩
    by_cases hjk : j = k
    · subst k
      by_cases hp : ParallelStripAntistrip G (S i) (T j)
      · rw [if_pos hp] at hvAj hvBk
        exact Set.disjoint_left.mp (left_right_disjoint (hT j)) hvAj hvBk
      · rw [if_neg hp] at hvAj hvBk
        exact Set.disjoint_left.mp (left_right_disjoint (hT j)) hvBk hvAj
    · apply Set.disjoint_left.mp (hTT j k hjk)
      · by_cases hp : ParallelStripAntistrip G (S i) (T j)
        · rw [if_pos hp] at hvAj
          exact left_subset_stripVertices _ hvAj
        · rw [if_neg hp] at hvAj
          exact right_subset_stripVertices _ hvAj
      · by_cases hp : ParallelStripAntistrip G (S i) (T k)
        · rw [if_pos hp] at hvBk
          exact right_subset_stripVertices _ hvBk
        · rw [if_neg hp] at hvBk
          exact left_subset_stripVertices _ hvBk
  have hA₁B₁ : Disjoint A₁ B₁ := left_right_disjoint (hS i)
  have hcross : ∀ u ∈ X, ∀ v ∈ Y,
      G.Adj u v ↔ ((u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂)) := by
    intro u hu v hv
    constructor
    · intro hadj
      rcases hu with huS | ⟨F, hF, huF, hFne, hFsub⟩
      · by_cases hvL : v ∈ striationVertices S T
        · rcases hvL with hvSs | hvTs
          · obtain ⟨k, hvSk⟩ := Set.mem_iUnion.mp hvSs
            by_cases hki : k = i
            · subst k
              exact absurd (hSX hvSk) hv
            · have hno : ¬ G.Adj u v := by
                rcases lt_trichotomy i k with hik | hik | hik
                · exact hSanti i k hik u huS v hvSk
                · exact absurd hik.symm hki
                · exact fun huv => hSanti k i hik v hvSk u huS huv.symm
              exact False.elim (hno hadj)
          · obtain ⟨j, hvTj⟩ := Set.mem_iUnion.mp hvTs
            rcases strip_antistrip_cross (hS i) (hT j) (hpc i j) (hmid j) huS hvTj hadj with h | h
            · refine Or.inl ⟨h.1, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
              by_cases hp : ParallelStripAntistrip G (S i) (T j)
              · simpa only [if_pos hp] using h.2
              · simpa only [if_neg hp] using h.2
            · refine Or.inr ⟨h.1, Set.mem_iUnion.mpr ⟨j, ?_⟩⟩
              by_cases hp : ParallelStripAntistrip G (S i) (T j)
              · simpa only [if_pos hp] using h.2
              · simpa only [if_neg hp] using h.2
        · have hvM : v ∈ M := by rw [hpart]; exact hvL
          obtain ⟨D, hD, hvD⟩ := ComponentsOfSetBasics.exists_isComponent_mem G M hvM
          obtain ⟨k, hDsub⟩ := hassign D hD
          have huatt : u ∈ attachments G D (striationVertices S T) :=
            ⟨hLmemS i huS, v, hvD, hadj⟩
          have huk := hDsub huatt
          have hki : k = i := by
            by_contra hneki
            exact Set.disjoint_left.mp (hSS k i hneki) huk huS
          subst k
          exact absurd (hFside hD ⟨v, hvD⟩ hDsub hvD) hv
      · by_cases hvL : v ∈ striationVertices S T
        · have hvSi : v ∈ stripVertices (S i) :=
            hFsub ⟨hvL, u, huF, hadj.symm⟩
          exact absurd (hSX hvSi) hv
        · have hvM : v ∈ M := by rw [hpart]; exact hvL
          obtain ⟨D, hD, hvD⟩ := ComponentsOfSetBasics.exists_isComponent_mem G M hvM
          by_cases hFD : F = D
          · subst D
            exact absurd (hFside hF ⟨u, huF⟩ hFsub hvD) hv
          · exact absurd hadj
              (ComponentsOfSetBasics.anticomplete_of_isComponent G hF hD hFD u huF v hvD)
    · rintro (⟨huA, hvA⟩ | ⟨huB, hvB⟩)
      · rcases Set.mem_iUnion.mp hvA with ⟨j, hvj⟩
        by_cases hp : ParallelStripAntistrip G (S i) (T j)
        · rw [if_pos hp] at hvj
          exact hp.1.1 u huA v (Set.mem_union_left _ hvj)
        · rw [if_neg hp] at hvj
          have hc := (hpc i j).resolve_left hp
          exact hc.1.1 u huA v (Set.mem_union_left _ hvj)
      · rcases Set.mem_iUnion.mp hvB with ⟨j, hvj⟩
        by_cases hp : ParallelStripAntistrip G (S i) (T j)
        · rw [if_pos hp] at hvj
          exact hp.1.2 u huB v (Set.mem_union_left _ hvj)
        · rw [if_neg hp] at hvj
          have hc := (hpc i j).resolve_left hp
          exact hc.1.2 u huB v (Set.mem_union_left _ hvj)
  have hcompX : ∀ D : Set V, IsComponent G X D →
      (D ∩ A₁).Nonempty ∧ (D ∩ B₁).Nonempty := by
    intro D hD
    obtain ⟨v, hvD⟩ := ComponentsOfSetBasics.nonempty_of_isComponent G
      ⟨hA₁ne.choose, hSX (left_subset_stripVertices _ hA₁ne.choose_spec)⟩ hD
    have hmeetS : (D ∩ stripVertices (S i)).Nonempty := by
      rcases hD.1 hvD with hvS | ⟨F, hF, hvF, hFne, hFsub⟩
      · exact ⟨v, hvD, hvS⟩
      · have hFnonempty : F.Nonempty := ⟨v, hvF⟩
        obtain ⟨w, hwL, f, hfF, hwf⟩ := hne F hF hFnonempty
        have hwS : w ∈ stripVertices (S i) := hFsub ⟨hwL, f, hfF, hwf⟩
        have hZcon : ConnectedSet G (F ∪ {w}) :=
          ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hfF, hwf⟩
        have hZsub : F ∪ {w} ⊆ X := by
          rintro z (hz | hz)
          · exact hFside hF hFnonempty hFsub hz
          · simpa [show z = w from hz] using hSX hwS
        have hsw := component_swallow hD hZcon hZsub ⟨v, hvD, Or.inl hvF⟩
        exact ⟨w, hsw (Or.inr rfl), hwS⟩
    obtain ⟨w, hwD, hwS⟩ := hmeetS
    obtain ⟨p, hp, hwp⟩ := exists_rung_through (hS i) hwS
    have hp' := hp
    obtain ⟨a, b, hpab, ha, hb, -⟩ := hp
    have hpdata := rung_connected_subset hp'
    have hpD : {z : V | z ∈ p} ⊆ D :=
      component_swallow hD hpdata.1 (fun z hz => hSX (hpdata.2 hz)) ⟨w, hwD, hwp⟩
    exact ⟨⟨a, hpD (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hpab).1, ha⟩,
      ⟨b, hpD (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hpab).2, hb⟩⟩
  have hTcomplete : ∀ {j k : Fin n}, j ≠ k →
      Complete G (stripVertices (T j)) (stripVertices (T k)) := by
    intro j k hjk
    rcases lt_trichotomy j k with h | h | h
    · exact hTcomp j k h
    · exact absurd h hjk
    · exact fun x hx y hy => (hTcomp k j h y hy x hx).symm
  have hcompY : ∀ D : Set V, IsComponent G Y D →
      (D ∩ A₂).Nonempty ∧ (D ∩ B₂).Nonempty := by
    intro D hD
    have hYne : Y.Nonempty := ⟨hA₂ne.choose, hA₂Y hA₂ne.choose_spec⟩
    obtain ⟨v, hvD⟩ := ComponentsOfSetBasics.nonempty_of_isComponent G hYne hD
    have hvY : v ∈ Y := hD.1 hvD
    have fromT : ∀ {j : Fin n} {t : V}, t ∈ D → t ∈ stripVertices (T j) →
        (D ∩ A₂).Nonempty ∧ (D ∩ B₂).Nonempty := by
      intro j t htD htT
      have h0 : 0 < n := by omega
      have h1 : 1 < n := by omega
      obtain ⟨k, hjk⟩ : ∃ k : Fin n, j ≠ k := by
        by_cases h : j = ⟨0, h0⟩
        · exact ⟨⟨1, h1⟩, by rw [h]; simp [Fin.ext_iff]⟩
        · exact ⟨⟨0, h0⟩, h⟩
      obtain ⟨x, hx⟩ := left_nonempty (hT k)
      obtain ⟨y, hy⟩ := right_nonempty (hT k)
      have hxD : x ∈ D := component_add_adjacent hD htD (hTY k (left_subset_stripVertices _ hx))
        (hTcomplete hjk t htT x (left_subset_stripVertices _ hx))
      have hyD : y ∈ D := component_add_adjacent hD htD (hTY k (right_subset_stripVertices _ hy))
        (hTcomplete hjk t htT y (right_subset_stripVertices _ hy))
      by_cases hp : ParallelStripAntistrip G (S i) (T k)
      · exact ⟨⟨x, hxD, Set.mem_iUnion.mpr ⟨k, by rw [if_pos hp]; exact hx⟩⟩,
          ⟨y, hyD, Set.mem_iUnion.mpr ⟨k, by rw [if_pos hp]; exact hy⟩⟩⟩
      · exact ⟨⟨y, hyD, Set.mem_iUnion.mpr ⟨k, by rw [if_neg hp]; exact hy⟩⟩,
          ⟨x, hxD, Set.mem_iUnion.mpr ⟨k, by rw [if_neg hp]; exact hx⟩⟩⟩
    have fromS : ∀ {k : Fin m} {w : V}, k ≠ i → w ∈ D →
        w ∈ stripVertices (S k) →
        ∃ j : Fin n, ∃ t ∈ D, t ∈ stripVertices (T j) := by
      intro k w hki hwD hwS
      obtain ⟨p, hp, hwp⟩ := exists_rung_through (hS k) hwS
      have hp' := hp
      obtain ⟨a, b, hpab, ha, hb, -⟩ := hp
      have hpdata := rung_connected_subset hp'
      have hpD : {z : V | z ∈ p} ⊆ D :=
        component_swallow hD hpdata.1 (fun z hz => hSY k hki (hpdata.2 hz)) ⟨w, hwD, hwp⟩
      have haD := hpD (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hpab).1
      let j : Fin n := ⟨0, by omega⟩
      rcases hpc k j with hpar | hco
      · obtain ⟨t, ht⟩ := left_nonempty (hT j)
        have hat : G.Adj a t := hpar.1.1 a ha t (Set.mem_union_left _ ht)
        exact ⟨j, t, component_add_adjacent hD haD (hTY j (left_subset_stripVertices _ ht)) hat, left_subset_stripVertices _ ht⟩
      · obtain ⟨t, ht⟩ := right_nonempty (hT j)
        have hat : G.Adj a t := hco.1.1 a ha t (Set.mem_union_left _ ht)
        exact ⟨j, t, component_add_adjacent hD haD (hTY j (right_subset_stripVertices _ ht)) hat, right_subset_stripVertices _ ht⟩
    by_cases hvL : v ∈ striationVertices S T
    · rcases hvL with hvSs | hvTs
      · obtain ⟨k, hvSk⟩ := Set.mem_iUnion.mp hvSs
        have hki : k ≠ i := by
          intro h; subst k
          exact hvY (hSX hvSk)
        obtain ⟨j, t, htD, htT⟩ := fromS hki hvD hvSk
        exact fromT htD htT
      · obtain ⟨j, hvTj⟩ := Set.mem_iUnion.mp hvTs
        exact fromT hvD hvTj
    · have hvM : v ∈ M := by rw [hpart]; exact hvL
      obtain ⟨F, hF, hvF⟩ := ComponentsOfSetBasics.exists_isComponent_mem G M hvM
      obtain ⟨k, hFsub⟩ := hassign F hF
      have hFne : F.Nonempty := ⟨v, hvF⟩
      obtain ⟨w, hwL, f, hfF, hwf⟩ := hne F hF hFne
      have hwSk : w ∈ stripVertices (S k) := hFsub ⟨hwL, f, hfF, hwf⟩
      have hki : k ≠ i := by
        intro h; subst k
        exact hvY (hFside hF hFne hFsub hvF)
      have hFY : F ⊆ Y := by
        intro z hz
        show z ∈ Xᶜ
        intro hzX
        rcases hzX with hzSi | ⟨F', hF', hzF', hF'ne, hF'sub⟩
        · exact hMoff (hF.1 hz) (hLmemS i hzSi)
        · have hFF' : F = F' := by
            by_contra hneq
            exact Set.disjoint_left.mp
              (ComponentsOfSetBasics.disjoint_of_isComponent G hF hF' hneq) hz hzF'
          subst F'
          exact hvY (hFside hF hFne hF'sub hvF)
      have hZcon : ConnectedSet G (F ∪ {w}) :=
        ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨f, hfF, hwf⟩
      have hZsub : F ∪ {w} ⊆ Y := by
        rintro z (hz | hz)
        · exact hFY hz
        · simpa [show z = w from hz] using hSY k hki hwSk
      have hwD : w ∈ D :=
        component_swallow hD hZcon hZsub ⟨v, hvD, Or.inl hvF⟩ (Or.inr rfl)
      obtain ⟨j, t, htD, htT⟩ := fromS hki hwD hwSk
      exact fromT htD htT
  have hoddX : ∀ a b : V, A₁ = {a} → B₁ = {b} → ∀ p : List V,
      IsPathFrom G p a b → {v : V | v ∈ p} = X →
      Odd (pathLength p) ∧ 3 ≤ pathLength p := by
    intro a b haeq hbeq p hp hpX
    obtain ⟨R, hR⟩ := exists_rung (hS i)
    obtain ⟨a', b', hRab, ha', hb', hRtail, hRdrop, hRint⟩ := hR
    have ha'A₁ : a' ∈ A₁ := ha'
    have hb'B₁ : b' ∈ B₁ := hb'
    have haa : a' = a := by rw [haeq] at ha'A₁; exact ha'A₁
    have hbb : b' = b := by rw [hbeq] at hb'B₁; exact hb'B₁
    subst a'; subst b'
    have hRdata := rung_connected_subset
      ⟨a, b, hRab, ha', hb', hRtail, hRdrop, hRint⟩
    have hRsubp : {v : V | v ∈ R} ⊆ {v : V | v ∈ p} := by
      intro v hv
      rw [hpX]
      exact hSX (hRdata.2 hv)
    have hpR : {v : V | v ∈ p} ⊆ {v : V | v ∈ R} :=
      path_subset_of_connected hp hRsubp hRdata.1
        (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hRab).1
        (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hRab).2
    have hXeqS : X = stripVertices (S i) := by
      apply Set.Subset.antisymm
      · intro v hvX
        have hvp : v ∈ {z : V | z ∈ p} := by rw [hpX]; exact hvX
        exact hRdata.2 (hpR hvp)
      · exact hSX
    have htailA : ∀ v ∈ p.tail, v ∉ A₁ := by
      intro v hv hA
      have hvA₁ : v ∈ A₁ := hA
      have hva : v = a := by rw [haeq] at hvA₁; exact hvA₁
      subst v
      rcases p with _ | ⟨x, xs⟩
      · exact hp.1.1 rfl
      · simp only [List.tail_cons] at hv
        have hxa : x = a := by simpa using hp.2.1
        subst x
        exact (List.nodup_cons.mp (Workspace.ProofLemmas.PathBasics.path_nodup hp.1)).1 hv
    have hdropB : ∀ v ∈ p.dropLast, v ∉ B₁ := by
      intro v hv hB
      have hvB₁ : v ∈ B₁ := hB
      have hvb : v = b := by rw [hbeq] at hvB₁; exact hvB₁
      subst v
      have hpne : p ≠ [] := hp.1.1
      have hlast : p.getLast hpne = b := by
        have h := hp.2.2
        rw [List.getLast?_eq_some_getLast hpne] at h
        exact Option.some_injective _ h
      exact ((Workspace.ProofLemmas.PathBasics.mem_dropLast_iff
        (Workspace.ProofLemmas.PathBasics.path_nodup hp.1) hpne).mp hv).2 hlast.symm
    have hint : ∀ v ∈ SPGT.interior p, v ∈ middlePart (S i) := by
      intro v hv
      have hvS : v ∈ stripVertices (S i) := by
        rw [← hXeqS, ← hpX]
        exact Workspace.ProofLemmas.PathBasics.interior_subset hv
      rw [stripVertices_eq] at hvS
      rcases hvS with (hvA | hvB) | hvC
      · have hvA₁ : v ∈ A₁ := hvA
        have hva : v = a := by rw [haeq] at hvA₁; exact hvA₁
        exact False.elim (((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mp hv).2.1 hva)
      · have hvB₁ : v ∈ B₁ := hvB
        have hvb : v = b := by rw [hbeq] at hvB₁; exact hvB₁
        exact False.elim (((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mp hv).2.2 hvb)
      · exact hvC
    have hpRung : IsSRung G (S i) p := by
      have haeq' : leftPart (S i) = {a} := haeq
      have hbeq' : rightPart (S i) = {b} := hbeq
      have htailA' : ∀ v ∈ p.tail, v ∉ leftPart (S i) := htailA
      have hdropB' : ∀ v ∈ p.dropLast, v ∉ rightPart (S i) := hdropB
      have hint' : ∀ v ∈ SPGT.interior p, v ∈ middlePart (S i) := hint
      rcases hSi : S i with ⟨A, C, B⟩
      rw [hSi] at haeq' hbeq' htailA' hdropB' hint'
      simp only [leftPart, rightPart, middlePart] at haeq' hbeq' htailA' hdropB' hint' ⊢
      exact ⟨a, b, hp, by rw [haeq']; rfl, by rw [hbeq']; rfl,
        htailA', hdropB', hint'⟩
    have hodd : Odd (pathLength p) := hoddS i p hpRung
    refine ⟨hodd, ?_⟩
    by_contra hnot
    have hle : pathLength p ≤ 2 := by omega
    obtain ⟨q, hq⟩ := hodd
    have hpone : pathLength p = 1 := by omega
    have hpPair := eq_pair_of_pathLength_one hp hpone
    have hpairset : {v : V | v ∈ p} = ({a, b} : Set V) := by rw [hpPair]; ext z; simp
    have hab : a ≠ b := by
      intro heq; subst b
      have haA₁ : a ∈ A₁ := by rw [haeq]; rfl
      have haB₁ : a ∈ B₁ := by rw [hbeq]; rfl
      exact Set.disjoint_left.mp hA₁B₁ haA₁ haB₁
    rcases hnondeg with hlarge | ⟨z, hzX, hzS⟩
    · have hc : (stripVertices (S i)).ncard = 2 := by
        rw [← hXeqS, ← hpX, hpairset, Set.ncard_pair hab]
      omega
    · exact hzS (by rw [← hXeqS]; exact hzX)
  have hoddY : ∀ a b : V, A₂ = {a} → B₂ = {b} → ∀ p : List V,
      IsPathFrom G p a b → {v : V | v ∈ p} = Y →
      Odd (pathLength p) ∧ 3 ≤ pathLength p := by
    intro a b haeq hbeq p hp hpY
    exfalso
    have h0 : 0 < n := by omega
    have h1 : 1 < n := by omega
    let j : Fin n := ⟨0, h0⟩
    let k : Fin n := ⟨1, h1⟩
    have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
    obtain ⟨xL, hxL⟩ := left_nonempty (hT j)
    obtain ⟨xR, hxR⟩ := right_nonempty (hT j)
    obtain ⟨yL, hyL⟩ := left_nonempty (hT k)
    obtain ⟨yR, hyR⟩ := right_nonempty (hT k)
    obtain ⟨x, hxT, hxA⟩ : ∃ x, x ∈ stripVertices (T j) ∧ x ∈ A₂ := by
      by_cases hpj : ParallelStripAntistrip G (S i) (T j)
      · exact ⟨xL, left_subset_stripVertices _ hxL,
          Set.mem_iUnion.mpr ⟨j, by rw [if_pos hpj]; exact hxL⟩⟩
      · exact ⟨xR, right_subset_stripVertices _ hxR,
          Set.mem_iUnion.mpr ⟨j, by rw [if_neg hpj]; exact hxR⟩⟩
    obtain ⟨y, hyT, hyA⟩ : ∃ y, y ∈ stripVertices (T k) ∧ y ∈ A₂ := by
      by_cases hpk : ParallelStripAntistrip G (S i) (T k)
      · exact ⟨yL, left_subset_stripVertices _ hyL,
          Set.mem_iUnion.mpr ⟨k, by rw [if_pos hpk]; exact hyL⟩⟩
      · exact ⟨yR, right_subset_stripVertices _ hyR,
          Set.mem_iUnion.mpr ⟨k, by rw [if_neg hpk]; exact hyR⟩⟩
    have hxa : x = a := by rw [haeq] at hxA; exact hxA
    have hya : y = a := by rw [haeq] at hyA; exact hyA
    subst x; subst y
    exact Set.disjoint_left.mp (hTT j k hjk) hxT hyT
  exact ⟨X, Y, Set.union_compl_self X, disjoint_compl_right,
    A₁, B₁, A₂, B₂,
    fun v hv => hSX (left_subset_stripVertices _ hv),
    fun v hv => hSX (right_subset_stripVertices _ hv), hA₂Y, hB₂Y,
    hA₁ne, hB₁ne, hA₂ne, hB₂ne, hA₁B₁, hA₂B₂,
    hcross, hcompX, hcompY, hoddX, hoddY⟩

end Workspace.ProofLemmas.Thm96TwoJoin
