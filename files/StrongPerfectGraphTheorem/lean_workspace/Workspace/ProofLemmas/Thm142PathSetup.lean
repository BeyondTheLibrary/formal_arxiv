import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.DoubleDiamond
import Workspace.Types.Appearances
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

/-!
# 14.2: minimal `A`--`B` attachment-path infrastructure

PAPER (printed pp. 89–90, the closing two paragraphs of the proof of 14.2):

> *"Now assume that `X ⊆ A ∪ B`.  Assume `X ∩ A` is not complete to `X ∩ B`, and choose a path
> `a-f₁-⋯-f_k-b`, where `a ∈ A`, `b ∈ B` are nonadjacent and `f₁, …, f_k ∈ F`, with `k` minimum.
> Since `f₁` is minor, its neighbours in `A` are complete to its neighbours in `B`, and so
> `k ≥ 2`.  Let `A₀` be the set of all vertices `a ∈ A` such that `a` is adjacent to `f₁` and
> there is a nonneighbour `b` of `a` in `B` adjacent to `f_k`.  By assumption `A₀ ≠ ∅`.  Define
> `B₀` similarly in `B`.  If `A₀ = A` and `B₀ = B`, then `f₁` is `A`-complete, and so there are no
> edges between `{f₁, …, f_{k-1}}` and `B`, from the minimality of `k`; and similarly `f_k` is
> `B`-complete and there are no edges between `{f₂, …, f_k}` and `A`.  Choose a square
> `a₁-b₁-b₂-a₂-a₁`; then `a₁-b₁`, `a₂-b₂`, `f₁-⋯-f_k` form a prism, so `k = 2`, and we can add
> `f₁` to `C` and `f₂` to `D`, contrary to the maximality of the cube.  So we may assume that
> `A₀ ≠ A`.  …  But then the set of neighbours of `b` in the prism formed by `a₁-b₁`, `a₂-b₂`,
> `c-d` is not local, and yet none are in the path `a₁-b₁`, contrary to 10.4.  This proves
> 14.2."*

This is the `X ⊆ A ∪ B` branch of the second assertion of 14.2.  The companion `X ⊆ C ∪ D`
branch is `Workspace.ProofLemmas.CubeAttachmentsCDComplete`; the first assertion is
`Workspace.ProofLemmas.CubeMinorAttachmentContainment`.  Under `X ⊆ A ∪ B` the conclusion
`X ∩ (A ∪ C)` complete to `X ∩ (B ∪ D)` of 14.2 collapses to `X ∩ A` complete to `X ∩ B`, which
is what is stated here.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

namespace Thm142ABComplete

open Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

/-- A connected subset of the original component which still witnesses a nonedge between an
`A`-attachment and a `B`-attachment.  This is the property minimized in the opening sentence of
the last paragraph of the proof of 14.2. -/
private def BadAB {V : Type*} (G : SimpleGraph V) (A B F S : Set V) : Prop :=
  S ⊆ F ∧ ConnectedSet G S ∧
    ∃ a ∈ A, ∃ b ∈ B, ¬ G.Adj a b ∧
      (∃ x ∈ S, G.Adj a x) ∧ (∃ y ∈ S, G.Adj b y)

/-- The exact data supplied by the paper's choice of
`a-f₁-⋯-fₖ-b` with `k` minimum.  Recording minimality for connected vertex sets, rather
than for lists, lets every later use be discharged by taking the appropriate interval of `f`. -/
structure ABPathConfig {V : Type*} (G : SimpleGraph V) (A B C D F : Set V)
    (f : List V) (a b : V) : Prop where
  path : IsPathList G f
  len : 2 ≤ f.length
  subset : {z : V | z ∈ f} ⊆ F
  outside : ∀ z ∈ f, z ∉ A ∪ B ∪ C ∪ D
  memA : a ∈ A
  memB : b ∈ B
  nonadj : ¬ G.Adj a b
  adjA : ∀ (i : ℕ) (hi : i < f.length), G.Adj a (f[i]'hi) ↔ i = 0
  adjB : ∀ (i : ℕ) (hi : i < f.length), G.Adj b (f[i]'hi) ↔ i = f.length - 1
  minor : ∀ z ∈ f, MinorForCube G A B C D z
  minimal : ∀ S : Set V, S ⊆ {z : V | z ∈ f} → ConnectedSet G S →
    (∃ a' ∈ A, ∃ b' ∈ B, ¬ G.Adj a' b' ∧
      (∃ x ∈ S, G.Adj a' x) ∧ (∃ y ∈ S, G.Adj b' y)) →
    S = {z : V | z ∈ f}

/-- The paper's globally minimal attachment path exists, has at least two internal vertices,
and satisfies the connected-subpath minimality principle used throughout the rest of the proof. -/
theorem exists_minimal_ab_path {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A B C D F : Set V)
    (hAB : Disjoint A B)
    (hF : F ⊆ (A ∪ B ∪ C ∪ D)ᶜ) (hFconn : ConnectedSet G F)
    (hFminor : ∀ v ∈ F, MinorForCube G A B C D v)
    (a₀ b₀ : V) (ha₀A : a₀ ∈ A) (hb₀B : b₀ ∈ B) (ha₀b₀ : ¬ G.Adj a₀ b₀)
    (ha₀F : ∃ x ∈ F, G.Adj a₀ x) (hb₀F : ∃ y ∈ F, G.Adj b₀ y) :
    ∃ (f : List V) (a b : V), ABPathConfig G A B C D F f a b := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Set V, BadAB G A B F S ∧ S.ncard = n
  have hP : ∃ n, P n :=
    ⟨F.ncard, F, ⟨subset_rfl, hFconn, a₀, ha₀A, b₀, hb₀B, ha₀b₀, ha₀F, hb₀F⟩, rfl⟩
  let n₀ : ℕ := Nat.find hP
  obtain ⟨F₀, hbad₀, hcard₀⟩ := Nat.find_spec hP
  obtain ⟨hF₀F, hF₀conn, a, haA, b, hbB, hab, haF₀, hbF₀⟩ := hbad₀
  have hmin : ∀ S : Set V, S ⊆ F₀ → ConnectedSet G S →
      (∃ a' ∈ A, ∃ b' ∈ B, ¬ G.Adj a' b' ∧
        (∃ x ∈ S, G.Adj a' x) ∧ (∃ y ∈ S, G.Adj b' y)) → S = F₀ := by
    intro S hSF₀ hSconn hSwit
    by_contra hne
    have hlt : S.ncard < F₀.ncard :=
      Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨hSF₀, hne⟩) (Set.toFinite _)
    have hle : n₀ ≤ S.ncard :=
      Nat.find_min' hP ⟨S, ⟨hSF₀.trans hF₀F, hSconn, hSwit⟩, rfl⟩
    omega
  have haK : a ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inl haA))
  have hbK : b ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inr hbB))
  have haF : a ∉ F₀ := fun ha => hF (hF₀F ha) haK
  have hbF : b ∉ F₀ := fun hb => hF (hF₀F hb) hbK
  have habne : a ≠ b := by
    intro he
    exact (Set.disjoint_left.mp hAB haA) (he ▸ hbB)
  obtain ⟨p, hp, hp3, hpint, hpconn, ⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hF₀conn habne hab haF hbF haF₀ hbF₀
  have hIeq : {z : V | z ∈ interior p} = F₀ :=
    hmin _ hpint hpconn ⟨a, haA, b, hbB, hab, ⟨x, hx, hax⟩, ⟨y, hy, hby⟩⟩
  let f := interior p
  have hfpath : IsPathList G f := by
    dsimp [f]
    exact (PathGlue.isPathFrom_interior hp.1 hp3).1
  have hflen : f.length = p.length - 2 := by
    dsimp [f]
    exact PathBasics.interior_length p
  have hfpos : 0 < f.length := by omega
  have hp0 : p[0]'(by omega) = a :=
    PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
  have hplast : p[p.length - 1]'(by omega) = b :=
    PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
  have hfget : ∀ (i : ℕ) (hi : i < f.length), f[i]'hi = p[i + 1]'(by omega) := by
    intro i hi
    dsimp [f]
    exact interior_getElem p i hi
  have hadjA : ∀ (i : ℕ) (hi : i < f.length), G.Adj a (f[i]'hi) ↔ i = 0 := by
    intro i hi
    rw [hfget i hi, ← hp0, PathBasics.path_adj_iff hp.1 (by omega) (by omega)]
    omega
  have hadjB : ∀ (i : ℕ) (hi : i < f.length),
      G.Adj b (f[i]'hi) ↔ i = f.length - 1 := by
    intro i hi
    rw [hfget i hi, ← hplast, PathBasics.path_adj_iff hp.1 (by omega) (by omega)]
    rw [hflen]
    omega
  have hfsub : {z : V | z ∈ f} ⊆ F := by
    intro z hz
    exact hF₀F (by rw [← hIeq]; exact hz)
  have hlen2 : 2 ≤ f.length := by
    by_contra hnot
    have hlen1 : f.length = 1 := by omega
    have hminor := hFminor (f[0]'hfpos) (hfsub (List.getElem_mem hfpos))
    have haN : a ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C) := by
      refine ⟨⟨?_, haK⟩, Or.inl haA⟩
      rw [SimpleGraph.mem_neighborSet]
      exact ((hadjA 0 hfpos).mpr rfl).symm
    have hbN : b ∈ G.neighborSet (f[0]'hfpos) ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D) := by
      refine ⟨⟨?_, hbK⟩, Or.inl hbB⟩
      rw [SimpleGraph.mem_neighborSet]
      have := (hadjB 0 hfpos).mpr (by omega)
      exact this.symm
    exact hab (hminor.2.2 a haN b hbN)
  refine ⟨f, a, b, hfpath, hlen2, hfsub, ?_, haA, hbB, hab, hadjA, hadjB, ?_, ?_⟩
  · intro z hz
    exact hF (hfsub hz)
  · intro z hz
    exact hFminor z (hfsub hz)
  · intro S hS hconn hwit
    exact (hmin S (by rw [← hIeq]; exact hS) hconn hwit).trans hIeq.symm

/-- If a nonadjacent `A`--`B` pair attaches at positions `i,j` of the globally minimal path,
then those positions are the two ends of the path (in one of the two possible orientations).
This packages every later appeal to *"the minimality of `k`"*. -/
theorem attachment_indices_span {V : Type*} {G : SimpleGraph V} {A B C D F : Set V}
    {f : List V} {a b : V} (hcfg : ABPathConfig G A B C D F f a b)
    {a' b' : V} (ha'A : a' ∈ A) (hb'B : b' ∈ B) (ha'b' : ¬ G.Adj a' b')
    {i j : ℕ} (hi : i < f.length) (hj : j < f.length)
    (hai : G.Adj a' (f[i]'hi)) (hbj : G.Adj b' (f[j]'hj)) :
    (i = 0 ∧ j = f.length - 1) ∨ (j = 0 ∧ i = f.length - 1) := by
  have hneij : i ≠ j := by
    intro hij
    subst j
    have hminor := hcfg.minor (f[i]'hi) (List.getElem_mem hi)
    have haK : a' ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inl ha'A))
    have hbK : b' ∈ A ∪ B ∪ C ∪ D := Or.inl (Or.inl (Or.inr hb'B))
    have haN : a' ∈ G.neighborSet (f[i]'hi) ∩ (A ∪ B ∪ C ∪ D) ∩ (A ∪ C) := by
      refine ⟨⟨?_, haK⟩, Or.inl ha'A⟩
      rw [SimpleGraph.mem_neighborSet]
      exact hai.symm
    have hbN : b' ∈ G.neighborSet (f[i]'hi) ∩ (A ∪ B ∪ C ∪ D) ∩ (B ∪ D) := by
      refine ⟨⟨?_, hbK⟩, Or.inl hb'B⟩
      rw [SimpleGraph.mem_neighborSet]
      exact hbj.symm
    exact ha'b' (hminor.2.2 a' haN b' hbN)
  have hnd : f.Nodup := PathBasics.path_nodup hcfg.path
  rcases lt_or_gt_of_ne hneij with hij | hji
  · let S : Set V := {z : V | z ∈ (f.drop i).take (j - i + 1)}
    have hSsub : S ⊆ {z : V | z ∈ f} := by
      intro z hz
      obtain ⟨k, hk, -, -, rfl⟩ := (PathBasics.mem_slice_iff f (le_of_lt hij) hj).mp hz
      exact List.getElem_mem hk
    have hSconn : ConnectedSet G S :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_slice hcfg.path hij hj)
    have hfiS : f[i]'hi ∈ S := by
      exact (PathBasics.mem_slice_iff f (le_of_lt hij) hj).mpr ⟨i, hi, le_rfl, le_of_lt hij, rfl⟩
    have hfjS : f[j]'hj ∈ S := by
      exact (PathBasics.mem_slice_iff f (le_of_lt hij) hj).mpr ⟨j, hj, le_of_lt hij, le_rfl, rfl⟩
    have hSeq := hcfg.minimal S hSsub hSconn
      ⟨a', ha'A, b', hb'B, ha'b', ⟨f[i]'hi, hfiS, hai⟩, ⟨f[j]'hj, hfjS, hbj⟩⟩
    have hf0S : f[0]'(by omega) ∈ S := by
      rw [hSeq]
      exact List.getElem_mem (by omega)
    obtain ⟨k₀, hk₀, hik₀, -, heq₀⟩ :=
      (PathBasics.mem_slice_iff f (le_of_lt hij) hj).mp hf0S
    have hk₀0 : k₀ = 0 :=
      (List.Nodup.getElem_inj_iff hnd).mp (heq₀.trans rfl)
    have hi0 : i = 0 := by omega
    have hflS : f[f.length - 1]'(by omega) ∈ S := by
      rw [hSeq]
      exact List.getElem_mem (by omega)
    obtain ⟨k₁, hk₁, -, hk₁j, heq₁⟩ :=
      (PathBasics.mem_slice_iff f (le_of_lt hij) hj).mp hflS
    have hk₁last : k₁ = f.length - 1 :=
      (List.Nodup.getElem_inj_iff hnd).mp (heq₁.trans rfl)
    exact Or.inl ⟨hi0, by omega⟩
  · let S : Set V := {z : V | z ∈ (f.drop j).take (i - j + 1)}
    have hSsub : S ⊆ {z : V | z ∈ f} := by
      intro z hz
      obtain ⟨k, hk, -, -, rfl⟩ := (PathBasics.mem_slice_iff f (le_of_lt hji) hi).mp hz
      exact List.getElem_mem hk
    have hSconn : ConnectedSet G S :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_slice hcfg.path hji hi)
    have hfjS : f[j]'hj ∈ S := by
      exact (PathBasics.mem_slice_iff f (le_of_lt hji) hi).mpr ⟨j, hj, le_rfl, le_of_lt hji, rfl⟩
    have hfiS : f[i]'hi ∈ S := by
      exact (PathBasics.mem_slice_iff f (le_of_lt hji) hi).mpr ⟨i, hi, le_of_lt hji, le_rfl, rfl⟩
    have hSeq := hcfg.minimal S hSsub hSconn
      ⟨a', ha'A, b', hb'B, ha'b', ⟨f[i]'hi, hfiS, hai⟩, ⟨f[j]'hj, hfjS, hbj⟩⟩
    have hf0S : f[0]'(by omega) ∈ S := by
      rw [hSeq]
      exact List.getElem_mem (by omega)
    obtain ⟨k₀, hk₀, hjk₀, -, heq₀⟩ :=
      (PathBasics.mem_slice_iff f (le_of_lt hji) hi).mp hf0S
    have hk₀0 : k₀ = 0 :=
      (List.Nodup.getElem_inj_iff hnd).mp (heq₀.trans rfl)
    have hj0 : j = 0 := by omega
    have hflS : f[f.length - 1]'(by omega) ∈ S := by
      rw [hSeq]
      exact List.getElem_mem (by omega)
    obtain ⟨k₁, hk₁, -, hk₁i, heq₁⟩ :=
      (PathBasics.mem_slice_iff f (le_of_lt hji) hi).mp hflS
    have hk₁last : k₁ = f.length - 1 :=
      (List.Nodup.getElem_inj_iff hnd).mp (heq₁.trans rfl)
    exact Or.inr ⟨hj0, by omega⟩

/-- Replacing the two original ends by any nonadjacent `A`--`B` pair which sees the two ends of
the minimal interior produces the induced path written throughout the paper as
`a'-f₁-⋯-fₖ-b'`. -/
theorem full_path_of_end_attachments {V : Type*} {G : SimpleGraph V}
    {A B C D F : Set V} (hAB : Disjoint A B)
    {f : List V} {a b a' b' : V} (hcfg : ABPathConfig G A B C D F f a b)
    (ha'A : a' ∈ A) (hb'B : b' ∈ B) (ha'b' : ¬ G.Adj a' b')
    (hafirst : G.Adj a' (f[0]'(by have := hcfg.len; omega)))
    (hblast : G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega))) :
    IsPathFrom G (a' :: (f ++ [b'])) a' b' := by
  have hlen := hcfg.len
  have hfpos : 0 < f.length := by omega
  have hlast : f.length - 1 < f.length := by omega
  have hnd : f.Nodup := PathBasics.path_nodup hcfg.path
  have hfpath : IsPathFrom G f (f[0]'hfpos) (f[f.length - 1]'hlast) :=
    isPathFrom_self hcfg.path hfpos
  have ha'not : a' ∉ f := by
    intro ha'f
    exact hcfg.outside a' ha'f (Or.inl (Or.inl (Or.inl ha'A)))
  have hb'not : b' ∉ f := by
    intro hb'f
    exact hcfg.outside b' hb'f (Or.inl (Or.inl (Or.inr hb'B)))
  have ha'other : ∀ x ∈ f, x ≠ f[0]'hfpos → ¬ G.Adj a' x := by
    intro x hx hx0 hadj
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    rcases attachment_indices_span hcfg ha'A hb'B ha'b' hi hlast hadj hblast with h | h
    · exact hx0 ((List.Nodup.getElem_inj_iff hnd).mpr h.1)
    · omega
  have hb'other : ∀ x ∈ f, x ≠ f[f.length - 1]'hlast → ¬ G.Adj b' x := by
    intro x hx hxlast hadj
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
    rcases attachment_indices_span hcfg ha'A hb'B ha'b' hfpos hj hafirst hadj with h | h
    · exact hxlast ((List.Nodup.getElem_inj_iff hnd).mpr h.2)
    · omega
  exact PathAttach.isPathFrom_cons_concat hfpath hafirst hblast ha'b'
    (fun he => (Set.disjoint_left.mp hAB ha'A) (he ▸ hb'B))
    ha'not hb'not ha'other hb'other

/-- The hole `a'-f₁-⋯-fₖ-b'-d-c-a'` used in the paper shows that the number `k` of
internal vertices is even. -/
theorem even_length_of_end_attachments {V : Type*} {G : SimpleGraph V}
    {A B C D F : Set V} (hG : Berge G) (hcube : IsCube G A B C D)
    {f : List V} {a b a' b' : V} (hcfg : ABPathConfig G A B C D F f a b)
    (ha'A : a' ∈ A) (hb'B : b' ∈ B) (ha'b' : ¬ G.Adj a' b')
    (hafirst : G.Adj a' (f[0]'(by have := hcfg.len; omega)))
    (hblast : G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)))
    (hnoC : ∀ c ∈ C, ∀ x ∈ f, ¬ G.Adj c x)
    (hnoD : ∀ d ∈ D, ∀ x ∈ f, ¬ G.Adj d x) : Even f.length := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -, -, -, hDne⟩,
    ⟨cAC, cBD, aAD, aBC⟩, -, sCD⟩ := hcube
  obtain ⟨d, hdD⟩ := hDne
  obtain ⟨c, hcC, hcd⟩ := exists_adj_of_mem_right dCD sCD hdD
  let q := a' :: (f ++ [b'])
  have hq : IsPathFrom G q a' b' := by
    dsimp [q]
    exact full_path_of_end_attachments dAB hcfg ha'A hb'B ha'b' hafirst hblast
  have hqmem : ∀ x ∈ q, x = a' ∨ x ∈ f ∨ x = b' := by
    intro x hx
    simpa [q] using hx
  have hcq : c ∉ q := by
    intro hcq
    rcases hqmem c hcq with rfl | hcf | rfl
    · exact Set.disjoint_left.mp dAC ha'A hcC
    · exact hcfg.outside c hcf (Or.inl (Or.inr hcC))
    · exact Set.disjoint_left.mp dBC hb'B hcC
  have hdq : d ∉ q := by
    intro hdq
    rcases hqmem d hdq with rfl | hdf | rfl
    · exact Set.disjoint_left.mp dAD ha'A hdD
    · exact hcfg.outside d hdf (Or.inr hdD)
    · exact Set.disjoint_left.mp dBD hb'B hdD
  have hcint : ∀ x ∈ interior q, ¬ G.Adj c x := by
    intro x hx
    have hxi := (PathBasics.mem_interior_iff_of_pathFrom hq).mp hx
    rcases hqmem x hxi.1 with rfl | hxf | rfl
    · exact absurd rfl hxi.2.1
    · exact hnoC c hcC x hxf
    · exact absurd rfl hxi.2.2
  have hdint : ∀ x ∈ interior q, ¬ G.Adj d x := by
    intro x hx
    have hxi := (PathBasics.mem_interior_iff_of_pathFrom hq).mp hx
    rcases hqmem x hxi.1 with rfl | hxf | rfl
    · exact absurd rfl hxi.2.1
    · exact hnoD d hdD x hxf
    · exact absurd rfl hxi.2.2
  have hhole : IsHoleList G (d :: c :: q) :=
    PrismBasics.isHoleList_of_path_add_two_vertices hq
      (by
        simp only [q, pathLength, List.length_cons, List.length_append]
        have hlen := hcfg.len
        omega)
      (cAC a' ha'A c hcC).symm (cBD b' hb'B d hdD).symm hcd hcq hdq
      (fun hadj => aBC b' hb'B c hcC hadj.symm)
      (fun hadj => aAD a' ha'A d hdD hadj.symm) hcint hdint
  have heven := hG.1 (d :: c :: q) hhole
  have heven' : Even (f.length + 4) := by
    simpa [holeLength, q, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using heven
  exact (Nat.even_add.mp heven').mpr (by norm_num)

/-- The simultaneous cube symmetry `(A,B,C,D,f,a,b) ↦ (B,A,D,C,reverse f,b,a)` preserves
the minimal attachment-path configuration.  This justifies the paper's later "by symmetry" when
only the right-hand set `B'` is non-full. -/
theorem config_swap_reverse {V : Type*} {G : SimpleGraph V} {A B C D F : Set V}
    {f : List V} {a b : V} (hcfg : ABPathConfig G A B C D F f a b) :
    ABPathConfig G B A D C F f.reverse b a := by
  have hlen : 2 ≤ f.reverse.length := by simpa using hcfg.len
  have hrevlen : f.reverse.length = f.length := List.length_reverse
  refine ⟨PathBasics.isPathList_reverse hcfg.path, hlen, ?_, ?_, hcfg.memB, hcfg.memA,
    (fun hadj => hcfg.nonadj hadj.symm), ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact hcfg.subset (List.mem_reverse.mp hz)
  · intro z hz
    rw [union4_swap A B C D]
    exact hcfg.outside z (List.mem_reverse.mp hz)
  · intro i hi
    simp only [List.length_reverse] at hi ⊢
    simp only [List.getElem_reverse]
    have hk : f.length - 1 - i < f.length := by omega
    rw [hcfg.adjB (f.length - 1 - i) hk]
    have := hcfg.len
    omega
  · intro i hi
    simp only [List.length_reverse] at hi ⊢
    simp only [List.getElem_reverse]
    have hk : f.length - 1 - i < f.length := by omega
    rw [hcfg.adjA (f.length - 1 - i) hk]
    have := hcfg.len
    omega
  · intro z hz
    exact minorForCube_swap (hcfg.minor z (List.mem_reverse.mp hz))
  · intro S hS hconn hwit
    have hS' : S ⊆ {z : V | z ∈ f} := by
      intro z hz
      exact List.mem_reverse.mp (hS hz)
    obtain ⟨a', ha'B, b', hb'A, ha'b', ⟨x, hxS, ha'x⟩, ⟨y, hyS, hb'y⟩⟩ := hwit
    have heq := hcfg.minimal S hS' hconn
      ⟨b', hb'A, a', ha'B, (fun hadj => ha'b' hadj.symm),
        ⟨y, hyS, hb'y⟩, ⟨x, hxS, ha'x⟩⟩
    calc
      S = {z : V | z ∈ f} := heq
      _ = {z : V | z ∈ f.reverse} := by ext z; simp

/-- If every vertex of `A` belongs to the paper's set `A'`, only the first path vertex can
have a neighbour in `A`. -/
theorem no_A_after_first_of_left_full {V : Type*} {G : SimpleGraph V}
    {A B C D F : Set V} {f : List V} {a b : V}
    (hcfg : ABPathConfig G A B C D F f a b)
    (hfull : ∀ a' ∈ A, G.Adj a' (f[0]'(by have := hcfg.len; omega)) ∧
      ∃ b' ∈ B, ¬ G.Adj a' b' ∧
        G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega))) :
    ∀ a' ∈ A, ∀ (i : ℕ) (hi : i < f.length), 0 < i → ¬ G.Adj a' (f[i]'hi) := by
  intro a' ha'A i hi hi0 hai
  obtain ⟨-, b', hb'B, ha'b', hblast⟩ := hfull a' ha'A
  rcases attachment_indices_span hcfg ha'A hb'B ha'b' hi (by have := hcfg.len; omega)
      hai hblast with h | h
  · omega
  · have := hcfg.len; omega

/-- If every vertex of `B` belongs to the paper's set `B'`, only the last path vertex can
have a neighbour in `B`. -/
theorem no_B_before_last_of_right_full {V : Type*} {G : SimpleGraph V}
    {A B C D F : Set V} {f : List V} {a b : V}
    (hcfg : ABPathConfig G A B C D F f a b)
    (hfull : ∀ b' ∈ B, G.Adj b' (f[f.length - 1]'(by have := hcfg.len; omega)) ∧
      ∃ a' ∈ A, ¬ G.Adj a' b' ∧ G.Adj a' (f[0]'(by have := hcfg.len; omega))) :
    ∀ b' ∈ B, ∀ (i : ℕ) (hi : i < f.length), i < f.length - 1 →
      ¬ G.Adj b' (f[i]'hi) := by
  intro b' hb'B i hi hilast hbi
  obtain ⟨-, a', ha'A, ha'b', hafirst⟩ := hfull b' hb'B
  rcases attachment_indices_span hcfg ha'A hb'B ha'b' (by have := hcfg.len; omega) hi
      hafirst hbi with h | h
  · omega
  · have := hcfg.len; omega

/-- In the `X ⊆ A ∪ B` branch, no vertex of the minimal outside path has a neighbour in
`C ∪ D`; otherwise that cube vertex itself would be an attachment lying in `A ∪ B`. -/
theorem path_anticomplete_cd {V : Type*} {G : SimpleGraph V}
    {A B C D F X : Set V} {f : List V} {a b : V}
    (hcube : IsCube G A B C D) (hcfg : ABPathConfig G A B C D F f a b)
    (hX : X = attachments G F (A ∪ B ∪ C ∪ D)) (hXAB : X ⊆ A ∪ B) :
    Anticomplete G (C ∪ D) {z : V | z ∈ f} := by
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, -⟩, -, -⟩ := hcube
  intro x hx y hy hxy
  have hxK : x ∈ A ∪ B ∪ C ∪ D := by
    rcases hx with hxC | hxD
    · exact Or.inl (Or.inr hxC)
    · exact Or.inr hxD
  have hxatt : x ∈ X := by
    rw [hX]
    exact ⟨hxK, y, hcfg.subset hy, hxy⟩
  rcases hXAB hxatt with hxA | hxB <;> rcases hx with hxC | hxD
  · exact Set.disjoint_left.mp dAC hxA hxC
  · exact Set.disjoint_left.mp dAD hxA hxD
  · exact Set.disjoint_left.mp dBC hxB hxC
  · exact Set.disjoint_left.mp dBD hxB hxD

end Thm142ABComplete

end Workspace.ProofLemmas
