import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.KiteTailBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.StripSystemNeighbourhood
import Workspace.Statements.S02.Thm_2_6
import Workspace.Statements.S02.Thm_2_7
import Workspace.Statements.S04.Thm_4_5

/-!
# 8.6, claim (2)

PAPER (proof of 8.6, printed p. 46), verbatim:

> **(2) If there is a component `F` of `Z` such that for some `v ∈ V(J)`, all attachments of `F`
> in `V(S,N)` belong to `N_v`, then `G` admits a balanced skew partition.**
>
> For let `F' = V(G) \ (F ∪ N_v)`; then `F' ≠ ∅`, and every path in `G` from `F` to `F'` meets
> `N_v`.  Since `N_v` is not anticonnected, it follows that `(F ∪ F', N_v)` is a skew partition.
> By 4.2 we may assume it is not loose, and we will prove that it is balanced.  Let the
> neighbours of `v` in `J` be `u₁,…,u_k`; then every anticomponent of `N_v` is a subset of one of
> `N_{vu₁},…,N_{vu_k}`.  Choose a neighbour `w` of `u₁` in `J` different from `v, u₂`, choose
> `n₁ ∈ N_{u₁w}`, and choose `n₂ ∈ N_{vu₂}`.  Then `n₁, n₂` belong to strips `S_{u₁w}`, `S_{vu₂}`,
> where `u₁w`, `vu₂` are disjoint edges of `J`; and so `n₁, n₂` are not adjacent in `G`.  Let
> `K = {n₁} ∪ S_{vu₁} \ N_{vu₁}`.  Then `K` is connected (since every vertex of `S_{vu₁}` is in a
> `vu₁`-rung and `n₁` is complete to `N_{u₁v}`), every vertex in `N_{vu₁}` has a neighbour in `K`
> (for the same reason), and `n₂` is not in `K` and has no neighbour in `K`.  (For the last claim,
> `n₂` is not in `K` since it is in only one strip; and it has no neighbour in `S_{vu₁} \ N_{vu₁}`
> from the definition of a strip system; and it is not adjacent to `n₁` as we already saw.)  By
> 2.6, `(K, N_{vu₁})` is balanced, and therefore by 2.7.1, so is `(F, N_{vu₁})`.  By 4.5, `G`
> admits a balanced skew partition.  This proves (2).

The argument is reproduced step for step.  Note that the final citation of 4.5 supplies the skew
partition *and* its balance in one call: the transcribed `thm_4_5` takes the four sets
`(X,Y,L,R)` with `X` complete to `Y`, `L` anticomplete to `R`, and one of three side conditions,
the third of which is exactly *"`(L,Y)` is balanced"* — here `(F, N_{vu₁})`.  So the paper's
*"`(F ∪ F', N_v)` is a skew partition"* is the partition `(L ∪ R, X ∪ Y)` that 4.5 builds
internally, with

```
X = N_v \ N_{vu₁},   Y = N_{vu₁},   L = F,   R = F' = V(G) \ (F ∪ N_v).
```

The two sentences the paper leaves unargued — *"then `F' ≠ ∅`"* and *"`N_v` is not
anticonnected"*, together with *"every anticomponent of `N_v` is a subset of one of the
`N_{vu_i}`"* — are `StripSystemNeighbourhood`.  The 4.2 sentence (*"we may assume it is not
loose"*) is not needed on this route: 4.5 is applied directly.

The hypothesis `hFsep` below is the paper's *"every path in `G` from `F` to `F'` meets `N_v`"*;
at the call site inside 8.6 it comes from `F` being a **component** of `Z` and `Y` being empty.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm86ClaimTwo

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}

/-! ## Two small utilities -/

/-- A set of size `≥ 3` has a member avoiding any two prescribed elements.  (The paper's
*"choose a neighbour `w` of `u₁` in `J` different from `v, u₂`"*.) -/
theorem exists_mem_ne_two {α : Type*} [Finite α] {s : Set α} (hs : 3 ≤ s.ncard) (a b : α) :
    ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  by_contra hcon
  push_neg at hcon
  have hsub : s ⊆ ({a, b} : Set α) := by
    intro x hx
    rcases eq_or_ne x a with rfl | hxa
    · exact Or.inl rfl
    · exact Or.inr (hcon x hx hxa)
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({a, b} : Set α).ncard ≤ 2 := by
    have h3 := Set.ncard_insert_le a ({b} : Set α)
    rw [Set.ncard_singleton] at h3
    omega
  omega

/-- Reachability inside an induced subgraph is monotone in the vertex set. -/
theorem reachable_mono {A B : Set V} (hAB : A ⊆ B) {x y : V} (hx : x ∈ A) (hy : y ∈ A)
    (hr : (G.induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩) :
    (G.induce B).Reachable ⟨x, hAB hx⟩ ⟨y, hAB hy⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun z => ⟨z.1, hAB z.2⟩, fun {_ _} hab => hab⟩ : (G.induce A) →g (G.induce B)) p⟩

/-! ## Claim (2) -/

/-- **8.6, claim (2)** (printed p. 46).

PAPER: *"If there is a component `F` of `Z` such that for some `v ∈ V(J)`, all attachments of `F`
in `V(S,N)` belong to `N_v`, then `G` admits a balanced skew partition."* -/
theorem admitsBalancedSkewPartition_of_attachments_in_N
    (hG : Berge G) (hJ : IsKConnected J 3) (h : IsJStripSystem G J S N)
    {F : Set V} {v : U}
    (hFne : F.Nonempty)
    (hFdisj : Disjoint F (stripSystemVertices J S))
    (hFconn : ConnectedSet G F)
    (hFattach : attachments G F (stripSystemVertices J S) ⊆ N v)
    (hFsep : Anticomplete G F ((F ∪ N v)ᶜ)) :
    AdmitsBalancedSkewPartition G := by
  classical
  have hFdisj' : ∀ x ∈ F, x ∉ stripSystemVertices J S := fun x hx => Set.disjoint_left.mp hFdisj hx
  have hNv : N v ⊆ stripSystemVertices J S := StripSystemBasics.N_subset_vertices h v
  -- *"Let the neighbours of `v` in `J` be `u₁,…,u_k`"* — we need two of them.
  have hdegv : 3 ≤ (J.neighborSet v).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ v
  obtain ⟨u₁, hu₁, -⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet v) (by omega) v
  obtain ⟨u₂, hu₂, hu₂u₁⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet v) (by omega) u₁
  have hvu₁ : J.Adj v u₁ := hu₁
  have hvu₂ : J.Adj v u₂ := hu₂
  have hu₁v : J.Adj u₁ v := hvu₁.symm
  -- *"Choose a neighbour `w` of `u₁` in `J` different from `v, u₂`"*
  have hdegu₁ : 3 ≤ (J.neighborSet u₁).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ u₁
  obtain ⟨w, hw, hwv, hwu₂⟩ := exists_mem_ne_two hdegu₁ v u₂
  have hu₁w : J.Adj u₁ w := hw
  -- *"choose `n₁ ∈ N_{u₁w}`, and choose `n₂ ∈ N_{vu₂}`"*
  obtain ⟨n₁, hn₁N, hn₁S⟩ := StripSystemBasics.Nuv_nonempty h hu₁w
  obtain ⟨n₂, hn₂N, hn₂S⟩ := StripSystemBasics.Nuv_nonempty h hvu₂
  -- *"`u₁w`, `vu₂` are disjoint edges of `J`; and so `n₁, n₂` are not adjacent in `G`"*
  have hnodup : [u₁, w, v, u₂].Nodup := by
    have h1 : u₁ ≠ w := hu₁w.ne
    have h2 : u₁ ≠ v := hu₁v.ne
    have h3 : u₁ ≠ u₂ := fun hc => hu₂u₁ hc.symm
    have h4 : w ≠ v := hwv
    have h5 : w ≠ u₂ := hwu₂
    have h6 : v ≠ u₂ := hvu₂.ne
    simp [h1, h2, h3, h4, h5, h6]
  have hn₁n₂ : ¬ G.Adj n₁ n₂ :=
    StripSystemBasics.not_adj_of_disjoint_edges h hu₁w hvu₂ hnodup hn₁S hn₂S
  -- Abbreviations.
  obtain ⟨Y, hYdef⟩ : ∃ Y : Set V, Y = stripSystemNuv S N v u₁ := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Set V, K = {n₁} ∪ (S v u₁ \ Y) := ⟨_, rfl⟩
  have hYsubS : Y ⊆ S v u₁ := by rw [hYdef]; exact fun _ hx => hx.2
  have hYsubN : Y ⊆ N v := by rw [hYdef]; exact fun _ hx => hx.1
  have hn₁K : n₁ ∈ K := by rw [hKdef]; exact Or.inl rfl
  -- `S_{u₁w} ∩ N_v = ∅` (the paper's *"only one strip"*), since `v ∉ {u₁, w}`.
  have hSu₁wNv : ∀ x ∈ S u₁ w, x ∉ N v := by
    intro x hx hxN
    have := StripSystemBasics.strip_inter_N_eq_empty h hu₁w (Ne.symm hu₁v.ne) (Ne.symm hwv)
    rw [Set.eq_empty_iff_forall_notMem] at this
    exact this x ⟨hx, hxN⟩
  -- `K ⊆ V(S,N)` and `K ∩ N_v = ∅`.
  have hKsub : K ⊆ stripSystemVertices J S := by
    rw [hKdef]
    rintro x (rfl | hx)
    · exact StripSystemBasics.strip_subset_vertices hu₁w hn₁S
    · exact StripSystemBasics.strip_subset_vertices hvu₁ hx.1
  have hKNv : ∀ x ∈ K, x ∉ N v := by
    rw [hKdef]
    rintro x (rfl | hx)
    · exact hSu₁wNv x hn₁S
    · intro hxN
      exact hx.2 (by rw [hYdef]; exact ⟨hxN, hx.1⟩)
  -- `n₁` is complete to `N_{u₁v}` (sixth axiom at `u₁`, for the edges `u₁w` and `u₁v`).
  have hn₁compl : ∀ z, z ∈ N u₁ → z ∈ S u₁ v → G.Adj n₁ z := by
    intro z hzN hzS
    exact StripSystemBasics.Nuv_complete h hu₁w hu₁v hwv n₁ ⟨hn₁N, hn₁S⟩ z ⟨hzN, hzS⟩
  have hSsymm : S v u₁ = S u₁ v := StripSystemBasics.strip_symm h hvu₁
  /- The rung analysis, used twice.  For a `vu₁`-rung `R` we write `R = a :: l`, where `a` is the
  unique vertex of `R` in `N_v`; then `l ⊆ K`, `l` is connected, and (when `l ≠ []`) the `u₁`-end
  of `R` lies in `l` and is adjacent to `n₁`. -/
  have rung : ∀ R : List V, IsUVRung G J S N v u₁ R →
      ∃ (a : V) (l : List V), R = a :: l ∧ (∀ y ∈ R, (y ∈ N v ↔ y = a)) ∧
        (∀ y ∈ l, y ∈ K) ∧ ConnectedSet G {y : V | y ∈ l} ∧
        (l ≠ [] → ∃ z ∈ l, G.Adj n₁ z) ∧ (l = [] → G.Adj n₁ a) ∧
        (∀ b : V, ∀ l' : List V, l = b :: l' → G.Adj a b) := by
    rintro R ⟨-, s, t, hp, hsub, hs, ht⟩
    obtain ⟨hpl, hhead, hlast⟩ := hp
    obtain ⟨a, l, rfl⟩ : ∃ a l, R = a :: l := by
      cases R with
      | nil => exact absurd hhead (by simp)
      | cons a l => exact ⟨a, l, rfl⟩
    have has : a = s := by simpa using hhead
    subst has
    -- every vertex of `l` lies in `S_{vu₁}`, is not `a`, hence is not in `N_v`, hence in `K`
    have hlK : ∀ y ∈ l, y ∈ K := by
      intro y hy
      have hyR : y ∈ a :: l := List.mem_cons_of_mem _ hy
      have hya : y ≠ a := by
        rintro rfl
        exact (List.nodup_cons.mp hpl.2.1).1 hy
      have hyNv : y ∉ N v := fun hc => hya ((hs y hyR).mp hc)
      rw [hKdef]
      exact Or.inr ⟨hsub y hyR, fun hc => hyNv (hYsubN hc)⟩
    -- `l` is connected: consecutive entries of a path are adjacent
    have hlconn : ConnectedSet G {y : V | y ∈ l} := by
      refine KiteTailBasics.connectedSet_of_consecutive_adj l (fun i hi => ?_)
      have hi' : (i + 1) + 1 < (a :: l).length := by simp only [List.length_cons]; omega
      simpa using PathBasics.path_adj_succ hpl hi'
    -- the `u₁`-end
    have htmem : t ∈ a :: l := List.mem_of_getLast? hlast
    have htN : t ∈ N u₁ := (ht t htmem).mpr rfl
    have htadj : G.Adj n₁ t := hn₁compl t htN (hSsymm ▸ hsub t htmem)
    refine ⟨a, l, rfl, hs, hlK, hlconn, ?_, ?_, ?_⟩
    · intro hlne
      refine ⟨t, ?_, htadj⟩
      -- `l ≠ []` forces `t ∈ l`
      cases l with
      | nil => exact absurd rfl hlne
      | cons b l' =>
        rw [List.getLast?_cons_cons] at hlast
        exact List.mem_of_getLast? hlast
    · intro hlnil
      subst hlnil
      have : t = a := by simpa using hlast.symm
      rw [this] at htadj
      exact htadj
    · rintro b l' rfl
      have h0 : (0 : ℕ) + 1 < (a :: b :: l').length := by simp
      simpa using PathBasics.path_adj_succ hpl h0
  -- *"`K` is connected"*
  have hKconn : ConnectedSet G K := by
    have key : ∀ x, ∀ hx : x ∈ K, (G.induce K).Reachable ⟨x, hx⟩ ⟨n₁, hn₁K⟩ := by
      intro x hx
      have hx' : x ∈ ({n₁} : Set V) ∪ (S v u₁ \ Y) := by rw [← hKdef]; exact hx
      rcases hx' with hx1 | hx2
      · have : x = n₁ := hx1
        subst this
        exact SimpleGraph.Reachable.refl _
      · obtain ⟨R, hR, hxR⟩ := StripSystemBasics.exists_rung h hvu₁ hx2.1
        obtain ⟨a, l, rfl, hs, hlK, hlconn, hlz, -, -⟩ := rung R hR
        have hxa : x ≠ a := by
          rintro rfl
          exact hx2.2 (by rw [hYdef]; exact ⟨(hs x hxR).mpr rfl, hx2.1⟩)
        have hxl : x ∈ l := by
          rcases List.mem_cons.mp hxR with hc | hc
          · exact absurd hc hxa
          · exact hc
        obtain ⟨z, hzl, hzadj⟩ := hlz (List.ne_nil_of_mem hxl)
        have hstep : (G.induce K).Reachable ⟨x, hlK x hxl⟩ ⟨z, hlK z hzl⟩ :=
          reachable_mono (A := {y : V | y ∈ l}) (fun y hy => hlK y hy) hxl hzl
            (hlconn ⟨x, hxl⟩ ⟨z, hzl⟩)
        exact hstep.trans (SimpleGraph.Adj.reachable (show (G.induce K).Adj ⟨z, hlK z hzl⟩
          ⟨n₁, hn₁K⟩ from hzadj.symm))
    intro p q
    exact (key p.1 p.2).trans (key q.1 q.2).symm
  -- *"every vertex in `N_{vu₁}` has a neighbour in `K`"*
  have hYnbr : ∀ y ∈ Y, ∃ x ∈ K, G.Adj y x := by
    intro y hy
    have hyS : y ∈ S v u₁ := hYsubS hy
    have hyN : y ∈ N v := hYsubN hy
    obtain ⟨R, hR, hyR⟩ := StripSystemBasics.exists_rung h hvu₁ hyS
    obtain ⟨a, l, rfl, hs, hlK, -, -, hnil, hcons⟩ := rung R hR
    have hya : y = a := (hs y hyR).mp hyN
    subst hya
    cases l with
    | nil => exact ⟨n₁, hn₁K, (hnil rfl).symm⟩
    | cons b l' => exact ⟨b, hlK b List.mem_cons_self, hcons b l' rfl⟩
  -- *"`n₂` is not in `K` and has no neighbour in `K`"*
  have hn₂notS : n₂ ∉ S v u₁ := by
    intro hc
    have hne : s(v, u₂) ≠ s(v, u₁) := by
      intro hcon
      rcases Sym2.eq_iff.mp hcon with ⟨-, h2⟩ | ⟨h1, -⟩
      · exact hu₂u₁ h2
      · exact hvu₁.ne h1
    exact (Set.disjoint_left.mp (StripSystemBasics.strip_disjoint h hvu₂ hvu₁ hne) hn₂S) hc
  have hn₂K : n₂ ∉ K := by
    rw [hKdef]
    rintro (hc | hc)
    · exact hSu₁wNv n₁ hn₁S (hc ▸ hn₂N)
    · exact hn₂notS hc.1
  have hn₂anti : VertexAnticomplete G n₂ K := by
    intro x hx hadj
    have hx' : x ∈ ({n₁} : Set V) ∪ (S v u₁ \ Y) := by rw [← hKdef]; exact hx
    rcases hx' with hx1 | hx2
    · have : x = n₁ := hx1
      subst this
      exact hn₁n₂ hadj.symm
    · -- the sixth axiom at `v`: an edge between `S_{vu₁}` and `S_{vu₂}` has both ends in `N_v`
      have := StripSystemBasics.mem_N_of_adj h hvu₁ hvu₂ (fun hc => hu₂u₁ hc.symm)
        hx2.1 hn₂S hadj.symm
      exact hx2.2 (by rw [hYdef]; exact ⟨this.1, hx2.1⟩)
  have hn₂compl : VertexComplete G n₂ Y := by
    intro y hy
    exact StripSystemBasics.Nuv_complete h hvu₂ hvu₁ hu₂u₁ n₂ ⟨hn₂N, hn₂S⟩
      y ⟨hYsubN hy, hYsubS hy⟩
  have hKY : Disjoint K Y := by
    refine Set.disjoint_left.mpr (fun x hx hxY => ?_)
    exact hKNv x hx (hYsubN hxY)
  have hn₂notin : n₂ ∉ K ∪ Y := by
    rintro (hc | hc)
    · exact hn₂K hc
    · exact hn₂notS (hYsubS hc)
  -- *"By 2.6, `(K, N_{vu₁})` is balanced"*
  have hbalK : SPGT.Balanced G K Y :=
    _root_.Workspace.Statements.S02.SPGT.thm_2_6 G hG K Y hKY n₂ hn₂notin hn₂compl hn₂anti
  -- `K` is anticomplete to `F`: all attachments of `F` lie in `N_v`, and `K ∩ N_v = ∅`
  have hKF : Anticomplete G K F := by
    intro x hx f hf hadj
    exact hKNv x hx (hFattach ⟨hKsub hx, f, hf, hadj⟩)
  have hFcompl : F ⊆ (K ∪ Y)ᶜ := by
    intro f hf hc
    rcases hc with hc | hc
    · exact hFdisj' f hf (hKsub hc)
    · exact hFdisj' f hf (hNv (hYsubN hc))
  -- *"and therefore by 2.7.1, so is `(F, N_{vu₁})`"*
  have hbalF : SPGT.Balanced G F Y :=
    (_root_.Workspace.Statements.S02.SPGT.thm_2_7 G hG K Y hbalK F hFcompl).1 hKconn hYnbr hKF
  -- *"By 4.5, `G` admits a balanced skew partition."*
  -- `X = N_v \ N_{vu₁}`, `Y = N_{vu₁}`, `L = F`, `R = F' = V(G) \ (F ∪ N_v)`.
  have hXY : Complete G (N v \ Y) Y := by
    intro x hx y hy
    obtain ⟨w', hvw', hxw'⟩ := StripSystemBasics.mem_Nuv_of_mem_N h hx.1
    have hw'u₁ : w' ≠ u₁ := by
      rintro rfl
      exact hx.2 (by rw [hYdef]; exact hxw')
    exact StripSystemBasics.Nuv_complete h hvw' hvu₁ hw'u₁ x hxw'
      y ⟨hYsubN hy, hYsubS hy⟩
  have hn₂X : n₂ ∈ N v \ Y := ⟨hn₂N, fun hc => hn₂notS (hYsubS hc)⟩
  obtain ⟨y₀, hy₀⟩ := StripSystemBasics.Nuv_nonempty h hvu₁
  have hy₀Y : y₀ ∈ Y := by rw [hYdef]; exact hy₀
  -- *"then `F' ≠ ∅`"*
  obtain ⟨z₀, hz₀V, hz₀N⟩ := StripSystemNeighbourhood.exists_mem_not_mem_N hJ h v
  have hz₀ : z₀ ∈ ((F ∪ N v)ᶜ : Set V) := by
    rintro (hc | hc)
    · exact hFdisj' z₀ hc hz₀V
    · exact hz₀N hc
  refine _root_.Workspace.Statements.S04.SPGT.thm_4_5 G hG (N v \ Y) Y F ((F ∪ N v)ᶜ)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ⟨n₂, hn₂X⟩ ⟨y₀, hy₀Y⟩ hFne ⟨z₀, hz₀⟩ hFsep hXY (Or.inr (Or.inr hbalF))
  · -- cover
    ext z
    simp only [Set.mem_union, Set.mem_diff, Set.mem_compl_iff, Set.mem_univ, iff_true]
    by_cases hz : z ∈ F
    · tauto
    · by_cases hz2 : z ∈ N v
      · by_cases hz3 : z ∈ Y <;> tauto
      · tauto
  · exact Set.disjoint_left.mpr (fun x hx hxY => hx.2 hxY)
  · exact Set.disjoint_left.mpr (fun x hx hxF => hFdisj' x hxF (hNv hx.1))
  · exact Set.disjoint_left.mpr (fun x hx hxR => hxR (Or.inr hx.1))
  · exact Set.disjoint_left.mpr (fun x hx hxF => hFdisj' x hxF (hNv (hYsubN hx)))
  · exact Set.disjoint_left.mpr (fun x hx hxR => hxR (Or.inr (hYsubN hx)))
  · exact Set.disjoint_left.mpr (fun x hx hxR => hxR (Or.inl hx))

end Workspace.ProofLemmas.Thm86ClaimTwo
