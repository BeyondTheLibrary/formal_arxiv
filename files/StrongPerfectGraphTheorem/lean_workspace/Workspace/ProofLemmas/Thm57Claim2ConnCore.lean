import Workspace.ProofLemmas.Thm57Claim2DeletedWindow
import Workspace.ProofLemmas.Thm55Structure
import Workspace.ProofLemmas.Thm55BranchReach
import Workspace.ProofLemmas.Thm57EndgameEdgeDeletion
import Workspace.ProofLemmas.BranchClassification
import Workspace.ProofLemmas.Thm75BranchEnds

/-! # Connectivity toolkit for 5.7 (2)

Three general facts used by `Thm57Claim2Connectivity`.

* `rchIn_map` transports a connection of one graph along a map that collapses the deleted
  region to a single surviving vertex.  This is how *"there is a track in `H \ {c₁,c₂}`"*
  becomes a track of `H` with the window removed: an excursion into the interior of the
  window can only enter and leave through one vertex, so collapsing the interior turns the
  walk into a walk of the smaller graph.
* `trackEdges_eq_of_two_common` is the paper's *"there is only one branch of `H` containing
  `c₁` and `c₂`, since `J` is simple"*.
* `exists_exceptional` is the standard consequence of 5.5: after deleting two vertices, all
  the vertices that still see a branch-vertex form one piece, and the rest lies inside a
  single branch through the two deleted vertices.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57Claim2ConnCore

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments
open Workspace.ProofLemmas.NoCrossTrackBranch

variable {W : Type*} [Fintype W] [DecidableEq W]

/-! ### Transporting a connection along a collapsing map -/

private theorem rchIn_map_walk {H G : SimpleGraph W} {A Y : Set W} (π : W → W)
    (hmem : ∀ t ∈ A, π t ∈ Y)
    (hstep : ∀ c ∈ A, ∀ t ∈ A, H.Adj c t → π c = π t ∨ G.Adj (π c) (π t)) :
    ∀ {a b : W} (p : H.Walk a b), (∀ t ∈ p.support, t ∈ A) → RchIn G Y (π a) (π b) := by
  intro a b p
  induction p with
  | nil => intro hp; exact RchIn.refl (hmem _ (hp _ (by simp)))
  | @cons u v w hadj q ih =>
      intro hp
      have hsub : ∀ t ∈ q.support, t ∈ A := by
        intro t ht
        exact hp t (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ ht)
      have hu : u ∈ A := hp u (by simp)
      have hv : v ∈ A := hsub v q.start_mem_support
      have hrest : RchIn G Y (π v) (π w) := ih hsub
      rcases hstep u hu v hv hadj with heq | hadjG
      · rw [heq]; exact hrest
      · exact (RchIn.of_adj (hmem u hu) (hmem v hv) hadjG).trans hrest

/-- **Collapsing the deleted region.**  If `π` maps the surviving set `A` of `H` into `Y` and
sends every edge of `H` inside `A` either to a point or to an edge of `G`, then a connection
inside `A` becomes a connection of `G` inside `Y`. -/
theorem rchIn_map {H G : SimpleGraph W} {A Y : Set W} (π : W → W)
    (hmem : ∀ t ∈ A, π t ∈ Y)
    (hstep : ∀ c ∈ A, ∀ t ∈ A, H.Adj c t → π c = π t ∨ G.Adj (π c) (π t))
    {a b : W} (h : RchIn H A a b) : RchIn G Y (π a) (π b) := by
  obtain ⟨p, hp⟩ := walk_of_rchIn h
  exact rchIn_map_walk π hmem hstep p hp

/-! ### A branch is determined by any two of its vertices -/

/-- Two names for the same edge of `J` carry the same subdividing track. -/
theorem trackEdges_eq_of_sym2_eq {n : ℕ} {J : SimpleGraph (Fin n)} {T : Fin n → Fin n → List W}
    (hrev : ∀ u v : Fin n, J.Adj u v → T v u = (T u v).reverse)
    {u v u' v' : Fin n} (huv : J.Adj u v) (h : s(u, v) = s(u', v')) :
    trackEdges (T u' v') = trackEdges (T u v) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [hrev _ _ huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]

private theorem sym2_eq_of_pair {α : Type*} {x y p q : α} (hxy : x ≠ y)
    (hx : x = p ∨ x = q) (hy : y = p ∨ y = q) : s(p, q) = s(x, y) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> simp_all

/-- A vertex of a track lies on every track with the same edges. -/
theorem mem_of_trackEdges_eq {q t : List W} (h2 : 2 ≤ q.length)
    (hE : trackEdges q = trackEdges t) {x : W} (hx : x ∈ q) : x ∈ t := by
  obtain ⟨i, hi, hor⟩ := Workspace.ProofLemmas.BranchClassification.exists_edge_of_mem h2 hx
  have he : s(q[i]'(by omega), q[i + 1]'hi) ∈ trackEdges t := by
    rw [← hE]; exact ⟨i, hi, rfl⟩
  have hmem := Workspace.ProofLemmas.BranchClassification.mem_of_mem_trackEdges he
  rcases hor with h | h
  · rw [h]; exact hmem.1
  · rw [h]; exact hmem.2

/-- **The branch through two given vertices is unique.**

PAPER (printed p. 23): *"Now there is only one branch of `H` containing `c₁` and `c₂`, since
`J` is simple"*. -/
theorem trackEdges_eq_of_two_common {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H)
    {q q' : List W} (hq : IsBranch H q) (hq' : IsBranch H q')
    (hq2 : 2 ≤ q.length) (hq2' : 2 ≤ q'.length)
    {x y : W} (hxy : x ≠ y) (hxq : x ∈ q) (hyq : y ∈ q) (hxq' : x ∈ q') (hyq' : y ∈ q') :
    trackEdges q = trackEdges q' := by
  classical
  obtain ⟨n, J, hJ, hsub⟩ := hc3
  obtain ⟨ι, T, hS⟩ := exists_subData hsub
  have hdeg : ∀ u : Fin n, 3 ≤ (J.neighborSet u).ncard :=
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ
  obtain ⟨u, v, huv, hE⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_of_isBranch
      hS.inj hS.track hS.len hS.rev hS.disj hS.new hS.cover hS.edges hdeg hq hq2
  obtain ⟨c, d, hcd, hE'⟩ :=
    Workspace.ProofLemmas.BranchClassification.exists_trackEdges_eq_of_isBranch
      hS.inj hS.track hS.len hS.rev hS.disj hS.new hS.cover hS.edges hdeg hq' hq2'
  have hxT : x ∈ T u v := mem_of_trackEdges_eq hq2 hE hxq
  have hyT : y ∈ T u v := mem_of_trackEdges_eq hq2 hE hyq
  have hxT' : x ∈ T c d := mem_of_trackEdges_eq hq2' hE' hxq'
  have hyT' : y ∈ T c d := mem_of_trackEdges_eq hq2' hE' hyq'
  have hsame : s(u, v) = s(c, d) := by
    by_contra hne
    -- neither `x` nor `y` is interior to either track
    have hends : ∀ {z : W}, z ∈ T u v → z ∈ T c d →
        (z = ι u ∨ z = ι v) ∧ (z = ι c ∨ z = ι d) := by
      intro z hz hz'
      have hnint : z ∉ trackInterior (T u v) := fun hc => hS.disj u v c d huv hcd hne z hc hz'
      have hnint' : z ∉ trackInterior (T c d) := fun hc =>
        hS.disj c d u v hcd huv (Ne.symm hne) z hc hz
      exact ⟨Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          (hS.track u v huv).2.1 (hS.track u v huv).2.2 hz hnint,
        Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem
          (hS.track c d hcd).2.1 (hS.track c d hcd).2.2 hz' hnint'⟩
    obtain ⟨hx1, hx2⟩ := hends hxT hxT'
    obtain ⟨hy1, hy2⟩ := hends hyT hyT'
    have h1 : s(ι u, ι v) = s(x, y) := sym2_eq_of_pair hxy hx1 hy1
    have h2 : s(ι c, ι d) = s(x, y) := sym2_eq_of_pair hxy hx2 hy2
    apply hne
    rcases Sym2.eq_iff.mp (h1.trans h2.symm) with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hS.inj e1, hS.inj e2⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hS.inj e1, hS.inj e2⟩)
  rw [hE, hE',
    trackEdges_eq_of_sym2_eq hS.rev huv hsame]

/-! ### The exceptional piece after deleting two vertices -/

/-- **What is left after deleting two vertices.**

There is a set `E` (possibly empty) such that all the other surviving vertices form one
connected piece, and `E`, if nonempty, lies together with the two deleted vertices inside a
single branch of `H`.  This is 5.5 in the form the proof of 5.7 (2) uses it. -/
theorem exists_exceptional {H : SimpleGraph W} (hc3 : CyclicallyThreeConnected H) (x y : W) :
    ∃ E : Set W,
      E ⊆ ({x, y} : Set W)ᶜ ∧
      (∀ e ∈ E, ∀ w ∈ ({x, y} : Set W)ᶜ, H.Adj e w → w ∈ E) ∧
      (∀ e ∈ E, e ∉ branchVertices H) ∧
      (∀ a ∈ ({x, y} : Set W)ᶜ \ E, ∀ b ∈ ({x, y} : Set W)ᶜ \ E,
        RchIn H (({x, y} : Set W)ᶜ) a b) ∧
      (E.Nonempty → ∃ q : List W, IsBranch H q ∧
        E ∪ ({x, y} : Set W) ⊆ {v : W | v ∈ q}) := by
  classical
  set S : Set W := ({x, y} : Set W)ᶜ with hSdef
  set K : Set W := {w : W | ∃ hw : w ∈ S, ∃ b ∈ branchVertices H, RchIn H S w b} with hKdef
  refine ⟨S \ K, Set.diff_subset, ?_, ?_, ?_, ?_⟩
  · -- closed under adjacency inside `S`
    rintro e ⟨heS, heK⟩ w hwS hadj
    refine ⟨hwS, ?_⟩
    rintro ⟨-, b, hb, hwb⟩
    exact heK ⟨heS, b, hb, (RchIn.of_adj heS hwS hadj).trans hwb⟩
  · rintro e ⟨heS, heK⟩ hbv
    exact heK ⟨heS, e, hbv, RchIn.refl heS⟩
  · -- everything outside `E` is joined
    rintro a ⟨haS, haE⟩ b ⟨hbS, hbE⟩
    have haK : a ∈ K := by
      by_contra hc
      exact haE ⟨haS, hc⟩
    have hbK : b ∈ K := by
      by_contra hc
      exact hbE ⟨hbS, hc⟩
    obtain ⟨-, ba, hba, hab⟩ := haK
    obtain ⟨-, bb, hbb, hbbr⟩ := hbK
    exact hab.trans
      ((Workspace.ProofLemmas.Thm55BranchReach.branch_rchIn_compl_pair hc3 hba hbb
        hab.mem_right hbbr.mem_right).trans hbbr.symm)
  · intro hne
    have hcard : ({x, y} : Set W).ncard ≤ 2 := by
      have h1 := Set.ncard_insert_le x ({y} : Set W)
      have h2 : ({y} : Set W).ncard = 1 := Set.ncard_singleton y
      omega
    obtain ⟨q, hq, hsub, -⟩ :=
      Workspace.ProofLemmas.Thm55Structure.branchless_side_contained H hc3
        ({x, y} : Set W) (S \ K) hcard hne Set.diff_subset
        (by
          rintro e ⟨heS, heK⟩ w hwS hadj
          refine ⟨hwS, ?_⟩
          rintro ⟨-, b, hb, hwb⟩
          exact heK ⟨heS, b, hb, (RchIn.of_adj heS hwS hadj).trans hwb⟩)
        (by
          rintro e ⟨heS, heK⟩ hbv
          exact heK ⟨heS, e, hbv, RchIn.refl heS⟩)
    exact ⟨q, hq, hsub⟩

end Workspace.ProofLemmas.Thm57Claim2ConnCore
