import Workspace.ProofLemmas.Thm58BranchBranchCycleGap
import Workspace.Statements.S02.Thm_2_4

/-!
# The two triangle links of 5.8 (7)

PAPER (5.8 (7), printed p. 28): *"If `p₁` has only one neighbour `r ∈ R_{u₁v₁}`,
then we may assume that `r` is in the interior of `R_{u₁v₁}`, by (6), and so `r`
can be linked onto `T`, contrary to 2.4.  If `p₁` has two nonadjacent neighbours
in `R_{u₁v₁}`, then `p₁` can be linked onto `T`, again a contradiction."*

Both sentences are carried out here: the cycle of `Thm58BranchBranchCycle` is cut
into the two paths `P`, `Q` by `Thm58BranchBranchCut.link_of_hole_cut`, the third
path is `R` (extended by `p₁` in the first sentence), and the contradiction with
2.4 comes from the fact that the linked vertex sees at most one vertex of the
triangle `T`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm58BranchBranchLinkSteps

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm58BranchBranch
open Workspace.ProofLemmas.Thm58BranchBranchCycle

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
variable {H : SimpleGraph (Fin n)} {K : Set V}
variable {φ : H.lineGraph ≃g G.induce K} {N : Fin n → Set V}
variable {F : Set V} {P : List V} {p₁ p₂ : V}

/-- A vertex linked onto a triangle is adjacent to two of its vertices, so it
cannot miss two of them. This is the use of 2.4 in both sentences. -/
theorem absurd_of_link (hG : Berge G) {v α β t : V}
    (hlink : VertexCanBeLinkedOntoTriangle G v α β t)
    (h1 : ¬ (G.Adj v α ∧ G.Adj v β)) (h2 : ¬ (G.Adj v α ∧ G.Adj v t))
    (h3 : ¬ (G.Adj v β ∧ G.Adj v t)) : False := by
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG v α β t hlink with hh | hh | hh
  · exact h1 hh
  · exact h2 hh
  · exact h3 hh

/-- The image under `φ` of the edge read off a vertex of the appearance. -/
theorem symm_val {y : V} (hy : y ∈ K) : (↑(φ (φ.symm ⟨y, hy⟩)) : V) = y :=
  congrArg Subtype.val (φ.apply_symm_apply ⟨y, hy⟩)

/-- Distinct vertices of the appearance read off distinct edges. -/
theorem symm_edge_ne {x y : V} (hx : x ∈ K) (hy : y ∈ K) (hxy : x ≠ y) :
    (φ.symm ⟨x, hx⟩).1 ≠ (φ.symm ⟨y, hy⟩).1 := by
  intro hh
  exact hxy (((symm_val (φ := φ) hx).symm.trans
    (congrArg (fun d : H.edgeSet => (↑(φ d) : V)) (Subtype.ext hh))).trans (symm_val (φ := φ) hy))

/-- Every neighbour of the first end lies on the first branch. -/
theorem edge_mem_trackEdges_of_adj (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ : List (Fin n)} (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    {y : V} (hy : y ∈ K) (hpy : G.Adj p₁ y) : (φ.symm ⟨y, hy⟩).1 ∈ trackEdges q₁ := by
  have hpF : p₁ ∈ F := by
    rw [← h.2.2.2.2.2.2.2.1]
    exact PathBasics.head_mem h.2.2.2.2.2.2.1.2.1
  have hval := symm_val (φ := φ) hy
  exact hX₁ ⟨(φ.symm ⟨y, hy⟩).2, hval.symm ▸ hy, p₁, ⟨hpF, ends_ne h⟩, hval.symm ▸ hpy.symm⟩

/-- The star of `c` is contained in the appearance. -/
theorem star_subset_K (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂) (c : Fin n) :
    N c ⊆ K := by
  intro y hy
  rw [h.2.2.2.1 c] at hy
  obtain ⟨e, he, _, rfl⟩ := hy
  exact (φ ⟨e, he⟩).2

/-- A vertex of the star of `c` reads off an edge incident with `c`. -/
theorem star_edge (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂) {c : Fin n} {x : V}
    (hx : x ∈ N c) (hxK : x ∈ K) : c ∈ (φ.symm ⟨x, hxK⟩).1 := by
  rw [h.2.2.2.1 c] at hx
  obtain ⟨e, he, ⟨-, hce⟩, hxe⟩ := hx
  have h1 : (⟨x, hxK⟩ : ↥K) = φ ⟨e, he⟩ := Subtype.ext hxe
  rw [h1]
  simpa using hce


/-- PAPER (5.8 (7), printed p. 28): *"If `p₁` has only one neighbour
`r ∈ R_{u₁v₁}`, then we may assume that `r` is in the interior of `R_{u₁v₁}`, by
(6), and so `r` can be linked onto `T`, contrary to 2.4."* -/
theorem interior_singleton_absurd
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {r : V} (hrK : r ∈ K) (hpr : G.Adj p₁ r)
    (hunique : ∀ y ∈ K, G.Adj p₁ y → y = r)
    (hinternal : ∀ c ∈ branchVertices H, c ∉ (φ.symm ⟨r, hrK⟩).1) : False := by
  classical
  have hrq : (φ.symm ⟨r, hrK⟩).1 ∈ trackEdges q₁ := edge_mem_trackEdges_of_adj h hX₁ hrK hpr
  obtain ⟨Z, R, j, α, β, t, u, cfg, hZ0⟩ :=
    cycle_config_at_interior_edge h hq₁ hq₂ hX₁ hX₂ hrK hrq hinternal
  obtain ⟨h4, hnd, hZadj⟩ := cfg.hole
  have hinj : ∀ (a b : ℕ) (x : V), Z[a]? = some x → Z[b]? = some x → a = b := by
    intro a b x hx hy
    obtain ⟨ha, hxa⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hb, hxb⟩ := List.getElem?_eq_some_iff.mp hy
    exact hnd.getElem_inj_iff.mp (hxa.trans hxb.symm)
  have hp₁F : p₁ ∈ F := by
    rw [← h.2.2.2.2.2.2.2.1]
    exact PathBasics.head_mem h.2.2.2.2.2.2.1.2.1
  have hp₁K : p₁ ∉ K := h.2.2.2.2.1 hp₁F
  have hp₁Z : p₁ ∉ Z := fun hh => hp₁K (cfg.subK p₁ hh)
  have htK : t ∈ K := star_subset_K h u cfg.tN
  have hp₁t : p₁ ≠ t := fun hh => hp₁K (hh ▸ htK)
  -- the third path, extended by `p₁`
  obtain ⟨z, hzlast, hzadj⟩ := cfg.plast
  have hzR : z ∈ R := PathBasics.getLast_mem hzlast
  have hRfrom : IsPathFrom G R t z := ⟨cfg.rpath, cfg.rhead, hzlast⟩
  have hsingle : IsPathFrom G [p₁] p₁ p₁ := ⟨PathBasics.isPathList_singleton G p₁, rfl, rfl⟩
  have hR' : IsPathFrom G (R ++ [p₁]) t p₁ := by
    refine PathGlue.glue_path hRfrom hsingle ?_ ?_
    · intro x hx hx'
      rw [List.mem_singleton] at hx'
      exact cfg.pnot (hx' ▸ hx)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rw [SimpleGraph.adj_comm, hzadj x hx]
      constructor
      · intro hh; exact ⟨hh, rfl⟩
      · rintro ⟨hh, -⟩; exact hh
  -- the deleted vertex of the hole is `r`
  have hrnot : r ∉ Z.drop 1 := by
    intro hh
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hh
    rw [List.getElem?_drop] at hi
    have := hinj 0 (1 + i) r hZ0 hi
    omega
  have hjpos := cfg.jpos
  have hjlt := cfg.jlt
  have hr0 : Z[0]'(by omega) = r := by
    obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp hZ0
    exact hh
  -- the link
  have hlink : VertexCanBeLinkedOntoTriangle G r α β t := by
    refine Thm58BranchBranchCut.link_of_hole_cut ⟨h4, hnd, hZadj⟩ cfg.jpos cfg.jlt
      cfg.alphaZ cfg.betaZ hR'.1 hR'.2.1 ?_ ?_ ?_ ?_ ⟨p₁, by simp, hpr.symm⟩
    · intro x hx
      rcases List.mem_append.mp hx with hx' | hx'
      · exact cfg.rdisj x hx'
      · rw [List.mem_singleton] at hx'
        exact hx' ▸ hp₁Z
    · intro x hx zz hzz
      have hzzZ : zz ∈ Z := List.mem_of_mem_drop hzz
      rcases List.mem_append.mp hx with hx' | hx'
      · exact cfg.rcross x hx' zz hzzZ
      · rw [List.mem_singleton] at hx'
        subst hx'
        constructor
        · intro hadj
          exact absurd (hunique zz (cfg.subK zz hzzZ) hadj ▸ hzz) hrnot
        · rintro ⟨hh, -⟩
          exact absurd hh hp₁t
    · refine ⟨1, le_refl 1, cfg.jpos, Z[1]'(by omega), List.getElem?_eq_getElem (by omega), ?_⟩
      have hmod : (0 + 1) % Z.length = 1 := Nat.mod_eq_of_lt (by omega)
      have := (hZadj 0 1 (by omega) (by omega)).mpr (Or.inl hmod.symm)
      rwa [hr0] at this
    · refine ⟨Z.length - 1, by omega, by omega, Z[Z.length - 1]'(by omega),
        List.getElem?_eq_getElem (by omega), ?_⟩
      have hmod : ((Z.length - 1) + 1) % Z.length = 0 := by
        have hh : (Z.length - 1) + 1 = Z.length := by omega
        rw [hh, Nat.mod_self]
      have := (hZadj 0 (Z.length - 1) (by omega) (by omega)).mpr (Or.inr hmod.symm)
      rwa [hr0] at this
  -- `r` sees at most one vertex of the triangle
  have hαK : α ∈ K := star_subset_K h u cfg.alphaN
  have hβK : β ∈ K := star_subset_K h u cfg.betaN
  have hαZ : α ∈ Z := by
    obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp cfg.alphaZ
    exact hh ▸ List.getElem_mem hlt
  have hβZ : β ∈ Z := by
    obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp cfg.betaZ
    exact hh ▸ List.getElem_mem hlt
  have htZ : t ∉ Z := cfg.rdisj t (PathBasics.head_mem cfg.rhead)
  have hαβ : α ≠ β := by
    intro hh
    have := hinj j (j + 1) α cfg.alphaZ (hh ▸ cfg.betaZ)
    omega
  have hαt : α ≠ t := fun hh => htZ (hh ▸ hαZ)
  have hβt : β ≠ t := fun hh => htZ (hh ▸ hβZ)
  have hval := symm_val (φ := φ) hrK
  have hune : u ∉ (φ.symm ⟨r, hrK⟩).1 := hinternal u cfg.ubranch
  have hpair : ∀ x y : V, x ∈ N u → y ∈ N u → x ≠ y → ¬ (G.Adj r x ∧ G.Adj r y) := by
    rintro x y hx hy hxy ⟨h1, h2⟩
    refine no_two_star_neighbors h.2.2.1.2 h.2.2.2.1 hx hy hxy
      (φ.symm ⟨r, hrK⟩).2 hune ?_ ?_
    · rwa [show (↑(φ ⟨(φ.symm ⟨r, hrK⟩).1, (φ.symm ⟨r, hrK⟩).2⟩) : V) = r from hval]
    · rwa [show (↑(φ ⟨(φ.symm ⟨r, hrK⟩).1, (φ.symm ⟨r, hrK⟩).2⟩) : V) = r from hval]
  exact absurd_of_link h.1 hlink (hpair α β cfg.alphaN cfg.betaN hαβ)
    (hpair α t cfg.alphaN cfg.tN hαt) (hpair β t cfg.betaN cfg.tN hβt)


/-- PAPER (5.8 (7), printed p. 28): *"If `p₁` has two nonadjacent neighbours in
`R_{u₁v₁}`, then `p₁` can be linked onto `T`, again a contradiction."* -/
theorem nonadjacent_neighbors_absurd
    (h : Thm58Setup.Ready G m J n H K φ N F P p₁ p₂)
    {q₁ q₂ : List (Fin n)} (hq₁ : IsBranch H q₁) (hq₂ : IsBranch H q₂)
    (hX₁ : edgeAttachments φ (F \ {p₂}) ⊆ trackEdges q₁)
    (hX₂ : edgeAttachments φ (F \ {p₁}) ⊆ trackEdges q₂)
    {a b : V} (haK : a ∈ K) (hbK : b ∈ K)
    (hpa : G.Adj p₁ a) (hpb : G.Adj p₁ b) (hab : a ≠ b) (hnadj : ¬ G.Adj a b) : False := by
  classical
  have haq := edge_mem_trackEdges_of_adj h hX₁ haK hpa
  have hbq := edge_mem_trackEdges_of_adj h hX₁ hbK hpb
  obtain ⟨Z, R, j, α, β, t, u, cfg, i, k, hi1, hi2, hk1, hk2, hik⟩ :=
    cycle_config_separating h hq₁ hq₂ hX₁ hX₂ haK hbK haq hbq hab hnadj
  obtain ⟨h4, hnd, hZadj⟩ := cfg.hole
  have hinj : ∀ (c d : ℕ) (x : V), Z[c]? = some x → Z[d]? = some x → c = d := by
    intro c d x hx hy
    obtain ⟨hc, hxc⟩ := List.getElem?_eq_some_iff.mp hx
    obtain ⟨hd, hxd⟩ := List.getElem?_eq_some_iff.mp hy
    exact hnd.getElem_inj_iff.mp (hxc.trans hxd.symm)
  obtain ⟨z, hzlast, hzadj⟩ := cfg.plast
  have hzR : z ∈ R := PathBasics.getLast_mem hzlast
  have hlink : VertexCanBeLinkedOntoTriangle G p₁ α β t := by
    refine Thm58BranchBranchCut.link_of_hole_cut ⟨h4, hnd, hZadj⟩ cfg.jpos cfg.jlt
      cfg.alphaZ cfg.betaZ cfg.rpath cfg.rhead cfg.rdisj ?_ ?_ ?_
      ⟨z, hzR, (hzadj z hzR).mpr rfl⟩
    · intro x hx zz hzz
      exact cfg.rcross x hx zz (List.mem_of_mem_drop hzz)
    · rcases hik with ⟨hA, -⟩ | ⟨hA, -⟩
      · exact ⟨i, hi1, hi2, a, hA, hpa⟩
      · exact ⟨i, hi1, hi2, b, hA, hpb⟩
    · rcases hik with ⟨-, hB⟩ | ⟨-, hB⟩
      · exact ⟨k, hk1, hk2, b, hB, hpb⟩
      · exact ⟨k, hk1, hk2, a, hB, hpa⟩
  have hαZ : α ∈ Z := by
    obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp cfg.alphaZ
    exact hh ▸ List.getElem_mem hlt
  have hβZ : β ∈ Z := by
    obtain ⟨hlt, hh⟩ := List.getElem?_eq_some_iff.mp cfg.betaZ
    exact hh ▸ List.getElem_mem hlt
  have htZ : t ∉ Z := cfg.rdisj t (PathBasics.head_mem cfg.rhead)
  have hαβ : α ≠ β := by
    intro hh
    have := hinj j (j + 1) α cfg.alphaZ (hh ▸ cfg.betaZ)
    omega
  have hαt : α ≠ t := fun hh => htZ (hh ▸ hαZ)
  have hβt : β ≠ t := fun hh => htZ (hh ▸ hβZ)
  have hpair : ∀ x y : V, x ∈ N u → y ∈ N u → x ≠ y → ¬ (G.Adj p₁ x ∧ G.Adj p₁ y) := by
    rintro x y hx hy hxy ⟨h1, h2⟩
    have hxK := star_subset_K h u hx
    have hyK := star_subset_K h u hy
    exact no_two_star_edges_on_branch hq₁ cfg.ubranch
      (edge_mem_trackEdges_of_adj h hX₁ hxK h1) (edge_mem_trackEdges_of_adj h hX₁ hyK h2)
      (symm_edge_ne hxK hyK hxy) (star_edge h hx hxK) (star_edge h hy hyK)
  exact absurd_of_link h.1 hlink (hpair α β cfg.alphaN cfg.betaN hαβ)
    (hpair α t cfg.alphaN cfg.tN hαt) (hpair β t cfg.betaN cfg.tN hβt)

end Workspace.ProofLemmas.Thm58BranchBranchLinkSteps
