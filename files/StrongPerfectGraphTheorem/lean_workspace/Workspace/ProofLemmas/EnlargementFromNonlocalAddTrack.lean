import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm101ThetaAddBranch

/-!
# Adding a track at two arbitrary stars of a line graph

This is the graph construction used in the unproved sentence after outcome 1 of 5.8.  It is
the arbitrary-degree version of `Thm101ThetaAddBranch`: the new path attaches to all old
edges incident with either of its two ends, rather than to two edges at each end.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
variable {V W : Type*}

/-- A graph obtained by adding one new track between two old vertices. -/
structure IsBranchExtension {W Z : Type*} (H : SimpleGraph W) (c₁ c₂ : W)
    (D : SimpleGraph Z) (rho : W → Z) (q : List Z) : Prop where
  inj : Function.Injective rho
  oldAdj : ∀ x y, H.Adj x y → D.Adj (rho x) (rho y)
  track : IsTrackFrom D q (rho c₁) (rho c₂)
  length : 2 ≤ q.length
  newInterior : ∀ x ∈ trackInterior q, x ∉ Set.range rho
  cover : ∀ x, x ∈ Set.range rho ∨ x ∈ trackInterior q
  edges : D.edgeSet = Sym2.map rho '' H.edgeSet ∪ trackEdges q

private theorem getElem_idx_eq {A : Type*} (q : List A) {i j : ℕ}
    (hij : i = j) (hi : i < q.length) (hj : j < q.length) :
    q[i]'hi = q[j]'hj := by
  subst j
  rfl

private def edgeAt (q : List W) (i : Fin (q.length - 1)) : Sym2 W :=
  s(q[i.val]'(by have := i.isLt; omega), q[i.val + 1]'(by have := i.isLt; omega))

private theorem edgeAt_injective (q : List W) (hnd : q.Nodup) :
    Function.Injective (edgeAt q) := by
  intro i j hij
  dsimp [edgeAt] at hij
  rcases Sym2.eq_iff.mp hij with ⟨h1, -⟩ | ⟨h1, h2⟩
  · exact Fin.val_injective (hnd.getElem_inj_iff.mp h1)
  · have h1' := hnd.getElem_inj_iff.mp h1
    have h2' := hnd.getElem_inj_iff.mp h2
    exact Fin.val_injective (by omega)

private theorem trackEdges_eq_range (q : List W) :
    trackEdges q = Set.range (edgeAt q) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by have := i.isLt; omega, rfl⟩

private theorem trackEdges_disjoint_diag (q : List W) (hnd : q.Nodup) :
    Disjoint (trackEdges q) (@Sym2.diagSet W) := by
  rw [Set.disjoint_left]
  intro e he hdiag
  obtain ⟨i, hi, rfl⟩ := he
  rw [Sym2.mem_diagSet_iff_eq] at hdiag
  exact (by omega : i ≠ i + 1) (hnd.getElem_inj_iff.mp hdiag)

private theorem trackEdges_map {A B : Type*} (g : A → B) (q : List A) :
    trackEdges (q.map g) = Sym2.map g '' trackEdges q := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hi' : i + 1 < q.length := by simpa using hi
    refine ⟨s(q[i]'(by omega), q[i + 1]'hi'), ⟨i, hi', rfl⟩, ?_⟩
    simp [Sym2.map_pair_eq]
  · rintro ⟨e, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, by simpa using hi, ?_⟩
    simp [Sym2.map_pair_eq]

section NewTrack

variable (W)

private def newTrack (l : ℕ) (c₁ c₂ : W) : List (W ⊕ Fin (l - 1)) :=
  Sum.inl c₁ :: (List.ofFn (fun i : Fin (l - 1) => Sum.inr i) ++ [Sum.inl c₂])

private theorem newTrack_length (l : ℕ) (c₁ c₂ : W) (hl : 0 < l) :
    (newTrack W l c₁ c₂).length = l + 1 := by
  simp [newTrack]
  omega

private theorem newTrack_nodup (l : ℕ) (c₁ c₂ : W) (hc : c₁ ≠ c₂) :
    (newTrack W l c₁ c₂).Nodup := by
  unfold newTrack
  rw [List.nodup_cons]
  constructor
  · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    rintro (⟨i, hi⟩ | h)
    · simp at hi
    · exact hc (Sum.inl_injective h)
  · rw [List.nodup_append]
    refine ⟨List.nodup_ofFn.mpr Sum.inr_injective, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have hy' : y = Sum.inl c₂ := List.mem_singleton.mp hy
    subst y
    exact Sum.inr_ne_inl

private theorem newTrack_interior (l : ℕ) (c₁ c₂ : W) :
    trackInterior (newTrack W l c₁ c₂) =
      List.ofFn (fun i : Fin (l - 1) => Sum.inr i) := by
  simp [newTrack, trackInterior]

private theorem newTrack_cover (l : ℕ) (c₁ c₂ : W) (v : W ⊕ Fin (l - 1)) :
    v ∈ Set.range (@Sum.inl W (Fin (l - 1))) ∨ v ∈ trackInterior (newTrack W l c₁ c₂) := by
  cases v with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr i =>
      right
      rw [newTrack_interior]
      simp

private theorem old_mem_newEdge_iff (l : ℕ) (c₁ c₂ c : W) (hl : 0 < l)
    (i : ℕ) (hi : i + 1 < (newTrack W l c₁ c₂).length) :
    Sum.inl c ∈ s((newTrack W l c₁ c₂)[i]'(by omega),
      (newTrack W l c₁ c₂)[i + 1]'hi) ↔
      (i = 0 ∧ c = c₁) ∨ (i + 1 = l ∧ c = c₂) := by
  have hlen := newTrack_length W l c₁ c₂ hl
  rw [Sym2.mem_iff]
  by_cases hi0 : i = 0
  · subst i
    simp only [newTrack, List.getElem_cons_zero]
    by_cases hl1 : l = 1
    · subst l
      simp
    · have hpos : 0 < l - 1 := by omega
      have hget :
          (List.ofFn (fun j : Fin (l - 1) => Sum.inr j) ++ [Sum.inl c₂])[0]
            = Sum.inr (⟨0, hpos⟩ : Fin (l - 1)) := by
        rw [List.getElem_append_left (by simp; omega)]
        simp
      rw [List.getElem_cons_succ, hget]
      simp
      omega
  · have hipos : 0 < i := by omega
    have hiInt : i < l := by omega
    have hgeti : (newTrack W l c₁ c₂)[i]'(by omega) =
        Sum.inr (⟨i - 1, by omega⟩ : Fin (l - 1)) := by
      unfold newTrack
      rw [List.getElem_cons]
      split
      · omega
      · rw [List.getElem_append_left (by simp; omega)]
        simp
    rw [hgeti]
    by_cases hilast : i + 1 = l
    · have hlast : (newTrack W l c₁ c₂)[i + 1]'hi = Sum.inl c₂ := by
        have hlast' : (newTrack W l c₁ c₂)[l]'(by omega) = Sum.inl c₂ := by
          unfold newTrack
          rw [List.getElem_cons]
          split
          · omega
          · apply List.getElem_concat_length
            simp
        exact (getElem_idx_eq (newTrack W l c₁ c₂) hilast hi (by omega)).trans hlast'
      rw [hlast]
      simp [hi0, hilast]
    · have hnext : i + 1 < l := by omega
      have hgetnext : (newTrack W l c₁ c₂)[i + 1]'hi =
          Sum.inr (⟨i, by omega⟩ : Fin (l - 1)) := by
        unfold newTrack
        rw [List.getElem_cons]
        split
        · omega
        · rw [List.getElem_append_left (by simp; omega)]
          simp
      rw [hgetnext]
      simp [hi0, hilast]

end NewTrack

private theorem old_ne_newEdge (l : ℕ) (H : SimpleGraph W) (c₁ c₂ : W)
    (hl : 0 < l) (hnadj : ¬ H.Adj c₁ c₂) (e : H.edgeSet) (i : Fin l) :
    Sym2.map (@Sum.inl W (Fin (l - 1))) (e : Sym2 W) ≠
      edgeAt (newTrack W l c₁ c₂)
        (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
      intro heq
      have hx : Sum.inl x ∈ edgeAt (newTrack W l c₁ c₂)
          (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i) := by
        rw [← heq]
        exact Sym2.mem_map.mpr ⟨x, Sym2.mem_mk_left _ _, rfl⟩
      have hy : Sum.inl y ∈ edgeAt (newTrack W l c₁ c₂)
          (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i) := by
        rw [← heq]
        exact Sym2.mem_map.mpr ⟨y, Sym2.mem_mk_right _ _, rfl⟩
      have hx' := (old_mem_newEdge_iff W l c₁ c₂ x hl i.val (by
        rw [newTrack_length W l c₁ c₂ hl]; omega)).mp hx
      have hy' := (old_mem_newEdge_iff W l c₁ c₂ y hl i.val (by
        rw [newTrack_length W l c₁ c₂ hl]; omega)).mp hy
      rcases hx' with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> rcases hy' with ⟨-, rfl⟩ | ⟨-, rfl⟩
      · exact he.ne rfl
      · exact hnadj he
      · exact hnadj he.symm
      · exact he.ne rfl

private theorem lineGraph_old_old (H : SimpleGraph W)
    (D : SimpleGraph (W ⊕ Fin 0)) (r : W → W ⊕ Fin 0) (hr : Function.Injective r)
    (hold : ∀ e : H.edgeSet, Sym2.map r (e : Sym2 W) ∈ D.edgeSet)
    (e f : H.edgeSet) :
    D.lineGraph.Adj ⟨Sym2.map r (e : Sym2 W), hold e⟩
        ⟨Sym2.map r (f : Sym2 W), hold f⟩ ↔ H.lineGraph.Adj e f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hve, hvf⟩
    refine ⟨?_, ?_⟩
    · intro hef
      apply hne
      apply Subtype.ext
      rw [hef]
    · obtain ⟨a, hae, hav⟩ := Sym2.mem_map.mp hve
      obtain ⟨b, hbf, hbv⟩ := Sym2.mem_map.mp hvf
      have hab : a = b := hr (hav.trans hbv.symm)
      subst b
      exact ⟨a, hae, hbf⟩
  · rintro ⟨hne, a, hae, haf⟩
    refine ⟨?_, r a, Sym2.mem_map.mpr ⟨a, hae, rfl⟩,
      Sym2.mem_map.mpr ⟨a, haf, rfl⟩⟩
    intro hef
    apply hne
    apply Subtype.ext
    exact Sym2.map.injective hr (congrArg Subtype.val hef)

private theorem lineGraph_old_old' {Z : Type*} (H : SimpleGraph W)
    (D : SimpleGraph Z) (r : W → Z) (hr : Function.Injective r)
    (hold : ∀ e : H.edgeSet, Sym2.map r (e : Sym2 W) ∈ D.edgeSet)
    (e f : H.edgeSet) :
    D.lineGraph.Adj ⟨Sym2.map r (e : Sym2 W), hold e⟩
        ⟨Sym2.map r (f : Sym2 W), hold f⟩ ↔ H.lineGraph.Adj e f := by
  rw [SimpleGraph.lineGraph_adj_iff_exists, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hve, hvf⟩
    refine ⟨?_, ?_⟩
    · intro hef
      apply hne
      apply Subtype.ext
      rw [hef]
    · obtain ⟨a, hae, hav⟩ := Sym2.mem_map.mp hve
      obtain ⟨b, hbf, hbv⟩ := Sym2.mem_map.mp hvf
      have hab : a = b := hr (hav.trans hbv.symm)
      subst b
      exact ⟨a, hae, hbf⟩
  · rintro ⟨hne, a, hae, haf⟩
    refine ⟨?_, r a, Sym2.mem_map.mpr ⟨a, hae, rfl⟩,
      Sym2.mem_map.mpr ⟨a, haf, rfl⟩⟩
    intro hef
    apply hne
    apply Subtype.ext
    exact Sym2.map.injective hr (congrArg Subtype.val hef)

private theorem lineGraph_new_new (D : SimpleGraph W) (q : List W) (hnd : q.Nodup)
    (hedge : ∀ i : Fin (q.length - 1), edgeAt q i ∈ D.edgeSet)
    (i j : Fin (q.length - 1)) :
    D.lineGraph.Adj ⟨edgeAt q i, hedge i⟩ ⟨edgeAt q j, hedge j⟩ ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hvi, hvj⟩
    dsimp [edgeAt] at hvi hvj
    rcases Sym2.mem_iff.mp hvi with hvi | hvi <;> rcases Sym2.mem_iff.mp hvj with hvj | hvj
    · have hidx := hnd.getElem_inj_iff.mp (hvi.symm.trans hvj)
      have hij : i = j := Fin.val_injective hidx
      subst j
      exact (hne rfl).elim
    · exact Or.inr (hnd.getElem_inj_iff.mp (hvj.symm.trans hvi))
    · exact Or.inl (hnd.getElem_inj_iff.mp (hvi.symm.trans hvj))
    · have hidx := hnd.getElem_inj_iff.mp (hvi.symm.trans hvj)
      have hij : i = j := Fin.val_injective (by omega)
      subst j
      exact (hne rfl).elim
  · intro hij
    have hne : (⟨edgeAt q i, hedge i⟩ : D.edgeSet) ≠ ⟨edgeAt q j, hedge j⟩ := by
      intro h
      have hv : edgeAt q i = edgeAt q j := congrArg Subtype.val h
      have heq := edgeAt_injective q hnd hv
      have := congrArg Fin.val heq
      omega
    rcases hij with hij | hij
    · refine ⟨hne, q[i.val + 1]'(by have := i.isLt; omega), Sym2.mem_mk_right _ _, ?_⟩
      dsimp [edgeAt]
      exact Sym2.mem_iff.mpr (Or.inl (hnd.getElem_inj_iff.mpr hij))
    · refine ⟨hne, q[j.val + 1]'(by have := j.isLt; omega), ?_, Sym2.mem_mk_right _ _⟩
      dsimp [edgeAt]
      exact Sym2.mem_iff.mpr (Or.inl (hnd.getElem_inj_iff.mpr hij))

private theorem lineGraph_old_new (l : ℕ) (H : SimpleGraph W) (c₁ c₂ : W)
    (hl : 0 < l) (hnadj : ¬ H.Adj c₁ c₂)
    (D : SimpleGraph (W ⊕ Fin (l - 1)))
    (hold : ∀ e : H.edgeSet,
      Sym2.map (@Sum.inl W (Fin (l - 1))) (e : Sym2 W) ∈ D.edgeSet)
    (hnew : ∀ i : Fin l, edgeAt (newTrack W l c₁ c₂)
      (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i) ∈ D.edgeSet)
    (e : H.edgeSet) (i : Fin l) :
    D.lineGraph.Adj
        ⟨Sym2.map (@Sum.inl W (Fin (l - 1))) (e : Sym2 W), hold e⟩
        ⟨edgeAt (newTrack W l c₁ c₂)
          (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i), hnew i⟩ ↔
      (i.val = 0 ∧ c₁ ∈ (e : Sym2 W)) ∨ (i.val + 1 = l ∧ c₂ ∈ (e : Sym2 W)) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨-, v, hvold, hvnew⟩
    obtain ⟨c, hce, hcv⟩ := Sym2.mem_map.mp hvold
    have hcnew : Sum.inl c ∈ edgeAt (newTrack W l c₁ c₂)
        (Fin.cast (by rw [newTrack_length W l c₁ c₂ hl]; omega) i) := by
      rwa [hcv]
    rcases (old_mem_newEdge_iff W l c₁ c₂ c hl i.val (by
      rw [newTrack_length W l c₁ c₂ hl]; omega)).mp hcnew with h | h
    · exact Or.inl ⟨h.1, by rw [← h.2]; exact hce⟩
    · exact Or.inr ⟨h.1, by rw [← h.2]; exact hce⟩
  · intro h
    refine ⟨fun heq => old_ne_newEdge l H c₁ c₂ hl hnadj e i
      (congrArg Subtype.val heq), ?_⟩
    rcases h with ⟨hi, hc⟩ | ⟨hi, hc⟩
    · refine ⟨Sum.inl c₁, Sym2.mem_map.mpr ⟨c₁, hc, rfl⟩, ?_⟩
      exact (old_mem_newEdge_iff W l c₁ c₂ c₁ hl i.val (by
        rw [newTrack_length W l c₁ c₂ hl]; omega)).mpr (Or.inl ⟨hi, rfl⟩)
    · refine ⟨Sum.inl c₂, Sym2.mem_map.mpr ⟨c₂, hc, rfl⟩, ?_⟩
      exact (old_mem_newEdge_iff W l c₁ c₂ c₂ hl i.val (by
        rw [newTrack_length W l c₁ c₂ hl]; omega)).mpr (Or.inr ⟨hi, rfl⟩)

/-- The canonical host extension and its line-graph isomorphism. -/
theorem addTrack {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (phi : H.lineGraph ≃g G.induce K)
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂)
    (hPK : ∀ x ∈ P, x ∉ K) (c₁ c₂ : W) (hc : c₁ ≠ c₂)
    (hnadj : ¬ H.Adj c₁ c₂)
    (h₁ : ∀ (e : Sym2 W) (he : e ∈ H.edgeSet), c₁ ∈ e →
      G.Adj p₁ (↑(phi ⟨e, he⟩) : V))
    (h₂ : ∀ (e : Sym2 W) (he : e ∈ H.edgeSet), c₂ ∈ e →
      G.Adj p₂ (↑(phi ⟨e, he⟩) : V))
    (hno : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ ∃ (e : Sym2 W) (he : e ∈ H.edgeSet), c₁ ∈ e ∧
        y = (↑(phi ⟨e, he⟩) : V)) ∨
      (x = p₂ ∧ ∃ (e : Sym2 W) (he : e ∈ H.edgeSet), c₂ ∈ e ∧
        y = (↑(phi ⟨e, he⟩) : V))) :
    ∃ (D : SimpleGraph (W ⊕ Fin (P.length - 1)))
      (q : List (W ⊕ Fin (P.length - 1)))
      (_psi : D.lineGraph ≃g G.induce (K ∪ {x : V | x ∈ P})),
      IsBranchExtension H c₁ c₂ D Sum.inl q ∧ q.length = P.length + 1 := by
  classical
  have hl : 0 < P.length := List.length_pos_of_ne_nil hP.1.1
  let q := newTrack W P.length c₁ c₂
  have hqlen : q.length = P.length + 1 := newTrack_length W P.length c₁ c₂ hl
  have hqedgeLen : q.length - 1 = P.length := by omega
  have hqnd : q.Nodup := newTrack_nodup W P.length c₁ c₂ hc
  let oldEmb : W ↪ (W ⊕ Fin (P.length - 1)) := Function.Embedding.inl
  let D : SimpleGraph (W ⊕ Fin (P.length - 1)) :=
    H.map oldEmb ⊔ SimpleGraph.fromEdgeSet (trackEdges q)
  have htrackEdgeSet : (SimpleGraph.fromEdgeSet (trackEdges q)).edgeSet = trackEdges q := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact sdiff_eq_left.mpr (trackEdges_disjoint_diag q hqnd)
  have hDedges : D.edgeSet =
      Sym2.map (@Sum.inl W (Fin (P.length - 1))) '' H.edgeSet ∪ trackEdges q := by
    simp only [D, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map, htrackEdgeSet]
    rfl
  have hold : ∀ e : H.edgeSet,
      Sym2.map (@Sum.inl W (Fin (P.length - 1))) (e : Sym2 W) ∈ D.edgeSet := by
    intro e
    rw [hDedges]
    exact Or.inl ⟨e, e.property, rfl⟩
  have hnew : ∀ i : Fin P.length,
      edgeAt q (Fin.cast hqedgeLen.symm i) ∈ D.edgeSet := by
    intro i
    rw [hDedges]
    right
    rw [trackEdges_eq_range]
    exact ⟨Fin.cast hqedgeLen.symm i, rfl⟩
  let edgeEmb : H.edgeSet ⊕ Fin P.length → D.edgeSet
    | Sum.inl e => ⟨Sym2.map (@Sum.inl W (Fin (P.length - 1))) (e : Sym2 W), hold e⟩
    | Sum.inr i => ⟨edgeAt q (Fin.cast hqedgeLen.symm i), hnew i⟩
  have hedgeEmb_inj : Function.Injective edgeEmb := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl f =>
        have hv := congrArg Subtype.val hab
        have hef : e = f := Subtype.ext (Sym2.map.injective Sum.inl_injective hv)
        simp [hef]
      | inr i =>
        have hv := congrArg Subtype.val hab
        exact (old_ne_newEdge P.length H c₁ c₂ hl hnadj e i
          (by simpa [edgeEmb, q] using hv)).elim
    | inr i =>
      cases b with
      | inl e =>
        have hv := congrArg Subtype.val hab
        exact (old_ne_newEdge P.length H c₁ c₂ hl hnadj e i
          (by simpa [edgeEmb, q] using hv.symm)).elim
      | inr j =>
        have hv := congrArg Subtype.val hab
        have hc' : Fin.cast hqedgeLen.symm i = Fin.cast hqedgeLen.symm j :=
          edgeAt_injective q hqnd (by simpa [edgeEmb] using hv)
        have hij : i = j := by
          apply Fin.ext
          simpa using congrArg Fin.val hc'
        simp [hij]
  have hedgeEmb_surj : Function.Surjective edgeEmb := by
    intro e
    have he : (e : Sym2 (W ⊕ Fin (P.length - 1))) ∈
        Sym2.map (@Sum.inl W (Fin (P.length - 1))) '' H.edgeSet ∪ trackEdges q := by
      rw [← hDedges]
      exact e.property
    rcases he with ⟨e₀, he₀, hval⟩ | he
    · let a : H.edgeSet := ⟨e₀, he₀⟩
      refine ⟨Sum.inl a, ?_⟩
      apply Subtype.ext
      simpa [edgeEmb, a] using hval
    · rw [trackEdges_eq_range] at he
      obtain ⟨j, hj⟩ := he
      let i : Fin P.length := Fin.cast hqedgeLen j
      refine ⟨Sum.inr i, ?_⟩
      apply Subtype.ext
      have hji : Fin.cast hqedgeLen.symm i = j := by apply Fin.ext; rfl
      simpa [edgeEmb, i, hji] using hj
  let edgeEquiv : (H.edgeSet ⊕ Fin P.length) ≃ D.edgeSet :=
    Equiv.ofBijective edgeEmb ⟨hedgeEmb_inj, hedgeEmb_surj⟩
  let target : Set V := K ∪ {x : V | x ∈ P}
  let vertexEmb : H.edgeSet ⊕ Fin P.length → target
    | Sum.inl e => ⟨(↑(phi e) : V), Or.inl (phi e).property⟩
    | Sum.inr i => ⟨P[i.val], Or.inr (List.getElem_mem _)⟩
  have hvertexEmb_inj : Function.Injective vertexEmb := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl f =>
        have hv : (↑(phi e) : V) = (↑(phi f) : V) := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have : e = f := phi.injective (Subtype.ext hv)
        simp [this]
      | inr i =>
        have hv : (↑(phi e) : V) = P[i.val] := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        exact (hPK P[i.val] (List.getElem_mem _) (by rw [← hv]; exact (phi e).property)).elim
    | inr i =>
      cases b with
      | inl e =>
        have hv : P[i.val] = (↑(phi e) : V) := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        exact (hPK P[i.val] (List.getElem_mem _) (by rw [hv]; exact (phi e).property)).elim
      | inr j =>
        have hv : P[i.val] = P[j.val] := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have hij : i.val = j.val := hP.1.2.1.getElem_inj_iff.mp hv
        simp [Fin.ext hij]
  have hvertexEmb_surj : Function.Surjective vertexEmb := by
    rintro ⟨x, hx⟩
    rcases hx with hxK | hxP
    · obtain ⟨e, he⟩ := phi.surjective ⟨x, hxK⟩
      refine ⟨Sum.inl e, ?_⟩
      apply Subtype.ext
      simpa [vertexEmb] using congrArg Subtype.val he
    · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxP
      refine ⟨Sum.inr ⟨i, hi⟩, ?_⟩
      exact Subtype.ext hix
  let vertexEquiv : (H.edgeSet ⊕ Fin P.length) ≃ target :=
    Equiv.ofBijective vertexEmb ⟨hvertexEmb_inj, hvertexEmb_surj⟩
  have htarget : ∀ (e : H.edgeSet) (i : Fin P.length),
      G.Adj P[i.val] (↑(phi e) : V) ↔
        (i.val = 0 ∧ c₁ ∈ (e : Sym2 W)) ∨
        (i.val + 1 = P.length ∧ c₂ ∈ (e : Sym2 W)) := by
    intro e i
    have hP0 : P[0]'hl = p₁ := by
      have h := hP.2.1
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hl] at h
      exact Option.some_injective _ h
    have hPL : P[P.length - 1]'(by omega) = p₂ := by
      have h := hP.2.2
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h
      exact Option.some_injective _ h
    constructor
    · intro hadj
      rcases hno P[i.val] (List.getElem_mem _) (↑(phi e) : V) (phi e).property hadj with h | h
      · left
        refine ⟨?_, ?_⟩
        · exact hP.1.2.1.getElem_inj_iff.mp (h.1.trans hP0.symm)
        · obtain ⟨f, hf, hcf, hval⟩ := h.2
          have heq : f = (e : Sym2 W) := by
            have hef : e = (⟨f, hf⟩ : H.edgeSet) :=
              phi.injective (Subtype.ext hval)
            exact (congrArg Subtype.val hef).symm
          rwa [← heq]
      · right
        refine ⟨?_, ?_⟩
        · have hii : i.val = P.length - 1 :=
            hP.1.2.1.getElem_inj_iff.mp (h.1.trans hPL.symm)
          omega
        · obtain ⟨f, hf, hcf, hval⟩ := h.2
          have heq : f = (e : Sym2 W) := by
            have hef : e = (⟨f, hf⟩ : H.edgeSet) :=
              phi.injective (Subtype.ext hval)
            exact (congrArg Subtype.val hef).symm
          rwa [← heq]
    · rintro (⟨hi, hc₁e⟩ | ⟨hi, hc₂e⟩)
      · have hpi : P[i.val] = p₁ := (hP.1.2.1.getElem_inj_iff.mpr hi).trans hP0
        rw [hpi]
        exact h₁ e e.property hc₁e
      · have hil : i.val = P.length - 1 := by omega
        have hpi : P[i.val] = p₂ := (hP.1.2.1.getElem_inj_iff.mpr hil).trans hPL
        rw [hpi]
        exact h₂ e e.property hc₂e
  have hrel : ∀ a b : H.edgeSet ⊕ Fin P.length,
      D.lineGraph.Adj (edgeEmb a) (edgeEmb b) ↔
        (G.induce target).Adj (vertexEmb a) (vertexEmb b) := by
    intro a b
    cases a with
    | inl e =>
      cases b with
      | inl f =>
        exact (lineGraph_old_old' H D _ Sum.inl_injective hold e f).trans phi.map_adj_iff.symm
      | inr i =>
        change D.lineGraph.Adj _ _ ↔ G.Adj (↑(phi e) : V) P[i.val]
        rw [G.adj_comm]
        exact (lineGraph_old_new P.length H c₁ c₂ hl hnadj D hold hnew e i).trans
          (htarget e i).symm
    | inr i =>
      cases b with
      | inl e =>
        rw [D.lineGraph.adj_comm]
        exact (lineGraph_old_new P.length H c₁ c₂ hl hnadj D hold hnew e i).trans
          (htarget e i).symm
      | inr j =>
        have ht := lineGraph_new_new D q hqnd (fun k => by
          rw [hDedges]
          right
          rw [trackEdges_eq_range]
          exact ⟨k, rfl⟩) (Fin.cast hqedgeLen.symm i) (Fin.cast hqedgeLen.symm j)
        exact ht.trans (hP.1.2.2 i.val j.val i.isLt j.isLt).symm
  let psi : D.lineGraph ≃g G.induce target :=
    { toEquiv := edgeEquiv.symm.trans vertexEquiv
      map_rel_iff' := by
        intro e f
        have hr := (hrel (edgeEquiv.symm e) (edgeEquiv.symm f)).symm
        have he : edgeEmb (edgeEquiv.symm e) = e := edgeEquiv.apply_symm_apply e
        have hf : edgeEmb (edgeEquiv.symm f) = f := edgeEquiv.apply_symm_apply f
        simpa only [he, hf] using hr }
  refine ⟨D, q, ?_, ?_, hqlen⟩
  · simpa [target] using psi
  · refine ⟨Sum.inl_injective, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a b hab
      apply (SimpleGraph.mem_edgeSet D).mp
      rw [hDedges]
      left
      refine ⟨s(a, b), hab, ?_⟩
      simp
    · refine ⟨⟨?_, hqnd, ?_⟩, ?_, ?_⟩
      · simpa [q, newTrack]
      · intro i hi
        apply (SimpleGraph.mem_edgeSet _).mp
        rw [hDedges]
        right
        exact ⟨i, hi, rfl⟩
      · simp [q, newTrack]
      · change (newTrack W P.length c₁ c₂).getLast? = some (Sum.inl c₂)
        unfold newTrack
        rw [← List.cons_append]
        exact List.getLast?_concat
    · simp [q, trackLength, hqlen]
      omega
    · intro v hv
      rw [show trackInterior q = List.ofFn (fun i : Fin (P.length - 1) => Sum.inr i) by
        exact newTrack_interior W P.length c₁ c₂] at hv
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      rintro ⟨c, hc'⟩
      exact Sum.inl_ne_inr hc'
    · intro v
      exact newTrack_cover W P.length c₁ c₂ v
    · exact hDedges

end Workspace.ProofLemmas.EnlargementFromNonlocalAddTrack
