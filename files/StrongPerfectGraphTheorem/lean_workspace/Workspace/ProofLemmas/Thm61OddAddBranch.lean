import Workspace.ProofLemmas.Thm101ThetaAddBranch

/-! Adding the antipath as a branch in the complement construction of 6.1(7).
The finite track bookkeeping is the construction of `Thm101ThetaAddBranch`,
with arbitrary incident stars in place of its two-edge stars. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Workspace.ProofLemmas.Thm61OddAddBranch
open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.ThetaData

private theorem thetaP_length (m ℓ : ℕ) (z z' : Fin m) (hℓ : 0 < ℓ) :
    (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
      List (Fin m ⊕ Fin (ℓ - 1))).length = ℓ + 1 := by
  simp
  omega

private theorem thetaP_get_zero (m ℓ : ℕ) (z z' : Fin m) :
    (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
      List (Fin m ⊕ Fin (ℓ - 1)))[0]'(by simp) = Sum.inl z := by
  simp

private theorem thetaP_get_last (m ℓ : ℕ) (z z' : Fin m) (hℓ : 0 < ℓ) :
    (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
      List (Fin m ⊕ Fin (ℓ - 1)))[ℓ]'(by simp; omega) = Sum.inl z' := by
  simp only [List.getElem_cons, show ℓ ≠ 0 by omega]
  apply List.getElem_concat_length
  simp

private theorem thetaP_get_internal (m ℓ : ℕ) (z z' : Fin m) (i : ℕ)
    (hi0 : 0 < i) (hiℓ : i < ℓ) :
    (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
      List (Fin m ⊕ Fin (ℓ - 1)))[i]'(by simp; omega) =
      Sum.inr (⟨i - 1, by omega⟩ : Fin (ℓ - 1)) := by
  rw [List.getElem_cons]
  split
  · omega
  · rw [List.getElem_append_left (by simp; omega)]
    simp only [List.getElem_ofFn]

private theorem thetaP_old_mem_edge_iff (m ℓ : ℕ) (z z' c : Fin m) (hℓ : 0 < ℓ)
    (i : ℕ) (hi : i + 1 < ℓ + 1) :
    Sum.inl c ∈ s(
      (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
        List (Fin m ⊕ Fin (ℓ - 1)))[i]'(by simp; omega),
      (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
        List (Fin m ⊕ Fin (ℓ - 1)))[i + 1]'(by simp; omega)) ↔
      (i = 0 ∧ c = z) ∨ (i + 1 = ℓ ∧ c = z') := by
  rw [Sym2.mem_iff]
  by_cases hi0 : i = 0
  · subst i
    rw [thetaP_get_zero m ℓ z z']
    by_cases hℓ1 : ℓ = 1
    · subst ℓ
      rw [thetaP_get_last m 1 z z' (by omega)]
      simp
    · rw [thetaP_get_internal m ℓ z z' 1 (by omega) (by omega)]
      simp
      omega
  · have hii : 0 < i := by omega
    rw [thetaP_get_internal m ℓ z z' i hii (by omega)]
    by_cases hilast : i + 1 = ℓ
    · have hv := thetaP_get_last m ℓ z z' hℓ
      have hv' :
          (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
            List (Fin m ⊕ Fin (ℓ - 1)))[i + 1]'(by simp; omega) = Sum.inl z' := by
        subst ℓ
        exact hv
      rw [hv']
      simp [hi0, hilast]
    · rw [thetaP_get_internal m ℓ z z' (i + 1) (by omega) (by omega)]
      simp [hi0, hilast]

private theorem thetaP_nodup (m ℓ : ℕ) (z z' : Fin m) (hzz' : z ≠ z') :
    (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
      List (Fin m ⊕ Fin (ℓ - 1))).Nodup := by
  rw [List.nodup_cons]
  constructor
  · simp only [List.mem_append, List.mem_ofFn, List.mem_singleton]
    rintro (⟨i, hi⟩ | h)
    · simp at hi
    · exact hzz' (Sum.inl_injective h)
  · rw [List.nodup_append]
    refine ⟨List.nodup_ofFn.mpr Sum.inr_injective, by simp, ?_⟩
    intro x hx y hy
    simp only [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    have hy' : y = Sum.inl z' := List.mem_singleton.mp hy
    subst y
    exact Sum.inr_ne_inl

private theorem thetaP_interior (m ℓ : ℕ) (z z' : Fin m) :
    trackInterior
      (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
        List (Fin m ⊕ Fin (ℓ - 1))) =
      List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) := by
  simp [trackInterior]

private theorem thetaP_cover (m ℓ : ℕ) (z z' : Fin m) (v : Fin m ⊕ Fin (ℓ - 1)) :
    v ∈ Set.range (@Sum.inl (Fin m) (Fin (ℓ - 1))) ∨
      v ∈ trackInterior
        (Sum.inl z :: (List.ofFn (fun i : Fin (ℓ - 1) => Sum.inr i) ++ [Sum.inl z']) :
          List (Fin m ⊕ Fin (ℓ - 1))) := by
  cases v with
  | inl c => exact Or.inl ⟨c, rfl⟩
  | inr i =>
      right
      rw [thetaP_interior]
      simp

private def thetaEdgeAt {W : Type*} (q : List W) (i : Fin (q.length - 1)) : Sym2 W :=
  s(q[i.val]'(by have := i.isLt; omega), q[i.val + 1]'(by have := i.isLt; omega))

private theorem thetaEdgeAt_injective {W : Type*} (q : List W) (hnd : q.Nodup) :
    Function.Injective (thetaEdgeAt q) := by
  intro i j hij
  dsimp [thetaEdgeAt] at hij
  rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Fin.val_injective (hnd.getElem_inj_iff.mp h1)
  · have e1 := hnd.getElem_inj_iff.mp h1
    have e2 := hnd.getElem_inj_iff.mp h2
    exact Fin.val_injective (by omega)

private theorem thetaTrackEdges_eq_range {W : Type*} (q : List W) :
    trackEdges q = Set.range (thetaEdgeAt q) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, by have := i.isLt; omega, rfl⟩

private theorem thetaTrackEdges_disjoint_diag {W : Type*} (q : List W) (hnd : q.Nodup) :
    Disjoint (trackEdges q) (@Sym2.diagSet W) := by
  rw [Set.disjoint_left]
  intro e he hdiag
  obtain ⟨i, hi, rfl⟩ := he
  rw [Sym2.mem_diagSet_iff_eq] at hdiag
  exact (by omega : i ≠ i + 1) (hnd.getElem_inj_iff.mp hdiag)

private theorem thetaTrackEdges_map {A B : Type*} (g : A → B) (q : List A) :
    trackEdges (q.map g) = Sym2.map g '' trackEdges q := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨s(q[i]'(by simpa using Nat.lt_of_succ_lt hi), q[i + 1]'(by simpa using hi)),
      ⟨i, by simpa using hi, rfl⟩, ?_⟩
    simp [Sym2.map_pair_eq]
  · rintro ⟨e, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, by simpa using hi, ?_⟩
    simp [Sym2.map_pair_eq]

private theorem thetaOld_ne_edgeAt (m ℓ : ℕ) (Theta : SimpleGraph (Fin m)) (z z' : Fin m)
    (hℓ : 0 < ℓ) (hznadj : ¬ Theta.Adj z z') (e : Theta.edgeSet)
    (i : Fin ℓ) :
    Sym2.map (@Sum.inl (Fin m) (Fin (ℓ - 1))) (e : Sym2 (Fin m)) ≠
      thetaEdgeAt
        (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
          List (Fin m ⊕ Fin (ℓ - 1)))
        (Fin.cast (by simp; omega) i) := by
  rcases e with ⟨e, he⟩
  intro heq
  revert heq
  induction e using Sym2.ind with
  | _ x y =>
    intro heq
    have hxy : Theta.Adj x y := he
    have hxmem : Sum.inl x ∈
        thetaEdgeAt
          (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
            List (Fin m ⊕ Fin (ℓ - 1)))
          (Fin.cast (by simp; omega) i) := by
      rw [← heq]
      exact Sym2.mem_map.mpr ⟨x, Sym2.mem_mk_left _ _, rfl⟩
    have hymem : Sum.inl y ∈
        thetaEdgeAt
          (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
            List (Fin m ⊕ Fin (ℓ - 1)))
          (Fin.cast (by simp; omega) i) := by
      rw [← heq]
      exact Sym2.mem_map.mpr ⟨y, Sym2.mem_mk_right _ _, rfl⟩
    have hx := thetaP_old_mem_edge_iff m ℓ z z' x hℓ i.val (by omega) |>.mp hxmem
    have hy := thetaP_old_mem_edge_iff m ℓ z z' y hℓ i.val (by omega) |>.mp hymem
    rcases hx with ⟨hi0, hxz⟩ | ⟨hil, hxz'⟩ <;>
      rcases hy with ⟨hj0, hyz⟩ | ⟨hjl, hyz'⟩
    · exact hxy.ne (hxz.trans hyz.symm)
    · subst x; subst y; exact hznadj hxy
    · subst x; subst y; exact hznadj hxy.symm
    · exact hxy.ne (hxz'.trans hyz'.symm)

private theorem thetaLineGraph_edgeAt_adj_iff {W : Type*} (D : SimpleGraph W) (q : List W)
    (hnd : q.Nodup) (hedge : ∀ i : Fin (q.length - 1), thetaEdgeAt q i ∈ D.edgeSet)
    (i j : Fin (q.length - 1)) :
    D.lineGraph.Adj ⟨thetaEdgeAt q i, hedge i⟩ ⟨thetaEdgeAt q j, hedge j⟩ ↔
      (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hvi, hvj⟩
    dsimp [thetaEdgeAt] at hvi hvj
    rcases Sym2.mem_iff.mp hvi with hvi | hvi <;>
      rcases Sym2.mem_iff.mp hvj with hvj | hvj
    · have hidx := hnd.getElem_inj_iff.mp (hvi.symm.trans hvj)
      have hij : i = j := Fin.val_injective hidx
      subst j
      exact (hne rfl).elim
    · right
      exact hnd.getElem_inj_iff.mp (hvj.symm.trans hvi)
    · left
      exact hnd.getElem_inj_iff.mp (hvi.symm.trans hvj)
    · have hidx := hnd.getElem_inj_iff.mp (hvi.symm.trans hvj)
      have hijv : i.val = j.val := by omega
      have hij : i = j := Fin.val_injective hijv
      subst j
      exact (hne rfl).elim
  · intro hij
    have hne : (⟨thetaEdgeAt q i, hedge i⟩ : D.edgeSet) ≠
        ⟨thetaEdgeAt q j, hedge j⟩ := by
      intro h
      have hv : thetaEdgeAt q i = thetaEdgeAt q j := congrArg Subtype.val h
      have heq := thetaEdgeAt_injective q hnd hv
      have : i.val = j.val := congrArg Fin.val heq
      omega
    rcases hij with hij | hij
    · refine ⟨hne, q[i.val + 1]'(by have := i.isLt; omega), Sym2.mem_mk_right _ _, ?_⟩
      dsimp [thetaEdgeAt]
      apply Sym2.mem_iff.mpr
      left
      exact hnd.getElem_inj_iff.mpr hij
    · refine ⟨hne, q[j.val + 1]'(by have := j.isLt; omega), ?_, Sym2.mem_mk_right _ _⟩
      dsimp [thetaEdgeAt]
      apply Sym2.mem_iff.mpr
      left
      exact hnd.getElem_inj_iff.mpr hij

private theorem thetaLineGraph_map_adj_iff {A W : Type*} (Theta : SimpleGraph A)
    (D : SimpleGraph W) (r : A → W) (hr : Function.Injective r)
    (hedge : ∀ e : Theta.edgeSet, Sym2.map r (e : Sym2 A) ∈ D.edgeSet)
    (e f : Theta.edgeSet) :
    D.lineGraph.Adj ⟨Sym2.map r (e : Sym2 A), hedge e⟩
        ⟨Sym2.map r (f : Sym2 A), hedge f⟩ ↔
      Theta.lineGraph.Adj e f := by
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

private theorem thetaLineGraph_old_new_adj_iff (m ℓ : ℕ) (Theta : SimpleGraph (Fin m))
    (z z' : Fin m) (hℓ : 0 < ℓ) (hznadj : ¬ Theta.Adj z z')
    (D : SimpleGraph (Fin m ⊕ Fin (ℓ - 1)))
    (p : List (Fin m ⊕ Fin (ℓ - 1)))
    (hp : p = Sum.inl z ::
      (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']))
    (hold : ∀ e : Theta.edgeSet,
      Sym2.map (@Sum.inl (Fin m) (Fin (ℓ - 1))) (e : Sym2 (Fin m)) ∈ D.edgeSet)
    (hnew : ∀ i : Fin ℓ,
      thetaEdgeAt p (Fin.cast (by rw [hp]; simp; omega) i) ∈ D.edgeSet)
    (e : Theta.edgeSet) (i : Fin ℓ) :
    D.lineGraph.Adj
        ⟨Sym2.map (@Sum.inl (Fin m) (Fin (ℓ - 1))) (e : Sym2 (Fin m)), hold e⟩
        ⟨thetaEdgeAt p (Fin.cast (by rw [hp]; simp; omega) i), hnew i⟩ ↔
      (i.val = 0 ∧ z ∈ (e : Sym2 (Fin m))) ∨
        (i.val + 1 = ℓ ∧ z' ∈ (e : Sym2 (Fin m))) := by
  subst p
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨-, v, hvold, hvnew⟩
    obtain ⟨c, hce, hcv⟩ := Sym2.mem_map.mp hvold
    have hcnew : Sum.inl c ∈ thetaEdgeAt
        (Sum.inl z :: (List.ofFn (fun j : Fin (ℓ - 1) => Sum.inr j) ++ [Sum.inl z']) :
          List (Fin m ⊕ Fin (ℓ - 1)))
        (Fin.cast (by simp; omega) i) := by
      rwa [hcv]
    rcases (thetaP_old_mem_edge_iff m ℓ z z' c hℓ i.val (by omega)).mp hcnew with
      ⟨hi, hc⟩ | ⟨hi, hc⟩
    · exact Or.inl ⟨hi, by rwa [← hc]⟩
    · exact Or.inr ⟨hi, by rwa [← hc]⟩
  · intro h
    have hne := thetaOld_ne_edgeAt m ℓ Theta z z' hℓ hznadj e i
    refine ⟨fun heq => hne (congrArg Subtype.val heq), ?_⟩
    rcases h with ⟨hi, hze⟩ | ⟨hi, hz'e⟩
    · refine ⟨Sum.inl z, Sym2.mem_map.mpr ⟨z, hze, rfl⟩, ?_⟩
      apply (thetaP_old_mem_edge_iff m ℓ z z' z hℓ i.val (by omega)).mpr
      exact Or.inl ⟨hi, rfl⟩
    · refine ⟨Sum.inl z', Sym2.mem_map.mpr ⟨z', hz'e, rfl⟩, ?_⟩
      apply (thetaP_old_mem_edge_iff m ℓ z z' z' hℓ i.val (by omega)).mpr
      exact Or.inr ⟨hi, rfl⟩

/-- Paper, 6.1(7): "there is a `J`-enlargement that appears in the complement
of `G`." A path attached to the two incident stars of an appearance adds
one new branch between the corresponding host vertices. -/
theorem add_branch {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (K : Set V) (m : ℕ) (Θ : SimpleGraph (Fin m))
    (φ : Θ.lineGraph ≃g G.induce K)
    (z z' : Fin m) (hzz' : z ≠ z') (hznadj : ¬ Θ.Adj z z')
    (f : List V) (f₁ fn : V) (hf : IsPathFrom G f f₁ fn)
    (hfK : ∀ x ∈ f, x ∈ Kᶜ)
    (hattach : ∀ (i : Fin f.length) (e : Θ.edgeSet),
      G.Adj f[i.val] (↑(φ e) : V) ↔
        (i.val = 0 ∧ z ∈ (e : Sym2 (Fin m))) ∨
        (i.val + 1 = f.length ∧ z' ∈ (e : Sym2 (Fin m)))) :
    ∃ (H : SimpleGraph (Fin (m + (f.length - 1))))
      (ρ : Fin m → Fin (m + (f.length - 1)))
      (p : List (Fin (m + (f.length - 1))))
      (_ψ : H.lineGraph ≃g G.induce (K ∪ {x : V | x ∈ f})),
      IsThetaBranchExtension Θ z z' H ρ p ∧ p.length = f.length + 1 := by
  classical
  have hflen : 0 < f.length := List.length_pos_of_ne_nil hf.1.1
  let p₀ : List (Fin m ⊕ Fin (f.length - 1)) :=
    Sum.inl z :: (List.ofFn (fun i : Fin (f.length - 1) => Sum.inr i) ++ [Sum.inl z'])
  have hp₀def : p₀ = Sum.inl z ::
      (List.ofFn (fun i : Fin (f.length - 1) => Sum.inr i) ++ [Sum.inl z']) := rfl
  have hp₀len : p₀.length = f.length + 1 := by
    rw [hp₀def]
    exact thetaP_length m f.length z z' hflen
  have hp₀edgeLen : p₀.length - 1 = f.length := by omega
  have hp₀nd : p₀.Nodup := by
    rw [hp₀def]
    exact thetaP_nodup m f.length z z' hzz'
  let oldEmb : Fin m ↪ (Fin m ⊕ Fin (f.length - 1)) := Function.Embedding.inl
  let D : SimpleGraph (Fin m ⊕ Fin (f.length - 1)) :=
    Θ.map oldEmb ⊔ SimpleGraph.fromEdgeSet (trackEdges p₀)
  have htrackEdgeSet : (SimpleGraph.fromEdgeSet (trackEdges p₀)).edgeSet = trackEdges p₀ := by
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    exact sdiff_eq_left.mpr (thetaTrackEdges_disjoint_diag p₀ hp₀nd)
  have hDedges : D.edgeSet =
      Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) '' Θ.edgeSet ∪ trackEdges p₀ := by
    simp only [D, SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_map, htrackEdgeSet]
    rfl
  have hold : ∀ e : Θ.edgeSet,
      Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) (e : Sym2 (Fin m)) ∈ D.edgeSet := by
    intro e
    rw [hDedges]
    exact Or.inl ⟨e, e.property, rfl⟩
  have hnew : ∀ i : Fin f.length,
      thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm i) ∈ D.edgeSet := by
    intro i
    rw [hDedges]
    right
    rw [thetaTrackEdges_eq_range]
    exact ⟨Fin.cast hp₀edgeLen.symm i, rfl⟩
  let edgeEmb : Θ.edgeSet ⊕ Fin f.length → D.edgeSet
    | Sum.inl e => ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1)))
        (e : Sym2 (Fin m)), hold e⟩
    | Sum.inr i => ⟨thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm i), hnew i⟩
  have hedgeEmb_inj : Function.Injective edgeEmb := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl e' =>
        have hval := congrArg Subtype.val hab
        have hee : e = e' := Subtype.ext
          (Sym2.map.injective Sum.inl_injective hval)
        simp [hee]
      | inr i =>
        have hval := congrArg Subtype.val hab
        exact (thetaOld_ne_edgeAt m f.length Θ z z' hflen hznadj e i
          (by simpa [edgeEmb, hp₀def] using hval)).elim
    | inr i =>
      cases b with
      | inl e =>
        have hval := congrArg Subtype.val hab
        exact (thetaOld_ne_edgeAt m f.length Θ z z' hflen hznadj e i
          (by simpa [edgeEmb, hp₀def] using hval.symm)).elim
      | inr j =>
        have hval := congrArg Subtype.val hab
        have hc : Fin.cast hp₀edgeLen.symm i = Fin.cast hp₀edgeLen.symm j :=
          thetaEdgeAt_injective p₀ hp₀nd (by simpa [edgeEmb] using hval)
        have hij : i = j := by
          apply Fin.ext
          exact congrArg (fun k : Fin (p₀.length - 1) => k.val) hc
        simp [hij]
  have hedgeEmb_surj : Function.Surjective edgeEmb := by
    intro e
    have he : (e : Sym2 (Fin m ⊕ Fin (f.length - 1))) ∈
        Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) '' Θ.edgeSet ∪
          trackEdges p₀ := by
      rw [← hDedges]
      exact e.property
    rcases he with ⟨e₀, he₀, hval⟩ | he
    · let a : Θ.edgeSet := ⟨e₀, he₀⟩
      refine ⟨Sum.inl a, ?_⟩
      apply Subtype.ext
      simpa [edgeEmb, a] using hval
    · rw [thetaTrackEdges_eq_range] at he
      obtain ⟨j, hj⟩ := he
      let i : Fin f.length := Fin.cast hp₀edgeLen j
      refine ⟨Sum.inr i, ?_⟩
      apply Subtype.ext
      have hji : Fin.cast hp₀edgeLen.symm i = j := by
        apply Fin.ext
        rfl
      simpa [edgeEmb, i, hji] using hj
  let edgeEquiv : (Θ.edgeSet ⊕ Fin f.length) ≃ D.edgeSet :=
    Equiv.ofBijective edgeEmb ⟨hedgeEmb_inj, hedgeEmb_surj⟩

  let target : Set V := K ∪ {x : V | x ∈ f}
  let vertexEmb : Θ.edgeSet ⊕ Fin f.length → target
    | Sum.inl e => ⟨(↑(φ e) : V), Or.inl (φ e).property⟩
    | Sum.inr i => ⟨f[i.val], Or.inr (List.getElem_mem _)⟩
  have hvertexEmb_inj : Function.Injective vertexEmb := by
    intro a b hab
    cases a with
    | inl e =>
      cases b with
      | inl e' =>
        have hv : (↑(φ e) : V) = (↑(φ e') : V) := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have heq : φ e = φ e' := Subtype.ext hv
        have : e = e' := φ.injective heq
        simp [this]
      | inr i =>
        have hv : (↑(φ e) : V) = f[i.val] := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have hnot := hfK f[i.val] (List.getElem_mem i.isLt)
        have hmem : f[i.val] ∈ K := by
          rw [← hv]
          exact (φ e).property
        exact (hnot hmem).elim
    | inr i =>
      cases b with
      | inl e =>
        have hv : f[i.val] = (↑(φ e) : V) := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have hnot := hfK f[i.val] (List.getElem_mem i.isLt)
        have hmem : f[i.val] ∈ K := by
          rw [hv]
          exact (φ e).property
        exact (hnot hmem).elim
      | inr j =>
        have hv : f[i.val] = f[j.val] := by
          simpa [vertexEmb] using congrArg (fun x : target => (x : V)) hab
        have hij : i.val = j.val := hf.1.2.1.getElem_inj_iff.mp hv
        have : i = j := Fin.val_injective hij
        simp [this]
  have hvertexEmb_surj : Function.Surjective vertexEmb := by
    intro x
    rcases x with ⟨x, hx⟩
    rcases hx with hxK | hxf
    · obtain ⟨e, he⟩ := φ.surjective ⟨x, hxK⟩
      refine ⟨Sum.inl e, ?_⟩
      apply Subtype.ext
      simpa [vertexEmb] using congrArg Subtype.val he
    · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hxf
      refine ⟨Sum.inr ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      exact hix
  let vertexEquiv : (Θ.edgeSet ⊕ Fin f.length) ≃ target :=
    Equiv.ofBijective vertexEmb ⟨hvertexEmb_inj, hvertexEmb_surj⟩

  have hrel : ∀ a b : Θ.edgeSet ⊕ Fin f.length,
      D.lineGraph.Adj (edgeEmb a) (edgeEmb b) ↔
        (G.induce target).Adj (vertexEmb a) (vertexEmb b) := by
    intro a b
    cases a with
    | inl e =>
      cases b with
      | inl e' =>
        change D.lineGraph.Adj
            ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) (e : Sym2 (Fin m)), hold e⟩
            ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) (e' : Sym2 (Fin m)), hold e'⟩ ↔
          G.Adj (↑(φ e) : V) (↑(φ e') : V)
        exact (thetaLineGraph_map_adj_iff Θ D _ Sum.inl_injective hold e e').trans
          φ.map_adj_iff.symm
      | inr i =>
        change D.lineGraph.Adj
            ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) (e : Sym2 (Fin m)), hold e⟩
            ⟨thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm i), hnew i⟩ ↔
          G.Adj (↑(φ e) : V) f[i.val]
        rw [G.adj_comm]
        exact (thetaLineGraph_old_new_adj_iff m f.length Θ z z' hflen hznadj D p₀
          hp₀def hold hnew e i).trans
          (hattach i e).symm
    | inr i =>
      cases b with
      | inl e =>
        rw [D.lineGraph.adj_comm]
        change D.lineGraph.Adj
            ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) (e : Sym2 (Fin m)), hold e⟩
            ⟨thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm i), hnew i⟩ ↔
          G.Adj f[i.val] (↑(φ e) : V)
        exact (thetaLineGraph_old_new_adj_iff m f.length Θ z z' hflen hznadj D p₀
          hp₀def hold hnew e i).trans
          (hattach i e).symm
      | inr j =>
        change D.lineGraph.Adj
            ⟨thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm i), hnew i⟩
            ⟨thetaEdgeAt p₀ (Fin.cast hp₀edgeLen.symm j), hnew j⟩ ↔
          G.Adj f[i.val] f[j.val]
        have htrack := thetaLineGraph_edgeAt_adj_iff D p₀ hp₀nd
          (fun k => by
            rw [hDedges]
            right
            rw [thetaTrackEdges_eq_range]
            exact ⟨k, rfl⟩)
          (Fin.cast hp₀edgeLen.symm i) (Fin.cast hp₀edgeLen.symm j)
        have hpath := hf.1.2.2 i.val j.val i.isLt j.isLt
        exact htrack.trans hpath.symm
  let psiD : D.lineGraph ≃g G.induce target :=
    { toEquiv := edgeEquiv.symm.trans vertexEquiv
      map_rel_iff' := by
        intro e e'
        have hr := (hrel (edgeEquiv.symm e) (edgeEquiv.symm e')).symm
        have he : edgeEmb (edgeEquiv.symm e) = e := edgeEquiv.apply_symm_apply e
        have he' : edgeEmb (edgeEquiv.symm e') = e' := edgeEquiv.apply_symm_apply e'
        change (G.induce target).Adj
            (vertexEmb (edgeEquiv.symm e)) (vertexEmb (edgeEquiv.symm e')) ↔
          D.lineGraph.Adj e e'
        simpa only [he, he'] using hr }

  let finEquiv : (Fin m ⊕ Fin (f.length - 1)) ≃ Fin (m + (f.length - 1)) := finSumFinEquiv
  let H : SimpleGraph (Fin (m + (f.length - 1))) := D.map finEquiv.toEmbedding
  let rho : Fin m → Fin (m + (f.length - 1)) := fun c => finEquiv (Sum.inl c)
  let p : List (Fin (m + (f.length - 1))) := p₀.map finEquiv
  let mapIso : D ≃g H := SimpleGraph.Iso.map finEquiv D
  let psi : H.lineGraph ≃g G.induce target := mapIso.lineGraph.symm.trans psiD
  refine ⟨H, rho, p, ?_, ?_, ?_⟩
  · simpa [target] using psi
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact finEquiv.injective.comp Sum.inl_injective
    · intro c d hcd
      change (D.map finEquiv.toEmbedding).Adj
        (finEquiv (Sum.inl c)) (finEquiv (Sum.inl d))
      apply (SimpleGraph.map_adj_apply).mpr
      apply (SimpleGraph.mem_edgeSet D).mp
      rw [hDedges]
      left
      refine ⟨s(c, d), hcd, ?_⟩
      simp
    · refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · simp [p, hp₀def]
      · exact hp₀nd.map finEquiv.injective
      · intro i hi
        simp only [p, List.length_map, List.getElem_map]
        apply (SimpleGraph.map_adj_apply).mpr
        apply (SimpleGraph.mem_edgeSet D).mp
        rw [hDedges]
        right
        exact ⟨i, by simpa [p] using hi, rfl⟩
      · simp [p, hp₀def, rho]
      · change (p₀.map finEquiv).getLast? = some (finEquiv (Sum.inl z'))
        rw [List.getLast?_map]
        have hp₀last : p₀.getLast? = some (Sum.inl z') := by
          rw [hp₀def]
          rw [← List.cons_append]
          exact List.getLast?_concat
        rw [hp₀last]
        rfl
    · simp [p, hp₀len]
      omega
    · intro v hv
      have hinter : trackInterior p = (trackInterior p₀).map finEquiv := by
        simp [p, trackInterior]
      rw [hinter] at hv
      obtain ⟨x, hx, hxv⟩ := List.mem_map.mp hv
      rw [hp₀def, thetaP_interior] at hx
      simp only [List.mem_ofFn] at hx
      obtain ⟨i, rfl⟩ := hx
      rintro ⟨c, hc⟩
      have : Sum.inr i = Sum.inl c := finEquiv.injective (hxv.trans hc.symm)
      exact Sum.inr_ne_inl this
    · intro v
      let x := finEquiv.symm v
      rcases thetaP_cover m f.length z z' x with hx | hx
      · obtain ⟨c, hc⟩ := hx
        left
        refine ⟨c, ?_⟩
        simpa [rho, x] using congrArg finEquiv hc
      · right
        have hinter : trackInterior p = (trackInterior p₀).map finEquiv := by
          simp [p, trackInterior]
        rw [hinter]
        refine List.mem_map.mpr ⟨x, hx, ?_⟩
        simp [x]
    · change (D.map finEquiv.toEmbedding).edgeSet =
          Sym2.map (fun c : Fin m => finEquiv (Sum.inl c)) '' Θ.edgeSet ∪
            trackEdges (p₀.map finEquiv)
      rw [SimpleGraph.edgeSet_map, hDedges, Set.image_union]
      have holdMap : Sym2.map (⇑finEquiv) ''
          (Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) '' Θ.edgeSet) =
          Sym2.map rho '' Θ.edgeSet := by
        ext e
        constructor
        · rintro ⟨e', ⟨e₀, he₀, rfl⟩, rfl⟩
          refine ⟨e₀, he₀, ?_⟩
          induction e₀ using Sym2.ind with
          | _ a b => simp [rho, Sym2.map_mk]
        · rintro ⟨e₀, he₀, rfl⟩
          refine ⟨Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) e₀,
            ⟨e₀, he₀, rfl⟩, ?_⟩
          induction e₀ using Sym2.ind with
          | _ a b => simp [rho, Sym2.map_mk]
      change Sym2.map (⇑finEquiv) ''
          (Sym2.map (@Sum.inl (Fin m) (Fin (f.length - 1))) '' Θ.edgeSet) ∪
            Sym2.map (⇑finEquiv) '' trackEdges p₀ =
        Sym2.map (fun c : Fin m => finEquiv (Sum.inl c)) '' Θ.edgeSet ∪
          trackEdges (p₀.map finEquiv)
      rw [holdMap]
      exact congrArg (fun s => Sym2.map rho '' Θ.edgeSet ∪ s)
        (thetaTrackEdges_map finEquiv p₀).symm
  · simp [p, hp₀len]


end Workspace.ProofLemmas.Thm61OddAddBranch
