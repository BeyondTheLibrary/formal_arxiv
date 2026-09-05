import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.StripSystemBasics
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.TrackToRungPath

/-!
# Degrees on the two sides of an appearance — merged attempt

Union of the two half-lanes `Half_LH_1.lean` (the five `L(H)`-side theorems) and
`Half_GK_2.lean` (the six `G|K`-side theorems), plus the helpers both introduced.

Four of the `G|K`-side statements carry the repaired signature with the extra clause

  `hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b`

which is the formal content of the paper's *"for each **edge** `uv` of `J`, choose a `uv`-rung
`R_{uv}`"*.  Without it they are FALSE; see
`ProofAttempts/LineGraphDegree/LineGraphDegree_Refutation.lean`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LineGraphDegree

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT

/-! ## The `L(H)` side -/

section LineGraph

variable {W : Type*} {H : SimpleGraph W}

/-- The `L(H)`-neighbours of the edge `e` are the edges of `H` other than `e` that meet `e`. -/
theorem mem_lineGraph_neighborSet_iff (e f : H.edgeSet) :
    f ∈ H.lineGraph.neighborSet e ↔
      (f ≠ e ∧ ∃ w : W, w ∈ (e : Sym2 W) ∧ w ∈ (f : Sym2 W)) := by
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨h, w, h1, h2⟩
    exact ⟨h.symm, w, h1, h2⟩
  · rintro ⟨h, w, h1, h2⟩
    exact ⟨h.symm, w, h1, h2⟩

/-! ### Auxiliary facts about the neighbours of an edge in `L(H)` -/

/-- If both ends of `e = ab` have finitely many neighbours in `H`, then `e` has finitely many
neighbours in `L(H)`: every one of them is an edge `ax` or `by`. -/
theorem lineGraph_neighborSet_finite {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (hfa : (H.neighborSet a).Finite) (hfb : (H.neighborSet b).Finite) :
    (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).Finite := by
  refine Set.Finite.of_finite_image ?_ (Subtype.val_injective.injOn)
  refine Set.Finite.subset
    ((hfa.image (fun x => s(a, x))).union (hfb.image (fun y => s(b, y)))) ?_
  rintro f ⟨g, hg, rfl⟩
  rw [mem_lineGraph_neighborSet_iff] at hg
  obtain ⟨-, w, hwe, hwg⟩ := hg
  have hw : w = a ∨ w = b := by
    simpa [Sym2.mem_iff] using hwe
  obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hwg
  have hgadj : H.Adj w x := by
    have : (g : Sym2 W) ∈ H.edgeSet := g.2
    rw [hx] at this
    exact this
  rcases hw with rfl | rfl
  · exact Or.inl ⟨x, hgadj, hx.symm⟩
  · exact Or.inr ⟨x, hgadj, hx.symm⟩

/-- The `L(H)`-neighbourhood of `e = ab` is contained in the union of the two "stars". -/
theorem lineGraph_neighborSet_infinite_left {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (hinf : (H.neighborSet a).Infinite) :
    (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).Infinite := by
  have hAdj : H.Adj a b := hab
  have hinj : Set.InjOn (fun x => s(a, x)) (H.neighborSet a \ {b}) := by
    intro x _ y _ hxy
    exact Sym2.congr_right.mp hxy
  have h1 : ((fun x => s(a, x)) '' (H.neighborSet a \ {b})).Infinite :=
    ((hinf.diff (Set.finite_singleton b)).image hinj)
  have hsub : (fun x => s(a, x)) '' (H.neighborSet a \ {b}) ⊆
      Subtype.val '' (H.lineGraph.neighborSet ⟨s(a, b), hab⟩) := by
    rintro _ ⟨x, ⟨hx, hxb⟩, rfl⟩
    have hxadj : H.Adj a x := hx
    refine ⟨⟨s(a, x), hxadj⟩, ?_, rfl⟩
    rw [mem_lineGraph_neighborSet_iff]
    refine ⟨?_, a, by simp, by simp⟩
    intro hcon
    have : s(a, x) = s(a, b) := congrArg Subtype.val hcon
    exact hxb (Sym2.congr_right.mp this)
  exact Set.Infinite.of_image Subtype.val (h1.mono hsub)

/-- **Every vertex of a subdivision has degree `≥ 2`.**

An interior vertex of a track has its two track-neighbours; a branch-vertex `ι u` has the
`deg_J(u) ≥ 3` first edges of the tracks at `u`. -/
theorem two_le_degree_of_isSubdivision {U : Type*} [Fintype U] {J : SimpleGraph U}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) (w : W) :
    2 ≤ (H.neighborSet w).ncard := by
  obtain ⟨ι, T, hinj, htrack, hlen, hrev, hdisj, hnew, hcover, hedge⟩ := hsub
  -- `W` is finite, since every vertex is either an `ι u` or lies on one of the finitely many
  -- tracks.
  haveI hWfin : Finite W := by
    have hsubset : (Set.univ : Set W) ⊆
        Set.range ι ∪ ⋃ (u : U) (v : U), {x : W | x ∈ T u v} := by
      intro x _
      rcases hcover x with ⟨u, rfl⟩ | ⟨u, v, huv, hx⟩
      · exact Or.inl ⟨u, rfl⟩
      · refine Or.inr ?_
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        exact ⟨u, v, List.tail_subset _ (List.dropLast_subset _ hx)⟩
    have hfin : (Set.univ : Set W).Finite := by
      refine Set.Finite.subset ?_ hsubset
      refine Set.Finite.union (Set.finite_range ι) ?_
      exact Set.finite_iUnion (fun u => Set.finite_iUnion (fun v => (T u v).finite_toSet))
    exact Set.finite_univ_iff.mp hfin
  -- the second vertex of the track `T u v`
  have hsecond : ∀ u v : U, J.Adj u v →
      ∃ z : W, H.Adj (ι u) z ∧ z ∈ T u v ∧ (z = ι v ∨ z ∈ trackInterior (T u v)) := by
    intro u v huv
    have htf := htrack u v huv
    obtain ⟨htl, hhead, hlast⟩ := htf
    obtain ⟨hnil, hnodup, hadjs⟩ := htl
    have hlen2 : 2 ≤ (T u v).length := by
      have := hlen u v huv
      unfold trackLength at this
      omega
    have h0 : (T u v)[0]'(by omega) = ι u :=
      SubdivisionCounting.track_head (htrack u v huv) (by omega)
    refine ⟨(T u v)[1]'(by omega), ?_, List.getElem_mem _, ?_⟩
    · have := hadjs 0 (by omega)
      rw [h0] at this
      exact this
    · rcases Nat.lt_or_ge (T u v).length 3 with hlt | hge
      · left
        exact SubdivisionCounting.track_last (htrack u v huv) (by omega)
      · right
        have := SubdivisionCounting.mem_trackInterior_getElem (T u v) 0 (by omega)
        simpa using this
  rcases hcover w with ⟨u, rfl⟩ | ⟨u, v, huv, hw⟩
  · -- `w = ι u` is an old vertex: it has degree `≥ 3` in `J`, hence at least two `H`-neighbours
    have hdeg : 3 ≤ (J.neighborSet u).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ u
    have hex : ∃ v₁ ∈ J.neighborSet u, ∃ v₂ ∈ J.neighborSet u, v₁ ≠ v₂ := by
      by_contra hno
      push_neg at hno
      have hle : (J.neighborSet u).ncard ≤ 1 := by
        rw [Set.ncard_le_one (Set.toFinite _)]
        intro x hx y hy
        exact hno x hx y hy
      omega
    obtain ⟨v₁, hv₁, v₂, hv₂, hv12⟩ := hex
    have hadj1 : J.Adj u v₁ := hv₁
    have hadj2 : J.Adj u v₂ := hv₂
    obtain ⟨z₁, hz₁adj, hz₁mem, hz₁alt⟩ := hsecond u v₁ hadj1
    obtain ⟨z₂, hz₂adj, hz₂mem, hz₂alt⟩ := hsecond u v₂ hadj2
    have hsne : s(u, v₁) ≠ s(u, v₂) := fun h => hv12 (Sym2.congr_right.mp h)
    have hzne : z₁ ≠ z₂ := by
      rcases hz₁alt with h1 | h1
      · rcases hz₂alt with h2 | h2
        · intro h
          exact hv12 (hinj (by rw [← h1, h, h2]))
        · intro h
          exact hdisj u v₂ u v₁ hadj2 hadj1 (Ne.symm hsne) z₂ h2 (by rw [← h]; exact hz₁mem)
      · intro h
        exact hdisj u v₁ u v₂ hadj1 hadj2 hsne z₁ h1 (by rw [h]; exact hz₂mem)
    have hsub2 : ({z₁, z₂} : Set W) ⊆ H.neighborSet (ι u) := by
      rintro x (rfl | rfl)
      · exact hz₁adj
      · exact hz₂adj
    calc 2 = ({z₁, z₂} : Set W).ncard := (Set.ncard_pair hzne).symm
      _ ≤ (H.neighborSet (ι u)).ncard := Set.ncard_le_ncard hsub2 (Set.toFinite _)
  · -- `w` is an internal vertex of the track `T u v`
    obtain ⟨htl, hhead, hlast⟩ := htrack u v huv
    obtain ⟨hnil, hnodup, hadjs⟩ := htl
    obtain ⟨j, hj, hjw⟩ := (SubdivisionCounting.mem_trackInterior_iff (T u v) w).mp hw
    have hA : H.Adj ((T u v)[j]'(by omega)) ((T u v)[j + 1]'(by omega)) := hadjs j (by omega)
    have hB : H.Adj ((T u v)[j + 1]'(by omega)) ((T u v)[j + 2]'(by omega)) := by
      have := hadjs (j + 1) (by omega)
      exact this
    have hne : ((T u v)[j]'(by omega)) ≠ ((T u v)[j + 2]'(by omega)) := by
      intro h
      have := (List.Nodup.getElem_inj_iff hnodup).mp h
      omega
    have hsub2 : ({((T u v)[j]'(by omega)), ((T u v)[j + 2]'(by omega))} : Set W) ⊆
        H.neighborSet w := by
      rintro x (rfl | rfl)
      · rw [← hjw]
        exact hA.symm
      · rw [← hjw]
        exact hB
    calc 2 = ({((T u v)[j]'(by omega)), ((T u v)[j + 2]'(by omega))} : Set W).ncard :=
          (Set.ncard_pair hne).symm
      _ ≤ (H.neighborSet w).ncard := Set.ncard_le_ncard hsub2 (Set.toFinite _)

/-- **An edge with a branch-vertex end has `L(H)`-degree `≥ 3`.**

The `≥ 3` edges at the branch-vertex supply `≥ 2` neighbours, and the other end of `e` — which
has degree `≥ 2` — supplies one more, distinct from those because an edge meeting both ends of
`e` is `e` itself. -/
theorem three_le_lineGraph_degree_of_branch {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (ha : a ∈ branchVertices H) (hb : 2 ≤ (H.neighborSet b).ncard) :
    3 ≤ (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard := by
  have hAdj : H.Adj a b := hab
  have hne : a ≠ b := hAdj.ne
  have ha3 : 3 ≤ (H.neighborSet a).ncard := ha
  have hfa : (H.neighborSet a).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have hfb : (H.neighborSet b).Finite := Set.finite_of_ncard_ne_zero (by omega)
  -- two neighbours of `a` other than `b`
  have hbmem : b ∈ H.neighborSet a := hAdj
  have hcarda : (H.neighborSet a \ {b}).ncard = (H.neighborSet a).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hbmem
  have hex2 : ∃ x₁ ∈ H.neighborSet a \ {b}, ∃ x₂ ∈ H.neighborSet a \ {b}, x₁ ≠ x₂ := by
    by_contra hno
    push_neg at hno
    have hle : (H.neighborSet a \ {b}).ncard ≤ 1 := by
      rw [Set.ncard_le_one hfa.diff]
      intro x hx y hy
      exact hno x hx y hy
    omega
  obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := hex2
  -- a neighbour of `b` other than `a`
  have hamem : a ∈ H.neighborSet b := hAdj.symm
  have hcardb : (H.neighborSet b \ {a}).ncard = (H.neighborSet b).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hamem
  have hexy : (H.neighborSet b \ {a}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨y, hy⟩ := hexy
  -- the three edges
  have hx₁adj : H.Adj a x₁ := hx₁.1
  have hx₂adj : H.Adj a x₂ := hx₂.1
  have hyadj : H.Adj b y := hy.1
  have hx₁b : x₁ ≠ b := hx₁.2
  have hx₂b : x₂ ≠ b := hx₂.2
  have hya : y ≠ a := hy.2
  set f₁ : H.edgeSet := ⟨s(a, x₁), hx₁adj⟩ with hf₁
  set f₂ : H.edgeSet := ⟨s(a, x₂), hx₂adj⟩ with hf₂
  set f₃ : H.edgeSet := ⟨s(b, y), hyadj⟩ with hf₃
  have h12 : f₁ ≠ f₂ := by
    intro h
    exact hx12 (Sym2.congr_right.mp (congrArg Subtype.val h))
  have h13 : f₁ ≠ f₃ := by
    intro h
    have h' : s(a, x₁) = s(b, y) := congrArg Subtype.val h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨hab', -⟩ | ⟨-, hx₁b'⟩
    · exact hne hab'
    · exact hx₁b hx₁b'
  have h23 : f₂ ≠ f₃ := by
    intro h
    have h' : s(a, x₂) = s(b, y) := congrArg Subtype.val h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨hab', -⟩ | ⟨-, hx₂b'⟩
    · exact hne hab'
    · exact hx₂b hx₂b'
  have hmem1 : f₁ ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rw [mem_lineGraph_neighborSet_iff]
    refine ⟨?_, a, by simp, by rw [hf₁]; simp⟩
    intro h
    exact hx₁b (Sym2.congr_right.mp (congrArg Subtype.val h))
  have hmem2 : f₂ ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rw [mem_lineGraph_neighborSet_iff]
    refine ⟨?_, a, by simp, by rw [hf₂]; simp⟩
    intro h
    exact hx₂b (Sym2.congr_right.mp (congrArg Subtype.val h))
  have hmem3 : f₃ ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rw [mem_lineGraph_neighborSet_iff]
    refine ⟨?_, b, by simp, by rw [hf₃]; simp⟩
    intro h
    have h' : s(b, y) = s(a, b) := congrArg Subtype.val h
    rw [Sym2.eq_iff] at h'
    rcases h' with ⟨hba, -⟩ | ⟨-, hya'⟩
    · exact hne hba.symm
    · exact hya hya'
  have hsub3 : ({f₁, f₂, f₃} : Set H.edgeSet) ⊆ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ := by
    rintro g (rfl | rfl | rfl)
    · exact hmem1
    · exact hmem2
    · exact hmem3
  have hcard3 : ({f₁, f₂, f₃} : Set H.edgeSet).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨f₁, f₂, f₃, h12, h13, h23, rfl⟩
  calc 3 = ({f₁, f₂, f₃} : Set H.edgeSet).ncard := hcard3.symm
    _ ≤ (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard :=
        Set.ncard_le_ncard hsub3 (lineGraph_neighborSet_finite hab hfa hfb)

/-- **An edge between two non-branch vertices has `L(H)`-degree `≤ 2`.** -/
theorem lineGraph_degree_le_two_of_not_branch {a b : W} (hab : s(a, b) ∈ H.edgeSet)
    (ha : (H.neighborSet a).ncard ≤ 2) (hb : (H.neighborSet b).ncard ≤ 2) :
    (H.lineGraph.neighborSet ⟨s(a, b), hab⟩).ncard ≤ 2 := by
  have hAdj : H.Adj a b := hab
  have hne : a ≠ b := hAdj.ne
  by_cases hfa : (H.neighborSet a).Finite
  · by_cases hfb : (H.neighborSet b).Finite
    · -- the interesting case
      have hbmem : b ∈ H.neighborSet a := hAdj
      have hamem : a ∈ H.neighborSet b := hAdj.symm
      have hcarda : (H.neighborSet a \ {b}).ncard = (H.neighborSet a).ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hbmem
      have hcardb : (H.neighborSet b \ {a}).ncard = (H.neighborSet b).ncard - 1 :=
        Set.ncard_diff_singleton_of_mem hamem
      have hAsub : ∀ x ∈ H.neighborSet a \ {b}, ∀ y ∈ H.neighborSet a \ {b}, x = y := by
        rw [← Set.ncard_le_one hfa.diff]
        omega
      have hBsub : ∀ x ∈ H.neighborSet b \ {a}, ∀ y ∈ H.neighborSet b \ {a}, x = y := by
        rw [← Set.ncard_le_one hfb.diff]
        omega
      -- split the neighbourhood into the edges through `a` and the edges through `b`
      set A : Set H.edgeSet :=
        {f | f ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ ∧ a ∈ (f : Sym2 W)} with hA
      set B : Set H.edgeSet :=
        {f | f ∈ H.lineGraph.neighborSet ⟨s(a, b), hab⟩ ∧ b ∈ (f : Sym2 W)} with hB
      have hcover : H.lineGraph.neighborSet ⟨s(a, b), hab⟩ ⊆ A ∪ B := by
        intro f hf
        have hf' := hf
        rw [mem_lineGraph_neighborSet_iff] at hf'
        obtain ⟨-, w, hwe, hwf⟩ := hf'
        have hw : w = a ∨ w = b := by simpa [Sym2.mem_iff] using hwe
        rcases hw with rfl | rfl
        · exact Or.inl ⟨hf, hwf⟩
        · exact Or.inr ⟨hf, hwf⟩
      have hAss : A.Subsingleton := by
        intro f hf g hg
        obtain ⟨hfn, hfa'⟩ := hf
        obtain ⟨hgn, hga'⟩ := hg
        obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hfa'
        obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hga'
        have hxadj : H.Adj a x := by
          have : (f : Sym2 W) ∈ H.edgeSet := f.2
          rw [hx] at this; exact this
        have hyadj : H.Adj a y := by
          have : (g : Sym2 W) ∈ H.edgeSet := g.2
          rw [hy] at this; exact this
        have hxb : x ≠ b := by
          intro hcon
          rw [mem_lineGraph_neighborSet_iff] at hfn
          exact hfn.1 (Subtype.ext (by rw [hx, hcon]))
        have hyb : y ≠ b := by
          intro hcon
          rw [mem_lineGraph_neighborSet_iff] at hgn
          exact hgn.1 (Subtype.ext (by rw [hy, hcon]))
        have := hAsub x ⟨hxadj, hxb⟩ y ⟨hyadj, hyb⟩
        exact Subtype.ext (by rw [hx, hy, this])
      have hBss : B.Subsingleton := by
        intro f hf g hg
        obtain ⟨hfn, hfb'⟩ := hf
        obtain ⟨hgn, hgb'⟩ := hg
        obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.mp hfb'
        obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp hgb'
        have hxadj : H.Adj b x := by
          have : (f : Sym2 W) ∈ H.edgeSet := f.2
          rw [hx] at this; exact this
        have hyadj : H.Adj b y := by
          have : (g : Sym2 W) ∈ H.edgeSet := g.2
          rw [hy] at this; exact this
        have hxa : x ≠ a := by
          intro hcon
          rw [mem_lineGraph_neighborSet_iff] at hfn
          exact hfn.1 (Subtype.ext (by rw [hx, hcon, Sym2.eq_swap]))
        have hya : y ≠ a := by
          intro hcon
          rw [mem_lineGraph_neighborSet_iff] at hgn
          exact hgn.1 (Subtype.ext (by rw [hy, hcon, Sym2.eq_swap]))
        have := hBsub x ⟨hxadj, hxa⟩ y ⟨hyadj, hya⟩
        exact Subtype.ext (by rw [hx, hy, this])
      have hAcard : A.ncard ≤ 1 := by
        rcases hAss.eq_empty_or_singleton with h | ⟨z, h⟩ <;> rw [h] <;> simp
      have hBcard : B.ncard ≤ 1 := by
        rcases hBss.eq_empty_or_singleton with h | ⟨z, h⟩ <;> rw [h] <;> simp
      have hfin : (A ∪ B).Finite := (hAss.finite).union (hBss.finite)
      have := Set.ncard_le_ncard hcover hfin
      have hun := Set.ncard_union_le A B
      omega
    · -- `b` has infinitely many neighbours: so does `e` in `L(H)`, and `ncard = 0`
      have hinf : (H.neighborSet b).Infinite := hfb
      have hab' : s(b, a) ∈ H.edgeSet := by rw [Sym2.eq_swap]; exact hab
      have hI := lineGraph_neighborSet_infinite_left hab' hinf
      have hEq : (⟨s(b, a), hab'⟩ : H.edgeSet) = ⟨s(a, b), hab⟩ := Subtype.ext Sym2.eq_swap
      rw [hEq] at hI
      rw [hI.ncard]
      omega
  · -- `a` has infinitely many neighbours: so does `e` in `L(H)`, and `ncard = 0`
    have hinf : (H.neighborSet a).Infinite := hfa
    rw [(lineGraph_neighborSet_infinite_left hab hinf).ncard]
    omega

/-- **The `L(H)`-side dichotomy.**  For a subdivision of a 3-connected graph, an edge of `H` has
`L(H)`-degree `≥ 3` exactly when one of its ends is a branch-vertex. -/
theorem three_le_lineGraph_degree_iff {U : Type*} [Fintype U] {J : SimpleGraph U}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) (e : H.edgeSet) :
    3 ≤ (H.lineGraph.neighborSet e).ncard ↔ ∃ w ∈ branchVertices H, w ∈ (e : Sym2 W) := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ a b =>
    have hab : s(a, b) ∈ H.edgeSet := he
    have hda : 2 ≤ (H.neighborSet a).ncard := two_le_degree_of_isSubdivision hJ hsub a
    have hdb : 2 ≤ (H.neighborSet b).ncard := two_le_degree_of_isSubdivision hJ hsub b
    constructor
    · intro h3
      by_contra hno
      push_neg at hno
      have hna : a ∉ branchVertices H := fun hh => hno a hh (by simp)
      have hnb : b ∉ branchVertices H := fun hh => hno b hh (by simp)
      have ha2 : (H.neighborSet a).ncard ≤ 2 := by
        have : ¬ (3 ≤ (H.neighborSet a).ncard) := hna
        omega
      have hb2 : (H.neighborSet b).ncard ≤ 2 := by
        have : ¬ (3 ≤ (H.neighborSet b).ncard) := hnb
        omega
      have := lineGraph_degree_le_two_of_not_branch hab ha2 hb2
      omega
    · rintro ⟨w, hw, hwe⟩
      have hw' : w = a ∨ w = b := by simpa [Sym2.mem_iff] using hwe
      rcases hw' with rfl | rfl
      · exact three_le_lineGraph_degree_of_branch hab hw hdb
      · have hab' : s(w, a) ∈ H.edgeSet := by
          rw [Sym2.eq_swap]; exact hab
        have hstep := three_le_lineGraph_degree_of_branch hab' hw hda
        have hEq : (⟨s(w, a), hab'⟩ : H.edgeSet) = ⟨s(a, w), hab⟩ :=
          Subtype.ext (Sym2.eq_swap)
        rwa [hEq] at hstep

end LineGraph

/-! ## The `G|K` side -/

section StripSide

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}

/-- `V(L(H))` for a choice of rungs: the union of the vertex sets of the rungs.  This is
literally the set `StripSystems.FormsLineGraph` uses. -/
def rungVertices (J : SimpleGraph U) (R : U → U → List V) : Set V :=
  ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}

theorem rungVertices_eq (J : SimpleGraph U) (R : U → U → List V) :
    rungVertices J R = ⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v} := rfl

theorem mem_rungVertices_iff {R : U → U → List V} {x : V} :
    x ∈ rungVertices J R ↔ ∃ u v : U, J.Adj u v ∧ x ∈ R u v := by
  simp only [rungVertices, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]

/-! ### Helpers for the `G|K` side -/

/-- **Two neighbours of a rung-end inside `N_c`.**

PAPER (sixth axiom, first half): *"`N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`"*.  Since `J` is
3-connected, `c` has at least two neighbours besides `d`, and the `c`-ends of those rungs are two
distinct neighbours of `x` lying in `N_c` and in the union of the rungs. -/
theorem exists_two_neighbours_in_N (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    {c d : U} (hcd : J.Adj c d) {x : V} (hxc : x ∈ N c) (hxS : x ∈ S c d) :
    ∃ s₁ s₂ : V, s₁ ≠ s₂ ∧ s₁ ∈ N c ∧ s₂ ∈ N c ∧
      s₁ ∈ rungVertices J R ∧ s₂ ∈ rungVertices J R ∧ G.Adj x s₁ ∧ G.Adj x s₂ := by
  have h3 : 3 ≤ (J.neighborSet c).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected J hJ c
  have hsub : J.neighborSet c ⊆ insert d (J.neighborSet c \ {d}) := by
    intro z hz
    by_cases hzd : z = d
    · simp [hzd]
    · exact Set.mem_insert_of_mem _ ⟨hz, by simpa using hzd⟩
  have hle : (J.neighborSet c).ncard ≤ (J.neighborSet c \ {d}).ncard + 1 :=
    le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) (Set.ncard_insert_le _ _)
  have h2 : 1 < (J.neighborSet c \ {d}).ncard := by omega
  obtain ⟨e₁, he₁⟩ : (J.neighborSet c \ {d}).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by omega)
  obtain ⟨e₂, he₂, he₂₁⟩ := Set.exists_ne_of_one_lt_ncard h2 e₁
  have hce₁ : J.Adj c e₁ := he₁.1
  have hce₂ : J.Adj c e₂ := he₂.1
  have hne₁ : e₁ ≠ d := by simpa using he₁.2
  have hne₂ : e₂ ≠ d := by simpa using he₂.2
  obtain ⟨s₁, hs₁R, hs₁S, hs₁N, -⟩ := StripSystemBasics.exists_rung_head (hR c e₁ hce₁)
  obtain ⟨s₂, hs₂R, hs₂S, hs₂N, -⟩ := StripSystemBasics.exists_rung_head (hR c e₂ hce₂)
  have hedge : s(c, e₁) ≠ s(c, e₂) := by
    intro h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨-, h⟩ | ⟨h, -⟩
    · exact he₂₁ h.symm
    · subst h
      exact J.irrefl hce₂
  have hdisj := StripSystemBasics.strip_disjoint hSN hce₁ hce₂ hedge
  have hs12 : s₁ ≠ s₂ := by
    intro h
    subst h
    exact Set.disjoint_left.mp hdisj hs₁S hs₂S
  refine ⟨s₁, s₂, hs12, hs₁N, hs₂N, mem_rungVertices_iff.mpr ⟨c, e₁, hce₁, hs₁R⟩,
    mem_rungVertices_iff.mpr ⟨c, e₂, hce₂, hs₂R⟩, ?_, ?_⟩
  · exact StripSystemBasics.Nuv_complete hSN hcd hce₁ (Ne.symm hne₁) x ⟨hxc, hxS⟩ s₁ ⟨hs₁N, hs₁S⟩
  · exact StripSystemBasics.Nuv_complete hSN hcd hce₂ (Ne.symm hne₂) x ⟨hxc, hxS⟩ s₂ ⟨hs₂N, hs₂S⟩

/-- Three neighbours of a rung-end `x ∈ N_c`: the two `c`-ends of other rungs at `c` supplied by
`exists_two_neighbours_in_N`, plus any further `K`-neighbour of `x` outside `N_c`. -/
theorem three_le_rung_degree_aux (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    {c d : U} (hcd : J.Adj c d) {x : V} (hxc : x ∈ N c) (hxS : x ∈ S c d)
    {y : V} (hyK : y ∈ rungVertices J R) (hxy : G.Adj x y) (hyN : y ∉ N c) :
    3 ≤ (G.neighborSet x ∩ rungVertices J R).ncard := by
  obtain ⟨s₁, s₂, hne, hs₁N, hs₂N, hs₁K, hs₂K, ha₁, ha₂⟩ :=
    exists_two_neighbours_in_N hSN hJ hR hcd hxc hxS
  have hy₁ : s₁ ≠ y := fun h => hyN (h ▸ hs₁N)
  have hy₂ : s₂ ≠ y := fun h => hyN (h ▸ hs₂N)
  have hsub : ({s₁, s₂, y} : Set V) ⊆ G.neighborSet x ∩ rungVertices J R := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨ha₁, hs₁K⟩
    · exact ⟨ha₂, hs₂K⟩
    · exact ⟨hxy, hyK⟩
  have hcard : ({s₁, s₂, y} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne, hy₁]),
      Set.ncard_insert_of_notMem (by simp [hy₂]), Set.ncard_singleton]
  calc (3 : ℕ) = ({s₁, s₂, y} : Set V).ncard := hcard.symm
    _ ≤ (G.neighborSet x ∩ rungVertices J R).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

/-- The head of the rung `R c d` (its unique vertex in `N_c`) has a `K`-neighbour outside `N_c`:
the next vertex of the rung, or — when the rung has length `0` — the `d`-end of another rung
at `d`. -/
theorem exists_third_neighbour_head (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) (hxc : x ∈ N c) :
    ∃ y : V, y ∈ rungVertices J R ∧ G.Adj x y ∧ y ∉ N c := by
  obtain ⟨-, s, t, hpf, hsubS, hsN, htN⟩ := hR c d hcd
  have hxs : x = s := (hsN x hx).mp hxc
  have hpos : 0 < (R c d).length := by
    rcases Nat.eq_zero_or_pos (R c d).length with h | h
    · exact absurd (List.eq_nil_of_length_eq_zero h) hpf.1.1
    · exact h
  have hhead : (R c d)[0]'hpos = s := by
    have h1 : (R c d)[0]? = some s := by rw [← List.head?_eq_getElem?]; exact hpf.2.1
    rw [List.getElem?_eq_getElem hpos] at h1
    exact Option.some_inj.mp h1
  by_cases hlen : 1 < (R c d).length
  · have hadj : G.Adj ((R c d)[0]'hpos) ((R c d)[1]'hlen) :=
      (hpf.1.2.2 0 1 hpos hlen).mpr (Or.inl rfl)
    refine ⟨(R c d)[1]'hlen, mem_rungVertices_iff.mpr ⟨c, d, hcd, List.getElem_mem hlen⟩, ?_, ?_⟩
    · rw [hxs, ← hhead]; exact hadj
    · intro hmem
      have h1 : (R c d)[1]'hlen = s := (hsN _ (List.getElem_mem hlen)).mp hmem
      rw [hhead, h1] at hadj
      exact G.irrefl hadj
  · have hlen1 : (R c d).length = 1 := by omega
    have hlast : (R c d)[0]'hpos = t := by
      have h1 : (R c d)[(R c d).length - 1]? = some t := by
        rw [← List.getLast?_eq_getElem?]; exact hpf.2.2
      rw [hlen1] at h1
      norm_num at h1
      rw [List.getElem?_eq_getElem hpos] at h1
      exact Option.some_inj.mp h1
    have hxt : x = t := by rw [hxs, ← hhead]; exact hlast
    have hxd : x ∈ N d := (htN x hx).mpr hxt
    have hxS : x ∈ S c d := hsubS x hx
    have hxSdc : x ∈ S d c := by rw [← StripSystemBasics.strip_symm hSN hcd]; exact hxS
    have hdeg : 3 ≤ (J.neighborSet d).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ d
    obtain ⟨f, hf, hfc⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet d) (by omega) c
    have hdf : J.Adj d f := hf
    obtain ⟨y, hyR, hyS, hyN, -⟩ := StripSystemBasics.exists_rung_head (hR d f hdf)
    refine ⟨y, mem_rungVertices_iff.mpr ⟨d, f, hdf, hyR⟩, ?_, ?_⟩
    · exact StripSystemBasics.Nuv_complete hSN hcd.symm hdf (Ne.symm hfc) x ⟨hxd, hxSdc⟩ y
        ⟨hyN, hyS⟩
    · intro hyc
      have hempty :=
        StripSystemBasics.strip_inter_N_eq_empty hSN hdf hcd.ne (Ne.symm hfc)
      rw [Set.eq_empty_iff_forall_notMem] at hempty
      exact hempty y ⟨hyS, hyc⟩

/-- The mirror of `exists_third_neighbour_head` at the `d`-end of the rung. -/
theorem exists_third_neighbour_last (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) (hxd : x ∈ N d) :
    ∃ y : V, y ∈ rungVertices J R ∧ G.Adj x y ∧ y ∉ N d := by
  obtain ⟨-, s, t, hpf, hsubS, hsN, htN⟩ := hR c d hcd
  have hxt : x = t := (htN x hx).mp hxd
  have hpos : 0 < (R c d).length := by
    rcases Nat.eq_zero_or_pos (R c d).length with h | h
    · exact absurd (List.eq_nil_of_length_eq_zero h) hpf.1.1
    · exact h
  have hlt1 : (R c d).length - 1 < (R c d).length := by omega
  have hlast : (R c d)[(R c d).length - 1]'hlt1 = t := by
    have h1 : (R c d)[(R c d).length - 1]? = some t := by
      rw [← List.getLast?_eq_getElem?]; exact hpf.2.2
    rw [List.getElem?_eq_getElem hlt1] at h1
    exact Option.some_inj.mp h1
  by_cases hlen : 1 < (R c d).length
  · have h2 : (R c d).length - 2 < (R c d).length := by omega
    have hadj : G.Adj ((R c d)[(R c d).length - 1]'hlt1) ((R c d)[(R c d).length - 2]'h2) :=
      (hpf.1.2.2 ((R c d).length - 1) ((R c d).length - 2) hlt1 h2).mpr (Or.inr (by omega))
    refine ⟨(R c d)[(R c d).length - 2]'h2,
      mem_rungVertices_iff.mpr ⟨c, d, hcd, List.getElem_mem h2⟩, ?_, ?_⟩
    · rw [hxt, ← hlast]; exact hadj
    · intro hmem
      have h1 : (R c d)[(R c d).length - 2]'h2 = t := (htN _ (List.getElem_mem h2)).mp hmem
      rw [hlast, h1] at hadj
      exact G.irrefl hadj
  · have hlen1 : (R c d).length = 1 := by omega
    have hhead : (R c d)[(R c d).length - 1]'hlt1 = s := by
      have h1 : (R c d)[0]? = some s := by rw [← List.head?_eq_getElem?]; exact hpf.2.1
      rw [List.getElem?_eq_getElem hpos] at h1
      have h0 : (R c d).length - 1 = 0 := by omega
      simp only [h0]
      exact Option.some_inj.mp h1
    have hxs : x = s := by rw [hxt, ← hlast]; exact hhead
    have hxc : x ∈ N c := (hsN x hx).mpr hxs
    have hxS : x ∈ S c d := hsubS x hx
    have hdeg : 3 ≤ (J.neighborSet c).ncard :=
      SubdivisionCounting.three_le_degree_of_three_connected J hJ c
    obtain ⟨e, he, hed⟩ := Set.exists_ne_of_one_lt_ncard (s := J.neighborSet c) (by omega) d
    have hce : J.Adj c e := he
    obtain ⟨y, hyR, hyS, hyN, -⟩ := StripSystemBasics.exists_rung_head (hR c e hce)
    refine ⟨y, mem_rungVertices_iff.mpr ⟨c, e, hce, hyR⟩, ?_, ?_⟩
    · exact StripSystemBasics.Nuv_complete hSN hcd hce (Ne.symm hed) x ⟨hxc, hxS⟩ y ⟨hyN, hyS⟩
    · intro hyd
      have hempty :=
        StripSystemBasics.strip_inter_N_eq_empty hSN hce (Ne.symm hcd.ne) (Ne.symm hed)
      rw [Set.eq_empty_iff_forall_notMem] at hempty
      exact hempty y ⟨hyS, hyd⟩

/-- **No edge from an interior rung-vertex to a different strip.**

PAPER (sixth axiom, second half): *"and there are no other edges between `S_{uv}` and `S_{uw}`"*
together with the fifth axiom *"if `uv, wx ∈ E(J)` with `u,v,w,x` all distinct, then there are no
edges between `S_{uv}` and `S_{wx}`"*.  An edge leaving the strip `S_{cd}` forces its end in
`S_{cd}` into `N_c` or into `N_d`. -/
theorem not_adj_of_interior_of_ne_edge (hSN : IsJStripSystem G J S N)
    {c d a b : U} (hcd : J.Adj c d) (hab : J.Adj a b) (hne : s(a, b) ≠ s(c, d))
    {x y : V} (hx : x ∈ S c d) (hy : y ∈ S a b) (hxc : x ∉ N c) (hxd : x ∉ N d) :
    ¬ G.Adj x y := by
  intro hadj
  by_cases hac : a = c
  · subst hac
    have hbd : b ≠ d := by rintro rfl; exact hne rfl
    exact hxc (StripSystemBasics.mem_N_of_adj hSN hcd hab (Ne.symm hbd) hx hy hadj).1
  · by_cases had : a = d
    · subst had
      have hbc : b ≠ c := by
        rintro rfl
        exact hne (Sym2.eq_swap)
      have hxS : x ∈ S a c := by rw [← StripSystemBasics.strip_symm hSN hcd]; exact hx
      exact hxd (StripSystemBasics.mem_N_of_adj hSN hcd.symm hab (Ne.symm hbc) hxS hy hadj).1
    · by_cases hbc : b = c
      · subst hbc
        have hadne : a ≠ d := fun h => had h
        have hyS : y ∈ S b a := by rw [← StripSystemBasics.strip_symm hSN hab]; exact hy
        exact hxc (StripSystemBasics.mem_N_of_adj hSN hcd hab.symm (Ne.symm hadne) hx hyS hadj).1
      · by_cases hbd : b = d
        · subst hbd
          have hacne : a ≠ c := fun h => hac h
          have hxS : x ∈ S b c := by rw [← StripSystemBasics.strip_symm hSN hcd]; exact hx
          have hyS : y ∈ S b a := by rw [← StripSystemBasics.strip_symm hSN hab]; exact hy
          exact hxd
            (StripSystemBasics.mem_N_of_adj hSN hcd.symm hab.symm (Ne.symm hacne) hxS hyS hadj).1
        · -- the two edges are disjoint
          have hcdne : c ≠ d := hcd.ne
          have habne : a ≠ b := hab.ne
          have hca : c ≠ a := fun h => hac h.symm
          have hcb : c ≠ b := fun h => hbc h.symm
          have hda : d ≠ a := fun h => had h.symm
          have hdb : d ≠ b := fun h => hbd h.symm
          have hnd : [c, d, a, b].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
              not_or]
            tauto
          exact StripSystemBasics.strip_anticomplete hSN hcd hab hnd x hx y hy hadj

/-! ### The repaired statements

Each of the four statements below carries the extra hypothesis

  `(hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b)`

which is the formal content of the paper's *"for each **edge** `uv` of `J`, choose a `uv`-rung
`R_{uv}`"*.  Without it all four are FALSE; see
`ProofAttempts/LineGraphDegree/LineGraphDegree_Refutation.lean` for a machine-checked
counterexample.  (The stronger, more literal clause `R d c = (R c d).reverse` implies `hRsym`
via `List.mem_reverse`.) -/

/-- The chosen rungs live in pairwise disjoint strips, so `K` meets the strip `S_{cd}` in exactly
the vertex set of the rung `R_{cd}`. -/
theorem mem_rung_of_mem_strip (hSN : IsJStripSystem G J S N) {R : U → U → List V}
    (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    (hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b)
    {c d : U} (hcd : J.Adj c d) {x : V}
    (hxK : x ∈ rungVertices J R) (hxS : x ∈ S c d) : x ∈ R c d := by
  obtain ⟨a, b, hab, hxab⟩ := mem_rungVertices_iff.mp hxK
  have hxSab : x ∈ S a b := StripSystemBasics.rung_subset_strip (hR a b hab) x hxab
  have heq : s(a, b) = s(c, d) := StripSystemBasics.edge_eq_of_mem_strips hSN hab hcd hxSab hxS
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hxab
  · exact hRsym _ _ hcd x hxab

/-- **An interior vertex of a rung has no `K`-neighbour outside that rung.**

PAPER (sixth axiom of a `J`-strip system): *"and there are no other edges between `S_{uv}` and
`S_{uw}`"* — an edge leaving the strip forces both its ends into `N_u`. -/
theorem neighbor_mem_rung_of_not_end (hSN : IsJStripSystem G J S N) {R : U → U → List V}
    (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    (hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b)
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) (hxc : x ∉ N c) (hxd : x ∉ N d)
    {y : V} (hyK : y ∈ rungVertices J R) (hadj : G.Adj x y) : y ∈ R c d := by
  have hxS : x ∈ S c d := StripSystemBasics.rung_subset_strip (hR c d hcd) x hx
  obtain ⟨a, b, hab, hyab⟩ := mem_rungVertices_iff.mp hyK
  have hyS : y ∈ S a b := StripSystemBasics.rung_subset_strip (hR a b hab) y hyab
  by_cases hedge : s(a, b) = s(c, d)
  · have hyScd : y ∈ S c d := by
      rw [Sym2.eq_iff] at hedge
      rcases hedge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyS
      · rw [StripSystemBasics.strip_symm hSN hcd]; exact hyS
    exact mem_rung_of_mem_strip hSN hR hRsym hcd hyK hyScd
  · exact absurd hadj (not_adj_of_interior_of_ne_edge hSN hcd hab hedge hxS hyS hxc hxd)

/-- **An interior vertex of a rung has `G|K`-degree `≤ 2`.**

Its `K`-neighbours all lie on its own rung, which is an induced path of `G`. -/
theorem rung_degree_le_two_of_interior (hSN : IsJStripSystem G J S N) {R : U → U → List V}
    (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    (hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b)
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) (hxc : x ∉ N c) (hxd : x ∉ N d) :
    (G.neighborSet x ∩ rungVertices J R).ncard ≤ 2 := by
  classical
  obtain ⟨-, s, t, hpf, hsubS, hsN, htN⟩ := hR c d hcd
  obtain ⟨i, hi, hxi⟩ := List.mem_iff_getElem.mp hx
  set y₁ : V := if h : 0 < i then (R c d)[i - 1]'(by omega) else x with hy₁
  set y₂ : V := if h : i + 1 < (R c d).length then (R c d)[i + 1]'h else x with hy₂
  have hsub : G.neighborSet x ∩ rungVertices J R ⊆ ({y₁, y₂} : Set V) := by
    rintro z ⟨hzadj, hzK⟩
    have hzp : z ∈ R c d :=
      neighbor_mem_rung_of_not_end hSN hR hRsym hcd hx hxc hxd hzK hzadj
    obtain ⟨j, hj, hzj⟩ := List.mem_iff_getElem.mp hzp
    have hadj' : G.Adj ((R c d)[i]'hi) ((R c d)[j]'hj) := by rw [hxi, hzj]; exact hzadj
    rcases (hpf.1.2.2 i j hi hj).mp hadj' with h | h
    · right
      have hij : i + 1 < (R c d).length := by omega
      simp only [Set.mem_singleton_iff, hy₂, dif_pos hij]
      rw [← hzj]
      congr 1
      omega
    · left
      have hi0 : 0 < i := by omega
      simp only [hy₁, dif_pos hi0]
      rw [← hzj]
      congr 1
      omega
  calc (G.neighborSet x ∩ rungVertices J R).ncard ≤ ({y₁, y₂} : Set V).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ 2 := by
        have h := Set.ncard_insert_le y₁ ({y₂} : Set V)
        simpa using h

/-- **An end of a rung has `G|K`-degree `≥ 3`.**

PAPER (sixth axiom, first half): *"`N_u ∩ S_{uv}` is complete to `N_u ∩ S_{uw}`"*.  The `c`-ends
of the `deg_J(c) - 1 ≥ 2` other rungs at `c` are neighbours of `x`, and one more comes either
from the next vertex of `x`'s own rung or — when that rung has length `0`, so that `x` is also
its `d`-end — from the `d`-ends of the other rungs at `d`. -/
theorem three_le_rung_degree_of_end (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) (hxc : x ∈ N c) :
    3 ≤ (G.neighborSet x ∩ rungVertices J R).ncard := by
  obtain ⟨y, hyK, hxy, hyN⟩ := exists_third_neighbour_head hSN hJ hR hcd hx hxc
  exact three_le_rung_degree_aux hSN hJ hR hcd hxc
    (StripSystemBasics.rung_subset_strip (hR c d hcd) x hx) hyK hxy hyN

/-- **The `G|K`-side dichotomy.**  A vertex of the rung `R_{cd}` has `G|K`-degree `≥ 3` exactly
when it is one of the two ends of the rung. -/
theorem three_le_rung_degree_iff (hSN : IsJStripSystem G J S N) (hJ : IsKConnected J 3)
    {R : U → U → List V} (hR : ∀ c d : U, J.Adj c d → IsUVRung G J S N c d (R c d))
    (hRsym : ∀ a b : U, J.Adj a b → ∀ y : V, y ∈ R b a → y ∈ R a b)
    {c d : U} (hcd : J.Adj c d) {x : V} (hx : x ∈ R c d) :
    3 ≤ (G.neighborSet x ∩ rungVertices J R).ncard ↔ (x ∈ N c ∨ x ∈ N d) := by
  constructor
  · intro h3
    by_contra hcon
    have hc1 : x ∉ N c := fun h => hcon (Or.inl h)
    have hc2 : x ∉ N d := fun h => hcon (Or.inr h)
    have hle :=
      rung_degree_le_two_of_interior hSN hR hRsym hcd hx hc1 hc2
    omega
  · rintro (hxc | hxd)
    · obtain ⟨y, hyK, hxy, hyN⟩ := exists_third_neighbour_head hSN hJ hR hcd hx hxc
      exact three_le_rung_degree_aux hSN hJ hR hcd hxc
        (StripSystemBasics.rung_subset_strip (hR c d hcd) x hx) hyK hxy hyN
    · obtain ⟨y, hyK, hxy, hyN⟩ := exists_third_neighbour_last hSN hJ hR hcd hx hxd
      have hxS : x ∈ S d c := by
        rw [← StripSystemBasics.strip_symm hSN hcd]
        exact StripSystemBasics.rung_subset_strip (hR c d hcd) x hx
      exact three_le_rung_degree_aux hSN hJ hR hcd.symm hxd hxS hyK hxy hyN

end StripSide

end Workspace.ProofLemmas.LineGraphDegree
