import Workspace.ProofLemmas.Thm75Endgame
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.Statements.S02.Thm_2_2

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim3Exact

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Workspace.ProofLemmas
open Thm75EndgameHelpers

private theorem all_other_mem_of_subsingleton_diff {V : Type*} {N X : Set V} {a : V}
    (hsub : (N \ X).Subsingleton) (haN : a ∈ N) (haX : a ∉ X) : N \ {a} ⊆ X := by
  intro x hx
  by_contra hxX
  have hxa : x = a := hsub ⟨hx.1, hxX⟩ ⟨haN, haX⟩
  exact hx.2 (by simpa using hxa)

private theorem exists_mem_ne_two {V : Type*} [Finite V] (N : Set V)
    (hcard : 3 ≤ N.ncard) (a b : V) : ∃ x ∈ N, x ≠ a ∧ x ≠ b := by
  classical
  by_contra hno
  push Not at hno
  have hsub : N ⊆ ({a, b} : Set V) := by
    intro x hx
    by_cases hxa : x = a
    · exact Or.inl hxa
    · exact Or.inr (hno x hx hxa)
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hp : ({a, b} : Set V).ncard ≤ 2 := by
    exact (Set.ncard_insert_le a {b}).trans (by simp)
  omega

private theorem odd_path_complete_witness_contra {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (Y : Set V) (hYanti : AnticonnectedSet G Y)
    {p : List V} {s t z : V} (hp : IsPathFrom G p s t)
    (hlen : 2 ≤ pathLength p) (hodd : Odd (pathLength p))
    (hout : ∀ x ∈ p, x ∉ Y)
    (hs : VertexComplete G s Y) (ht : VertexComplete G t Y)
    (honly : ∀ x ∈ p, VertexComplete G x Y → x = s ∨ x = t)
    (hz : VertexComplete G z Y)
    (hznbr : ∀ x ∈ SPGT.interior p, ¬ G.Adj z x) : False := by
  have hlenList : 3 ≤ p.length := by
    simp only [pathLength] at hlen
    omega
  have hendsNot : ¬ G.Adj s t := by
    have h := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hp.1 hlenList
    have h0 := Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
    have hl := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
    rw [h0, hl] at h
    exact h
  have hnoedge : ¬ ∃ u ∈ p, ∃ v ∈ p, EdgeComplete G Y u v := by
    rintro ⟨u, hu, v, hv, huv, huc, hvc⟩
    rcases honly u hu huc with rfl | rfl <;>
      rcases honly v hv hvc with rfl | rfl
    · exact G.irrefl huv
    · exact hendsNot huv
    · exact hendsNot huv.symm
    · exact G.irrefl huv
  obtain ⟨w, hw, hzw⟩ :=
    Workspace.Statements.S02.SPGT.thm_2_2 G hG Y hYanti p s t hp hout hodd hs ht hnoedge z hz
  exact hznbr w hw hzw

private theorem third_prism_path_meets_left_nset_only_at_end
    {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W)
    {a₁ a₂ r₁ b₁ b₂ r₂ z : V} {P₁ P₂ R : List V}
    (hform : FormPrism G ![a₁, a₂, r₁] ![b₁, b₂, r₂] P₁ P₂ R)
    (ha₁N : a₁ ∈ NSet G H K φ c) (hzN : z ∈ NSet G H K φ c) (hzR : z ∈ R) :
    z = r₁ := by
  have hP₁ : IsPathFrom G P₁ a₁ b₁ := by
    simpa using Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path
      (R := ![P₁, P₂, R]) hform (0 : Fin 3)
  have ha₁P : a₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).1
  have hdisj := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint
    (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  by_cases hza : z = a₁
  · subst z
    exact (hdisj a₁ ha₁P hzR).elim
  have hadj : G.Adj a₁ z := nset_clique G H K φ c a₁ ha₁N z hzN (Ne.symm hza)
  have hcross := (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross
    (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    a₁ ha₁P z hzR).mp hadj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hcross
  rcases hcross with ⟨_, hzr⟩ | ⟨hab, _⟩
  · exact hzr
  · exact (hform.2.2.1 0 0 hab).elim

private theorem third_prism_path_meets_right_nset_only_at_end
    {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W)
    {a₁ a₂ r₁ b₁ b₂ r₂ z : V} {P₁ P₂ R : List V}
    (hform : FormPrism G ![a₁, a₂, r₁] ![b₁, b₂, r₂] P₁ P₂ R)
    (hb₁N : b₁ ∈ NSet G H K φ c) (hzN : z ∈ NSet G H K φ c) (hzR : z ∈ R) :
    z = r₂ := by
  have hP₁ : IsPathFrom G P₁ a₁ b₁ := by
    simpa using Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path
      (R := ![P₁, P₂, R]) hform (0 : Fin 3)
  have hb₁P : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁).2
  have hdisj := Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint
    (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
  by_cases hzb : z = b₁
  · subst z
    exact (hdisj b₁ hb₁P hzR).elim
  have hadj : G.Adj b₁ z := nset_clique G H K φ c b₁ hb₁N z hzN (Ne.symm hzb)
  have hcross := (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross
    (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3)) (by decide)
    b₁ hb₁P z hzR).mp hadj
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hcross
  rcases hcross with ⟨hab, _⟩ | ⟨_, hzr⟩
  · exact (hform.2.2.1 0 0 hab.symm).elim
  · exact hzr

private theorem far_rung_end_complete
    {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    {c₁ c₂ : W} (Y X : Set V) (hYanti : AnticonnectedSet G Y)
    (hYK : ∀ y ∈ Y, y ∉ K)
    (hX : X = {x : V | VertexComplete G x Y})
    (hX₂ : X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) = ∅)
    {n₁ n₁' r₁ r₂ b₁ b₂ : V} {P₁ P₂ R : List V}
    (hn₁N : n₁ ∈ NSet G H K φ c₁) (hn₁'N : n₁' ∈ NSet G H K φ c₁)
    (hr₂N : r₂ ∈ NSet G H K φ c₂)
    (hr₁X : r₁ ∈ X) (hn₁'X : n₁' ∈ X)
    (hmiss₂ : (NSet G H K φ c₂ \ X).Subsingleton)
    (hb₁N : b₁ ∈ NSet G H K φ c₂)
    (hform : FormPrism G ![n₁, n₁', r₁] ![b₁, b₂, r₂] P₁ P₂ R)
    (hReven : Even (pathLength R)) (hRlen : 2 ≤ pathLength R)
    (hRK : ∀ v ∈ R, v ∈ K) : r₂ ∈ X := by
  by_contra hr₂X
  have hb₁r₂ : b₁ ≠ r₂ := (hform.2.1 0 2 (by decide)).ne
  have hb₁X : b₁ ∈ X :=
    all_other_mem_of_subsingleton_diff hmiss₂ hr₂N hr₂X
      ⟨hb₁N, by simpa using hb₁r₂⟩
  have hRfrom : IsPathFrom G R r₁ r₂ := by
    simpa using Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path
      (R := ![P₁, P₂, R]) hform (2 : Fin 3)
  have hP₁from : IsPathFrom G P₁ n₁ b₁ := by
    simpa using Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path
      (R := ![P₁, P₂, R]) hform (0 : Fin 3)
  have hb₁P₁ : b₁ ∈ P₁ := (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₁from).2
  have hb₁R : b₁ ∉ R :=
    Workspace.ProofLemmas.HyperprismFromPrism.formPrism_disjoint
      (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3))
      (by decide) b₁ hb₁P₁
  have hb₁r₂adj : G.Adj b₁ r₂ := hform.2.1 0 2 (by decide)
  have hb₁other : ∀ x ∈ R, x ≠ r₂ → ¬ G.Adj b₁ x := by
    intro x hxR hxr₂ hadj
    have hcross := (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross
      (R := ![P₁, P₂, R]) hform (i := (0 : Fin 3)) (j := (2 : Fin 3))
      (by decide) b₁ hb₁P₁ x hxR).mp hadj
    simp only [Matrix.cons_val_zero] at hcross
    rcases hcross with ⟨hbn, _⟩ | ⟨_, hxr⟩
    · exact (hform.2.2.1 0 0 hbn.symm).elim
    · exact hxr₂ hxr
  let q := R ++ [b₁]
  have hq : IsPathFrom G q r₁ b₁ := by
    exact Workspace.ProofLemmas.PathAttach.isPathFrom_concat hRfrom hb₁r₂adj hb₁R hb₁other
  have hqLen : pathLength q = pathLength R + 1 := by
    simp only [q, pathLength, List.length_append, List.length_singleton]
    have hRpos : 0 < R.length := Workspace.ProofLemmas.PathBasics.path_length_pos hRfrom.1
    omega
  have hqodd : Odd (pathLength q) := by
    obtain ⟨k, hk⟩ := hReven
    refine ⟨k, ?_⟩
    omega
  have hqout : ∀ x ∈ q, x ∉ Y := by
    intro x hx hxY
    apply hYK x hxY
    rcases List.mem_append.mp hx with hxR | hxlast
    · exact hRK x hxR
    · have hxb : x = b₁ := by simpa using hxlast
      rw [hxb]
      exact nset_subset_K G H K φ c₂ hb₁N
  have hr₁c : VertexComplete G r₁ Y := by simpa [hX] using hr₁X
  have hb₁c : VertexComplete G b₁ Y := by simpa [hX] using hb₁X
  have honly : ∀ x ∈ q, VertexComplete G x Y → x = r₁ ∨ x = b₁ := by
    intro x hxq hxc
    have hxX : x ∈ X := by simpa [hX] using hxc
    rcases List.mem_append.mp hxq with hxR | hxb
    · have hxK : x ∈ K := hRK x hxR
      have hxN : x ∈ NSet G H K φ c₁ ∪ NSet G H K φ c₂ := by
        by_contra hxN
        have hempty : x ∈ (∅ : Set V) := by
          rw [← hX₂]
          exact ⟨hxX, hxK, hxN⟩
        exact hempty
      rcases hxN with hxN | hxN
      · exact Or.inl (third_prism_path_meets_left_nset_only_at_end
          G H K φ c₁ hform hn₁N hxN hxR)
      · have hxr₂ := third_prism_path_meets_right_nset_only_at_end
          G H K φ c₂ hform hb₁N hxN hxR
        exact (hr₂X (hxr₂ ▸ hxX)).elim
    · right
      simpa using hxb
  have hn₁'c : VertexComplete G n₁' Y := by simpa [hX] using hn₁'X
  have hn₁'no : ∀ x ∈ SPGT.interior q, ¬ G.Adj n₁' x := by
    intro x hxint hadj
    have hxi := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).mp hxint
    rcases List.mem_append.mp hxi.1 with hxR | hxb
    · have hP₂from : IsPathFrom G P₂ n₁' b₂ := by
        simpa using Workspace.ProofLemmas.HyperprismFromPrism.formPrism_path
          (R := ![P₁, P₂, R]) hform (1 : Fin 3)
      have hn₁'P₂ : n₁' ∈ P₂ :=
        (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hP₂from).1
      have hcross := (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_cross
        (R := ![P₁, P₂, R]) hform (i := (1 : Fin 3)) (j := (2 : Fin 3))
        (by decide) n₁' hn₁'P₂ x hxR).mp hadj
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hcross
      rcases hcross with ⟨_, hxr₁⟩ | ⟨hn'b₂, _⟩
      · exact hxi.2.1 hxr₁
      · exact (hform.2.2.1 1 1 hn'b₂).elim
    · have hxb' : x = b₁ := by simpa using hxb
      exact hxi.2.2 hxb'
  exact odd_path_complete_witness_contra G hG Y hYanti hq
    (by rw [hqLen]; omega) hqodd hqout hr₁c hb₁c honly hn₁'c hn₁'no

private theorem alternate_rung_contradiction
    {V W : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K)
    {c₁ c₂ : W} (Y X : Set V) (hYanti : AnticonnectedSet G Y)
    (hYK : ∀ y ∈ Y, y ∉ K)
    (hX : X = {x : V | VertexComplete G x Y})
    (hX₂ : X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) = ∅)
    {n₁ n₂' r₁ r₂ : V} {p : List V}
    (hn₁X : n₁ ∉ X) (hn₂'X : n₂' ∈ X) (hr₁X : r₁ ∈ X) (hr₂X : r₂ ∈ X)
    (hp : IsPathFrom G p n₁ n₂') (hpe : Even (pathLength p)) (hplen : 2 ≤ pathLength p)
    (hpK : ∀ x ∈ p, x ∈ K)
    (hpint : ∀ x ∈ SPGT.interior p,
      x ∉ NSet G H K φ c₁ ∧ x ∉ NSet G H K φ c₂)
    (hpstart : r₁ ∉ p ∧ G.Adj r₁ n₁ ∧
      ∀ x ∈ p, x ≠ n₁ → ¬ G.Adj r₁ x)
    (hpend : r₂ ∉ p ∧ G.Adj r₂ n₂' ∧
      ∀ x ∈ p, x ≠ n₂' → ¬ G.Adj r₂ x) : False := by
  let q := r₁ :: p
  have hq : IsPathFrom G q r₁ n₂' := by
    exact Workspace.ProofLemmas.PathAttach.isPathFrom_cons hp hpstart.2.1 hpstart.1 hpstart.2.2
  have hqLen : pathLength q = pathLength p + 1 := by
    simp only [q, Workspace.ProofLemmas.PathBasics.pathLength_cons]
    have hppos : 0 < p.length := Workspace.ProofLemmas.PathBasics.path_length_pos hp.1
    simp only [pathLength]
    omega
  have hqodd : Odd (pathLength q) := by
    obtain ⟨k, hk⟩ := hpe
    refine ⟨k, ?_⟩
    omega
  have hqout : ∀ x ∈ q, x ∉ Y := by
    intro x hx hxY
    rcases List.mem_cons.mp hx with hxr | hxp
    · subst x
      have hr₁c : VertexComplete G r₁ Y := by simpa [hX] using hr₁X
      exact G.irrefl (hr₁c r₁ hxY)
    · exact hYK x hxY (hpK x hxp)
  have hr₁c : VertexComplete G r₁ Y := by simpa [hX] using hr₁X
  have hn₂'c : VertexComplete G n₂' Y := by simpa [hX] using hn₂'X
  have honly : ∀ x ∈ q, VertexComplete G x Y → x = r₁ ∨ x = n₂' := by
    intro x hxq hxc
    rcases List.mem_cons.mp hxq with rfl | hxp
    · exact Or.inl rfl
    right
    by_cases hxn₂ : x = n₂'
    · exact hxn₂
    have hxX : x ∈ X := by simpa [hX] using hxc
    by_cases hxn₁ : x = n₁
    · exact (hn₁X (hxn₁ ▸ hxX)).elim
    have hxint : x ∈ SPGT.interior p :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hp).mpr
        ⟨hxp, hxn₁, hxn₂⟩
    have hxavoid := hpint x hxint
    have hxN : x ∉ NSet G H K φ c₁ ∪ NSet G H K φ c₂ := by
      rintro (hxN | hxN)
      · exact hxavoid.1 hxN
      · exact hxavoid.2 hxN
    have hempty : x ∈ (∅ : Set V) := by
      rw [← hX₂]
      exact ⟨hxX, hpK x hxp, hxN⟩
    exact hempty.elim
  have hr₂c : VertexComplete G r₂ Y := by simpa [hX] using hr₂X
  have hr₂no : ∀ x ∈ SPGT.interior q, ¬ G.Adj r₂ x := by
    intro x hxint
    have hxi := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hq).mp hxint
    rcases List.mem_cons.mp hxi.1 with hxr | hxp
    · exact (hxi.2.1 hxr).elim
    · exact hpend.2.2 x hxp hxi.2.2
  exact odd_path_complete_witness_contra G hG Y hYanti hq
    (by rw [hqLen]; omega) hqodd hqout hr₁c hn₂'c honly hr₂c hr₂no

private theorem claim3_side {V U W : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (D : List W) (d₁ d₂ : W)
    (hbranch : IsBranch H D) (hfrom : IsTrackFrom H D d₁ d₂)
    (hodd : Odd (trackLength D)) (hlen : 3 ≤ trackLength D)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ d₁) (NSet G H K φ d₂) y)
    (X X₁ Rset : Set V) (r₁ r₂ : V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges D ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₁ : X₁ = X ∩ (NSet G H K φ d₁ ∪ NSet G H K φ d₂))
    (hr₁ : NSet G H K φ d₁ ∩ Rset = {r₁})
    (hr₂ : NSet G H K φ d₂ ∩ Rset = {r₂})
    (hX₂ : X ∩ (K \ (NSet G H K φ d₁ ∪ NSet G H K φ d₂)) = ∅) :
    NSet G H K φ d₁ \ {r₁} ⊆ X₁ := by
  classical
  obtain ⟨col⟩ := happ.1.2
  obtain ⟨hdne, hd₁b, hd₂b, hnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds
      J hJ H happ.1.1 D d₁ d₂ hbranch hfrom (by omega)
  have hcol : col d₁ ≠ col d₂ := colour_ne_of_odd col hfrom hodd
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy =>
    Workspace.ProofLemmas.Thm75DominantOutsideLineGraph.thm75DominantOutsideLineGraph
      G J hJ H K φ happ D d₁ d₂ hbranch hfrom hlen y (hYdom y hy)
  obtain ⟨s₁, s₂, hs₁N, hs₂N, hs₁D, hs₂D, hprisms⟩ :=
    Workspace.ProofLemmas.Thm75PrismThroughBranch.thm75PrismThroughBranch
      G hG J hJ H K φ happ D d₁ d₂ hbranch hfrom hodd hlen
  have hs₁R : s₁ ∈ Rset := by
    rw [hRset]
    exact (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hfrom.1).mp hs₁D
  have hs₂R : s₂ ∈ Rset := by
    rw [hRset]
    exact (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hfrom.1).mp hs₂D
  have hs₁eq : s₁ = r₁ := by
    have hm : s₁ ∈ ({r₁} : Set V) := by
      rw [← hr₁]
      exact ⟨hs₁N, hs₁R⟩
    simpa using hm
  have hs₂eq : s₂ = r₂ := by
    have hm : s₂ ∈ ({r₂} : Set V) := by
      rw [← hr₂]
      exact ⟨hs₂N, hs₂R⟩
    simpa using hm
  subst s₁
  subst s₂
  obtain ⟨hmiss₁, hmiss₂⟩ :=
    Workspace.ProofLemmas.Thm75Claim1.thm75Claim1
      G hG J hJ H K φ happ D d₁ d₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom
  rw [← hX] at hmiss₁ hmiss₂
  intro n₁ hn₁
  rw [hX₁]
  refine ⟨?_, Or.inl hn₁.1⟩
  by_contra hn₁X
  have hn₁r₁ : n₁ ≠ r₁ := by simpa using hn₁.2
  have hrest₁ : NSet G H K φ d₁ \ {n₁} ⊆ X :=
    all_other_mem_of_subsingleton_diff hmiss₁ hn₁.1 hn₁X
  have hr₁X : r₁ ∈ X := hrest₁ ⟨hs₁N, by simpa using hn₁r₁.symm⟩
  obtain ⟨n₁', hn₁'N, hn₁'r₁, hn₁'n₁⟩ :=
    exists_mem_ne_two (NSet G H K φ d₁)
      (Thm75DominanceTriangles.three_le_nset_ncard
        G H K φ d₁ hd₁b) r₁ n₁
  have hn₁'X : n₁' ∈ X := hrest₁ ⟨hn₁'N, by simpa using hn₁'n₁⟩
  obtain ⟨b₁, b₂, P₁, P₂, R, hb₁N, hb₂N, hform,
      hP₁even, hP₂even, hReven, hP₁len, hP₂len, hRlen, hP₁K, hP₂K, hRK⟩ :=
    hprisms n₁ n₁' hn₁.1 hn₁'N hn₁r₁ hn₁'r₁ hn₁'n₁.symm
  have hr₂X : r₂ ∈ X := far_rung_end_complete
    G hG H K φ Y X hYanti hYK hX hX₂ hn₁.1 hn₁'N hs₂N hr₁X hn₁'X hmiss₂
      hb₁N hform hReven hRlen hRK
  obtain ⟨n₂, hn₂N, hn₂r₂, hrest₂⟩ :
      ∃ n₂, n₂ ∈ NSet G H K φ d₂ ∧ n₂ ≠ r₂ ∧
        NSet G H K φ d₂ \ {n₂} ⊆ X := by
    by_cases hall : NSet G H K φ d₂ ⊆ X
    · obtain ⟨n₂, hn₂N, hn₂r₂⟩ := nset_ne G H K φ d₂ hd₂b r₂
      exact ⟨n₂, hn₂N, hn₂r₂, fun _ hz => hall hz.1⟩
    · obtain ⟨n₂, hn₂N, hn₂X⟩ := Set.not_subset.mp hall
      have hn₂r₂ : n₂ ≠ r₂ := fun h => hn₂X (h ▸ hr₂X)
      exact ⟨n₂, hn₂N, hn₂r₂,
        all_other_mem_of_subsingleton_diff hmiss₂ hn₂N hn₂X⟩
  obtain ⟨n₂', hn₂'N, hn₂'r₂, hn₂'n₂⟩ :=
    exists_mem_ne_two (NSet G H K φ d₂)
      (Thm75DominanceTriangles.three_le_nset_ncard
        G H K φ d₂ hd₂b) r₂ n₂
  have hn₂'X : n₂' ∈ X := hrest₂ ⟨hn₂'N, by simpa using hn₂'n₂⟩
  obtain ⟨e₁, he₁, he₁d, hn₁eq⟩ := hn₁.1
  obtain ⟨e₂, he₂, he₂d, hn₂'eq⟩ := hn₂'N
  have he₁D : e₁ ∉ trackEdges D := by
    intro he₁D
    have hm : n₁ ∈ NSet G H K φ d₁ ∩ Rset := by
      refine ⟨hn₁.1, ?_⟩
      rw [hRset]
      exact ⟨e₁, he₁, he₁D, hn₁eq⟩
    rw [hr₁] at hm
    exact hn₁r₁ (by simpa using hm)
  have he₂D : e₂ ∉ trackEdges D := by
    intro he₂D
    have hm : n₂' ∈ NSet G H K φ d₂ ∩ Rset := by
      refine ⟨⟨e₂, he₂, he₂d, hn₂'eq⟩, ?_⟩
      rw [hRset]
      exact ⟨e₂, he₂, he₂D, hn₂'eq⟩
    rw [hr₂] at hm
    exact hn₂'r₂ (by simpa using hm)
  obtain ⟨p, hp, hpe, hplen, hpK, hpint, hpfront, hpback⟩ :=
    exists_even_rung_path G hJ happ.1.1 col K φ hbranch hfrom hcol hd₁b hd₂b hdne
      (by omega) he₁ he₂ he₁d.2 he₂d.2 he₁D he₂D
  have hr₁I : r₁ ∈ NSet G H K φ d₁ ∩ Rset := by rw [hr₁]; simp
  have hr₂I : r₂ ∈ NSet G H K φ d₂ ∩ Rset := by rw [hr₂]; simp
  obtain ⟨f₁, hf₁, hf₁d, hr₁eq⟩ := hr₁I.1
  obtain ⟨f₂, hf₂, hf₂d, hr₂eq⟩ := hr₂I.1
  have hf₁D : f₁ ∈ trackEdges D := by
    rw [hRset] at hr₁I
    obtain ⟨g, hg, hgD, hr₁g⟩ := hr₁I.2
    have hfg : f₁ = g := phi_inj φ hf₁ hg (hr₁eq.symm.trans hr₁g)
    exact hfg ▸ hgD
  have hf₂D : f₂ ∈ trackEdges D := by
    rw [hRset] at hr₂I
    obtain ⟨g, hg, hgD, hr₂g⟩ := hr₂I.2
    have hfg : f₂ = g := phi_inj φ hf₂ hg (hr₂eq.symm.trans hr₂g)
    exact hfg ▸ hgD
  have hf₁e₁ : f₁ ≠ e₁ := by
    intro h
    subst f₁
    exact hn₁r₁ (hn₁eq.trans hr₁eq.symm)
  have hf₂e₂ : f₂ ≠ e₂ := by
    intro h
    subst f₂
    exact hn₂'r₂ (hn₂'eq.trans hr₂eq.symm)
  have hpstart : r₁ ∉ p ∧ G.Adj r₁ n₁ ∧
      ∀ x ∈ p, x ≠ n₁ → ¬ G.Adj r₁ x := by
    simpa [hr₁eq, hn₁eq] using hpfront f₁ hf₁ hf₁D hf₁d.2 hf₁e₁
  have hpend : r₂ ∉ p ∧ G.Adj r₂ n₂' ∧
      ∀ x ∈ p, x ≠ n₂' → ¬ G.Adj r₂ x := by
    simpa [hr₂eq, hn₂'eq] using hpback f₂ hf₂ hf₂D hf₂d.2 hf₂e₂
  have hp' : IsPathFrom G p n₁ n₂' := by
    simpa [hn₁eq, hn₂'eq] using hp
  exact (alternate_rung_contradiction G hG H K φ Y X hYanti hYK hX hX₂
    hn₁X hn₂'X hr₁X hr₂X hp' hpe hplen hpK hpint hpstart hpend).elim

private theorem isBranch_reverse {W : Type*} {H : SimpleGraph W} {q : List W}
    (hq : IsBranch H q) : IsBranch H q.reverse := by
  refine ⟨Workspace.ProofLemmas.TrackSlice.isTrackList_reverse hq.1, ?_, ?_⟩
  · intro v hv
    exact hq.2.1 v (Workspace.ProofLemmas.TrackSlice.mem_trackInterior_reverse.mp hv)
  · intro q' hq' hq'int hsub hverts
    have hsub' : trackEdges q ⊆ trackEdges q' := by
      simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using hsub
    have hverts' : ∀ v ∈ q, v ∈ q' := by
      intro v hv
      exact hverts v (by simpa using hv)
    have heq := hq.2.2 q' hq' hq'int hsub' hverts'
    simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using heq

theorem thm75Claim3Exact {V U W : Type*} [Fintype V] [DecidableEq V]
    [Fintype U] [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (X X₁ Rset : Set V) (r₁ r₂ : V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hr₁ : NSet G H K φ c₁ ∩ Rset = {r₁})
    (hr₂ : NSet G H K φ c₂ ∩ Rset = {r₂})
    (hX₂ : X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) = ∅) :
    (NSet G H K φ c₁ \ {r₁} ⊆ X₁) ∧
      (NSet G H K φ c₂ \ {r₂} ⊆ X₁) := by
  refine ⟨claim3_side G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen
    Y hYne hYanti hYdom X X₁ Rset r₁ r₂ hX hRset hX₁ hr₁ hr₂ hX₂, ?_⟩
  have hbranchRev : IsBranch H B.reverse := isBranch_reverse hbranch
  have hfromRev : IsTrackFrom H B.reverse c₂ c₁ :=
    Workspace.ProofLemmas.TrackSlice.isTrackFrom_reverse hfrom
  have hoddRev : Odd (trackLength B.reverse) := by
    simpa [trackLength] using hodd
  have hlenRev : 3 ≤ trackLength B.reverse := by
    simpa [trackLength] using hlen
  have hdomRev : ∀ y ∈ Y,
      IsDominantFor G (NSet G H K φ c₂) (NSet G H K φ c₁) y := by
    intro y hy
    exact ⟨(hYdom y hy).2, (hYdom y hy).1⟩
  have hRsetRev : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B.reverse ∧ x = (↑(φ ⟨e, he⟩) : V)} := by
    simpa [Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse] using hRset
  have hX₁Rev : X₁ = X ∩ (NSet G H K φ c₂ ∪ NSet G H K φ c₁) := by
    simpa [Set.union_comm] using hX₁
  have hX₂Rev : X ∩ (K \ (NSet G H K φ c₂ ∪ NSet G H K φ c₁)) = ∅ := by
    simpa [Set.union_comm] using hX₂
  exact claim3_side G hG J hJ H K φ happ B.reverse c₂ c₁ hbranchRev hfromRev
    hoddRev hlenRev Y hYne hYanti hdomRev X X₁ Rset r₂ r₁ hX hRsetRev hX₁Rev
      hr₂ hr₁ hX₂Rev

/-- The §7.5 endgame with Claim (3) supplied by the exact proof above. -/
theorem thm75EndgameExact {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
    [Fintype W]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (H : SimpleGraph W) (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    (happ : IsAppearance G J H K)
    (B : List W) (c₁ c₂ : W)
    (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hodd : Odd (trackLength B)) (hlen : 3 ≤ trackLength B)
    (Y : Set V) (hYne : Y.Nonempty) (hYanti : AnticonnectedSet G Y)
    (hYdom : ∀ y ∈ Y, IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y)
    (hYmax : ∀ Y' : Set V, Y ⊆ Y' → AnticonnectedSet G Y' →
      (∀ y ∈ Y', IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) y) → Y' = Y)
    (X X₀ X₁ Rset S T : Set V)
    (hX : X = {x : V | VertexComplete G x Y})
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)})
    (hX₀ : X₀ = X \ K)
    (hX₁ : X₁ = X ∩ (NSet G H K φ c₁ ∪ NSet G H K φ c₂))
    (hS : S = Rset \ X₁) (hT : T = (K \ Rset) \ X₁)
    (L M : Set V)
    (hLM : L ∪ M = (X₀ ∪ X₁ ∪ Y)ᶜ) (hLMdisj : Disjoint L M)
    (hLManti : Anticomplete G L M) (hSL : S ⊆ L) (hTM : T ⊆ M) :
    AdmitsBalancedSkewPartition G := by
  exact Workspace.ProofLemmas.Thm75Endgame.thm75Endgame_of_claim3
    G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen Y hYne hYanti hYdom hYmax
      X X₀ X₁ Rset S T hX hRset hX₀ hX₁ hS hT L M hLM hLMdisj hLManti hSL hTM
      (fun r₁ r₂ hr₁ hr₂ hX₂ =>
        thm75Claim3Exact G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom hodd hlen
          Y hYne hYanti hYdom X X₁ Rset r₁ r₂ hX hRset hX₁ hr₁ hr₂ hX₂)

end Workspace.ProofLemmas.Thm75Claim3Exact
