import Mathlib
import Workspace.Types.Core
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm192Setup
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.AntiholeCompletion
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.SegmentBasics
import Workspace.ProofLemmas.YEdgeConfiguration
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.Statements.S15.Thm_15_7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm192Infra

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem reachable_induce_mono {G : SimpleGraph V} {A B : Set V} (hAB : A ⊆ B)
    {u v : V} (hu : u ∈ A) (hv : v ∈ A)
    (hr : (G.induce A).Reachable ⟨u, hu⟩ ⟨v, hv⟩) :
    (G.induce B).Reachable ⟨u, hAB hu⟩ ⟨v, hAB hv⟩ := by
  obtain ⟨p⟩ := hr
  exact ⟨SimpleGraph.Walk.map
    (⟨fun w => ⟨w.1, hAB w.2⟩, fun {_ _} h => h⟩ : (G.induce A) →g (G.induce B)) p⟩

theorem exists_noncut_outside {G : SimpleGraph V} {A F : Set V}
    (hA : ConnectedSet G A) (hF : ConnectedSet G F) (hFA : F ⊆ A) (hne : F ≠ A)
    (hFne : F.Nonempty) :
    ∃ f ∈ A \ F, ConnectedSet G (A \ {f}) := by
  obtain ⟨r, hrF⟩ := hFne
  have hrA : r ∈ A := hFA hrF
  have hAFne : (A \ F).Nonempty := by
    rcases Set.eq_empty_or_nonempty (A \ F) with h | h
    · exact absurd (Set.Subset.antisymm hFA (Set.diff_eq_empty.mp h)) hne
    · exact h
  haveI : Nonempty ↥(A \ F) := ⟨⟨hAFne.choose, hAFne.choose_spec⟩⟩
  obtain ⟨fz, hfmax⟩ :=
    Finite.exists_max (fun z : ↥(A \ F) => (G.induce A).dist ⟨r, hrA⟩ ⟨z.1, z.2.1⟩)
  set f : V := (fz : V) with hfdef
  have hf : f ∈ A \ F := fz.2
  have hfmax' : ∀ (x : V) (hxA : x ∈ A) (hxF : x ∉ F),
      (G.induce A).dist ⟨r, hrA⟩ ⟨x, hxA⟩ ≤ (G.induce A).dist ⟨r, hrA⟩ ⟨f, hf.1⟩ :=
    fun x hxA hxF => hfmax ⟨x, ⟨hxA, hxF⟩⟩
  refine ⟨f, hf, ?_⟩
  have hFT : F ⊆ A \ {f} := by
    intro y hy
    refine ⟨hFA hy, ?_⟩
    intro hyf
    simp only [Set.mem_singleton_iff] at hyf
    exact hf.2 (hyf ▸ hy)
  have hrT : r ∈ A \ {f} := hFT hrF
  have reachF : ∀ (y : V) (hy : y ∈ F),
      (G.induce (A \ {f})).Reachable ⟨r, hFT hrF⟩ ⟨y, hFT hy⟩ :=
    fun y hy => reachable_induce_mono hFT hrF hy (hF ⟨r, hrF⟩ ⟨y, hy⟩)
  have key : ∀ (n : ℕ) (x : V) (hxA : x ∈ A) (hxF : x ∉ F) (hxf : x ∉ ({f} : Set V)),
      (G.induce A).dist ⟨r, hrA⟩ ⟨x, hxA⟩ ≤ n →
      (G.induce (A \ {f})).Reachable ⟨r, hrT⟩ ⟨x, ⟨hxA, hxf⟩⟩ := by
    intro n
    induction n with
    | zero =>
        intro x hxA hxF hxf hd
        have h0 : (G.induce A).dist ⟨r, hrA⟩ ⟨x, hxA⟩ = 0 := by omega
        have hxr : (⟨r, hrA⟩ : ↥A) = ⟨x, hxA⟩ :=
          ((hA ⟨r, hrA⟩ ⟨x, hxA⟩).dist_eq_zero_iff).mp h0
        have hval : r = x := congrArg Subtype.val hxr
        exact absurd (hval ▸ hrF) hxF
    | succ m ih =>
        intro x hxA hxF hxf hd
        by_cases h0 : (G.induce A).dist ⟨r, hrA⟩ ⟨x, hxA⟩ = 0
        · have hxr : (⟨r, hrA⟩ : ↥A) = ⟨x, hxA⟩ :=
            ((hA ⟨r, hrA⟩ ⟨x, hxA⟩).dist_eq_zero_iff).mp h0
          have hval : r = x := congrArg Subtype.val hxr
          exact absurd (hval ▸ hrF) hxF
        · obtain ⟨w, hw⟩ := (hA ⟨r, hrA⟩ ⟨x, hxA⟩).exists_walk_length_eq_dist
          set d := (G.induce A).dist ⟨r, hrA⟩ ⟨x, hxA⟩ with hddef
          have hd1 : 1 ≤ d := by omega
          have hklt : d - 1 < w.length := by omega
          have hadj := w.adj_getVert_succ hklt
          have hk1 : (d - 1) + 1 = w.length := by omega
          have hend : w.getVert ((d - 1) + 1) = ⟨x, hxA⟩ := by
            rw [hk1]; exact w.getVert_length
          have hdy : (G.induce A).dist ⟨r, hrA⟩ (w.getVert (d - 1)) ≤ d - 1 := by
            have h := SimpleGraph.dist_le (w.take (d - 1))
            rw [SimpleGraph.Walk.take_length] at h
            omega
          have hbridge : (G.induce A).dist ⟨r, hrA⟩
                ⟨((w.getVert (d - 1) : ↥A) : V), (w.getVert (d - 1)).2⟩
              = (G.induce A).dist ⟨r, hrA⟩ (w.getVert (d - 1)) := rfl
          have hyf : ((w.getVert (d - 1) : ↥A) : V) ≠ f := by
            intro he
            have heq : (w.getVert (d - 1) : ↥A) = ⟨f, hf.1⟩ := Subtype.ext he
            rw [heq] at hdy
            have hmx := hfmax' x hxA hxF
            omega
          have hadjG : G.Adj ((w.getVert (d - 1) : ↥A) : V) x := by
            have hthis : (G.induce A).Adj (w.getVert (d - 1)) (w.getVert ((d - 1) + 1)) := hadj
            rw [hend] at hthis
            exact hthis
          by_cases hyF : ((w.getVert (d - 1) : ↥A) : V) ∈ F
          · refine (reachF _ hyF).trans (SimpleGraph.Adj.reachable ?_)
            exact hadjG
          · have hreach := ih ((w.getVert (d - 1) : ↥A) : V) (w.getVert (d - 1)).2 hyF
              (by simpa using hyf) (by omega)
            refine hreach.trans (SimpleGraph.Adj.reachable ?_)
            exact hadjG
  intro p q
  have hall : ∀ (z : ↥(A \ {f})), (G.induce (A \ {f})).Reachable ⟨r, hrT⟩ z := by
    rintro ⟨z, hzA, hzf⟩
    by_cases hzF : z ∈ F
    · exact reachF z hzF
    · exact key ((G.induce A).dist ⟨r, hrA⟩ ⟨z, hzA⟩) z hzA hzF hzf le_rfl
  exact (hall p).symm.trans (hall q)

theorem holeFromCut {G : SimpleGraph V} {A : Set V} {P : List V} {a b z u : V} {i : ℕ}
    (hP : IsPathFrom G P a b) (hPint : ∀ w ∈ SPGT.interior P, w ∈ A)
    (hzA : VertexAnticomplete G z A) (hza : G.Adj z a) (hzb : G.Adj z b)
    (hzu : G.Adj z u) (hzP : z ∉ P) (huP : u ∉ P)
    (hi : 0 < i) (hilen : i + 2 ≤ P.length)
    (huadj : ∀ (k : ℕ) (hk : k < P.length), i ≤ k → (G.Adj u (P[k]'hk) ↔ k = i)) :
    IsHoleList G (z :: u :: P.drop i) := by
  have hPl : IsPathList G P := hP.1
  have hpos : 0 < P.length := PathBasics.path_length_pos hPl
  set n : ℕ := P.length - 1 with hndef
  have hn : n < P.length := by omega
  have hin : i < n := by omega
  have hilt : i < P.length := by omega
  have hbeq : (P[n]'hn) = b := PathBasics.getElem_last_of_getLast? hP.2.2 hpos
  have hslice : (P.drop i).take (n - i + 1) = P.drop i := by
    refine List.take_of_length_le ?_
    simp only [List.length_drop]
    omega
  have hpsl : IsPathFrom G ((P.drop i).take (n - i + 1)) (P[i]'hilt) b := by
    have := PathBasics.isPathFrom_slice hPl hin hn
    rwa [hbeq] at this
  -- the slice has length `n - i + 1`
  have hsllen : ((P.drop i).take (n - i + 1)).length = n - i + 1 :=
    PathBasics.length_slice P (le_of_lt hin) hn
  have hplen : 1 ≤ pathLength ((P.drop i).take (n - i + 1)) := by
    rw [PathBasics.pathLength_eq, hsllen]; omega
  have hsub : ∀ x ∈ (P.drop i).take (n - i + 1), x ∈ P := by
    intro x hx
    obtain ⟨k, hk, _, _, rfl⟩ := (PathBasics.mem_slice_iff P (le_of_lt hin) hn).mp hx
    exact List.getElem_mem hk
  rw [← hslice]
  refine PrismBasics.isHoleList_of_path_add_two_vertices hpsl hplen
    ((huadj i hilt le_rfl).mpr rfl) hzb hzu.symm (fun hc => huP (hsub _ hc))
    (fun hc => hzP (hsub _ hc)) ?_ ?_ ?_ ?_
  · rw [← hbeq]
    intro hc
    exact absurd ((huadj n hn (by omega)).mp hc) (by omega)
  · exact hzA _ (hPint _ (PathBasics.getElem_mem_interior hPl hilt hi (by omega)))
  · intro x hx
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (PathBasics.mem_interior_slice_iff hPl hin hn).mp hx
    intro hc
    exact absurd ((huadj k hk (by omega)).mp hc) (by omega)
  · intro x hx
    obtain ⟨k, hk, hk1, hk2, rfl⟩ := (PathBasics.mem_interior_slice_iff hPl hin hn).mp hx
    exact hzA _ (hPint _ (PathBasics.getElem_mem_interior hPl hk (by omega) (by omega)))

theorem antipathExtendToAntihole {G : SimpleGraph V} (hG : InF6 G)
    {W : Set V} {u v : V} {Q R : List V}
    (hadjuv : G.Adj u v)
    (hQ : IsAntipathFrom G Q u v) (hQint : ∀ w ∈ SPGT.interior Q, w ∈ W)
    (hR : IsAntipathFrom G R v u) (hRlen : 4 ≤ R.length)
    (hRint : ∀ w ∈ SPGT.interior R, VertexComplete G w W)
    {C : List V} (hC : IsHoleList G C) (hClen : 4 < holeLength C)
    {c₀ c₁ c₂ : V} (h01 : c₀ ≠ c₁) (h02 : c₀ ≠ c₂) (h12 : c₁ ≠ c₂)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hd₀ : c₀ ∈ Q ++ SPGT.interior R) (hd₁ : c₁ ∈ Q ++ SPGT.interior R)
    (hd₂ : c₂ ∈ Q ++ SPGT.interior R) :
    False := by
  classical
  have hQ3 : 3 ≤ Q.length := AntiholeCompletion.three_le_length_of_antipath hQ hadjuv
  have hQp : IsPathFrom Gᶜ Q u v := hQ
  have hRp : IsPathFrom Gᶜ R v u := hR
  have hRl : IsPathList Gᶜ R := hRp.1
  have hv0 : R[0]'(show 0 < R.length by omega) = v :=
    PathBasics.getElem_zero_of_head? hRp.2.1 (by omega)
  have hulast : R[R.length - 1]'(show R.length - 1 < R.length by omega) = u :=
    PathBasics.getElem_last_of_getLast? hRp.2.2 (by omega)
  obtain ⟨w₀, hw₀eq⟩ : ∃ w : V, R[1]'(show 1 < R.length by omega) = w := ⟨_, rfl⟩
  obtain ⟨w₁, hw₁eq⟩ :
      ∃ w : V, R[R.length - 2]'(show R.length - 2 < R.length by omega) = w := ⟨_, rfl⟩
  have hIR : IsPathFrom Gᶜ (SPGT.interior R) w₀ w₁ := by
    have he : SPGT.interior R = (R.drop 1).take (R.length - 2 - 1 + 1) := by
      rw [PathBasics.interior_eq_drop_take]; congr 1; omega
    rw [he, ← hw₀eq, ← hw₁eq]
    exact PathBasics.isPathFrom_slice hRl (by omega) (by omega)
  have hdisj : ∀ x ∈ Q, x ∉ SPGT.interior R := by
    intro x hx hxIR
    have hmem := (PathBasics.mem_interior_iff_of_pathFrom hRp).mp hxIR
    have hxint : x ∈ SPGT.interior Q :=
      (PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hx, hmem.2.2, hmem.2.1⟩
    exact G.irrefl ((hRint x hxIR) x (hQint x hxint))
  have hcross : ∀ x ∈ Q, ∀ y ∈ SPGT.interior R,
      (Gᶜ.Adj x y ↔ (x = v ∧ y = w₀) ∨ (x = u ∧ y = w₁)) := by
    intro x hx y hy
    obtain ⟨k, hk, hk1, hk2, hkv⟩ := PathBasics.exists_getElem_of_mem_interior hRl hy
    constructor
    · intro hadj
      by_cases hxu : x = u
      · refine Or.inr ⟨hxu, ?_⟩
        have hadj' : Gᶜ.Adj (R[R.length - 1]'(show R.length - 1 < R.length by omega))
            (R[k]'hk) := by rw [hulast, hkv, ← hxu]; exact hadj
        have hidx := (PathBasics.path_adj_iff hRl
          (show R.length - 1 < R.length by omega) hk).mp hadj'
        have hkeq : k = R.length - 2 := by omega
        subst hkeq
        exact hkv.symm.trans hw₁eq
      · by_cases hxv : x = v
        · refine Or.inl ⟨hxv, ?_⟩
          have hadj' : Gᶜ.Adj (R[0]'(show 0 < R.length by omega)) (R[k]'hk) := by
            rw [hv0, hkv, ← hxv]; exact hadj
          have hidx := (PathBasics.path_adj_iff hRl
            (show 0 < R.length by omega) hk).mp hadj'
          have hkeq : k = 1 := by omega
          subst hkeq
          exact hkv.symm.trans hw₀eq
        · exfalso
          have hxint : x ∈ SPGT.interior Q :=
            (PathBasics.mem_interior_iff_of_pathFrom hQp).mpr ⟨hx, hxu, hxv⟩
          exact hadj.2 (((hRint y hy) x (hQint x hxint)).symm)
    · rintro (⟨hxv, hyw⟩ | ⟨hxu, hyw⟩)
      · rw [hxv, hyw, ← hw₀eq, ← hv0]
        exact (PathBasics.path_adj_iff hRl (by omega) (by omega)).mpr (Or.inl (by omega))
      · rw [hxu, hyw, ← hw₁eq, ← hulast]
        exact (PathBasics.path_adj_iff hRl (by omega) (by omega)).mpr (Or.inr (by omega))
  have hlen : 4 ≤ Q.length + (SPGT.interior R).length := by
    rw [PathBasics.interior_length]; omega
  have hD : IsAntiholeList G (Q ++ SPGT.interior R) :=
    PathGlue.glue_hole hQp hIR hdisj hcross hlen
  have hDl : 4 < holeLength (Q ++ SPGT.interior R) := by
    simp only [holeLength, List.length_append, PathBasics.interior_length]
    omega
  have hncard := _root_.Workspace.Statements.S15.SPGT.thm_15_7 G hG C
    (Q ++ SPGT.interior R) hC hClen hD hDl
  have hsub : ({c₀, c₁, c₂} : Set V) ⊆
      {w : V | w ∈ C} ∩ {w : V | w ∈ Q ++ SPGT.interior R} := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hc₀, hd₀⟩
    · exact ⟨hc₁, hd₁⟩
    · exact ⟨hc₂, hd₂⟩
  have h3 : ({c₀, c₁, c₂} : Set V).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [h01, h02]) (Set.toFinite _),
      Set.ncard_pair h12]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem uniqueNeighbourSetForm {G : SimpleGraph V} {F : Set V} {v a : V} :
    {f ∈ F | G.Adj v f} = ({a} : Set V) ↔
      (a ∈ F ∧ G.Adj v a ∧ ∀ b ∈ F, G.Adj v b → b = a) := by
  constructor
  · intro h
    have ha : a ∈ {f ∈ F | G.Adj v f} := by rw [h]; exact rfl
    refine ⟨ha.1, ha.2, ?_⟩
    intro b hb hvb
    have : b ∈ ({a} : Set V) := by rw [← h]; exact ⟨hb, hvb⟩
    simpa using this
  · rintro ⟨haF, hva, huniq⟩
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hb, hvb⟩; exact huniq b hb hvb
    · rintro rfl; exact ⟨haF, hva⟩

theorem oddWheelFromParities {G : SimpleGraph V} (hG : InF7 G) {C : List V} {W : Set V}
    (hW : IsWheel G C W) {u v : V}
    (hu : ¬ VertexComplete G u W) (hv : ¬ VertexComplete G v W)
    (hpar : OppositeWheelParity G C W u v) :
    False := by
  classical
  have hBerge : Berge G := hG.1.1.1.1
  have hC : IsHoleList G C := hW.1.1
  have hn6 : 6 ≤ C.length := hW.1.2
  have hn : 0 < C.length := by omega
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hW
  have hno : ¬ IsOddWheel G C W := fun h => hG.2.1 ⟨C, W, h⟩
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hpar.2.1
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hpar.2.2.1
  have hncI : ¬ SegmentBasics.CycVert G W C i := by
    rw [OddWheelParityFacts.cycVert_iff' hn hi, hiu]; exact hu
  have hncJ : ¬ SegmentBasics.CycVert G W C j := by
    rw [OddWheelParityFacts.cycVert_iff' hn hj, hjv]; exact hv
  have hij : i ≠ j := by
    rintro rfl
    exact hpar.1 (hiu.symm.trans hjv)
  have hcount : WheelParity.cycCount G W C i % 2 ≠ WheelParity.cycCount G W C j % 2 := by
    intro h
    refine hpar.2.2.2 ?_
    have hs := (WheelParity.sameWheelParity_iff hC heven hi hj hij).mpr h
    rwa [hiu, hjv] at hs
  -- the running count has the same parity at any two non-`W`-complete positions
  have contra : ∀ s m : ℕ, s < m → m < C.length →
      ¬ SegmentBasics.CycVert G W C s → ¬ SegmentBasics.CycVert G W C m →
      WheelParity.cycCount G W C m % 2 = WheelParity.cycCount G W C s % 2 := by
    intro s m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro hsm hmC hs hm
      have hex : ∃ t₀, s ≤ t₀ ∧ t₀ ≤ m - 1 ∧ ¬ SegmentBasics.CycVert G W C t₀ ∧
          ∀ t, t₀ < t → t ≤ m - 1 → SegmentBasics.CycVert G W C t := by
        have hspec := Nat.findGreatest_spec
          (P := fun t => ¬ SegmentBasics.CycVert G W C t ∧ s ≤ t)
          (m := s) (n := m - 1) (by omega) ⟨hs, le_rfl⟩
        refine ⟨_, hspec.2, Nat.findGreatest_le _, hspec.1, ?_⟩
        intro t h1 h2
        by_contra hcv
        exact Nat.findGreatest_is_greatest h1 h2 ⟨hcv, le_trans hspec.2 (le_of_lt h1)⟩
      obtain ⟨t₀, ht₀s, ht₀m, ht₀nc, ht₀max⟩ := hex
      set L : ℕ := m - 1 - t₀ with hLdef
      have hrun : ∀ t < L, SegmentBasics.CycVert G W C (t₀ + 1 + t) := by
        intro t htL
        exact ht₀max (t₀ + 1 + t) (by omega) (by omega)
      have hnext : ¬ SegmentBasics.CycVert G W C (t₀ + 1 + L) := by
        rw [show t₀ + 1 + L = m by omega]; exact hm
      have hprev : ¬ SegmentBasics.CycVert G W C (t₀ + 1 + (C.length - 1)) := by
        refine fun hcv => ht₀nc ((SegmentBasics.cycVert_congr ?_).mp hcv)
        rw [show t₀ + 1 + (C.length - 1) = t₀ + C.length by omega, Nat.add_mod_right]
      have hcc := OddWheelParityFacts.cycCount_run hC hrun hnext
      rw [show t₀ + 1 + L = m by omega] at hcc
      have hstep : WheelParity.cycCount G W C (t₀ + 1) = WheelParity.cycCount G W C t₀ := by
        rw [WheelParity.cycCount_succ, if_neg]
        · omega
        · exact fun hce => ht₀nc (YEdgeConfiguration.cycVert_of_cycEdge hC hce)
      have hLpar : (L - 1) % 2 = 0 := by
        rcases Nat.eq_zero_or_pos L with h0 | hL1
        · rw [h0]
        · have h2 : L + 1 ≤ C.length := by omega
          have hodd := YEdgeConfiguration.run_odd' hC hW hno hL1 h2 hrun hnext hprev
          omega
      have ht₀par : WheelParity.cycCount G W C t₀ % 2 = WheelParity.cycCount G W C s % 2 := by
        rcases eq_or_lt_of_le ht₀s with he | hlt
        · rw [he]
        · exact ih t₀ (by omega) hlt (by omega) hs ht₀nc
      omega
  rcases lt_trichotomy i j with h | h | h
  · exact hcount (contra i j h hj hncI hncJ).symm
  · exact hij h
  · exact hcount (contra j i h hi hncJ hncI)

/-! ### Two `W`-complete vertices in the interior of an `x₀`–`x₁` path

Claim (2) of 19.2 delivers, in its right disjunct, an `x₀`–`x₁` path `P` with interior in
`A` together with **at least two** `Y₀`-complete edges of `P`.  The paper cites this twice —
at claim (3) (*"all members of `Y₀` have at least two neighbours in `A` (since `A` contains
two `Y₀`-complete vertices)"*) and at claim (9) (*"by (2) there are two `Y₀`-complete
vertices in `A`"*) — and shorthands it as *"is a wheel"* at claims (6) and (10).  The
shorthand is lossy: `IsWheel` carries no clause giving a hub vertex a rim neighbour, and can
be mined for at most **one** such vertex.  The real content is the edge count, and this is
the lemma that converts it.

The argument inspects `W` only through `EdgeComplete`/`VertexComplete`, so it is stated for
an arbitrary `W` (`Y \ {y}` at every call site).  It needs neither `Berge` nor any length
hypothesis:

* `Set.one_lt_ncard` produces two *distinct* `Sym2` edges of `P`, both `W`-complete;
* `x₀x₁` is not an edge (`Thm192Setup.x0_not_adj_x1`), so each of them has at most one end
  in `{x₀,x₁}` and therefore yields an end in `interior P`;
* if those two ends coincide at `c`, the two remaining ends are distinct and cannot both lie
  in `{x₀,x₁}` — that would make `c ∈ A ⊆ A₁` an `X₁`-complete vertex, contradicting
  `Thm192Setup.wheelSystemA_no_complete`. -/
theorem two_complete_in_interior {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {A W : Set V} {P : List V} (hws : IsWheelSystem G z A₀ x 2)
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A)
    (hcard : 2 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G W u v}.ncard) :
    ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
      VertexComplete G c W ∧ VertexComplete G d W := by
  classical
  -- the vertices of `P` other than `x₀, x₁` are exactly the interior ones
  have hmemI : ∀ u : V, u ∈ P → u ≠ x 0 → u ≠ x 1 → u ∈ SPGT.interior P := fun u hu h0 h1 =>
    (PathBasics.mem_interior_iff_of_pathFrom hP).mpr ⟨hu, h0, h1⟩
  -- no vertex of `A ⊆ A₁` is `{x₀,x₁}`-complete
  have hnoc : ∀ u ∈ A, ¬ (G.Adj u (x 0) ∧ G.Adj u (x 1)) := by
    rintro u hu ⟨h0, h1⟩
    refine Thm192Setup.wheelSystemA_no_complete u (hAsub hu) ?_
    rw [Thm192Setup.wheelSystemX_one]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact h0
    · exact h1
  have hx01 : ¬ G.Adj (x 0) (x 1) := Thm192Setup.x0_not_adj_x1 hws
  -- each `W`-complete edge of `P` has an endpoint in `interior P`
  have pick : ∀ u v : V, u ∈ P → v ∈ P → EdgeComplete G W u v →
      ∃ c d : V, s(c, d) = s(u, v) ∧ d ∈ P ∧ G.Adj c d ∧ c ∈ SPGT.interior P ∧
        VertexComplete G c W ∧ VertexComplete G d W := by
    intro u v huP hvP ⟨hadj, hcu, hcv⟩
    by_cases hu0 : u = x 0
    · subst hu0
      have hv0 : v ≠ x 0 := fun h => (hadj.ne) h.symm
      have hv1 : v ≠ x 1 := fun h => hx01 (h ▸ hadj)
      exact ⟨v, x 0, Sym2.eq_swap, huP, hadj.symm, hmemI v hvP hv0 hv1, hcv, hcu⟩
    by_cases hu1 : u = x 1
    · subst hu1
      have hv1 : v ≠ x 1 := fun h => (hadj.ne) h.symm
      have hv0 : v ≠ x 0 := fun h => hx01 (h ▸ hadj.symm)
      exact ⟨v, x 1, Sym2.eq_swap, huP, hadj.symm, hmemI v hvP hv0 hv1, hcv, hcu⟩
    · exact ⟨u, v, rfl, hvP, hadj, hmemI u huP hu0 hu1, hcu, hcv⟩
  -- two distinct `W`-complete edges of `P`
  have h2 : ∃ e₁ ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G W u v},
      ∃ e₂ ∈ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G W u v}, e₁ ≠ e₂ :=
    (Set.one_lt_ncard (Set.toFinite _)).mp hcard
  obtain ⟨e₁, ⟨u₁, hu₁, v₁, hv₁, he₁, hE₁⟩, e₂, ⟨u₂, hu₂, v₂, hv₂, he₂, hE₂⟩, hene⟩ := h2
  obtain ⟨c₁, d₁, hs₁, hd₁P, hadj₁, hc₁I, hc₁c, hd₁c⟩ := pick u₁ v₁ hu₁ hv₁ hE₁
  obtain ⟨c₂, d₂, hs₂, hd₂P, hadj₂, hc₂I, hc₂c, hd₂c⟩ := pick u₂ v₂ hu₂ hv₂ hE₂
  by_cases hcc : c₁ = c₂
  · subst hcc
    have hdd : d₁ ≠ d₂ := by
      rintro rfl
      exact hene (he₁.trans (hs₁.symm.trans (hs₂.trans he₂.symm)))
    by_cases hd₁0 : d₁ = x 0
    · by_cases hd₂0 : d₂ = x 0
      · exact absurd (hd₁0.trans hd₂0.symm) hdd
      by_cases hd₂1 : d₂ = x 1
      · exact absurd (hnoc c₁ (hPint c₁ hc₁I) ⟨hd₁0 ▸ hadj₁, hd₂1 ▸ hadj₂⟩) not_false
      · exact ⟨c₁, hc₁I, d₂, hmemI d₂ hd₂P hd₂0 hd₂1, hadj₂.ne, hc₁c, hd₂c⟩
    by_cases hd₁1 : d₁ = x 1
    · by_cases hd₂1 : d₂ = x 1
      · exact absurd (hd₁1.trans hd₂1.symm) hdd
      by_cases hd₂0 : d₂ = x 0
      · exact absurd (hnoc c₁ (hPint c₁ hc₁I) ⟨hd₂0 ▸ hadj₂, hd₁1 ▸ hadj₁⟩) not_false
      · exact ⟨c₁, hc₁I, d₂, hmemI d₂ hd₂P hd₂0 hd₂1, hadj₂.ne, hc₁c, hd₂c⟩
    · exact ⟨c₁, hc₁I, d₁, hmemI d₁ hd₁P hd₁0 hd₁1, hadj₁.ne, hc₁c, hd₁c⟩
  · exact ⟨c₁, hc₁I, c₂, hc₂I, hcc, hc₁c, hc₂c⟩

/-- Neighbour form of `two_complete_in_interior`: *"all members of `W` have at least two
neighbours in the interior of `P`"*.  Immediate, since `VertexComplete G c W` unfolds to
`∀ w ∈ W, G.Adj c w`. -/
theorem two_neighbours_in_interior {G : SimpleGraph V} {z : V} {A₀ : Set V} {x : ℕ → V}
    {A W : Set V} {P : List V} (hws : IsWheelSystem G z A₀ x 2)
    (hAsub : A ⊆ wheelSystemA G z A₀ x 1) (hP : IsPathFrom G P (x 0) (x 1))
    (hPint : ∀ w ∈ SPGT.interior P, w ∈ A)
    (hcard : 2 ≤ {e : Sym2 V | ∃ u ∈ P, ∃ v ∈ P, e = s(u, v) ∧ EdgeComplete G W u v}.ncard) :
    ∀ w ∈ W, ∃ c ∈ SPGT.interior P, ∃ d ∈ SPGT.interior P, c ≠ d ∧
      G.Adj w c ∧ G.Adj w d := by
  obtain ⟨c, hcI, d, hdI, hcd, hcW, hdW⟩ :=
    two_complete_in_interior hws hAsub hP hPint hcard
  exact fun w hw => ⟨c, hcI, d, hdI, hcd, (hcW w hw).symm, (hdW w hw).symm⟩

end Workspace.ProofLemmas.Thm192Infra
