import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Wheels
import Workspace.Types.WheelSystems
import Workspace.Types.Classes
import Workspace.Types.Appearances
import Workspace.Statements.S15.Thm_15_2
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.WheelBasics
import Workspace.ProofLemmas.WheelParity
import Workspace.ProofLemmas.OddWheelParityFacts
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# 23.1, first paragraph — the connected set `F` and its attachments (proof attempt)
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm231AttachmentSet

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.WheelSystems Workspace.Types.WheelSystems.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Small pieces the printed proof uses without comment -/

private theorem singleton_connected (H : SimpleGraph V) (v : V) :
    ConnectedSet H ({v} : Set V) := by
  intro p q
  have hpq : p = q := Subtype.ext (p.2.trans q.2.symm)
  rw [hpq]

/-- Every vertex lies in an anticomponent of `V(G)` — a maximal anticonnected set. -/
private theorem exists_anticomponent (G : SimpleGraph V) (v : V) :
    ∃ B : Set V, IsAnticomponent G Set.univ B ∧ v ∈ B := by
  classical
  obtain ⟨B, hB⟩ := Set.Finite.exists_maximal
    (s := {B : Set V | AnticonnectedSet G B ∧ v ∈ B}) (Set.toFinite _)
    ⟨({v} : Set V), singleton_connected Gᶜ v, rfl⟩
  refine ⟨B, ⟨Set.subset_univ _, hB.1.1, ?_⟩, hB.1.2⟩
  intro D hBD _ hD
  have hvD : v ∈ D := hBD hB.1.2
  exact Set.Subset.antisymm (hB.2 ⟨hD, hvD⟩ hBD) hBD

/-- A hole of length `≥ 6` contains no four-cycle. -/
private theorem no_four_cycle {G : SimpleGraph V} {C : List V} (hC : IsHoleList G C)
    (hn : 6 ≤ C.length) {p q r s : V} (hp : p ∈ C) (hq : q ∈ C) (hr : r ∈ C) (hs : s ∈ C)
    (hpr : p ≠ r) (hqs : q ≠ s)
    (hpq : G.Adj p q) (hqr : G.Adj q r) (hrs : G.Adj r s) (hsp : G.Adj s p) : False := by
  obtain ⟨i, hi, hiv⟩ := List.getElem_of_mem hp
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hq
  obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hr
  obtain ⟨l, hl, hlv⟩ := List.getElem_of_mem hs
  have e1 := WheelParity.hole_adj_index hC hi hj (by rw [hiv, hjv]; exact hpq)
  have e2 := WheelParity.hole_adj_index hC hj hk (by rw [hjv, hkv]; exact hqr)
  have e3 := WheelParity.hole_adj_index hC hk hl (by rw [hkv, hlv]; exact hrs)
  have e4 := WheelParity.hole_adj_index hC hl hi (by rw [hlv, hiv]; exact hsp)
  have hik : i ≠ k := by rintro rfl; exact hpr (hiv.symm.trans hkv)
  have hjl : j ≠ l := by rintro rfl; exact hqs (hjv.symm.trans hlv)
  rcases e1 with h1 | h1 | ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases e2 with h2 | h2 | ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
      rcases e3 with h3 | h3 | ⟨h3, h3'⟩ | ⟨h3, h3'⟩ <;>
        rcases e4 with h4 | h4 | ⟨h4, h4'⟩ | ⟨h4, h4'⟩ <;> omega

/-- The paper's *"there is a path `P` in `G` joining them such that none of its interior
vertices is in …"*: the `G`-analogue of `InducedPathExtraction.exists_antipath_interior_in`. -/
private theorem exists_path_interior_in {G : SimpleGraph V} {N : Set V}
    (hN : ConnectedSet G N) {u w : V} (huN : u ∉ N) (hwN : w ∉ N)
    (hu : ∃ t ∈ N, G.Adj u t) (hw : ∃ t ∈ N, G.Adj w t) :
    ∃ q : List V, IsPathFrom G q u w ∧ ∀ t ∈ SPGT.interior q, t ∈ N := by
  obtain ⟨c, hcN, huc⟩ := hu
  obtain ⟨d, hdN, hwd⟩ := hw
  have h1 : ConnectedSet G (N ∪ {u}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hN ⟨c, hcN, huc⟩
  have h2 : ConnectedSet G ((N ∪ {u}) ∪ {w}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton h1 ⟨d, Or.inl hdN, hwd⟩
  obtain ⟨q, hq, hqmem⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected h2 (Or.inl (Or.inr rfl)) (Or.inr rfl)
  refine ⟨q, hq, ?_⟩
  intro z hz
  rw [PathBasics.mem_interior_iff_of_pathFrom hq] at hz
  obtain ⟨hzq, hzu, hzw⟩ := hz
  rcases hqmem z hzq with h | h
  · rcases h with h | h
    · exact h
    · exact absurd h hzu
  · exact absurd h hzw

/-- One end of a path with at least three vertices has a neighbour in the interior. -/
private theorem end_adj_interior {G : SimpleGraph V} {Q : List V} {u w : V}
    (hQ : IsPathFrom G Q u w) (hlen : 3 ≤ Q.length) :
    ∃ f, f ∈ SPGT.interior Q ∧ G.Adj u f := by
  refine ⟨Q[1]'(by omega),
    PathBasics.getElem_mem_interior hQ.1 (by omega) le_rfl (by omega), ?_⟩
  have h0 : Q[0]'(show 0 < Q.length by omega) = u :=
    PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
  have hadj := PathBasics.path_adj_succ hQ.1 (i := 0) (show 0 + 1 < Q.length by omega)
  rw [h0] at hadj
  exact hadj

/-! ### The theorem -/

/-- The first paragraph of the printed proof of 23.1: the set `F` (the interior of
the minimal subpath `P'`) together with the four properties 16.2 needs of it, and
the two attachments of `F` in `C` that are nonadjacent and of opposite
wheel-parity. -/
theorem exists_interior_set (G : SimpleGraph V) (hG : InF8 G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G)
    (C : List V) (Y : Set V) (hopt : OptimalWheel G C Y) :
    ∃ F : Set V,
      (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧
      ConnectedSet G F ∧ (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
      ∃ a ∈ attachments G F {u : V | u ∈ C},
        ∃ b ∈ attachments G F {u : V | u ∈ C},
          OppositeWheelParity G C Y a b ∧ ¬ G.Adj a b := by
  classical
  have hwheel : IsWheel G C Y := hopt.1
  have hCh : IsHoleList G C := hwheel.1.1
  have hClen : 6 ≤ C.length := hwheel.1.2
  have hBerge : Berge G := hG.1.1.1.1.1
  have hF6 : InF6 G := hG.1.1
  have heven := WheelBasics.even_cycCount_of_wheel hBerge hwheel
  obtain ⟨π, hπ2, hπ⟩ := OddWheelParityFacts.exists_parity' hCh heven
  -- *"There are two nonadjacent `Y`-complete vertices in `C` with opposite wheel-parity,
  -- say `a, b`"* — the four ends of the two disjoint `Y`-complete edges of the rim carry
  -- both parities, and no four of them can form a square inside a hole of length `≥ 6`.
  obtain ⟨a, b, haC, hbC, haY, hbY, hab, hnadjab, hnsameab⟩ :
      ∃ a b : V, a ∈ C ∧ b ∈ C ∧ VertexComplete G a Y ∧ VertexComplete G b Y ∧
        a ≠ b ∧ ¬ G.Adj a b ∧ ¬ SameWheelParity G C Y a b := by
    obtain ⟨p, q, r, s, hpC, hqC, hrC, hsC, hEpq, hErs, hpr, hps, hqr, hqs⟩ := hwheel.2.2
    have hpq : G.Adj p q := hEpq.1
    have hrs : G.Adj r s := hErs.1
    have hmk : ∀ u w : V, u ∈ C → w ∈ C → VertexComplete G u Y → VertexComplete G w Y →
        π u ≠ π w → ¬ G.Adj u w →
        ∃ a b : V, a ∈ C ∧ b ∈ C ∧ VertexComplete G a Y ∧ VertexComplete G b Y ∧
          a ≠ b ∧ ¬ G.Adj a b ∧ ¬ SameWheelParity G C Y a b := by
      intro u w hu hw hcu hcw hne hnadj
      have huw : u ≠ w := by intro h; exact hne (by rw [h])
      exact ⟨u, w, hu, hw, hcu, hcw, huw, hnadj,
        fun hsm => hne ((hπ u w hu hw huw).mp hsm)⟩
    have hπpq : π p ≠ π q := by
      intro h
      exact OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hCh heven hpC hqC hEpq
        ((hπ p q hpC hqC hpq.ne).mpr h)
    have hπrs : π r ≠ π s := by
      intro h
      exact OddWheelParityFacts.not_sameWheelParity_of_edgeComplete hCh heven hrC hsC hErs
        ((hπ r s hrC hsC hrs.ne).mpr h)
    by_cases hcase : π p = π r
    · by_cases h1 : G.Adj p s
      · by_cases h2 : G.Adj q r
        · exact (no_four_cycle hCh hClen hpC hqC hrC hsC hpr hqs hpq h2 hrs h1.symm).elim
        · exact hmk q r hqC hrC hEpq.2.2 hErs.2.1
            (by rw [← hcase]; exact fun h => hπpq h.symm) h2
      · exact hmk p s hpC hsC hEpq.2.1 hErs.2.2 (by rw [hcase]; exact hπrs) h1
    · by_cases h1 : G.Adj p r
      · by_cases h2 : G.Adj q s
        · exact (no_four_cycle hCh hClen hpC hqC hsC hrC hps hqr hpq h2 hrs.symm h1.symm).elim
        · refine hmk q s hqC hsC hEpq.2.2 hErs.2.2 ?_ h2
          have := hπ2 p; have := hπ2 q; have := hπ2 r; have := hπ2 s
          omega
      · exact hmk p r hpC hrC hEpq.2.1 hErs.2.1 hcase h1
  -- *"and by 15.2, there is a path `P` in `G` joining them such that none of its interior
  -- vertices is in `Y` or is `Y`-complete"* — 15.2 with `X` the set of `Y`-complete vertices.
  have hXYdisj : Disjoint {v : V | VertexComplete G v Y} Y := by
    rw [Set.disjoint_left]
    intro v hvX hvY
    exact G.irrefl (hvX v hvY)
  have h152 := _root_.Workspace.Statements.S15.SPGT.thm_15_2 G hF6 hbsp
    {v : V | VertexComplete G v Y} Y ⟨a, haY⟩ hwheel.2.1.1 hXYdisj (fun v hv => hv)
  have hXYne : {v : V | VertexComplete G v Y} ∪ Y ≠ Set.univ := by
    intro hun
    rcases h152.1 hun with hcompleteG | ⟨⟨B₁, B₂, hB12, hB1, hB2, hall⟩, hcard⟩
    · exact hnadjab (hcompleteG a b hab)
    · have hcover : ∀ v : V, v ∈ B₁ ∨ v ∈ B₂ := by
        intro v
        obtain ⟨B, hB, hvB⟩ := exists_anticomponent G v
        rcases hall B hB with h | h
        · exact Or.inl (h ▸ hvB)
        · exact Or.inr (h ▸ hvB)
      have hsub : (Set.univ : Set V) ⊆ B₁ ∪ B₂ := fun v _ => hcover v
      have h4 : (Set.univ : Set V).ncard ≤ 4 := by
        refine le_trans (Set.ncard_le_ncard hsub (Set.toFinite _)) ?_
        refine le_trans (Set.ncard_union_le _ _) ?_
        have hc1 := hcard B₁ hB1
        have hc2 := hcard B₂ hB2
        omega
      rw [Set.ncard_univ] at h4
      have hcard' : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
      have hle : C.length ≤ Fintype.card V :=
        List.Nodup.length_le_card (HoleBasics.hole_nodup hCh)
      omega
  obtain ⟨hNconn, hXnbr⟩ := h152.2 hXYne
  have hXnt : ({v : V | VertexComplete G v Y}).Nontrivial := ⟨a, haY, b, hbY, hab⟩
  obtain ⟨za, hza, hadja⟩ := hXnbr hXnt a haY
  obtain ⟨zb, hzb, hadjb⟩ := hXnbr hXnt b hbY
  have haN : a ∉ ({v : V | VertexComplete G v Y} ∪ Y)ᶜ := fun h => h (Or.inl haY)
  have hbN : b ∉ ({v : V | VertexComplete G v Y} ∪ Y)ᶜ := fun h => h (Or.inl hbY)
  obtain ⟨P, hP, hPint⟩ :=
    exists_path_interior_in hNconn haN hbN ⟨za, hza, hadja⟩ ⟨zb, hzb, hadjb⟩
  have hPprop : ∀ t ∈ SPGT.interior P, t ∉ Y ∧ ¬ VertexComplete G t Y := by
    intro t ht
    have h := hPint t ht
    exact ⟨fun hy => h (Or.inr hy), fun hc => h (Or.inl hc)⟩
  -- *"but we may choose a subpath `P'` of `P`, with ends `a', b'` say, such that
  -- `a', b' ∈ V(C)` have opposite wheel-parity and `P'` has minimum length"* — run as a
  -- descent on the length of the subpath.
  have key : ∀ n : ℕ, ∀ (Q : List V) (u w : V), Q.length ≤ n →
      IsPathFrom G Q u w → (∀ t ∈ Q, t ∈ P) →
      (∀ t ∈ SPGT.interior Q, t ∈ SPGT.interior P) →
      u ∈ C → w ∈ C → u ≠ w → ¬ SameWheelParity G C Y u w →
      ∃ F : Set V,
        (∀ f ∈ F, f ∉ C) ∧ (∀ f ∈ F, f ∉ Y) ∧
        ConnectedSet G F ∧ (∀ f ∈ F, ¬ VertexComplete G f Y) ∧
        ∃ a ∈ attachments G F {u : V | u ∈ C},
          ∃ b ∈ attachments G F {u : V | u ∈ C},
            OppositeWheelParity G C Y a b ∧ ¬ G.Adj a b := by
    intro n
    induction n with
    | zero =>
        intro Q u w hlen hQ _ _ _ _ _ _
        exact absurd hlen (by have := PathBasics.path_length_pos hQ.1; omega)
    | succ m ih =>
        intro Q u w hlen hQ hQP hQint huC hwC huw hnsame
        have hπuw : π u ≠ π w := fun h => hnsame ((hπ u w huC hwC huw).mpr h)
        by_cases hint : ∃ t ∈ SPGT.interior Q, t ∈ C
        · -- *"It follows that no vertex of the interior of `P'` is in `C`"*: otherwise one of
          -- the two halves is a strictly shorter subpath with ends of opposite parity.
          obtain ⟨t, htint, htC⟩ := hint
          obtain ⟨k, hk, hk1, hk2, hkt⟩ :=
            PathBasics.exists_getElem_of_mem_interior hQ.1 htint
          obtain ⟨-, htu, htw⟩ := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp htint
          by_cases hpar : π u = π t
          · -- descend on the second half `t … w`
            have hπtw : π t ≠ π w := by rw [← hpar]; exact hπuw
            have hklt : k < Q.length - 1 := by omega
            have hlast : Q.length - 1 < Q.length := by omega
            refine ih ((Q.drop k).take (Q.length - 1 - k + 1)) t w ?_
              ⟨PathBasics.isPathList_slice hQ.1 hklt hlast, ?_, ?_⟩ ?_ ?_ htC hwC
              (fun h => hπtw (by rw [h])) (fun hs => hπtw ((hπ t w htC hwC (fun h => hπtw (by rw [h]))).mp hs))
            · rw [PathBasics.length_slice Q (le_of_lt hklt) hlast]; omega
            · rw [PathBasics.head?_slice Q (le_of_lt hklt) hlast]
              exact congrArg some hkt
            · rw [PathBasics.getLast?_slice Q (le_of_lt hklt) hlast]
              exact congrArg some (PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega))
            · intro z hz
              rw [PathBasics.mem_slice_iff Q (le_of_lt hklt) hlast] at hz
              obtain ⟨idx, hidx, -, -, rfl⟩ := hz
              exact hQP _ (List.getElem_mem hidx)
            · intro z hz
              rw [PathBasics.mem_interior_slice_iff hQ.1 hklt hlast] at hz
              obtain ⟨idx, hidx, hlo, hhi, rfl⟩ := hz
              exact hQint _ (PathBasics.getElem_mem_interior hQ.1 hidx (by omega) (by omega))
          · -- descend on the first half `u … t`
            have hπut : π u ≠ π t := hpar
            have hk0 : (0 : ℕ) < k := by omega
            refine ih ((Q.drop 0).take (k - 0 + 1)) u t ?_
              ⟨PathBasics.isPathList_slice hQ.1 hk0 hk, ?_, ?_⟩ ?_ ?_ huC htC
              (fun h => hπut (by rw [h])) (fun hs => hπut ((hπ u t huC htC (fun h => hπut (by rw [h]))).mp hs))
            · rw [PathBasics.length_slice Q (Nat.zero_le k) hk]; omega
            · rw [PathBasics.head?_slice Q (Nat.zero_le k) hk]
              exact congrArg some (PathBasics.getElem_zero_of_head? hQ.2.1 (by omega))
            · rw [PathBasics.getLast?_slice Q (Nat.zero_le k) hk]
              exact congrArg some hkt
            · intro z hz
              rw [PathBasics.mem_slice_iff Q (Nat.zero_le k) hk] at hz
              obtain ⟨idx, hidx, -, -, rfl⟩ := hz
              exact hQP _ (List.getElem_mem hidx)
            · intro z hz
              rw [PathBasics.mem_interior_slice_iff hQ.1 hk0 hk] at hz
              obtain ⟨idx, hidx, hlo, hhi, rfl⟩ := hz
              exact hQint _ (PathBasics.getElem_mem_interior hQ.1 hidx (by omega) (by omega))
        · -- no interior vertex of `Q` lies on `C`: this is the paper's `P'`.
          push_neg at hint
          -- *"Suppose `a', b'` are adjacent; … and so `a, b` are adjacent, a contradiction."*
          have hnadjuw : ¬ G.Adj u w := by
            intro hadj
            have hcu : VertexComplete G u Y := by
              by_contra hc
              exact hnsame (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete
                hCh heven huC hwC hadj hc)
            have hcw : VertexComplete G w Y := by
              by_contra hc
              exact hnsame (WheelParity.sameWheelParity_symm
                (OddWheelParityFacts.sameWheelParity_of_adj_of_not_complete
                  hCh heven hwC huC hadj.symm hc))
            have huP : u ∈ P := hQP u (PathBasics.isPathFrom_ends_mem hQ).1
            have hwP : w ∈ P := hQP w (PathBasics.isPathFrom_ends_mem hQ).2
            have hu2 : u = a ∨ u = b := by
              by_contra hcon
              push_neg at hcon
              exact (hPprop u ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
                ⟨huP, hcon.1, hcon.2⟩)).2 hcu
            have hw2 : w = a ∨ w = b := by
              by_contra hcon
              push_neg at hcon
              exact (hPprop w ((PathBasics.mem_interior_iff_of_pathFrom hP).mpr
                ⟨hwP, hcon.1, hcon.2⟩)).2 hcw
            rcases hu2 with hu' | hu' <;> rcases hw2 with hw' | hw'
            · exact huw (hu'.trans hw'.symm)
            · exact hnadjab (by rw [← hu', ← hw']; exact hadj)
            · exact hnadjab (by rw [← hw', ← hu']; exact hadj.symm)
            · exact huw (hu'.trans hw'.symm)
          -- `Q` has at least three vertices
          have hpos : 0 < Q.length := PathBasics.path_length_pos hQ.1
          have hlen2 : 2 ≤ Q.length := by
            by_contra hcon
            push_neg at hcon
            obtain ⟨hum, hwm⟩ := PathBasics.isPathFrom_ends_mem hQ
            obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hum
            obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hwm
            have hij : i = j := by omega
            subst hij
            exact huw (hiu.symm.trans hjw)
          have hlen3 : 3 ≤ Q.length := by
            rcases Nat.lt_or_ge Q.length 3 with hlt | hge
            · exfalso
              have h2' : Q.length = 2 := by omega
              exact hnadjuw (PathBasics.isPathFrom_ends_adj_of_length_one hQ
                (by rw [PathBasics.pathLength_eq, h2']))
            · exact hge
          -- *"Let `F` be the interior of `P'`"*
          refine ⟨{z : V | z ∈ SPGT.interior Q}, hint, ?_, ?_, ?_, u, ?_, w, ?_,
            ⟨huw, huC, hwC, hnsame⟩, hnadjuw⟩
          · exact fun f hf => (hPprop f (hQint f hf)).1
          · have hIntPath : IsPathList G (SPGT.interior Q) := by
              rw [PathBasics.interior_eq_drop_take]
              exact PathBasics.isPathList_take
                (PathBasics.isPathList_drop hQ.1 (by omega)) (by omega)
            exact InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hIntPath
          · exact fun f hf => (hPprop f (hQint f hf)).2
          · obtain ⟨f, hf, hadjf⟩ := end_adj_interior hQ hlen3
            exact ⟨huC, f, hf, hadjf⟩
          · obtain ⟨f, hf, hadjf⟩ :=
              end_adj_interior (PathBasics.isPathFrom_reverse hQ) (by simpa using hlen3)
            exact ⟨hwC, f, PathBasics.mem_interior_reverse.mp hf, hadjf⟩
  exact key P.length P a b le_rfl hP (fun t ht => ht) (fun t ht => ht) haC hbC hab hnsameab

end Workspace.ProofLemmas.Thm231AttachmentSet
