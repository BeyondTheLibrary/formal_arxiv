import Workspace.ProofLemmas.Thm175Claim4CleanPaths
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S02.Thm_2_3

/-! The exceptional interval in the first paragraph of the proof of 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Exceptional

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

theorem x₁_not_complete (s : Setup c) : ¬ VertexComplete G s.x₁ (wSet s) := by
  have hs := s.hXlong
  have hqpath : IsPathList Gᶜ s.qX := by
    have hh := PathBasics.isPathList_take s.hanti.1 (k := s.qX.length) (by omega)
    simpa using hh
  have h0 := PathBasics.getElem_zero_of_head? s.hxhead (show 0 < s.qX.length by omega)
  have hadj := PathBasics.path_adj_succ hqpath (i := 0) hs
  rw [h0] at hadj
  have hne : s.qX[1]'hs ≠ s.x₁ := by
    intro he
    have := hqpath.2.1.getElem_inj_iff.mp (he.trans h0.symm)
    omega
  have hw : s.qX[1]'hs ∈ wSet s := Or.inl ⟨(s.hXverts _).mp (List.getElem_mem hs), hne⟩
  intro hc
  exact ((SimpleGraph.compl_adj G _ _).mp hadj).2 (hc _ hw)

/-- PAPER: "By 2.3 it contains exactly one, and only two `W`-complete
vertices; so `j=i+1`."  This extracts the two consecutive vertices from the
hole formed by an interval with no internal neighbour of `x₁`. -/
theorem two_consecutive (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (a d : ℕ) (had : a < d) (hd : d < c.core.p.length)
    (hxa : G.Adj s.x₁ (c.core.p[a]'(lt_trans had hd)))
    (hxd : G.Adj s.x₁ (c.core.p[d]'hd))
    (hno : ∀ k (hk : k < c.core.p.length), a < k → k < d → ¬ G.Adj s.x₁ (c.core.p[k]'hk))
    (hodd : Odd (edges G (wSet s) ((c.core.p.drop a).take (d - a + 1))).ncard) :
    Even (d - a) ∧ ∃ i, ∃ hi : i + 1 < c.core.p.length,
      a ≤ i ∧ i + 1 < d ∧
      VertexComplete G (c.core.p[i]'(by omega)) (wSet s) ∧
      VertexComplete G (c.core.p[i + 1]'hi) (wSet s) ∧
      ∀ k (hk : k < c.core.p.length), a ≤ k → k ≤ d →
        VertexComplete G (c.core.p[k]'hk) (wSet s) → k = i ∨ k = i + 1 := by
  classical
  let P := c.core.p
  let T := (P.drop a).take (d - a + 1)
  have hplen : P.length = c.core.p.length := rfl
  change Odd (edges G (wSet s) T).ncard at hodd
  have hT := PathBasics.isPathFrom_slice c.core.hp.1 had hd
  have hTlen : T.length = d - a + 1 := PathBasics.length_slice P (by omega) hd
  have hTsub : ∀ v ∈ T, v ∈ P := fun v hv => List.drop_subset _ _ (List.take_subset _ _ hv)
  have hdnot : ¬ VertexComplete G (P[d]'hd) (wSet s) := by
    intro hc
    have he := (hfirst _ (List.getElem_mem hd)).mp (complete_X_of_complete_wSet s hc hxd)
    have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
      (show 0 < P.length by omega)
    have := c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
    omega
  have hlong : a + 2 ≤ d := by
    have hpos : 0 < (edges G (wSet s) T).ncard := by rw [Nat.odd_iff] at hodd; omega
    obtain ⟨e, u, hu, v, hv, he, hE⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
    obtain ⟨i, hi, hai, hid, hiu⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hu
    obtain ⟨j, hj, haj, hjd, hjv⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hv
    have hin : i ≠ d := by intro he; subst i; exact hdnot (hiu ▸ hE.2.1)
    have hjn : j ≠ d := by intro he; subst j; exact hdnot (hjv ▸ hE.2.2)
    have hijn : i ≠ j := by
      intro he
      subst j
      rw [← hiu, ← hjv] at hE
      exact G.irrefl hE.1
    omega
  have hxT : s.x₁ ∉ T := fun hm => x₁_notMem_p s (hTsub _ hm)
  have hxint : ∀ v ∈ SPGT.interior T, ¬ G.Adj s.x₁ v := by
    intro v hv
    obtain ⟨k, hk, hak, hkd, hkv⟩ := (PathBasics.mem_interior_slice_iff c.core.hp.1 had hd).mp hv
    exact hkv ▸ hno k hk hak hkd
  have hC : IsHoleList G (s.x₁ :: T) := PrismBasics.isHoleList_of_path_add_vertex hT
    (by change 2 ≤ T.length - 1; rw [hTlen]; omega) hxa hxd hxT hxint
  have hCout : ∀ v ∈ s.x₁ :: T, v ∉ wSet s := by
    intro v hv
    rcases List.mem_cons.mp hv with he | hv
    · exact he ▸ x₁_notMem_wSet s
    · exact p_out_wSet s v (hTsub v hv)
  have hCE : edges G (wSet s) (s.x₁ :: T) = edges G (wSet s) T := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, he, hE⟩
      have huT : u ∈ T := by
        rcases List.mem_cons.mp hu with hu | hu
        · exact (x₁_not_complete s (hu ▸ hE.2.1)).elim
        · exact hu
      have hvT : v ∈ T := by
        rcases List.mem_cons.mp hv with hv | hv
        · exact (x₁_not_complete s (hv ▸ hE.2.2)).elim
        · exact hv
      exact ⟨u, huT, v, hvT, he, hE⟩
    · rintro ⟨u, hu, v, hv, he, hE⟩
      exact ⟨u, List.mem_cons_of_mem _ hu, v, List.mem_cons_of_mem _ hv, he, hE⟩
  have hB : Berge G := hG.1.1.1.1
  have hpar : Even (d - a) := by
    have hh := hB.1 _ hC
    rw [Nat.even_iff] at hh ⊢
    change (T.length + 1) % 2 = 0 at hh
    rw [hTlen] at hh
    omega
  refine ⟨hpar, ?_⟩
  rcases (_root_.Workspace.Statements.S02.SPGT.thm_2_3 G hB (wSet s)
    (wSet_anticonnected s) (s.x₁ :: T) (Or.inr hC) hCout).2 hC with heven | ⟨u, v, hpair, hne, huv⟩
  · change Even (edges G (wSet s) (s.x₁ :: T)).ncard at heven
    rw [hCE] at heven
    exact (Nat.not_odd_iff_even.mpr heven hodd).elim
  · have hu : u ∈ s.x₁ :: T ∧ VertexComplete G u (wSet s) := by
      change u ∈ {w | w ∈ s.x₁ :: T ∧ VertexComplete G w (wSet s)}
      rw [hpair]
      simp
    have hv : v ∈ s.x₁ :: T ∧ VertexComplete G v (wSet s) := by
      change v ∈ {w | w ∈ s.x₁ :: T ∧ VertexComplete G w (wSet s)}
      rw [hpair]
      simp
    have huT : u ∈ T := by
      rcases List.mem_cons.mp hu.1 with he | huT
      · exact (x₁_not_complete s (he ▸ hu.2)).elim
      · exact huT
    have hvT : v ∈ T := by
      rcases List.mem_cons.mp hv.1 with he | hvT
      · exact (x₁_not_complete s (he ▸ hv.2)).elim
      · exact hvT
    obtain ⟨i, hi, hai, hid, hiu⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp huT
    obtain ⟨j, hj, haj, hjd, hjv⟩ := (PathBasics.mem_slice_iff P (by omega) hd).mp hvT
    have hiC : VertexComplete G (P[i]'hi) (wSet s) := hiu ▸ hu.2
    have hjC : VertexComplete G (P[j]'hj) (wSet s) := hjv ▸ hv.2
    have hin : i ≠ d := by intro he; subst i; exact hdnot hiC
    have hjn : j ≠ d := by intro he; subst j; exact hdnot hjC
    have honly : ∀ k (hk : k < P.length), a ≤ k → k ≤ d →
        VertexComplete G (P[k]'hk) (wSet s) → k = i ∨ k = j := by
      intro k hk hak hkd hc
      have hm : P[k]'hk ∈ ({u, v} : Set V) := by
        rw [← hpair]
        exact ⟨List.mem_cons_of_mem _ ((PathBasics.mem_slice_iff P (by omega) hd).mpr
          ⟨k, hk, hak, hkd, rfl⟩), hc⟩
      rcases hm with he | he
      · exact Or.inl (c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hiu.symm))
      · exact Or.inr (c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hjv.symm))
    have hadj : G.Adj (P[i]'hi) (P[j]'hj) := by rw [hiu, hjv]; exact huv
    rcases (PathBasics.path_adj_iff c.core.hp.1 hi hj).mp hadj with hij | hji
    · subst j
      exact ⟨i, hj, hai, by omega, hiC, hjC, honly⟩
    · subst i
      exact ⟨j, hi, haj, by omega, hjC, hiC,
        fun k hk hak hkd hc => (honly k hk hak hkd hc).symm⟩

end Workspace.ProofLemmas.Thm175Claim4Exceptional
