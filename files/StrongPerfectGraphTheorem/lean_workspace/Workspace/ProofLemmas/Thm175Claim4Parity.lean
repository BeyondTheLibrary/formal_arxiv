import Workspace.ProofLemmas.Thm175Claim4Setup

/-! The interval reduction in the first sentence of the proof of 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Parity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem slice_edges_mono (G : SimpleGraph V) (A : Set V) (P : List V)
    {a b d e : ℕ} (hab : a ≤ b) (hbd : b ≤ d) (hde : d ≤ e)
    (he : e < P.length) :
    edges G A ((P.drop b).take (d - b + 1)) ⊆
      edges G A ((P.drop a).take (e - a + 1)) := by
  have hsub : ∀ v ∈ (P.drop b).take (d - b + 1),
      v ∈ (P.drop a).take (e - a + 1) := by
    intro v hv
    obtain ⟨i, hi, hbi, hid, hiv⟩ :=
      (PathBasics.mem_slice_iff P hbd (lt_of_le_of_lt hde he)).mp hv
    exact (PathBasics.mem_slice_iff P (by omega) he).mpr
      ⟨i, hi, by omega, by omega, hiv⟩
  rintro f ⟨u, hu, v, hv, rfl, hE⟩
  exact ⟨u, hsub u hu, v, hsub v hv, rfl, hE⟩

/-- Cutting an induced path at a vertex partitions its complete edges. -/
theorem slice_edges_split (G : SimpleGraph V) (A : Set V) (P : List V)
    (hP : IsPathList G P) {a m d : ℕ} (ham : a ≤ m) (hmd : m ≤ d)
    (hd : d < P.length) :
    (edges G A ((P.drop a).take (d - a + 1))).ncard =
      (edges G A ((P.drop a).take (m - a + 1))).ncard +
      (edges G A ((P.drop m).take (d - m + 1))).ncard := by
  have hmem {i j : ℕ} (hij : i ≤ j) (hj : j < P.length) {v : V} :=
    @PathBasics.mem_slice_iff V P i j hij hj v
  have hunion : edges G A ((P.drop a).take (d - a + 1)) =
      edges G A ((P.drop a).take (m - a + 1)) ∪
      edges G A ((P.drop m).take (d - m + 1)) := by
    apply Set.Subset.antisymm
    · rintro f ⟨u, hu, v, hv, rfl, hE⟩
      obtain ⟨i, hi, hai, hid, rfl⟩ := (hmem (by omega) hd).mp hu
      obtain ⟨j, hj, haj, hjd, rfl⟩ := (hmem (by omega) hd).mp hv
      have hij := (PathBasics.path_adj_iff hP hi hj).mp hE.1
      by_cases hm : i ≤ m ∧ j ≤ m
      · left
        exact ⟨_, (hmem ham (by omega)).mpr ⟨i, hi, hai, hm.1, rfl⟩,
          _, (hmem ham (by omega)).mpr ⟨j, hj, haj, hm.2, rfl⟩, rfl, hE⟩
      · right
        exact ⟨_, (hmem hmd hd).mpr ⟨i, hi, by omega, hid, rfl⟩,
          _, (hmem hmd hd).mpr ⟨j, hj, by omega, hjd, rfl⟩, rfl, hE⟩
    · exact Set.union_subset
        (slice_edges_mono G A P le_rfl ham hmd hd)
        (slice_edges_mono G A P ham hmd le_rfl hd)
  have hdisj : Disjoint (edges G A ((P.drop a).take (m - a + 1)))
      (edges G A ((P.drop m).take (d - m + 1))) := by
    refine Set.disjoint_left.mpr ?_
    rintro f ⟨u, hu, v, hv, hf, hE⟩ ⟨u', hu', v', hv', hf', hE'⟩
    obtain ⟨i, hi, -, him, rfl⟩ := (hmem ham (by omega)).mp hu
    obtain ⟨j, hj, -, hjm, rfl⟩ := (hmem ham (by omega)).mp hv
    obtain ⟨k, hk, hmk, -, rfl⟩ := (hmem hmd hd).mp hu'
    obtain ⟨l, hl, hml, -, rfl⟩ := (hmem hmd hd).mp hv'
    have hij := (PathBasics.path_adj_iff hP hi hj).mp hE.1
    rcases Sym2.eq_iff.mp (hf.symm.trans hf') with ⟨hik, hjl⟩ | ⟨hil, hjk⟩
    · have := hP.2.1.getElem_inj_iff.mp hik
      have := hP.2.1.getElem_inj_iff.mp hjl
      omega
    · have := hP.2.1.getElem_inj_iff.mp hil
      have := hP.2.1.getElem_inj_iff.mp hjk
      omega
  rw [hunion, Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _)]

/-- PAPER: "For suppose not; then we may choose `P'` such that no internal
vertex of `P'` is adjacent to `x₁`."  Add the two edge counts when an internal
neighbour splits an interval. -/
theorem parity_of_intervals_without_internal_neighbor
    (G : SimpleGraph V) (A : Set V) (P : List V) (hP : IsPathList G P) (x : V)
    (hbase : ∀ a d (had : a < d) (hd : d < P.length),
      G.Adj x (P[a]'(lt_trans had hd)) → G.Adj x (P[d]'hd) →
      (∀ k (hk : k < P.length), a < k → k < d → ¬ G.Adj x (P[k]'hk)) →
      Even (edges G A ((P.drop a).take (d - a + 1))).ncard) :
    ∀ a d (had : a < d) (hd : d < P.length),
      G.Adj x (P[a]'(lt_trans had hd)) → G.Adj x (P[d]'hd) →
      Even (edges G A ((P.drop a).take (d - a + 1))).ncard := by
  intro a d had hd hxa hxd
  generalize hn : d - a = n
  induction n using Nat.strong_induction_on generalizing a d with
  | h n ih =>
    rw [← hn]
    by_cases hex : ∃ k, ∃ hk : k < P.length,
        a < k ∧ k < d ∧ G.Adj x (P[k]'hk)
    · obtain ⟨k, hk, hak, hkd, hxk⟩ := hex
      have hleft := ih (k - a) (by omega) a k hak hk hxa hxk rfl
      have hright := ih (d - k) (by omega) k d hkd hd hxk hxd rfl
      rw [slice_edges_split G A P hP (a := a) (m := k) (d := d)
        (by omega) (by omega) hd]
      exact hleft.add hright
    · apply hbase a d had hd hxa hxd
      intro k hk hak hkd hxk
      exact hex ⟨k, hk, hak, hkd, hxk⟩

end Workspace.ProofLemmas.Thm175Claim4Parity
