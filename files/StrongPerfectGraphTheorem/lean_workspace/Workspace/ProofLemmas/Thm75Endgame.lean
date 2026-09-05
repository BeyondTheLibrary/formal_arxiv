import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.Thm75Setup
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionCompose
import Workspace.ProofLemmas.SubdivisionTrackExpansion
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.TrackGlueAtCommonEndpoint
import Workspace.ProofLemmas.TrackToRungPath
import Workspace.ProofLemmas.Thm75BranchEnds
import Workspace.ProofLemmas.Thm75Claim1
import Workspace.ProofLemmas.Thm75AnticonnectedUnion
import Workspace.ProofLemmas.Thm75DominantOutsideLineGraph
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S04.Thm_4_2
import Workspace.Statements.S04.Thm_4_3
import Workspace.Statements.S04.Thm_4_6

/-!
Development file for the helper lemmas of `Thm75Endgame`.  Everything here is proved;
nothing is `sorry`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Thm75EndgameHelpers

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.Thm75Setup

/-! ### A separation lemma -/

/-- If there is no `Γ`-edge between `P` and `Q`, then any `Γ`-connected subset of `P ∪ Q`
lies entirely inside `P` or entirely inside `Q`. -/
theorem sep_split {V : Type*} (Γ : SimpleGraph V) (P Q D : Set V)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, ¬ Γ.Adj p q)
    (hD : D ⊆ P ∪ Q) (hconn : (Γ.induce D).Preconnected) :
    (∀ x ∈ D, x ∈ P) ∨ (∀ x ∈ D, x ∈ Q) := by
  classical
  by_cases hall : ∀ x ∈ D, x ∈ P
  · exact Or.inl hall
  · push_neg at hall
    obtain ⟨d, hdD, hdP⟩ := hall
    have hdQ : d ∈ Q := (hD hdD).resolve_left hdP
    right
    have key : ∀ (a b : ↥D), (Γ.induce D).Walk a b → ((a : V) ∈ Q → (b : V) ∈ Q) := by
      intro a b w
      induction w with
      | nil => exact fun h => h
      | @cons x y z hxy w ih =>
        intro hx
        refine ih ?_
        rcases hD y.2 with hyP | hyQ
        · exact absurd (show Γ.Adj (y : V) (x : V) from (show Γ.Adj (x : V) (y : V) from hxy).symm)
            (hsep (y : V) hyP (x : V) hx)
        · exact hyQ
    intro x hxD
    obtain ⟨w⟩ := hconn ⟨d, hdD⟩ ⟨x, hxD⟩
    exact key _ _ w hdQ

/-! ### Elementary facts about `NSet` -/

variable {V W : Type*}

theorem phi_inj {G : SimpleGraph V} {H : SimpleGraph W} {K : Set V}
    (φ : H.lineGraph ≃g G.induce K) {e f : Sym2 W} (he : e ∈ H.edgeSet) (hf : f ∈ H.edgeSet)
    (h : (↑(φ ⟨e, he⟩) : V) = (↑(φ ⟨f, hf⟩) : V)) : e = f := by
  have h1 : (⟨e, he⟩ : H.edgeSet) = ⟨f, hf⟩ := φ.injective (Subtype.ext h)
  exact congrArg Subtype.val h1

theorem nset_subset_K (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) : NSet G H K φ c ⊆ K := by
  rintro x ⟨e, he, -, rfl⟩
  exact Subtype.coe_prop _

theorem mem_nset (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) {e : Sym2 W} (he : e ∈ H.edgeSet) (hce : c ∈ e) :
    (↑(φ ⟨e, he⟩) : V) ∈ NSet G H K φ c := ⟨e, he, ⟨he, hce⟩, rfl⟩

/-- `N_c` is a clique of `G`: two distinct edges of `H` at `c` meet, so are adjacent in `L(H)`. -/
theorem nset_clique (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) :
    ∀ x ∈ NSet G H K φ c, ∀ y ∈ NSet G H K φ c, x ≠ y → G.Adj x y := by
  rintro x ⟨e, he, hec, rfl⟩ y ⟨f, hf, hfc, rfl⟩ hne
  have hEne : (⟨e, he⟩ : H.edgeSet) ≠ ⟨f, hf⟩ := fun hcon => hne (by rw [hcon])
  have hadj : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := by
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    exact ⟨hEne, c, hec.2, hfc.2⟩
  exact φ.map_rel_iff.mpr hadj

/-- A branch-vertex `c` gives at least two distinct vertices of `N_c`. -/
theorem nset_two [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) (hc : c ∈ branchVertices H) :
    ∃ x y, x ∈ NSet G H K φ c ∧ y ∈ NSet G H K φ c ∧ x ≠ y := by
  classical
  have hcard : 3 ≤ (H.neighborSet c).ncard := hc
  obtain ⟨w₁, hw₁⟩ : (H.neighborSet c).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hdiff : (H.neighborSet c \ {w₁}).ncard = (H.neighborSet c).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hw₁
  obtain ⟨w₂, hw₂⟩ : (H.neighborSet c \ {w₁}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hne : w₁ ≠ w₂ := fun h => hw₂.2 (by rw [← h]; rfl)
  have he₁ : s(c, w₁) ∈ H.edgeSet := hw₁
  have he₂ : s(c, w₂) ∈ H.edgeSet := hw₂.1
  refine ⟨_, _, mem_nset G H K φ c he₁ (by simp), mem_nset G H K φ c he₂ (by simp), ?_⟩
  intro hcon
  have := phi_inj φ he₁ he₂ hcon
  exact hne (Sym2.congr_right.mp this)

/-! ### Bipartite parity along a track -/

/-- Along a track of a bipartite graph the colour alternates. -/
theorem track_colour {H : SimpleGraph W} (col : H.Coloring (Fin 2)) {q : List W}
    (hq : IsTrackList H q) :
    ∀ (i : ℕ) (hi : i < q.length) (h0 : 0 < q.length),
      ((col (q[i]'hi) : ℕ) + i) % 2 = ((col (q[0]'h0) : ℕ)) % 2 := by
  intro i
  induction i with
  | zero => intro hi h0; simp
  | succ n ih =>
    intro hi h0
    have hn : n < q.length := by omega
    have hprev := ih hn h0
    have hadj : H.Adj (q[n]'hn) (q[n + 1]'hi) := hq.2.2 n (by omega)
    have hcol : col (q[n]'hn) ≠ col (q[n + 1]'hi) := col.valid hadj
    have hne : ((col (q[n]'hn) : ℕ)) ≠ ((col (q[n + 1]'hi) : ℕ)) := fun h => hcol (Fin.ext h)
    have b1 : ((col (q[n]'hn) : ℕ)) < 2 := (col (q[n]'hn)).isLt
    have b2 : ((col (q[n + 1]'hi) : ℕ)) < 2 := (col (q[n + 1]'hi)).isLt
    omega

/-! ### List end lemmas -/

theorem head_getElem {α : Type*} {l : List α} {a : α} (h : l.head? = some a)
    (h0 : 0 < l.length) : l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

theorem last_getElem {α : Type*} {l : List α} {b : α} (h : l.getLast? = some b)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = b := by
  have hne : l ≠ [] := by intro hc; subst hc; simp at h0
  have h1 : l.getLast? = some (l.getLast hne) := List.getLast?_eq_some_getLast hne
  rw [h] at h1
  have h2 : b = l.getLast hne := Option.some_injective _ h1
  rw [h2]
  exact (List.getLast_eq_getElem hne).symm

/-! ### Parity of a track in a bipartite host -/

theorem colour_ends {H : SimpleGraph W} (col : H.Coloring (Fin 2)) {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) :
    ((col b : ℕ) + trackLength q) % 2 = ((col a : ℕ)) % 2 := by
  have h0 : 0 < q.length := List.length_pos_iff.mpr hfrom.1.1
  have ha : q[0]'h0 = a := head_getElem hfrom.2.1 h0
  have hb : q[q.length - 1]'(by omega) = b := last_getElem hfrom.2.2 h0
  have hcol := track_colour col hfrom.1 (q.length - 1) (by omega) h0
  rw [ha, hb] at hcol
  simpa [trackLength] using hcol

theorem colour_ne_of_odd {H : SimpleGraph W} (col : H.Coloring (Fin 2)) {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) (hodd : Odd (trackLength q)) : col a ≠ col b := by
  have h := colour_ends col hfrom
  obtain ⟨k, hk⟩ := hodd
  rw [hk] at h
  intro hcon
  rw [hcon] at h
  omega

theorem track_odd_of_colour_ne {H : SimpleGraph W} (col : H.Coloring (Fin 2)) {q : List W}
    {a b : W} (hfrom : IsTrackFrom H q a b) (hne : col a ≠ col b) : Odd (trackLength q) := by
  have h := colour_ends col hfrom
  have hne' : ((col a : Fin 2) : ℕ) ≠ ((col b : Fin 2) : ℕ) := fun hh => hne (Fin.ext hh)
  rcases Nat.even_or_odd (trackLength q) with hev | ho
  · exfalso
    obtain ⟨k, hk⟩ := hev
    rw [hk] at h
    omega
  · exact ho

theorem no_common_neighbour {H : SimpleGraph W} (col : H.Coloring (Fin 2)) {a b : W}
    (hne : col a ≠ col b) (z : W) (h1 : H.Adj a z) (h2 : H.Adj b z) : False := by
  have c1 : ((col a : Fin 2) : ℕ) ≠ ((col z : Fin 2) : ℕ) := fun hh => col.valid h1 (Fin.ext hh)
  have c2 : ((col b : Fin 2) : ℕ) ≠ ((col z : Fin 2) : ℕ) := fun hh => col.valid h2 (Fin.ext hh)
  have c3 : ((col a : Fin 2) : ℕ) ≠ ((col b : Fin 2) : ℕ) := fun hh => hne (Fin.ext hh)
  have b1 : ((col a : Fin 2) : ℕ) < 2 := (col a).isLt
  have b2 : ((col b : Fin 2) : ℕ) < 2 := (col b).isLt
  have b3 : ((col z : Fin 2) : ℕ) < 2 := (col z).isLt
  omega

/-- PAPER: *"since there are no edges between `Nc₁` and `Nc₂`"*.  Two edges of `H`, one at `c₁`
and one at `c₂`, never meet: they cannot both contain `c₁` (or `c₂`), since `c₁c₂` is not an edge,
and they cannot meet at a third vertex, since `c₁`, `c₂` have different biparity. -/
theorem nset_anticomplete {H : SimpleGraph W} (col : H.Coloring (Fin 2)) (G : SimpleGraph V)
    (K : Set V) (φ : H.lineGraph ≃g G.induce K) {c₁ c₂ : W}
    (hcol : col c₁ ≠ col c₂) (hnadj : ¬ H.Adj c₁ c₂) :
    Anticomplete G (NSet G H K φ c₁) (NSet G H K φ c₂) := by
  rintro x ⟨e, he, hec, rfl⟩ y ⟨f, hf, hfc, rfl⟩ hadj
  have hne : c₁ ≠ c₂ := fun h => hcol (by rw [h])
  have hlg : H.lineGraph.Adj ⟨e, he⟩ ⟨f, hf⟩ := φ.map_rel_iff.mp hadj
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hlg
  obtain ⟨-, z, hze, hzf⟩ := hlg
  by_cases hz1 : z = c₁
  · subst hz1
    have hfe : f = s(z, c₂) := (Sym2.mem_and_mem_iff hne).mp ⟨hzf, hfc.2⟩
    rw [hfe] at hf
    exact hnadj hf
  · by_cases hz2 : z = c₂
    · subst hz2
      have hee : e = s(c₁, z) := (Sym2.mem_and_mem_iff hne).mp ⟨hec.2, hze⟩
      rw [hee] at he
      exact hnadj he
    · have he' : e = s(c₁, z) := (Sym2.mem_and_mem_iff (Ne.symm hz1)).mp ⟨hec.2, hze⟩
      have hf' : f = s(c₂, z) := (Sym2.mem_and_mem_iff (Ne.symm hz2)).mp ⟨hfc.2, hzf⟩
      refine no_common_neighbour col hcol z ?_ ?_
      · rw [he'] at he; exact he
      · rw [hf'] at hf; exact hf

/-! ### The edges of a track at its two ends -/

theorem first_edge_mem {q : List W} (h1 : 1 < q.length) :
    s(q[0]'(by omega), q[1]'h1) ∈ trackEdges q := ⟨0, h1, rfl⟩

theorem last_edge_mem {q : List W} (h1 : 1 < q.length) :
    s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)) ∈ trackEdges q := by
  have hidx : q.length - 2 + 1 = q.length - 1 := by omega
  refine ⟨q.length - 2, by omega, ?_⟩
  congr 1
  exact (Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q hidx
    (by omega) (by omega)).symm

theorem trackEdges_eq_first {H : SimpleGraph W} {q : List W} {a b : W} (hfrom : IsTrackFrom H q a b)
    (h1 : 1 < q.length) {e : Sym2 W} (he : e ∈ trackEdges q) (hae : a ∈ e) :
    e = s(q[0]'(by omega), q[1]'h1) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd : q.Nodup := hfrom.1.2.1
  have ha : q[0]'(by omega : 0 < q.length) = a := head_getElem hfrom.2.1 (by omega)
  have hdisj : a = q[i]'(by omega) ∨ a = q[i + 1]'hi := by simpa using hae
  have hi0 : i = 0 := by
    rcases hdisj with h | h
    · have hq : q[i]'(by omega) = q[0]'(by omega : 0 < q.length) := by rw [← h, ha]
      exact hnd.getElem_inj_iff.mp hq
    · have hq : q[i + 1]'hi = q[0]'(by omega : 0 < q.length) := by rw [← h, ha]
      have := hnd.getElem_inj_iff.mp hq
      omega
  subst hi0
  rfl

theorem trackEdges_eq_last {H : SimpleGraph W} {q : List W} {a b : W} (hfrom : IsTrackFrom H q a b)
    (h1 : 1 < q.length) {e : Sym2 W} (he : e ∈ trackEdges q) (hbe : b ∈ e) :
    e = s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)) := by
  obtain ⟨i, hi, rfl⟩ := he
  have hnd : q.Nodup := hfrom.1.2.1
  have hb : q[q.length - 1]'(by omega) = b := last_getElem hfrom.2.2 (by omega)
  have hdisj : b = q[i]'(by omega) ∨ b = q[i + 1]'hi := by simpa using hbe
  have hi0 : i = q.length - 2 := by
    rcases hdisj with h | h
    · have hq : q[i]'(by omega) = q[q.length - 1]'(by omega : q.length - 1 < q.length) := by
        rw [← h, hb]
      have := hnd.getElem_inj_iff.mp hq
      omega
    · have hq : q[i + 1]'hi = q[q.length - 1]'(by omega : q.length - 1 < q.length) := by
        rw [← h, hb]
      have := hnd.getElem_inj_iff.mp hq
      omega
  subst hi0
  have hidx : q.length - 2 + 1 = q.length - 1 := by omega
  congr 1
  exact Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q hidx
    (by omega) (by omega)

theorem trackEdges_subset_edgeSet {H : SimpleGraph W} {q : List W} (hq : IsTrackList H q) :
    trackEdges q ⊆ H.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact hq.2.2 i hi

theorem exists_first_edge {H : SimpleGraph W} {q : List W} {a b : W} (hfrom : IsTrackFrom H q a b)
    (h1 : 1 < q.length) : ∃ e, e ∈ trackEdges q ∧ a ∈ e := by
  refine ⟨s(q[0]'(by omega), q[1]'h1), first_edge_mem h1, ?_⟩
  have ha : q[0]'(by omega : 0 < q.length) = a := head_getElem hfrom.2.1 (by omega)
  rw [← ha]
  simp

theorem exists_last_edge {H : SimpleGraph W} {q : List W} {a b : W} (hfrom : IsTrackFrom H q a b)
    (h1 : 1 < q.length) : ∃ e, e ∈ trackEdges q ∧ b ∈ e := by
  refine ⟨s(q[q.length - 2]'(by omega), q[q.length - 1]'(by omega)), last_edge_mem h1, ?_⟩
  have hb : q[q.length - 1]'(by omega) = b := last_getElem hfrom.2.2 (by omega)
  rw [← hb]
  simp

theorem trackEdges_first_unique {H : SimpleGraph W} {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) (h1 : 1 < q.length) {e f : Sym2 W}
    (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q) (hae : a ∈ e) (haf : a ∈ f) : e = f := by
  rw [trackEdges_eq_first hfrom h1 he hae, trackEdges_eq_first hfrom h1 hf haf]

theorem trackEdges_last_unique {H : SimpleGraph W} {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) (h1 : 1 < q.length) {e f : Sym2 W}
    (he : e ∈ trackEdges q) (hf : f ∈ trackEdges q) (hbe : b ∈ e) (hbf : b ∈ f) : e = f := by
  rw [trackEdges_eq_last hfrom h1 he hbe, trackEdges_eq_last hfrom h1 hf hbf]

/-! ### The two ends of the rung -/

/-- PAPER: *"Let the ends of `Rc₁c₂` (that is, the end-edges of `Bc₁c₂`) be `r₁, r₂`, where
`rᵢ ∈ Ncᵢ`."*  The rung meets `Nc₁` and `Nc₂` in exactly one vertex each. -/
theorem rung_ends (G : SimpleGraph V) {H : SimpleGraph W} (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) {B : List W} {c₁ c₂ : W} (hfrom : IsTrackFrom H B c₁ c₂)
    (h1 : 1 < B.length) (Rset : Set V)
    (hRset : Rset = {x : V | ∃ (e : Sym2 W) (he : e ∈ H.edgeSet),
      e ∈ trackEdges B ∧ x = (↑(φ ⟨e, he⟩) : V)}) :
    ∃ r₁ r₂ : V, NSet G H K φ c₁ ∩ Rset = {r₁} ∧ NSet G H K φ c₂ ∩ Rset = {r₂} := by
  classical
  obtain ⟨e₁, he₁mem, he₁c⟩ := exists_first_edge hfrom h1
  obtain ⟨e₂, he₂mem, he₂c⟩ := exists_last_edge hfrom h1
  have he₁E : e₁ ∈ H.edgeSet := trackEdges_subset_edgeSet hfrom.1 he₁mem
  have he₂E : e₂ ∈ H.edgeSet := trackEdges_subset_edgeSet hfrom.1 he₂mem
  refine ⟨(↑(φ ⟨e₁, he₁E⟩) : V), (↑(φ ⟨e₂, he₂E⟩) : V), ?_, ?_⟩
  · apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨mem_nset G H K φ c₁ he₁E he₁c, by rw [hRset]; exact ⟨e₁, he₁E, he₁mem, rfl⟩⟩
    · rintro x ⟨⟨f, hf, hfc, rfl⟩, hxR⟩
      rw [hRset] at hxR
      obtain ⟨g, hg, hgmem, hxg⟩ := hxR
      have hfg : f = g := phi_inj φ hf hg hxg
      subst hfg
      have : f = e₁ := trackEdges_first_unique hfrom h1 hgmem he₁mem hfc.2 he₁c
      subst this
      rfl
  · apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · exact ⟨mem_nset G H K φ c₂ he₂E he₂c, by rw [hRset]; exact ⟨e₂, he₂E, he₂mem, rfl⟩⟩
    · rintro x ⟨⟨f, hf, hfc, rfl⟩, hxR⟩
      rw [hRset] at hxR
      obtain ⟨g, hg, hgmem, hxg⟩ := hxR
      have hfg : f = g := phi_inj φ hf hg hxg
      subst hfg
      have : f = e₂ := trackEdges_last_unique hfrom h1 hgmem he₂mem hfc.2 he₂c
      subst this
      rfl

/-! ### Vertices of `L(H)` off `Nc₁ ∪ Nc₂` -/

theorem not_mem_nset_of_not_mem (G : SimpleGraph V) {H : SimpleGraph W} (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) {e : Sym2 W} (he : e ∈ H.edgeSet) (hce : c ∉ e) :
    (↑(φ ⟨e, he⟩) : V) ∉ NSet G H K φ c := by
  rintro ⟨f, hf, hfc, hxf⟩
  exact hce ((phi_inj φ he hf hxf) ▸ hfc.2)

theorem middle_edge_not_first {H : SimpleGraph W} {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) {i : ℕ} (hi : i + 1 < q.length) (hi0 : i ≠ 0) :
    a ∉ s(q[i]'(by omega), q[i + 1]'hi) := by
  intro hmem
  have hnd : q.Nodup := hfrom.1.2.1
  have ha : q[0]'(by omega : 0 < q.length) = a := head_getElem hfrom.2.1 (by omega)
  have hdisj : a = q[i]'(by omega) ∨ a = q[i + 1]'hi := by simpa using hmem
  rcases hdisj with h | h
  · have hq : q[i]'(by omega) = q[0]'(by omega : 0 < q.length) := by rw [← h, ha]
    exact hi0 (hnd.getElem_inj_iff.mp hq)
  · have hq : q[i + 1]'hi = q[0]'(by omega : 0 < q.length) := by rw [← h, ha]
    have := hnd.getElem_inj_iff.mp hq
    omega

theorem middle_edge_not_last {H : SimpleGraph W} {q : List W} {a b : W}
    (hfrom : IsTrackFrom H q a b) {i : ℕ} (hi : i + 1 < q.length) (hil : i + 1 ≠ q.length - 1) :
    b ∉ s(q[i]'(by omega), q[i + 1]'hi) := by
  intro hmem
  have hnd : q.Nodup := hfrom.1.2.1
  have hb : q[q.length - 1]'(by omega) = b := last_getElem hfrom.2.2 (by omega)
  have hdisj : b = q[i]'(by omega) ∨ b = q[i + 1]'hi := by simpa using hmem
  rcases hdisj with h | h
  · have hq : q[i]'(by omega) = q[q.length - 1]'(by omega : q.length - 1 < q.length) := by
      rw [← h, hb]
    have := hnd.getElem_inj_iff.mp hq
    omega
  · have hq : q[i + 1]'hi = q[q.length - 1]'(by omega : q.length - 1 < q.length) := by
      rw [← h, hb]
    exact hil (hnd.getElem_inj_iff.mp hq)

/-- PAPER: the interior of `Rc₁c₂` is nonempty, since `Bc₁c₂` has length `≥ 3`.  This gives a
vertex of the rung outside `Nc₁ ∪ Nc₂`, i.e. `S ≠ ∅`. -/
theorem exists_rung_middle {H : SimpleGraph W} {B : List W} {c₁ c₂ : W}
    (hfrom : IsTrackFrom H B c₁ c₂) (hlen : 3 ≤ trackLength B) :
    ∃ e, e ∈ trackEdges B ∧ c₁ ∉ e ∧ c₂ ∉ e := by
  have hB : 4 ≤ B.length := by simp only [trackLength] at hlen; omega
  refine ⟨s(B[1]'(by omega), B[1 + 1]'(by omega)), ⟨1, by omega, rfl⟩, ?_, ?_⟩
  · exact middle_edge_not_first hfrom (by omega) (by omega)
  · exact middle_edge_not_last hfrom (by omega) (by omega)

/-- PAPER (implicit in *"`T = (V(L(H)) \ V(Rc₁c₂)) \ X₁`"* being one side of the separation):
`L(H)` has a vertex off the rung and off `Nc₁ ∪ Nc₂`.  Since `J` is 3-connected, `J - {c₁, c₂}`
is connected and has an edge; the first edge of the corresponding branch of `H` is disjoint from
`{c₁, c₂}` and is not an edge of `Bc₁c₂`. -/
theorem exists_far_edge {U : Type*} [Fintype U] [Finite W] {J : SimpleGraph U}
    {H : SimpleGraph W} (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) {B : List W}
    {c₁ c₂ : W} (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hc₁ : c₁ ∈ branchVertices H) (hc₂ : c₂ ∈ branchVertices H) (hne : c₁ ≠ c₂) :
    ∃ g, g ∈ H.edgeSet ∧ g ∉ trackEdges B ∧ c₁ ∉ g ∧ c₂ ∉ g := by
  classical
  obtain ⟨ι, T, hinj, htrack, hlenT, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard := fun u =>
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices hinj htrack hlenT
      hdisj hnew hdeg
  have hbr : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj
      hcover hedges
  obtain ⟨a, ha⟩ := hbr hc₁
  obtain ⟨b, hb⟩ := hbr hc₂
  have hab : a ≠ b := by rintro rfl; exact hne (ha.symm.trans hb)
  have hcard : 3 < Fintype.card U := hJ.1
  have hsc : ({a, b} : Set U).ncard ≤ 2 := by
    have h1 : ({a, b} : Set U).ncard ≤ ({b} : Set U).ncard + 1 := Set.ncard_insert_le _ _
    simpa using h1
  have hcompl : 2 ≤ ((({a, b} : Set U))ᶜ).ncard := by
    have h1 := Set.ncard_add_ncard_compl ({a, b} : Set U)
    rw [Nat.card_eq_fintype_card] at h1
    omega
  have hconn := hJ.2 ({a, b} : Set U) (by omega)
  obtain ⟨d, hd⟩ : ((({a, b} : Set U))ᶜ).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hdiff : (((({a, b} : Set U))ᶜ) \ {d}).ncard = ((({a, b} : Set U))ᶜ).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hd
  obtain ⟨d', hd'⟩ : (((({a, b} : Set U))ᶜ) \ {d}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hdd' : d ≠ d' := fun h => hd'.2 (by rw [← h]; rfl)
  have hsne : (⟨d, hd⟩ : ↥((({a, b} : Set U))ᶜ)) ≠ ⟨d', hd'.1⟩ := fun h =>
    hdd' (congrArg Subtype.val h)
  obtain ⟨cc, hcadj⟩ := Workspace.ProofLemmas.SubdivisionCounting.exists_adj_of_reachable
    (hconn.preconnected ⟨d, hd⟩ ⟨d', hd'.1⟩) hsne
  have huv : J.Adj d (cc : U) := hcadj
  have hdna : d ≠ a := fun h => hd (by rw [h]; exact Or.inl rfl)
  have hdnb : d ≠ b := fun h => hd (by rw [h]; exact Or.inr rfl)
  have hcna : (cc : U) ≠ a := fun h => cc.2 (by rw [h]; exact Or.inl rfl)
  have hcnb : (cc : U) ≠ b := fun h => cc.2 (by rw [h]; exact Or.inr rfl)
  -- the first edge of the track of `H` attached to the edge `d (cc)` of `J`
  have hqfrom : IsTrackFrom H (T d (cc : U)) (ι d) (ι (cc : U)) := htrack _ _ huv
  have hq2 : 2 ≤ (T d (cc : U)).length := by
    have := hlenT _ _ huv; simp only [trackLength] at this; omega
  have hadj01 : H.Adj ((T d (cc : U))[0]'(by omega)) ((T d (cc : U))[1]'(by omega)) :=
    hqfrom.1.2.2 0 (by omega)
  have h0 : (T d (cc : U))[0]'(by omega) = ι d := head_getElem hqfrom.2.1 (by omega)
  set x : W := (T d (cc : U))[1]'(by omega) with hxdef
  have hg : s(ι d, x) ∈ H.edgeSet := by rw [← h0]; exact hadj01
  -- `x` is not an image of `ι` unless it is `ι (cc)`
  have hxcase : x ∉ Set.range ι ∨ x = ι (cc : U) := by
    by_cases hint : x ∈ trackInterior (T d (cc : U))
    · exact Or.inl (hnew d (cc : U) huv x hint)
    · rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem hqfrom.2.1 hqfrom.2.2
        (List.getElem_mem (by omega)) hint with h | h
      · exfalso
        have hnd : (T d (cc : U)).Nodup := hqfrom.1.2.1
        have h10 : x = (T d (cc : U))[0]'(by omega) := by rw [h0]; exact h
        have h10' : (T d (cc : U))[1]'(by omega) = (T d (cc : U))[0]'(by omega) := h10
        exact absurd (hnd.getElem_inj_iff.mp h10') (by omega)
      · exact Or.inr h
  have hxa : x ≠ ι a := by
    rcases hxcase with h | h
    · exact fun hc => h ⟨a, hc.symm⟩
    · rw [h]; exact fun hc => hcna (hinj hc)
  have hxb : x ≠ ι b := by
    rcases hxcase with h | h
    · exact fun hc => h ⟨b, hc.symm⟩
    · rw [h]; exact fun hc => hcnb (hinj hc)
  refine ⟨s(ι d, x), hg, ?_, ?_, ?_⟩
  · -- not an edge of `B`
    rintro ⟨i, hi, heq⟩
    have hmem : ι d ∈ s((B)[i]'(by omega), (B)[i + 1]'hi) := by rw [← heq]; simp
    have hdB : ι d ∈ B := by
      rcases Sym2.mem_iff.mp hmem with h | h <;> rw [h] <;> exact List.getElem_mem _
    have hdint : ι d ∉ trackInterior B := fun hc => hbranch.2.1 _ hc (hrange ⟨d, rfl⟩)
    rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem hfrom.2.1 hfrom.2.2 hdB
      hdint with h | h
    · exact hdna (hinj (h.trans ha.symm))
    · exact hdnb (hinj (h.trans hb.symm))
  · rw [← ha]
    intro hc
    rcases Sym2.mem_iff.mp hc with h | h
    · exact hdna (hinj h.symm)
    · exact hxa h.symm
  · rw [← hb]
    intro hc
    rcases Sym2.mem_iff.mp hc with h | h
    · exact hdnb (hinj h.symm)
    · exact hxb h.symm

/-! ### A branch of a subdivision is one of the subdivision's tracks -/

theorem mem_of_mem_trackEdges {q : List W} {e : Sym2 W} (he : e ∈ trackEdges q) {w : W}
    (hw : w ∈ e) : w ∈ q := by
  obtain ⟨i, hi, rfl⟩ := he
  rcases Sym2.mem_iff.mp hw with h | h <;> rw [h] <;> exact List.getElem_mem _

theorem mem_trackInterior_of_not_range {U : Type*} {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    {u v : U} (huv : J.Adj u v) {w : W} (hw : w ∈ T u v) (hnr : w ∉ Set.range ι) :
    w ∈ trackInterior (T u v) := by
  by_contra hcon
  rcases Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem (htrack u v huv).2.1
    (htrack u v huv).2.2 hw hcon with h | h
  · exact hnr ⟨u, h.symm⟩
  · exact hnr ⟨v, h.symm⟩

theorem trackEdges_eq_of_sym2_eq {U : Type*} {J : SimpleGraph U} {T : U → U → List W}
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    {u v u' v' : U} (huv : J.Adj u v) (h : s(u, v) = s(u', v')) :
    trackEdges (T u' v') = trackEdges (T u v) := by
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rw [hrev _ _ huv, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]

/-- PAPER (printed p. 19–20, used silently): the branches of a subdivision `H` of `J` are exactly
the tracks the subdivision attaches to the edges of `J`. -/
theorem branch_eq_track {U : Type*} [Finite W] {J : SimpleGraph U} {H : SimpleGraph W}
    {ι : U → W} {T : U → U → List W}
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hdisj : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    (hrange : Set.range ι ⊆ branchVertices H) (hbrsub : branchVertices H ⊆ Set.range ι)
    {B : List W} {c₁ c₂ : W} (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hc₁ : c₁ ∈ branchVertices H) (hc₂ : c₂ ∈ branchVertices H) (hne : c₁ ≠ c₂)
    (hlen : 2 ≤ trackLength B) :
    ∃ u v : U, J.Adj u v ∧ ι u = c₁ ∧ ι v = c₂ ∧ trackEdges (T u v) = trackEdges B := by
  classical
  have hL : 3 ≤ B.length := by simp only [trackLength] at hlen; omega
  -- every edge of `B` lies on some track of the subdivision
  have hlab : ∀ (i : ℕ) (hi : i + 1 < B.length),
      ∃ u v : U, J.Adj u v ∧ s(B[i]'(by omega), B[i + 1]'hi) ∈ trackEdges (T u v) := by
    intro i hi
    have hmem : s(B[i]'(by omega), B[i + 1]'hi) ∈ H.edgeSet := hfrom.1.2.2 i hi
    rw [hedges] at hmem
    simpa using hmem
  obtain ⟨u₀, v₀, huv₀, he₀⟩ := hlab 0 (by omega)
  -- all edges of `B` lie on the same track
  have hall : ∀ (i : ℕ) (hi : i + 1 < B.length),
      s(B[i]'(by omega), B[i + 1]'hi) ∈ trackEdges (T u₀ v₀) := by
    intro i
    induction i with
    | zero => intro hi; exact he₀
    | succ n ih =>
      intro hi
      have hn : n + 1 < B.length := by omega
      have hprev := ih hn
      obtain ⟨u, v, huv, he⟩ := hlab (n + 1) hi
      -- the shared vertex `B[n+1]` is internal to `B`, hence not a branch-vertex
      have hwint : B[n + 1]'hn ∈ trackInterior B :=
        Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem B n (by omega)
      have hwnb : B[n + 1]'hn ∉ branchVertices H := hbranch.2.1 _ hwint
      have hwnr : B[n + 1]'hn ∉ Set.range ι := fun hc => hwnb (hrange hc)
      have hw₀ : B[n + 1]'hn ∈ T u₀ v₀ := mem_of_mem_trackEdges hprev (by simp)
      have hw₁ : B[n + 1]'hn ∈ T u v := mem_of_mem_trackEdges he (by simp)
      have hi₀ : B[n + 1]'hn ∈ trackInterior (T u₀ v₀) :=
        mem_trackInterior_of_not_range htrack huv₀ hw₀ hwnr
      have hsame : s(u₀, v₀) = s(u, v) := by
        by_contra hcon
        exact hdisj u₀ v₀ u v huv₀ huv hcon _ hi₀ hw₁
      rw [trackEdges_eq_of_sym2_eq hrev huv₀ hsame] at he
      exact he
  -- hence `trackEdges B ⊆ trackEdges (T u₀ v₀)`, and every vertex of `B` lies on that track
  have hsubE : trackEdges B ⊆ trackEdges (T u₀ v₀) := by
    rintro e ⟨i, hi, rfl⟩
    exact hall i hi
  have hsubV : ∀ w ∈ B, w ∈ T u₀ v₀ := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hw
    by_cases hlast : i + 1 < B.length
    · exact mem_of_mem_trackEdges (hall i hlast) (by simp)
    · have hi' : i = B.length - 1 := by omega
      subst hi'
      refine mem_of_mem_trackEdges (hall (B.length - 2) (by omega)) ?_
      have hidx : B.length - 2 + 1 = B.length - 1 := by omega
      rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq B hidx
        (by omega) (by omega)]
      simp
  -- maximality of the branch
  have hTint : ∀ w ∈ trackInterior (T u₀ v₀), w ∉ branchVertices H := fun w hw hcon =>
    hnew u₀ v₀ huv₀ w hw (hbrsub hcon)
  have hmax : trackEdges (T u₀ v₀) = trackEdges B :=
    hbranch.2.2 (T u₀ v₀) (htrack u₀ v₀ huv₀).1 hTint hsubE hsubV
  -- identify the two ends
  have hends : ∀ c : W, c ∈ B → c ∈ branchVertices H → c = ι u₀ ∨ c = ι v₀ := by
    intro c hcB hcb
    have hcT : c ∈ T u₀ v₀ := hsubV c hcB
    have hcint : c ∉ trackInterior (T u₀ v₀) := fun hcon =>
      hnew u₀ v₀ huv₀ c hcon (hbrsub hcb)
    exact Workspace.ProofLemmas.SubdivisionCompose.mem_ends_of_mem (htrack u₀ v₀ huv₀).2.1
      (htrack u₀ v₀ huv₀).2.2 hcT hcint
  have hc₁B : c₁ ∈ B := List.mem_of_mem_head? hfrom.2.1
  have hc₂B : c₂ ∈ B := List.mem_of_mem_getLast? hfrom.2.2
  rcases hends c₁ hc₁B hc₁ with h1 | h1 <;> rcases hends c₂ hc₂B hc₂ with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · exact ⟨u₀, v₀, huv₀, h1.symm, h2.symm, hmax⟩
  · refine ⟨v₀, u₀, huv₀.symm, h1.symm, h2.symm, ?_⟩
    rw [hrev u₀ v₀ huv₀, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    exact hmax
  · exact absurd (h1.trans h2.symm) hne

/-! ### Prefixes and suffixes of a track -/

theorem trackEdges_subset_of_prefix {pre suf : List W} :
    trackEdges pre ⊆ trackEdges (pre ++ suf) := by
  rintro e ⟨i, hi, rfl⟩
  refine ⟨i, by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_left (by omega), List.getElem_append_left (by omega)]

theorem trackEdges_subset_of_suffix {pre suf : List W} :
    trackEdges suf ⊆ trackEdges (pre ++ suf) := by
  rintro e ⟨i, hi, rfl⟩
  refine ⟨pre.length + i, by simp only [List.length_append]; omega, ?_⟩
  rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  congr 2
  omega

/-! ### Reshaping `expandTracks` so its first and last blocks are whole tracks -/

section Expand

open Workspace.ProofLemmas.SubdivisionCompose

variable {U : Type*} {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

theorem expandTracks_cons_cons' (hS : SubdivWitness J H ι T) (x y : U) (rest : List U)
    (hxy : J.Adj x y) (hch : List.IsChain J.Adj (y :: rest)) :
    expandTracks ι T (x :: y :: rest) = T x y ++ (expandTracks ι T (y :: rest)).tail := by
  have hlast : (T x y).dropLast ++ [ι y] = T x y :=
    List.dropLast_append_getLast? (ι y) (track_getLast? hS hxy)
  have hhead : (expandTracks ι T (y :: rest)).head? = some (ι y) := by
    rw [expandTracks_head? hS (y :: rest) hch]; rfl
  have hsplit : expandTracks ι T (y :: rest) = ι y :: (expandTracks ι T (y :: rest)).tail :=
    (List.cons_head?_tail hhead).symm
  calc expandTracks ι T (x :: y :: rest)
      = (T x y).dropLast ++ expandTracks ι T (y :: rest) := expandTracks_cons_cons x y rest
    _ = (T x y).dropLast ++ (ι y :: (expandTracks ι T (y :: rest)).tail) := by rw [← hsplit]
    _ = ((T x y).dropLast ++ [ι y]) ++ (expandTracks ι T (y :: rest)).tail := by simp
    _ = T x y ++ (expandTracks ι T (y :: rest)).tail := by rw [hlast]

theorem trackEdges_expand_prefix (hS : SubdivWitness J H ι T) {x y : U} {rest : List U}
    (hxy : J.Adj x y) (hch : List.IsChain J.Adj (y :: rest)) :
    trackEdges (T x y) ⊆ trackEdges (expandTracks ι T (x :: y :: rest)) := by
  rw [expandTracks_cons_cons' hS x y rest hxy hch]
  exact trackEdges_subset_of_prefix

theorem trackEdges_expand_suffix (hS : SubdivWitness J H ι T) {q : List U} {z x : U}
    (hz : q.getLast? = some z) (hch : List.IsChain J.Adj (q ++ [x])) (hzx : J.Adj z x) :
    trackEdges (T z x) ⊆ trackEdges (expandTracks ι T (q ++ [x])) := by
  have hq : List.IsChain J.Adj q := (List.isChain_append.mp hch).1
  have hEq := expandTracks_append_singleton hS q z x hz hch
  have hElast : (expandTracks ι T q).getLast? = some (ι z) := by
    rw [expandTracks_getLast? hS q hq, hz]; rfl
  have hdrop : (expandTracks ι T q).dropLast ++ [ι z] = expandTracks ι T q :=
    List.dropLast_append_getLast? (ι z) hElast
  have hTsplit : T z x = ι z :: (T z x).tail :=
    (List.cons_head?_tail (track_head? hS hzx)).symm
  have hstep : expandTracks ι T (q ++ [x]) = (expandTracks ι T q).dropLast ++ T z x := by
    calc expandTracks ι T (q ++ [x]) = expandTracks ι T q ++ (T z x).tail := hEq
      _ = ((expandTracks ι T q).dropLast ++ [ι z]) ++ (T z x).tail := by rw [hdrop]
      _ = (expandTracks ι T q).dropLast ++ (ι z :: (T z x).tail) := by simp
      _ = (expandTracks ι T q).dropLast ++ T z x := by rw [← hTsplit]
  rw [hstep]
  exact trackEdges_subset_of_suffix

end Expand

/-! ### A track of `J` from `a` to `b` with prescribed first and last edges -/

section JTrack

variable {U : Type*} [Fintype U] {J : SimpleGraph U}

/-- A connected set contains a track between any two of its vertices. -/
theorem exists_track_in_connected (S : Set U) (hS : ConnectedSet J S) {v w : U}
    (hv : v ∈ S) (hw : w ∈ S) :
    ∃ P : List U, IsTrackFrom J P v w ∧ ∀ x ∈ P, x ∈ S := by
  obtain ⟨a, ha, b, hb, P, hP, hPS, -, -⟩ :=
    Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack J S {v} {w} hS
      ⟨v, rfl⟩ ⟨w, rfl⟩ (Set.singleton_subset_iff.mpr hv) (Set.singleton_subset_iff.mpr hw)
  rw [Set.mem_singleton_iff] at ha hb
  subst ha
  subst hb
  exact ⟨P, hP, hPS⟩

/-- PAPER (used silently in the endgame of 7.5, *"they are joined by a path in `L(H)` using no
more vertices in `Nc₁ ∪ Nc₂`"*): in a 3-connected `J`, two adjacent vertices `a, b` are joined by
a track whose first edge is a prescribed edge `av ≠ ab` and whose last edge is a prescribed edge
`wb ≠ ab`.  (Deleting `a` and `b` leaves `J` connected, so `v` and `w` are joined off `{a,b}`.) -/
theorem exists_J_track (hJ : IsKConnected J 3) {a b v w : U} (hab : a ≠ b)
    (hav : J.Adj a v) (hbw : J.Adj b w) (hvb : v ≠ b) (hwa : w ≠ a) :
    ∃ t : List U, IsTrackFrom J (a :: (v :: t ++ [b])) a b ∧ (v :: t).getLast? = some w := by
  classical
  have hva : v ≠ a := (hav.ne).symm
  have hwb : w ≠ b := (hbw.ne).symm
  have hcard : ({a, b} : Set U).ncard < 3 := by
    have h1 : ({a, b} : Set U).ncard ≤ ({b} : Set U).ncard + 1 := Set.ncard_insert_le _ _
    simp only [Set.ncard_singleton] at h1
    omega
  have hconn : ConnectedSet J (({a, b} : Set U)ᶜ) := (hJ.2 _ hcard).preconnected
  have hvS : v ∈ (({a, b} : Set U))ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim hva hvb
  have hwS : w ∈ (({a, b} : Set U))ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    exact fun h => h.elim hwa hwb
  obtain ⟨P, hP, hPS⟩ := exists_track_in_connected _ hconn hvS hwS
  have hPa : a ∉ P := fun h => (hPS a h) (Or.inl rfl)
  have hPb : b ∉ P := fun h => (hPS b h) (Or.inr rfl)
  obtain ⟨t, rfl⟩ : ∃ t, P = v :: t := by
    cases P with
    | nil => exact absurd hP.1.1 (by simp)
    | cons c s =>
      have hc : c = v := by
        have h := hP.2.1
        simp only [List.head?_cons, Option.some_inj] at h
        exact h
      exact ⟨s, by rw [hc]⟩
  refine ⟨t, ?_, hP.2.2⟩
  -- glue `[a, v]` on the front
  have hav' : IsTrackFrom J [a, v] a v := by
    refine ⟨⟨by simp, by simp [hva.symm], ?_⟩, by simp, by simp⟩
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using hav
  have hglue1 : IsTrackFrom J ([a, v] ++ (v :: t).tail) a w := by
    refine (Workspace.ProofLemmas.TrackGlueAtCommonEndpoint J [a, v] (v :: t) a v w hav' hP
      ?_).1
    intro z hz1 hz2
    rcases (by simpa using hz1 : z = a ∨ z = v) with rfl | rfl
    · exact absurd hz2 hPa
    · rfl
  have hR1 : ([a, v] ++ (v :: t).tail) = a :: v :: t := by simp
  rw [hR1] at hglue1
  -- glue `[w, b]` on the back
  have hwb' : IsTrackFrom J [w, b] w b := by
    refine ⟨⟨by simp, by simp [hwb], ?_⟩, by simp, by simp⟩
    intro i hi
    have : i = 0 := by simp at hi; omega
    subst this
    simpa using hbw.symm
  have hglue2 : IsTrackFrom J ((a :: v :: t) ++ [w, b].tail) a b := by
    refine (Workspace.ProofLemmas.TrackGlueAtCommonEndpoint J (a :: v :: t) [w, b] a w b
      hglue1 hwb' ?_).1
    intro z hz1 hz2
    rcases (by simpa using hz2 : z = w ∨ z = b) with hzw | hzb
    · exact hzw
    · exfalso
      subst hzb
      rcases (by simpa using hz1 : z = a ∨ z = v ∨ z ∈ t) with h | h | h
      · exact hab h.symm
      · exact hvb h.symm
      · exact hPb (by simp [h])
  have hR2 : ((a :: v :: t) ++ [w, b].tail) = a :: (v :: t ++ [b]) := by simp
  rw [hR2] at hglue2
  exact hglue2

end JTrack

/-! ### The corresponding track of `H` -/

section HTrack

open Workspace.ProofLemmas.SubdivisionCompose

variable {U : Type*} [Fintype U] {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W}
  {T : U → U → List W}

/-- PAPER (endgame of 7.5, *"they are joined by a path in `L(H)` using no more vertices in
`Nc₁ ∪ Nc₂`"*): the `H`-track obtained by expanding the `J`-track of `exists_J_track`.  It runs
from `ι a` to `ι b` and contains the whole of `T a v` at its front and the whole of `T b w` at
its back, so its first and last edges are the prescribed ones. -/
theorem exists_H_track_pinned (hS : SubdivWitness J H ι T) (hJ : IsKConnected J 3)
    {a b v w : U} (hab : a ≠ b) (habe : J.Adj a b) (hav : J.Adj a v) (hbw : J.Adj b w)
    (hvb : v ≠ b) (hwa : w ≠ a) :
    ∃ τ : List W, IsTrackFrom H τ (ι a) (ι b) ∧ 2 ≤ τ.length ∧
      trackEdges (T a v) ⊆ trackEdges τ ∧ trackEdges (T b w) ⊆ trackEdges τ ∧
      (∀ z ∈ T a b, z ∈ τ → z = ι a ∨ z = ι b) := by
  obtain ⟨t, hτJ, hlastP⟩ := exists_J_track hJ hab hav hbw hvb hwa
  have hchJ : List.IsChain J.Adj (a :: (v :: t ++ [b])) :=
    List.isChain_iff_getElem.mpr hτJ.1.2.2
  refine ⟨expandTracks ι T (a :: (v :: t ++ [b])), ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact expandTracks_ne_nil hS hchJ (by simp)
  · exact expandTracks_nodup hS _ hchJ hτJ.1.2.1
  · exact List.isChain_iff_getElem.mp (expandTracks_isChain hS _ hchJ)
  · rw [expandTracks_head? hS _ hchJ, hτJ.2.1]; rfl
  · rw [expandTracks_getLast? hS _ hchJ, hτJ.2.2]; rfl
  · exact two_le_expandTracks_length hS hchJ (by simp)
  · exact trackEdges_expand_prefix hS hav hchJ.tail
  · have hq : (a :: v :: t).getLast? = some w := by
      rw [List.getLast?_cons_of_ne_nil (by simp)]
      exact hlastP
    have hsub : trackEdges (T w b) ⊆ trackEdges (expandTracks ι T (a :: (v :: t ++ [b]))) :=
      trackEdges_expand_suffix hS hq hchJ hbw.symm
    have heq : trackEdges (T b w) = trackEdges (T w b) := by
      rw [hS.rev b w hbw, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    rw [heq]
    exact hsub
  · have hbase : IsTrackFrom J [a, b] a b := by
      refine ⟨⟨by simp, by simp [habe.ne], ?_⟩, by simp, by simp⟩
      intro i hi
      have hi0 : i = 0 := by simp at hi; omega
      subst i
      simpa using habe
    have hbaseExpand : expandTracks ι T [a, b] = T a b := by
      have h := expandTracks_cons_cons' hS a b [] habe (by simp)
      simpa using h
    have hmeetJ : ∀ z ∈ [a, b], z ∈ a :: (v :: t ++ [b]) → z = a ∨ z = b := by
      intro z hz _
      simpa using hz
    have habAvoid : s(a, b) ∉ trackEdges (a :: (v :: t ++ [b])) := by
      intro he
      have hfirst := trackEdges_eq_first hτJ (by simp) he (by simp)
      have heq : s(a, b) = s(a, v) := by simpa using hfirst
      exact hvb (Sym2.congr_right.mp heq).symm
    have hmeet :=
      Workspace.ProofLemmas.SubdivisionTrackExpansion.expandTracks_meet_only_ends
        hS hbase hτJ hmeetJ (Or.inr habAvoid)
    intro z hzB hzτ
    exact hmeet z (by rw [hbaseExpand]; exact hzB) hzτ

end HTrack

/-! ### Locating an edge of `H` at a branch-vertex on one of the subdivision's tracks -/

section Locate

open Workspace.ProofLemmas.SubdivisionCompose

variable {U : Type*} {J : SimpleGraph U} {H : SimpleGraph W} {ι : U → W} {T : U → U → List W}

theorem edge_at_branch_vertex (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom H (T u v) (ι u) (ι v))
    (hrev : ∀ u v : U, J.Adj u v → T v u = (T u v).reverse)
    (hnew : ∀ u v : U, J.Adj u v → ∀ w ∈ trackInterior (T u v), w ∉ Set.range ι)
    (hedges : H.edgeSet = ⋃ (u : U) (v : U) (_ : J.Adj u v), trackEdges (T u v))
    {x : U} {e : Sym2 W} (he : e ∈ H.edgeSet) (hce : ι x ∈ e) :
    ∃ y : U, J.Adj x y ∧ e ∈ trackEdges (T x y) := by
  rw [hedges] at he
  simp only [Set.mem_iUnion] at he
  obtain ⟨p, q, hpq, hmem⟩ := he
  have hcT : ι x ∈ T p q := mem_of_mem_trackEdges hmem hce
  have hcint : ι x ∉ trackInterior (T p q) := fun hcon =>
    hnew p q hpq _ hcon ⟨x, rfl⟩
  rcases mem_ends_of_mem (htrack p q hpq).2.1 (htrack p q hpq).2.2 hcT hcint with h | h
  · have : x = p := hι h
    subst this
    exact ⟨q, hpq, hmem⟩
  · have : x = q := hι h
    subst this
    refine ⟨p, hpq.symm, ?_⟩
    rw [hrev _ _ hpq, Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse]
    exact hmem

end Locate

/-! ### PAPER: *"they are joined by a path in `L(H)` using no more vertices in `Nc₁ ∪ Nc₂`,
which is even (since `H` is bipartite)"* -/

section EvenPath

open Workspace.ProofLemmas.TrackToRungPath
open Workspace.ProofLemmas.SubdivisionCompose

variable {U : Type*} [Fintype U] [Finite W]

theorem exists_even_rung_path (G : SimpleGraph V) {J : SimpleGraph U} {H : SimpleGraph W}
    (hJ : IsKConnected J 3) (hsub : IsSubdivision J H) (col : H.Coloring (Fin 2))
    (K : Set V) (φ : H.lineGraph ≃g G.induce K)
    {B : List W} {c₁ c₂ : W} (hbranch : IsBranch H B) (hfrom : IsTrackFrom H B c₁ c₂)
    (hcol : col c₁ ≠ col c₂)
    (hc₁b : c₁ ∈ branchVertices H) (hc₂b : c₂ ∈ branchVertices H) (hc₁₂ : c₁ ≠ c₂)
    (hBlen : 2 ≤ trackLength B)
    {e₁ e₂ : Sym2 W} (he₁ : e₁ ∈ H.edgeSet) (he₂ : e₂ ∈ H.edgeSet)
    (hc₁e : c₁ ∈ e₁) (hc₂e : c₂ ∈ e₂)
    (hn₁ : e₁ ∉ trackEdges B) (hn₂ : e₂ ∉ trackEdges B) :
    ∃ p : List V, IsPathFrom G p (↑(φ ⟨e₁, he₁⟩) : V) (↑(φ ⟨e₂, he₂⟩) : V) ∧
      Even (pathLength p) ∧ 2 ≤ pathLength p ∧ (∀ x ∈ p, x ∈ K) ∧
      (∀ x ∈ SPGT.interior p, x ∉ NSet G H K φ c₁ ∧ x ∉ NSet G H K φ c₂) ∧
      (∀ (f : Sym2 W) (hf : f ∈ H.edgeSet), f ∈ trackEdges B → c₁ ∈ f → f ≠ e₁ →
        (↑(φ ⟨f, hf⟩) : V) ∉ p ∧
        G.Adj (↑(φ ⟨f, hf⟩) : V) (↑(φ ⟨e₁, he₁⟩) : V) ∧
        ∀ x ∈ p, x ≠ (↑(φ ⟨e₁, he₁⟩) : V) → ¬ G.Adj (↑(φ ⟨f, hf⟩) : V) x) ∧
      (∀ (f : Sym2 W) (hf : f ∈ H.edgeSet), f ∈ trackEdges B → c₂ ∈ f → f ≠ e₂ →
        (↑(φ ⟨f, hf⟩) : V) ∉ p ∧
        G.Adj (↑(φ ⟨f, hf⟩) : V) (↑(φ ⟨e₂, he₂⟩) : V) ∧
        ∀ x ∈ p, x ≠ (↑(φ ⟨e₂, he₂⟩) : V) → ¬ G.Adj (↑(φ ⟨f, hf⟩) : V) x) := by
  classical
  letI : Fintype W := Fintype.ofFinite W
  have hsub0 : IsSubdivision J H := hsub
  obtain ⟨ι, T, hι, htrack, hlenT, hrev, hdisj, hnew, hcover, hedges⟩ := hsub
  have hS : SubdivWitness J H ι T := ⟨hι, htrack, hlenT, hrev, hdisj, hnew⟩
  have hdeg : ∀ u : U, 3 ≤ (J.neighborSet u).ncard := fun u =>
    Workspace.ProofLemmas.SubdivisionCounting.three_le_degree_of_three_connected J hJ u
  have hrange : Set.range ι ⊆ branchVertices H :=
    Workspace.ProofLemmas.SubdivisionCounting.range_subset_branchVertices hι htrack hlenT
      hdisj hnew hdeg
  have hbrsub : branchVertices H ⊆ Set.range ι :=
    Workspace.ProofLemmas.SubdivisionCounting.branchVertices_subset_range htrack hrev hdisj
      hcover hedges
  obtain ⟨a, b, hab, ha, hb, hTB⟩ :=
    branch_eq_track htrack hrev hdisj hnew hedges hrange hbrsub hbranch hfrom hc₁b hc₂b hc₁₂
      hBlen
  -- locate the two prescribed edges on the subdivision's tracks
  have hc₁e' : ι a ∈ e₁ := by rw [ha]; exact hc₁e
  obtain ⟨v, hav, he₁T⟩ := edge_at_branch_vertex hι htrack hrev hnew hedges he₁ hc₁e'
  have hc₂e' : ι b ∈ e₂ := by rw [hb]; exact hc₂e
  obtain ⟨w, hbw, he₂T⟩ := edge_at_branch_vertex hι htrack hrev hnew hedges he₂ hc₂e'
  have hvb : v ≠ b := by
    rintro rfl
    exact hn₁ (hTB ▸ he₁T)
  have hwa : w ≠ a := by
    intro hwa'
    refine hn₂ ?_
    rw [← hTB, ← Workspace.ProofLemmas.SubdivisionCounting.trackEdges_reverse (T a b),
      ← hrev a b hab]
    rw [hwa'] at he₂T
    exact he₂T
  obtain ⟨τ, hτfrom, hτlen, hτ1, hτ2, hBτ⟩ :=
    exists_H_track_pinned hS hJ hab.ne hab hav hbw hvb hwa
  have hτfrom' : IsTrackFrom H τ c₁ c₂ := by rw [← ha, ← hb]; exact hτfrom
  have hnadj : ¬ H.Adj c₁ c₂ :=
    (Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H hsub0 B c₁ c₂
      hbranch hfrom hBlen).2.2.2
  have hτlist : IsTrackList H τ := hτfrom'.1
  have h1τ : 1 < τ.length := by omega
  have he₁τ : e₁ ∈ trackEdges τ := hτ1 he₁T
  have he₂τ : e₂ ∈ trackEdges τ := hτ2 he₂T
  have hfe : e₁ = s(τ[0]'(by omega), τ[1]'h1τ) :=
    trackEdges_eq_first hτfrom' h1τ he₁τ hc₁e
  have hle : e₂ = s(τ[τ.length - 2]'(by omega), τ[τ.length - 1]'(by omega)) :=
    trackEdges_eq_last hτfrom' h1τ he₂τ hc₂e
  have hidx2 : τ.length - 2 + 1 = τ.length - 1 := by omega
  have hleq : τ[τ.length - 2 + 1]'(by omega) = τ[τ.length - 1]'(by omega) :=
    Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq τ hidx2 (by omega)
      (by omega)
  have hle' : e₂ = s(τ[τ.length - 2]'(by omega), τ[τ.length - 2 + 1]'(by omega)) := by
    rw [hleq]; exact hle
  have hlenp : (trackRung φ τ hτlist).length = trackLength τ := trackRung_length φ τ hτlist
  have hτL : 1 ≤ trackLength τ := by simp only [trackLength]; omega
  have hlp : 0 < (trackRung φ τ hτlist).length := by
    rw [hlenp]; simp only [trackLength]; omega
  have hlp2 : τ.length - 2 < (trackRung φ τ hτlist).length := by
    rw [hlenp]; simp only [trackLength]; omega
  have hτthree : 3 ≤ τ.length := by
    by_contra hlt
    have hτtwo : τ.length = 2 := by omega
    have hfirst : τ[0]'(by omega) = c₁ := head_getElem hτfrom'.2.1 (by omega)
    have hlast : τ[1]'(by omega) = c₂ := by
      have h := last_getElem hτfrom'.2.2 (by omega)
      simpa [hτtwo] using h
    exact hnadj (by
      rw [← hfirst, ← hlast]
      exact hτlist.2.2 0 (by omega))
  refine ⟨trackRung φ τ hτlist, ⟨trackRung_isPathList φ τ hτlist hτL, ?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the first vertex of the rung is `φ e₁`
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlp]
    congr 1
    rw [trackRung_getElem φ τ hτlist 0 hlp h1τ (hfe ▸ he₁)]
    exact congrArg (fun z : H.edgeSet => (↑(φ z) : V)) (Subtype.ext hfe.symm)
  · -- the last vertex of the rung is `φ e₂`
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega : (trackRung φ τ hτlist).length - 1 < (trackRung φ τ hτlist).length)]
    congr 1
    have hidx3 : (trackRung φ τ hτlist).length - 1 = τ.length - 2 := by
      rw [hlenp]; simp only [trackLength]; omega
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq _ hidx3 (by omega)
      hlp2]
    rw [trackRung_getElem φ τ hτlist (τ.length - 2) hlp2 (by omega) (hle' ▸ he₂)]
    exact congrArg (fun z : H.edgeSet => (↑(φ z) : V)) (Subtype.ext hle'.symm)
  · -- parity
    obtain ⟨k, hk⟩ := track_odd_of_colour_ne col hτfrom' hcol
    refine ⟨k, ?_⟩
    simp only [pathLength, hlenp, hk]
    omega
  · -- the alternate line-graph path has at least two edges
    obtain ⟨k, hk⟩ := track_odd_of_colour_ne col hτfrom' hcol
    have hTLtwo : 2 ≤ trackLength τ := by simp only [trackLength]; omega
    simp only [pathLength]
    rw [hlenp, hk]
    omega
  · exact trackRung_subset_K φ τ hτlist
  · -- interior vertices avoid `Nc₁ ∪ Nc₂`
    intro x hx
    obtain ⟨j, hj, hjx⟩ :=
      (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_iff
        (trackRung φ τ hτlist) x).mp hx
    have hjp : j + 2 < trackLength τ := by rw [hlenp] at hj; exact hj
    have hjτ : j + 1 + 1 < τ.length := by simp only [trackLength] at hjp; omega
    have heτ : s(τ[j + 1]'(by omega), τ[j + 1 + 1]'hjτ) ∈ H.edgeSet :=
      trackEdge_mem_edgeSet hτlist (j + 1) hjτ
    have hbound : j + 1 < (trackRung φ τ hτlist).length := by rw [hlenp]; omega
    have hxeq : x = (↑(φ ⟨s(τ[j + 1]'(by omega), τ[j + 1 + 1]'hjτ), heτ⟩) : V) := by
      rw [← hjx]
      exact trackRung_getElem φ τ hτlist (j + 1) hbound hjτ heτ
    have hnc₁ : c₁ ∉ s(τ[j + 1]'(by omega), τ[j + 1 + 1]'hjτ) :=
      middle_edge_not_first hτfrom' hjτ (by omega)
    have hnc₂ : c₂ ∉ s(τ[j + 1]'(by omega), τ[j + 1 + 1]'hjτ) := by
      refine middle_edge_not_last hτfrom' hjτ ?_
      simp only [trackLength] at hjp
      omega
    rw [hxeq]
    exact ⟨not_mem_nset_of_not_mem G K φ c₁ heτ hnc₁,
      not_mem_nset_of_not_mem G K φ c₂ heτ hnc₂⟩
  · -- An edge at `c₁` different from the first edge of `τ` meets the rung only there.
    intro f hf hfB hcf hfe₁
    have hnotmem : (↑(φ ⟨f, hf⟩) : V) ∉ trackRung φ τ hτlist := by
      intro hmem
      obtain ⟨g, hg, hgτ, hfg⟩ :=
        (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hτlist).mp hmem
      have heq : f = g := phi_inj φ hf hg hfg
      have hgfirst : g = s(τ[0]'(by omega), τ[1]'h1τ) :=
        trackEdges_eq_first hτfrom' h1τ hgτ (heq ▸ hcf)
      exact hfe₁ (heq.trans (hgfirst.trans hfe.symm))
    have hadj : G.Adj (↑(φ ⟨f, hf⟩) : V) (↑(φ ⟨e₁, he₁⟩) : V) := by
      apply φ.map_rel_iff.mpr
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨fun h => hfe₁ (congrArg Subtype.val h), c₁, hcf, hc₁e⟩
    refine ⟨hnotmem, hadj, ?_⟩
    intro x hx hxfirst hfx
    obtain ⟨g, hg, hgτ, hxg⟩ :=
      (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hτlist).mp hx
    have hline : H.lineGraph.Adj ⟨f, hf⟩ ⟨g, hg⟩ := by
      apply φ.map_rel_iff.mp
      simpa [hxg] using hfx
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hline
    obtain ⟨hfgne, z, hzf, hzg⟩ := hline
    have hzB : z ∈ T a b := mem_of_mem_trackEdges (hTB ▸ hfB) hzf
    have hzτ : z ∈ τ := mem_of_mem_trackEdges hgτ hzg
    rcases hBτ z hzB hzτ with hzc | hzc
    · rw [ha] at hzc
      subst z
      have hgfirst : g = s(τ[0]'(by omega), τ[1]'h1τ) :=
        trackEdges_eq_first hτfrom' h1τ hgτ hzg
      apply hxfirst
      rw [hxg]
      apply congrArg (fun e : H.edgeSet => (↑(φ e) : V))
      exact Subtype.ext (hgfirst.trans hfe.symm)
    · rw [hb] at hzc
      subst z
      have hfends : f = s(c₁, c₂) := (Sym2.mem_and_mem_iff hc₁₂).mp ⟨hcf, hzf⟩
      exact hnadj (by
        show s(c₁, c₂) ∈ H.edgeSet
        rw [← hfends]
        exact hf)
  · -- Symmetrically, an edge at `c₂` different from the last edge meets the rung only there.
    intro f hf hfB hcf hfe₂
    have hnotmem : (↑(φ ⟨f, hf⟩) : V) ∉ trackRung φ τ hτlist := by
      intro hmem
      obtain ⟨g, hg, hgτ, hfg⟩ :=
        (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hτlist).mp hmem
      have heq : f = g := phi_inj φ hf hg hfg
      have hglast : g = s(τ[τ.length - 2]'(by omega), τ[τ.length - 1]'(by omega)) :=
        trackEdges_eq_last hτfrom' h1τ hgτ (heq ▸ hcf)
      exact hfe₂ (heq.trans (hglast.trans hle.symm))
    have hadj : G.Adj (↑(φ ⟨f, hf⟩) : V) (↑(φ ⟨e₂, he₂⟩) : V) := by
      apply φ.map_rel_iff.mpr
      rw [SimpleGraph.lineGraph_adj_iff_exists]
      exact ⟨fun h => hfe₂ (congrArg Subtype.val h), c₂, hcf, hc₂e⟩
    refine ⟨hnotmem, hadj, ?_⟩
    intro x hx hxlast hfx
    obtain ⟨g, hg, hgτ, hxg⟩ :=
      (Workspace.ProofLemmas.ThreeTracksLineGraphPrism.mem_trackRung_iff φ hτlist).mp hx
    have hline : H.lineGraph.Adj ⟨f, hf⟩ ⟨g, hg⟩ := by
      apply φ.map_rel_iff.mp
      simpa [hxg] using hfx
    rw [SimpleGraph.lineGraph_adj_iff_exists] at hline
    obtain ⟨hfgne, z, hzf, hzg⟩ := hline
    have hzB : z ∈ T a b := mem_of_mem_trackEdges (hTB ▸ hfB) hzf
    have hzτ : z ∈ τ := mem_of_mem_trackEdges hgτ hzg
    rcases hBτ z hzB hzτ with hzc | hzc
    · rw [ha] at hzc
      subst z
      have hfends : f = s(c₁, c₂) := (Sym2.mem_and_mem_iff hc₁₂).mp ⟨hzf, hcf⟩
      exact hnadj (by
        show s(c₁, c₂) ∈ H.edgeSet
        rw [← hfends]
        exact hf)
    · rw [hb] at hzc
      subst z
      have hglast : g = s(τ[τ.length - 2]'(by omega), τ[τ.length - 1]'(by omega)) :=
        trackEdges_eq_last hτfrom' h1τ hgτ hzg
      apply hxlast
      rw [hxg]
      apply congrArg (fun e : H.edgeSet => (↑(φ e) : V))
      exact Subtype.ext (hglast.trans hle.symm)

end EvenPath

/-! ### Small set-theoretic helpers for the skew partition -/

section SetHelpers

variable {V : Type*}

theorem reachable_of_subset (Γ : SimpleGraph V) {S S' : Set V} (hSS' : S ⊆ S')
    (hS : ConnectedSet Γ S) {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (ha' : a ∈ S') (hb' : b ∈ S') :
    (Γ.induce S').Reachable ⟨a, ha'⟩ ⟨b, hb'⟩ := by
  exact (hS ⟨a, ha⟩ ⟨b, hb⟩).map
    ({ toFun := fun z => ⟨(z : V), hSS' z.2⟩, map_rel' := fun h => h } :
      Γ.induce S →g Γ.induce S')

/-- A set split into two nonempty mutually anticomplete pieces is not connected. -/
theorem not_connectedSet_of_split (Γ : SimpleGraph V) (P Q : Set V)
    (hsep : ∀ p ∈ P, ∀ q ∈ Q, ¬ Γ.Adj p q) (hP : P.Nonempty) (hQ : Q.Nonempty)
    (hPQ : Disjoint P Q) : ¬ ConnectedSet Γ (P ∪ Q) := by
  intro hconn
  rcases sep_split Γ P Q (P ∪ Q) hsep (subset_rfl) hconn with h | h
  · obtain ⟨q, hq⟩ := hQ
    exact Set.disjoint_left.mp hPQ (h q (Or.inr hq)) hq
  · obtain ⟨p, hp⟩ := hP
    exact Set.disjoint_left.mp hPQ hp (h p (Or.inl hp))

/-- PAPER (*"`v` has a nonneighbour in `Y`, and so `Y ∪ v` is anticonnected"*). -/
theorem anticonnected_union_singleton (Γ : SimpleGraph V) (Y : Set V)
    (hY : AnticonnectedSet Γ Y) {v y₀ : V} (hy₀ : y₀ ∈ Y) (hnadj : ¬ Γ.Adj v y₀)
    (hvy : v ≠ y₀) : AnticonnectedSet Γ (Y ∪ {v}) := by
  have hsub : Y ⊆ Y ∪ {v} := Set.subset_union_left
  have hy₀' : y₀ ∈ Y ∪ {v} := Or.inl hy₀
  have hv' : v ∈ Y ∪ {v} := Or.inr rfl
  have key : ∀ a : ↥(Y ∪ {v} : Set V), (Γᶜ.induce (Y ∪ {v})).Reachable a ⟨y₀, hy₀'⟩ := by
    rintro ⟨a, ha⟩
    have haM : a ∈ Y ∪ ({v} : Set V) := ha
    rcases ha with haY | hav
    · exact reachable_of_subset Γᶜ hsub hY haY hy₀ _ hy₀'
    · have hav' : a = v := hav
      refine SimpleGraph.Adj.reachable
        (show (Γᶜ.induce (Y ∪ ({v} : Set V))).Adj ⟨a, haM⟩ ⟨y₀, hy₀'⟩ from ?_)
      show Γᶜ.Adj a y₀
      rw [SimpleGraph.compl_adj, hav']
      exact ⟨hvy, hnadj⟩
  intro a b
  exact (key a).trans (key b).symm

end SetHelpers

/-! ### More about `N_c` -/

section NSetMore

variable {V W : Type*}

/-- `Nc₁` and `Nc₂` are disjoint when `c₁c₂` is not an edge: a common vertex would be an edge of
`H` containing both `c₁` and `c₂`. -/
theorem nset_disjoint (G : SimpleGraph V) {H : SimpleGraph W} (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) {c₁ c₂ : W} (hne : c₁ ≠ c₂) (hnadj : ¬ H.Adj c₁ c₂) :
    ∀ x, x ∈ NSet G H K φ c₁ → x ∉ NSet G H K φ c₂ := by
  rintro x ⟨e, he, hec, rfl⟩ ⟨f, hf, hfc, hxf⟩
  have hef : e = f := phi_inj φ he hf hxf
  subst hef
  have hE : e = s(c₁, c₂) := (Sym2.mem_and_mem_iff hne).mp ⟨hec.2, hfc.2⟩
  rw [hE] at he
  exact hnadj he

/-- A branch-vertex `c` has `≥ 3` incident edges, so `N_c` has a vertex different from any
prescribed `r`. -/
theorem nset_ne [Finite W] (G : SimpleGraph V) (H : SimpleGraph W) (K : Set V)
    (φ : H.lineGraph ≃g G.induce K) (c : W) (hc : c ∈ branchVertices H) (r : V) :
    ∃ x, x ∈ NSet G H K φ c ∧ x ≠ r := by
  classical
  have hcard : 3 ≤ (H.neighborSet c).ncard := hc
  obtain ⟨w₁, hw₁⟩ : (H.neighborSet c).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hd1 : (H.neighborSet c \ {w₁}).ncard = (H.neighborSet c).ncard - 1 :=
    Set.ncard_diff_singleton_of_mem hw₁
  obtain ⟨w₂, hw₂⟩ : (H.neighborSet c \ {w₁}).Nonempty := by
    rw [← Set.ncard_pos (Set.toFinite _)]; omega
  have hne12 : w₁ ≠ w₂ := fun h => hw₂.2 (by rw [← h]; rfl)
  have he₁ : s(c, w₁) ∈ H.edgeSet := hw₁
  have he₂ : s(c, w₂) ∈ H.edgeSet := hw₂.1
  have hx₁ : (↑(φ ⟨s(c, w₁), he₁⟩) : V) ∈ NSet G H K φ c := mem_nset G H K φ c he₁ (by simp)
  have hx₂ : (↑(φ ⟨s(c, w₂), he₂⟩) : V) ∈ NSet G H K φ c := mem_nset G H K φ c he₂ (by simp)
  have hxne : (↑(φ ⟨s(c, w₁), he₁⟩) : V) ≠ (↑(φ ⟨s(c, w₂), he₂⟩) : V) := by
    intro hcon
    exact hne12 (Sym2.congr_right.mp (phi_inj φ he₁ he₂ hcon))
  by_cases h : (↑(φ ⟨s(c, w₁), he₁⟩) : V) = r
  · exact ⟨_, hx₂, fun hcon => hxne (h.trans hcon.symm)⟩
  · exact ⟨_, hx₁, h⟩

end NSetMore

/-! ### Two list utilities -/

section ListUtil

variable {V : Type*}

theorem mem_of_mem_interior {p : List V} {x : V} (h : x ∈ SPGT.interior p) : x ∈ p :=
  List.tail_subset _ (List.dropLast_subset _ h)

/-- An explicit induced path on four vertices. -/
theorem isPathList_four (G : SimpleGraph V) (a b c d : V)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hac : ¬ G.Adj a c) (hbd : ¬ G.Adj b d) (had : ¬ G.Adj a d)
    (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c) (h5 : b ≠ d) (h6 : c ≠ d) :
    IsPathList G [a, b, c, d] := by
  have hba : G.Adj b a := hab.symm
  have hcb : G.Adj c b := hbc.symm
  have hdc : G.Adj d c := hcd.symm
  have hca : ¬ G.Adj c a := fun h => hac h.symm
  have hdb : ¬ G.Adj d b := fun h => hbd h.symm
  have hda : ¬ G.Adj d a := fun h => had h.symm
  refine ⟨by simp, by simp [h1, h2, h3, h4, h5, h6], ?_⟩
  intro i j hi hj
  simp only [List.length_cons, List.length_nil] at hi hj
  interval_cases i <;> interval_cases j <;>
    simp [hab, hbc, hcd, hac, hbd, had, hba, hcb, hdc, hca, hdb, hda, G.irrefl]

end ListUtil

end Thm75EndgameHelpers

namespace Workspace.ProofLemmas.Thm75Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.ProofLemmas.Thm75Setup
open Thm75EndgameHelpers

theorem thm75Endgame_of_claim3 {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U]
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
    (hLManti : Anticomplete G L M) (hSL : S ⊆ L) (hTM : T ⊆ M)
    (hclaim3 : ∀ r₁ r₂ : V,
      NSet G H K φ c₁ ∩ Rset = {r₁} → NSet G H K φ c₂ ∩ Rset = {r₂} →
      X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) = ∅ →
      (NSet G H K φ c₁ \ {r₁} ⊆ X₁) ∧
        (NSet G H K φ c₂ \ {r₂} ⊆ X₁)) :
    AdmitsBalancedSkewPartition G := by
  classical
  by_contra hgoal
  obtain ⟨col⟩ := happ.1.2
  obtain ⟨hc₁₂, hc₁b, hc₂b, hnadj⟩ :=
    Workspace.ProofLemmas.Thm75BranchEnds.thm75BranchEnds J hJ H happ.1.1 B c₁ c₂ hbranch hfrom
      (by omega)
  have hcol : col c₁ ≠ col c₂ := colour_ne_of_odd col hfrom hodd
  have hBlen2 : 1 < B.length := by simp only [trackLength] at hlen; omega
  obtain ⟨r₁, r₂, hr₁, hr₂⟩ := rung_ends G K φ hfrom hBlen2 Rset hRset
  -- `Y` lies outside the line graph
  have hYK : ∀ y ∈ Y, y ∉ K := fun y hy =>
    Workspace.ProofLemmas.Thm75DominantOutsideLineGraph.thm75DominantOutsideLineGraph
      G J hJ H K φ happ B c₁ c₂ hbranch hfrom hlen y (hYdom y hy)
  -- membership in the two sides
  have hmemA : ∀ x : V, x ∈ L ∪ M ↔ x ∉ X₀ ∪ X₁ ∪ Y := by
    intro x; rw [hLM]; exact Iff.rfl
  have hXsub : X₀ ∪ X₁ ⊆ X := by
    rintro x (h | h)
    · rw [hX₀] at h; exact h.1
    · rw [hX₁] at h; exact h.1
  -- `S` is nonempty
  obtain ⟨e₀, he₀B, he₀c₁, he₀c₂⟩ := exists_rung_middle hfrom hlen
  have he₀E : e₀ ∈ H.edgeSet := trackEdges_subset_edgeSet hfrom.1 he₀B
  have hs₀X₁ : (↑(φ ⟨e₀, he₀E⟩) : V) ∉ X₁ := by
    rw [hX₁]
    rintro ⟨-, h | h⟩
    · exact not_mem_nset_of_not_mem G K φ c₁ he₀E he₀c₁ h
    · exact not_mem_nset_of_not_mem G K φ c₂ he₀E he₀c₂ h
  have hs₀S : (↑(φ ⟨e₀, he₀E⟩) : V) ∈ S := by
    rw [hS]
    exact ⟨by rw [hRset]; exact ⟨e₀, he₀E, he₀B, rfl⟩, hs₀X₁⟩
  have hs₀A : (↑(φ ⟨e₀, he₀E⟩) : V) ∈ L ∪ M := Or.inl (hSL hs₀S)
  have hLne : L.Nonempty := ⟨_, hSL hs₀S⟩
  -- `T` is nonempty
  obtain ⟨g₀, hg₀E, hg₀B, hg₀c₁, hg₀c₂⟩ :=
    exists_far_edge hJ happ.1.1 hbranch hfrom hc₁b hc₂b hc₁₂
  have ht₀X₁ : (↑(φ ⟨g₀, hg₀E⟩) : V) ∉ X₁ := by
    rw [hX₁]
    rintro ⟨-, h | h⟩
    · exact not_mem_nset_of_not_mem G K φ c₁ hg₀E hg₀c₁ h
    · exact not_mem_nset_of_not_mem G K φ c₂ hg₀E hg₀c₂ h
  have ht₀R : (↑(φ ⟨g₀, hg₀E⟩) : V) ∉ Rset := by
    rw [hRset]
    rintro ⟨f, hf, hfB, hxf⟩
    exact hg₀B (by rw [phi_inj φ hg₀E hf hxf]; exact hfB)
  have ht₀T : (↑(φ ⟨g₀, hg₀E⟩) : V) ∈ T := by
    rw [hT]
    exact ⟨⟨Subtype.coe_prop _, ht₀R⟩, ht₀X₁⟩
  have hMne : M.Nonempty := ⟨_, hTM ht₀T⟩
  -- `X₁` is nonempty, by claim (1)
  obtain ⟨hcl1, -⟩ :=
    Workspace.ProofLemmas.Thm75Claim1.thm75Claim1 G hG J hJ H K φ happ B c₁ c₂ hbranch hfrom
      hodd hlen Y hYne hYanti hYdom
  obtain ⟨n, n', hn, hn', hnn'⟩ := nset_two G H K φ c₁ hc₁b
  have hX₁ne : X₁.Nonempty := by
    by_cases hnX : n ∈ {x : V | VertexComplete G x Y}
    · exact ⟨n, by rw [hX₁, hX]; exact ⟨hnX, Or.inl hn⟩⟩
    · by_cases hn'X : n' ∈ {x : V | VertexComplete G x Y}
      · exact ⟨n', by rw [hX₁, hX]; exact ⟨hn'X, Or.inl hn'⟩⟩
      · exact absurd (hcl1 ⟨hn, hnX⟩ ⟨hn', hn'X⟩) hnn'
  -- the skew partition
  have hsepXY : ∀ p ∈ X₀ ∪ X₁, ∀ q ∈ Y, ¬ Gᶜ.Adj p q := by
    intro p hp q hq hadj
    have hpX : p ∈ X := hXsub hp
    rw [hX] at hpX
    exact ((SimpleGraph.compl_adj G p q).mp hadj).2 (hpX q hq)
  have hdisjXY : Disjoint (X₀ ∪ X₁) Y := by
    rw [Set.disjoint_left]
    intro p hp hq
    have hpX : p ∈ X := hXsub hp
    rw [hX] at hpX
    exact G.irrefl (hpX p hq)
  have hAB : IsSkewPartition G (L ∪ M) (X₀ ∪ X₁ ∪ Y) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hLM]; exact Set.compl_union_self _
    · rw [hLM]; exact disjoint_compl_left
    · exact not_connectedSet_of_split G L M hLManti hLne hMne hLMdisj
    · exact not_connectedSet_of_split Gᶜ (X₀ ∪ X₁) Y hsepXY
        (hX₁ne.mono Set.subset_union_right) hYne hdisjXY
  -- 4.2: we may assume the skew partition is not loose
  by_cases hloose : IsLooseSkewPartition G (L ∪ M) (X₀ ∪ X₁ ∪ Y)
  · exact hgoal (Workspace.Statements.S04.SPGT.thm_4_2 G hG ⟨_, _, hloose⟩)
  -- `Y` is an anticomponent of the cutset
  have hYcomp : IsAnticomponent G (X₀ ∪ X₁ ∪ Y) Y := by
    refine ⟨Set.subset_union_right, hYanti, ?_⟩
    intro D hYD hDB hDconn
    have hsep : ∀ p ∈ D \ Y, ∀ q ∈ Y, ¬ Gᶜ.Adj p q := by
      rintro p ⟨hpD, hpY⟩ q hq
      rcases hDB hpD with h | h
      · exact hsepXY p h q hq
      · exact absurd h hpY
    have hDsub : D ⊆ (D \ Y) ∪ Y := by
      intro x hx
      by_cases h : x ∈ Y
      · exact Or.inr h
      · exact Or.inl ⟨hx, h⟩
    rcases sep_split Gᶜ (D \ Y) Y D hsep hDsub hDconn with h | h
    · obtain ⟨y, hy⟩ := hYne
      exact absurd hy (h y (hYD hy)).2
    · exact Set.Subset.antisymm h hYD
  -- hence `X₂` is empty
  have hX₂ : X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro x ⟨hxX, hxK, hxN⟩
    refine hloose ⟨hAB, Or.inr ⟨x, ?_, Y, hYcomp, ?_⟩⟩
    · rw [hmemA]
      rintro ((h | h) | h)
      · rw [hX₀] at h; exact h.2 hxK
      · rw [hX₁] at h; exact hxN h.2
      · exact hYK x h hxK
    · rw [hX] at hxX; exact hxX
  -- claim (3)
  obtain ⟨h3₁, h3₂⟩ := hclaim3 r₁ r₂ hr₁ hr₂ hX₂
  -- the kernel `W = (Nc₁ \ {r₁}) ∪ (Nc₂ \ {r₂})`
  have hNanti : Anticomplete G (NSet G H K φ c₁) (NSet G H K φ c₂) :=
    nset_anticomplete col G K φ hcol hnadj
  have hP₁ne : (NSet G H K φ c₁ \ {r₁}).Nonempty := by
    obtain ⟨x, hx, hxr⟩ := nset_ne G H K φ c₁ hc₁b r₁
    exact ⟨x, hx, hxr⟩
  have hP₂ne : (NSet G H K φ c₂ \ {r₂}).Nonempty := by
    obtain ⟨x, hx, hxr⟩ := nset_ne G H K φ c₂ hc₂b r₂
    exact ⟨x, hx, hxr⟩
  have hPanti : Anticomplete G (NSet G H K φ c₁ \ {r₁}) (NSet G H K φ c₂ \ {r₂}) :=
    fun x hx y hy => hNanti x hx.1 y hy.1
  have hWanti : AnticonnectedSet G ((NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂})) :=
    Workspace.ProofLemmas.Thm75AnticonnectedUnion.thm75AnticonnectedUnion G _ _ hPanti hP₁ne
      hP₂ne
  have hWsub : (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}) ⊆ X₀ ∪ X₁ ∪ Y := by
    rintro x (hx | hx)
    · exact Or.inl (Or.inr (h3₁ hx))
    · exact Or.inl (Or.inr (h3₂ hx))
  have hPdisj12 : ∀ x, x ∈ NSet G H K φ c₁ \ {r₁} → x ∉ NSet G H K φ c₂ \ {r₂} :=
    fun x hx hx2 => nset_disjoint G K φ hc₁₂ hnadj x hx.1 hx2.1
  -- PAPER: *"every `W`-complete vertex is `Bc₁c₂`-dominant, and so belongs to `X ∪ Y`"*
  have hnoWcomp : ∀ v ∈ L ∪ M,
      ¬ VertexComplete G v ((NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂})) := by
    intro v hv hcomp
    have hdom : IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) v := by
      constructor
      · intro x hx y hy
        have hxr : x = r₁ := by
          by_contra hne
          exact hx.2 (hcomp x (Or.inl ⟨hx.1, hne⟩))
        have hyr : y = r₁ := by
          by_contra hne
          exact hy.2 (hcomp y (Or.inl ⟨hy.1, hne⟩))
        rw [hxr, hyr]
      · intro x hx y hy
        have hxr : x = r₂ := by
          by_contra hne
          exact hx.2 (hcomp x (Or.inr ⟨hx.1, hne⟩))
        have hyr : y = r₂ := by
          by_contra hne
          exact hy.2 (hcomp y (Or.inr ⟨hy.1, hne⟩))
        rw [hxr, hyr]
    by_cases hvX : v ∈ X
    · refine (hmemA v).mp hv ?_
      by_cases hvK : v ∈ K
      · by_cases hvN : v ∈ NSet G H K φ c₁ ∪ NSet G H K φ c₂
        · exact Or.inl (Or.inr (by rw [hX₁]; exact ⟨hvX, hvN⟩))
        · exfalso
          have hmem : v ∈ X ∩ (K \ (NSet G H K φ c₁ ∪ NSet G H K φ c₂)) := ⟨hvX, hvK, hvN⟩
          rw [hX₂] at hmem
          exact hmem
      · exact Or.inl (Or.inl (by rw [hX₀]; exact ⟨hvX, hvK⟩))
    · rw [hX] at hvX
      have hvX' : ¬ VertexComplete G v Y := hvX
      have hvY : ∃ y ∈ Y, ¬ G.Adj v y := by
        by_contra hcon
        refine hvX' ?_
        intro y hy
        by_contra h
        exact hcon ⟨y, hy, h⟩
      obtain ⟨y₀, hy₀Y, hy₀⟩ := hvY
      have hvy : v ≠ y₀ := by
        intro hcon
        exact (hmemA v).mp hv (Or.inr (by rw [hcon]; exact hy₀Y))
      have hanti' : AnticonnectedSet G (Y ∪ {v}) :=
        anticonnected_union_singleton G Y hYanti hy₀Y hy₀ hvy
      have hall : ∀ z ∈ Y ∪ ({v} : Set V),
          IsDominantFor G (NSet G H K φ c₁) (NSet G H K φ c₂) z := by
        rintro z (hz | hz)
        · exact hYdom z hz
        · have hzv : z = v := hz
          rw [hzv]; exact hdom
      have heq := hYmax (Y ∪ {v}) Set.subset_union_left hanti' hall
      have hvYm : v ∈ Y := by rw [← heq]; exact Or.inr rfl
      exact (hmemA v).mp hv (Or.inr hvYm)
  -- a component of the big side, and the kernel
  obtain ⟨A₁, hA₁comp, hs₀A₁⟩ :=
    Workspace.ProofLemmas.ComponentsOfSetBasics.exists_isComponent_mem G (L ∪ M) hs₀A
  have hkernel : IsKernel G (L ∪ M) (X₀ ∪ X₁ ∪ Y)
      ((NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂})) :=
    ⟨hAB, hWanti, hWsub, A₁, hA₁comp, fun v hv => hnoWcomp v (hA₁comp.1 hv)⟩
  -- PAPER: the even path of `L(H)` between the two parts of `W`
  have hpathgen : ∀ u ∈ NSet G H K φ c₁ \ {r₁}, ∀ v ∈ NSet G H K φ c₂ \ {r₂},
      ∃ p : List V, IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ L ∪ M) ∧
        Even (pathLength p) := by
    rintro u ⟨hu, hur⟩ v ⟨hv, hvr⟩
    obtain ⟨e, he, hec, rfl⟩ := hu
    obtain ⟨f, hf, hfc, rfl⟩ := hv
    have hn₁ : e ∉ trackEdges B := by
      intro hcon
      have hmem : (↑(φ ⟨e, he⟩) : V) ∈ NSet G H K φ c₁ ∩ Rset :=
        ⟨⟨e, he, hec, rfl⟩, by rw [hRset]; exact ⟨e, he, hcon, rfl⟩⟩
      rw [hr₁] at hmem
      exact hur hmem
    have hn₂ : f ∉ trackEdges B := by
      intro hcon
      have hmem : (↑(φ ⟨f, hf⟩) : V) ∈ NSet G H K φ c₂ ∩ Rset :=
        ⟨⟨f, hf, hfc, rfl⟩, by rw [hRset]; exact ⟨f, hf, hcon, rfl⟩⟩
      rw [hr₂] at hmem
      exact hvr hmem
    obtain ⟨p, hp, hpe, _hplen, hpK, hpint, _hpstart, _hpend⟩ :=
      exists_even_rung_path G hJ happ.1.1 col K φ hbranch hfrom hcol hc₁b hc₂b hc₁₂
        (by omega) he hf hec.2 hfc.2 hn₁ hn₂
    refine ⟨p, hp, ?_, hpe⟩
    intro x hx
    obtain ⟨hxN₁, hxN₂⟩ := hpint x hx
    have hxK : x ∈ K := hpK x (mem_of_mem_interior hx)
    rw [hmemA]
    rintro ((h | h) | h)
    · rw [hX₀] at h; exact h.2 hxK
    · rw [hX₁] at h; rcases h.2 with h' | h'; exacts [hxN₁ h', hxN₂ h']
    · exact hYK x h hxK
  -- the first hypothesis of 4.6
  have hpath : ∀ u ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}),
      ∀ v ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), ¬ G.Adj u v →
      (∃ x ∈ A₁, G.Adj u x) → (∃ x ∈ A₁, G.Adj v x) →
      ∃ p : List V, IsPathFrom G p u v ∧ (∀ x ∈ SPGT.interior p, x ∈ L ∪ M) ∧
        Even (pathLength p) := by
    intro u hu v hv hnadjuv _ _
    by_cases huv : u = v
    · subst huv
      refine ⟨[u], ⟨⟨by simp, by simp, ?_⟩, by simp, by simp⟩, ?_, ?_⟩
      · intro i j hi hj
        simp only [List.length_cons, List.length_nil] at hi hj
        have hi0 : i = 0 := by omega
        have hj0 : j = 0 := by omega
        subst hi0; subst hj0
        simp
      · simp [SPGT.interior]
      · simp [pathLength]
    · rcases hu with hu1 | hu2
      · rcases hv with hv1 | hv2
        · exact absurd (nset_clique G H K φ c₁ u hu1.1 v hv1.1 huv) hnadjuv
        · exact hpathgen u hu1 v hv2
      · rcases hv with hv1 | hv2
        · obtain ⟨p, hp, hpint, hpe⟩ := hpathgen v hv1 u hu2
          refine ⟨p.reverse, Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hp, ?_, ?_⟩
          · intro x hx
            exact hpint x (Workspace.ProofLemmas.PathBasics.mem_interior_reverse.mp hx)
          · simpa [pathLength] using hpe
        · exact absurd (nset_clique G H K φ c₂ u hu2.1 v hv2.1 huv) hnadjuv
  -- the structure of `Ḡ|W`: a complete bipartite graph between the two cliques
  have hpart : ∀ x ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}),
      ∀ y ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), Gᶜ.Adj x y →
      (x ∈ NSet G H K φ c₁ \ {r₁} ∧ y ∈ NSet G H K φ c₂ \ {r₂}) ∨
      (x ∈ NSet G H K φ c₂ \ {r₂} ∧ y ∈ NSet G H K φ c₁ \ {r₁}) := by
    rintro x (hx | hx) y (hy | hy) hadj
    · exact absurd (nset_clique G H K φ c₁ x hx.1 y hy.1
        ((SimpleGraph.compl_adj G x y).mp hadj).1) ((SimpleGraph.compl_adj G x y).mp hadj).2
    · exact Or.inl ⟨hx, hy⟩
    · exact Or.inr ⟨hx, hy⟩
    · exact absurd (nset_clique G H K φ c₂ x hx.1 y hy.1
        ((SimpleGraph.compl_adj G x y).mp hadj).1) ((SimpleGraph.compl_adj G x y).mp hadj).2
  have hcross : ∀ x ∈ NSet G H K φ c₁ \ {r₁}, ∀ y ∈ NSet G H K φ c₂ \ {r₂}, Gᶜ.Adj x y := by
    intro x hx y hy
    rw [SimpleGraph.compl_adj]
    exact ⟨fun h => hPdisj12 x hx (by rw [h]; exact hy), hNanti x hx.1 y hy.1⟩
  -- the second hypothesis of 4.6
  have hantipath : ∀ u ∈ A₁, ∀ v ∈ A₁, G.Adj u v →
      (∃ w ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), ¬ G.Adj u w) →
      (∃ w ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), ¬ G.Adj v w) →
      ∃ p : List V, IsAntipathFrom G p u v ∧
        (∀ x ∈ SPGT.interior p, x ∈ X₀ ∪ X₁ ∪ Y) ∧ Even (pathLength p) := by
    rintro u hu v hv hadjuv ⟨wu, hwu, hnu⟩ ⟨wv, hwv, hnv⟩
    have huA : u ∈ L ∪ M := hA₁comp.1 hu
    have hvA : v ∈ L ∪ M := hA₁comp.1 hv
    have huW : u ∉ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}) :=
      fun h => (hmemA u).mp huA (hWsub h)
    have hvW : v ∉ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}) :=
      fun h => (hmemA v).mp hvA (hWsub h)
    have hnadjc : ¬ Gᶜ.Adj u v := fun h => ((SimpleGraph.compl_adj G u v).mp h).2 hadjuv
    have hattu : ∃ f ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), Gᶜ.Adj u f := by
      refine ⟨wu, hwu, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => huW (by rw [h]; exact hwu), hnu⟩
    have hattv : ∃ f ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}), Gᶜ.Adj v f := by
      refine ⟨wv, hwv, ?_⟩
      rw [SimpleGraph.compl_adj]
      exact ⟨fun h => hvW (by rw [h]; exact hwv), hnv⟩
    obtain ⟨p, hp, h3, hint, -, -, -⟩ :=
      Workspace.ProofLemmas.MinimalConnectedIsPath.exists_path_interior_attached
        (G := Gᶜ) hWanti hadjuv.ne hnadjc huW hvW hattu hattv
    rcases Nat.even_or_odd (pathLength p) with hev | hod
    · exact ⟨p, hp, fun x hx => hWsub (hint x hx), hev⟩
    · exfalso
      have hnd : p.Nodup := hp.1.2.1
      have h4 : 4 ≤ p.length := by
        obtain ⟨k, hk⟩ := hod
        simp only [pathLength] at hk
        omega
      have he0 : p[0]'(by omega) = u :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
      by_cases hlen4 : p.length = 4
      · -- PAPER: *"it can be reordered to be an odd path that we have already shown impossible"*
        have he3 : p[3]'(by omega) = v := by
          have h := Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2
            (show 0 < p.length by omega)
          rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq p
            (show p.length - 1 = 3 by omega) (by omega) (by omega)] at h
          exact h
        have hw1 : p[1]'(by omega) ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}) :=
          hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem p 0
            (by omega))
        have hw2 : p[2]'(by omega) ∈ (NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂}) :=
          hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem p 1
            (by omega))
        have a01 : Gᶜ.Adj (p[0]'(by omega)) (p[1]'(by omega)) :=
          (hp.1.2.2 0 1 (by omega) (by omega)).mpr (Or.inl rfl)
        have a12 : Gᶜ.Adj (p[1]'(by omega)) (p[2]'(by omega)) :=
          (hp.1.2.2 1 2 (by omega) (by omega)).mpr (Or.inl rfl)
        have a23 : Gᶜ.Adj (p[2]'(by omega)) (p[3]'(by omega)) :=
          (hp.1.2.2 2 3 (by omega) (by omega)).mpr (Or.inl rfl)
        have n02 : ¬ Gᶜ.Adj (p[0]'(by omega)) (p[2]'(by omega)) := by
          intro h
          have := (hp.1.2.2 0 2 (by omega) (by omega)).mp h
          omega
        have n13 : ¬ Gᶜ.Adj (p[1]'(by omega)) (p[3]'(by omega)) := by
          intro h
          have := (hp.1.2.2 1 3 (by omega) (by omega)).mp h
          omega
        -- distinctness
        have d01 : p[0]'(by omega) ≠ p[1]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have d02 : p[0]'(by omega) ≠ p[2]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have d03 : p[0]'(by omega) ≠ p[3]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have d12 : p[1]'(by omega) ≠ p[2]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have d13 : p[1]'(by omega) ≠ p[3]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        have d23 : p[2]'(by omega) ≠ p[3]'(by omega) := fun h => by
          have := hnd.getElem_inj_iff.mp h; omega
        -- the reordered odd path `w₁-v-u-w₂`
        have g13 : G.Adj (p[1]'(by omega)) (p[3]'(by omega)) := by
          by_contra h
          exact n13 ((SimpleGraph.compl_adj G _ _).mpr ⟨d13, h⟩)
        have g02 : G.Adj (p[0]'(by omega)) (p[2]'(by omega)) := by
          by_contra h
          exact n02 ((SimpleGraph.compl_adj G _ _).mpr ⟨d02, h⟩)
        have ng01 : ¬ G.Adj (p[0]'(by omega)) (p[1]'(by omega)) :=
          ((SimpleGraph.compl_adj G _ _).mp a01).2
        have ng12 : ¬ G.Adj (p[1]'(by omega)) (p[2]'(by omega)) :=
          ((SimpleGraph.compl_adj G _ _).mp a12).2
        have ng23 : ¬ G.Adj (p[2]'(by omega)) (p[3]'(by omega)) :=
          ((SimpleGraph.compl_adj G _ _).mp a23).2
        have hq : IsPathList G [p[1]'(by omega), p[3]'(by omega), p[0]'(by omega),
            p[2]'(by omega)] :=
          isPathList_four G _ _ _ _ g13 (by rw [he0, he3]; exact hadjuv.symm) g02
            (fun h => ng01 h.symm) (fun h => ng23 h.symm) ng12
            d13 (Ne.symm d01) d12 (Ne.symm d03) (Ne.symm d23) d02
        have hqfrom : IsPathFrom G [p[1]'(by omega), p[3]'(by omega), p[0]'(by omega),
            p[2]'(by omega)] (p[1]'(by omega)) (p[2]'(by omega)) := ⟨hq, by simp, by simp⟩
        -- the even path between the same two ends
        obtain ⟨p', hp'from, hp'int, hp'even⟩ :=
          hpath _ hw1 _ hw2 ng12 ⟨v, hv, by rw [← he3]; exact g13⟩
            ⟨u, hu, by rw [← he0]; exact g02.symm⟩
        refine hgoal (Workspace.Statements.S04.SPGT.thm_4_3 G hG (L ∪ M) (X₀ ∪ X₁ ∪ Y) hAB
          (Or.inl ⟨_, _, _, p', hWsub hw1, hWsub hw2, hqfrom, ?_, ?_, hp'from, hp'int,
            hp'even⟩)).2
        · intro x hx
          have hx' : x ∈ [p[3]'(by omega), p[0]'(by omega)] := by
            simpa [SPGT.interior] using hx
          rcases (by simpa using hx' : x = p[3]'(by omega) ∨ x = p[0]'(by omega)) with h | h
          · rw [h, he3]; exact hvA
          · rw [h, he0]; exact huA
        · exact ⟨1, by simp [pathLength]⟩
      · -- PAPER: *"then `G|W` contains an antipath of length 3, which is impossible since its
        -- components are cliques"*
        have h6 : 6 ≤ p.length := by
          obtain ⟨k, hk⟩ := hod
          simp only [pathLength] at hk
          omega
        have hm1 := hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
          p 0 (by omega))
        have hm2 := hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
          p 1 (by omega))
        have hm3 := hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
          p 2 (by omega))
        have hm4 := hint _ (Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem
          p 3 (by omega))
        have a12 : Gᶜ.Adj (p[1]'(by omega)) (p[2]'(by omega)) :=
          (hp.1.2.2 1 2 (by omega) (by omega)).mpr (Or.inl rfl)
        have a23 : Gᶜ.Adj (p[2]'(by omega)) (p[3]'(by omega)) :=
          (hp.1.2.2 2 3 (by omega) (by omega)).mpr (Or.inl rfl)
        have a34 : Gᶜ.Adj (p[3]'(by omega)) (p[4]'(by omega)) :=
          (hp.1.2.2 3 4 (by omega) (by omega)).mpr (Or.inl rfl)
        have n14 : ¬ Gᶜ.Adj (p[1]'(by omega)) (p[4]'(by omega)) := by
          intro h
          have := (hp.1.2.2 1 4 (by omega) (by omega)).mp h
          omega
        rcases hpart _ hm1 _ hm2 a12 with ⟨q1, q2⟩ | ⟨q1, q2⟩
        · rcases hpart _ hm2 _ hm3 a23 with ⟨q2', q3⟩ | ⟨q2', q3⟩
          · exact hPdisj12 _ q2' q2
          · rcases hpart _ hm3 _ hm4 a34 with ⟨q3', q4⟩ | ⟨q3', q4⟩
            · exact n14 (hcross _ q1 _ q4)
            · exact hPdisj12 _ q3 q3'
        · rcases hpart _ hm2 _ hm3 a23 with ⟨q2', q3⟩ | ⟨q2', q3⟩
          · rcases hpart _ hm3 _ hm4 a34 with ⟨q3', q4⟩ | ⟨q3', q4⟩
            · exact hPdisj12 _ q3' q3
            · exact n14 ((hcross _ q4 _ q1).symm)
          · exact hPdisj12 _ q2 q2'
  exact hgoal (Workspace.Statements.S04.SPGT.thm_4_6 G hG (L ∪ M) (X₀ ∪ X₁ ∪ Y)
    ((NSet G H K φ c₁ \ {r₁}) ∪ (NSet G H K φ c₂ \ {r₂})) A₁ hAB hkernel hA₁comp hpath
    hantipath)

end Workspace.ProofLemmas.Thm75Endgame
