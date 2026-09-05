/-  Proof attempt for statement 5.1 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    THE PAPER'S PROOF (printed p. 23, "Proof of 5.1, assuming 5.4"):

      "Let G be Berge, and assume there is a nondegenerate appearance of K4 in G.
       Choose a 3-connected graph J maximal (under J-enlargement) such that there is a
       nondegenerate appearance of J in G; then the hypotheses of 5.4 are satisfied, and
       the claim follows from 5.4.  This proves 5.1."

    The only step needing work is the maximal choice.  Maximality "under J-enlargement"
    is realised as maximality of the number of edges: a `J`-enlargement `J'` carries a
    proper subgraph isomorphic to a subdivision `D` of `J`, and

        |E(J)| <= |E(D)| = |E(S)| < |E(J')|,

    so the edge count strictly increases along enlargement.  The count is bounded because
    an appearance of `J` in `G` embeds `E(J)` into `E(H) ~= K subseteq V(G)`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Statements.S05.Thm_5_4
import Workspace.ProofLemmas.ExtremalChoice

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S05

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.BasicClasses Workspace.Types.BasicClasses.SPGT

namespace SPGT

/-! ### Helper lemmas -/

/-- An entry of a list, at a position which is neither the first nor the last, is an
internal vertex of the corresponding track. -/
private theorem mem_trackInterior_getElem {W : Type*} (q : List W) (j : ℕ)
    (h : j + 2 < q.length) : q[j + 1]'(by omega) ∈ trackInterior q := by
  have hlen : j < q.tail.dropLast.length := by
    simp only [List.length_dropLast, List.length_tail]
    omega
  have hmem := List.getElem_mem hlen
  simp only [List.getElem_dropLast, List.getElem_tail] at hmem
  exact hmem

/-- If neither end of an edge of a track is an internal vertex, the track has exactly two
vertices. -/
private theorem track_edge_len_two {W : Type*} (q : List W) (i : ℕ) (hi : i + 1 < q.length)
    (h1 : q[i]'(by omega) ∉ trackInterior q)
    (h2 : q[i + 1]'hi ∉ trackInterior q) : q.length = 2 := by
  by_contra hne
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · exact h2 (mem_trackInterior_getElem q 0 (by omega))
  · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    exact h1 (mem_trackInterior_getElem q j (by omega))

private theorem track_head {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) (hlen : 0 < q.length) : q[0]'hlen = a := by
  have h' := h.2.1
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen] at h'
  exact Option.some_injective _ h'

private theorem track_last {W : Type*} {D : SimpleGraph W} {q : List W} {a b : W}
    (h : IsTrackFrom D q a b) (hlen : q.length = 2) : q[1]'(by omega) = b := by
  have h' := h.2.2
  rw [List.getLast?_eq_getElem?, show q.length - 1 = 1 from by omega,
    List.getElem?_eq_getElem (by omega)] at h'
  exact Option.some_injective _ h'

/-- The tracks that a subdivision attaches to distinct edges of `J` have disjoint edge sets. -/
private theorem trackEdges_disjoint {U W : Type*} {J : SimpleGraph U} {D : SimpleGraph W}
    {ι : U → W} {T : U → U → List W} (hι : Function.Injective ι)
    (htrack : ∀ u v : U, J.Adj u v → IsTrackFrom D (T u v) (ι u) (ι v))
    (hlen : ∀ u v : U, J.Adj u v → 1 ≤ trackLength (T u v))
    (hdisjint : ∀ u v u' v' : U, J.Adj u v → J.Adj u' v' → s(u, v) ≠ s(u', v') →
      ∀ w ∈ trackInterior (T u v), w ∉ T u' v')
    (u v u' v' : U) (huv : J.Adj u v) (hu'v' : J.Adj u' v')
    (f : Sym2 W) (hf1 : f ∈ trackEdges (T u v)) (hf2 : f ∈ trackEdges (T u' v')) :
    s(u, v) = s(u', v') := by
  by_contra hne
  obtain ⟨i, hi, hfi⟩ := hf1
  obtain ⟨j, hj, hfj⟩ := hf2
  have hq2 : 2 ≤ (T u v).length := by
    have := hlen u v huv
    simp only [trackLength] at this
    omega
  have hr2 : 2 ≤ (T u' v').length := by
    have := hlen u' v' hu'v'
    simp only [trackLength] at this
    omega
  -- both ends of `f`, read on `T u v`, lie on `T u' v'`, and vice versa
  have heq : s((T u v)[i]'(by omega), (T u v)[i + 1]'hi)
      = s((T u' v')[j]'(by omega), (T u' v')[j + 1]'hj) := by rw [← hfi, ← hfj]
  have hmemr : ((T u v)[i]'(by omega) ∈ T u' v') ∧ ((T u v)[i + 1]'hi ∈ T u' v') := by
    rcases Sym2.eq_iff.mp heq with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
  have hmemq : ((T u' v')[j]'(by omega) ∈ T u v) ∧ ((T u' v')[j + 1]'hj ∈ T u v) := by
    rcases Sym2.eq_iff.mp heq.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
    · exact ⟨e1 ▸ List.getElem_mem _, e2 ▸ List.getElem_mem _⟩
  have hqlen : (T u v).length = 2 :=
    track_edge_len_two (T u v) i hi
      (fun hmem => hdisjint u v u' v' huv hu'v' hne _ hmem hmemr.1)
      (fun hmem => hdisjint u v u' v' huv hu'v' hne _ hmem hmemr.2)
  have hrlen : (T u' v').length = 2 :=
    track_edge_len_two (T u' v') j hj
      (fun hmem => hdisjint u' v' u v hu'v' huv (Ne.symm hne) _ hmem hmemq.1)
      (fun hmem => hdisjint u' v' u v hu'v' huv (Ne.symm hne) _ hmem hmemq.2)
  obtain rfl : i = 0 := by omega
  obtain rfl : j = 0 := by omega
  have e1 : (T u v)[0]'(by omega) = ι u := track_head (htrack u v huv) (by omega)
  have e2 : (T u v)[1]'(by omega) = ι v := track_last (htrack u v huv) hqlen
  have e3 : (T u' v')[0]'(by omega) = ι u' := track_head (htrack u' v' hu'v') (by omega)
  have e4 : (T u' v')[1]'(by omega) = ι v' := track_last (htrack u' v' hu'v') hrlen
  rw [e1, e2, e3, e4] at heq
  rcases Sym2.eq_iff.mp heq with ⟨p1, p2⟩ | ⟨p1, p2⟩
  · exact hne (by rw [hι p1, hι p2])
  · exact hne (by rw [Sym2.eq_swap, hι p1, hι p2])

/-- Subdividing cannot decrease the number of edges. -/
private theorem edgeSet_ncard_le_of_isSubdivision {U W : Type*} [Finite W]
    (J : SimpleGraph U) (D : SimpleGraph W) (hsub : IsSubdivision J D) :
    J.edgeSet.ncard ≤ D.edgeSet.ncard := by
  classical
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  have key : ∀ e : Sym2 U, e ∈ J.edgeSet →
      ∃ f : Sym2 W, (∃ u v : U, J.Adj u v ∧ e = s(u, v) ∧ f ∈ trackEdges (T u v)) ∧
        f ∈ D.edgeSet := by
    intro e
    induction e using Sym2.ind with
    | _ u v =>
      intro he
      have huv : J.Adj u v := (SimpleGraph.mem_edgeSet _).mp he
      have ht := htrack u v huv
      have h2 : 2 ≤ (T u v).length := by
        have := hlen u v huv
        simp only [trackLength] at this
        omega
      refine ⟨s((T u v)[0]'(by omega), (T u v)[1]'(by omega)), ⟨u, v, huv, rfl, ?_⟩, ?_⟩
      · exact ⟨0, by omega, rfl⟩
      · exact (SimpleGraph.mem_edgeSet _).mpr (ht.1.2.2 0 (by omega))
  choose Φ₀ hΦ₀ using key
  have hinj : Function.Injective
      (fun e : ↥J.edgeSet => (⟨Φ₀ e.1 e.2, (hΦ₀ e.1 e.2).2⟩ : ↥D.edgeSet)) := by
    rintro ⟨e₁, he₁⟩ ⟨e₂, he₂⟩ heq
    have heq' : Φ₀ e₁ he₁ = Φ₀ e₂ he₂ := congrArg Subtype.val heq
    obtain ⟨u, v, huv, rfl, hm1⟩ := (hΦ₀ e₁ he₁).1
    obtain ⟨u', v', hu'v', rfl, hm2⟩ := (hΦ₀ e₂ he₂).1
    rw [heq'] at hm1
    exact Subtype.ext (trackEdges_disjoint hι htrack hlen hdisjint u v u' v' huv hu'v' _ hm1 hm2)
  have := Nat.card_le_card_of_injective _ hinj
  simpa only [Nat.card_coe_set_eq] using this

/-- In a connected graph, a vertex distinct from another reachable vertex has a neighbour. -/
private theorem exists_adj_of_reachable {X : Type*} {K : SimpleGraph X} {a b : X}
    (h : K.Reachable a b) (hab : a ≠ b) : ∃ c, K.Adj a c := by
  obtain ⟨p⟩ := h
  cases p with
  | nil => exact absurd rfl hab
  | cons hadj q => exact ⟨_, hadj⟩

/-- A 3-connected graph has no isolated vertex. -/
private theorem exists_adj_of_three_connected {U' : Type*} [Fintype U'] (J' : SimpleGraph U')
    (hJ' : IsKConnected J' 3) (v : U') : ∃ w, J'.Adj v w := by
  obtain ⟨hcard, hconn⟩ := hJ'
  have hc := hconn ∅ (by simp)
  rw [Set.compl_empty] at hc
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (by omega) v
  have hne : (⟨v, Set.mem_univ v⟩ : ↥(Set.univ : Set U')) ≠ ⟨w, Set.mem_univ w⟩ := by
    intro h
    exact hw (congrArg Subtype.val h).symm
  obtain ⟨c, hcadj⟩ :=
    exists_adj_of_reachable (hc.preconnected ⟨v, Set.mem_univ v⟩ ⟨w, Set.mem_univ w⟩) hne
  exact ⟨(c : U'), hcadj⟩

/-- A proper subgraph of a 3-connected graph has strictly fewer edges. -/
private theorem edgeSet_ncard_lt_of_ne_top {U' : Type*} [Fintype U'] (J' : SimpleGraph U')
    (hJ' : IsKConnected J' 3) (S : J'.Subgraph) (hSne : S ≠ ⊤)
    {W : Type*} (Dg : SimpleGraph W) (φ : S.coe ≃g Dg) :
    Dg.edgeSet.ncard < J'.edgeSet.ncard := by
  classical
  -- the image of `E(D)` in `E(J')`
  have hcard : Dg.edgeSet.ncard = S.coe.edgeSet.ncard := by
    simpa only [Nat.card_coe_set_eq] using (Nat.card_congr φ.symm.mapEdgeSet)
  have hmapinj : Function.Injective (Sym2.map (Subtype.val : ↥S.verts → U')) :=
    Sym2.map.injective Subtype.val_injective
  have himg : Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet ⊆ J'.edgeSet := by
    rintro x ⟨e, he, rfl⟩
    induction e using Sym2.ind with
    | _ a b =>
      rw [Sym2.map_mk]
      exact (SimpleGraph.mem_edgeSet _).mpr (S.adj_sub ((SimpleGraph.mem_edgeSet _).mp he))
  -- a missing edge
  have hmiss : ∃ x ∈ J'.edgeSet, x ∉ Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet := by
    by_cases hverts : S.verts = Set.univ
    · have hadj : ∃ a b, J'.Adj a b ∧ ¬ S.Adj a b := by
        by_contra hcon
        refine hSne ?_
        ext a b
        · rw [hverts]; simp
        · constructor
          · intro h; exact SimpleGraph.Subgraph.top_adj.mpr (S.adj_sub h)
          · intro h
            by_contra hc
            exact hcon ⟨a, b, SimpleGraph.Subgraph.top_adj.mp h, hc⟩
      obtain ⟨a, b, hab, hnab⟩ := hadj
      refine ⟨s(a, b), (SimpleGraph.mem_edgeSet _).mpr hab, ?_⟩
      rintro ⟨e, he, hee⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [Sym2.map_mk] at hee
        have hxy : S.Adj (x : U') (y : U') := S.coe_adj x y ▸ (SimpleGraph.mem_edgeSet _).mp he
        rcases Sym2.eq_iff.mp hee with ⟨p1, p2⟩ | ⟨p1, p2⟩
        · exact hnab (p1 ▸ p2 ▸ hxy)
        · exact hnab (p1 ▸ p2 ▸ S.symm hxy)
    · obtain ⟨v₀, hv₀⟩ : ∃ v₀ : U', v₀ ∉ S.verts := by
        by_contra hcon
        exact hverts (Set.eq_univ_of_forall (by simpa using hcon))
      obtain ⟨w, hw⟩ := exists_adj_of_three_connected J' hJ' v₀
      refine ⟨s(v₀, w), (SimpleGraph.mem_edgeSet _).mpr hw, ?_⟩
      rintro ⟨e, he, hee⟩
      induction e using Sym2.ind with
      | _ x y =>
        rw [Sym2.map_mk] at hee
        rcases Sym2.eq_iff.mp hee with ⟨p1, -⟩ | ⟨-, p2⟩
        · exact hv₀ (p1 ▸ x.2)
        · exact hv₀ (p2 ▸ y.2)
  obtain ⟨x₀, hx₀, hx₀'⟩ := hmiss
  have hss : Sym2.map (Subtype.val : ↥S.verts → U') '' S.coe.edgeSet ⊂ J'.edgeSet :=
    ⟨himg, fun hcon => hx₀' (hcon hx₀)⟩
  have := Set.ncard_lt_ncard hss (Set.toFinite _)
  rwa [Set.ncard_image_of_injective _ hmapinj, ← hcard] at this

/-- `K₄` is 3-connected. -/
private theorem k4_three_connected : IsKConnected (⊤ : SimpleGraph (Fin 4)) 3 := by
  refine ⟨by simp, fun S hS => ?_⟩
  have hne : (Sᶜ : Set (Fin 4)).Nonempty := by
    rcases Set.eq_empty_or_nonempty (Sᶜ : Set (Fin 4)) with h | h
    · exfalso
      have hu : S = Set.univ := by rwa [Set.compl_empty_iff] at h
      rw [hu, Set.ncard_univ] at hS
      simp [Nat.card_eq_fintype_card] at hS
    · exact h
  obtain ⟨x, hx⟩ := hne
  haveI : Nonempty (↥(Sᶜ : Set (Fin 4))) := ⟨⟨x, hx⟩⟩
  refine ⟨fun a b => ?_⟩
  by_cases hab : a = b
  · exact hab ▸ SimpleGraph.Reachable.refl a
  · refine SimpleGraph.Adj.reachable ?_
    show (⊤ : SimpleGraph (Fin 4)).Adj (a : Fin 4) (b : Fin 4)
    exact fun h => hab (Subtype.ext h)

/-- An appearance of `J` in `G` bounds the number of edges of `J` by `|V(G)|`. -/
private theorem edge_bound_of_appearance {Vx : Type*} [Fintype Vx] {U : Type*}
    (G : SimpleGraph Vx) (J : SimpleGraph U) {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set Vx)
    (happ : IsAppearance G J H K) : J.edgeSet.ncard ≤ Fintype.card Vx := by
  have h1 : J.edgeSet.ncard ≤ H.edgeSet.ncard :=
    edgeSet_ncard_le_of_isSubdivision J H happ.1.1
  obtain ⟨φ⟩ := happ.2
  have h2 : H.edgeSet.ncard = K.ncard := by
    simpa only [Nat.card_coe_set_eq] using Nat.card_congr φ.toEquiv
  have h3 : K.ncard ≤ Fintype.card Vx :=
    Workspace.ProofLemmas.ExtremalChoice.ncard_le_card K
  omega

variable {V : Type*} [Fintype V] [DecidableEq V]


/-- **5.1** (printed p. 18)

PAPER: *"Let `G` be Berge, and assume some nondegenerate `L(H)` is an induced subgraph of
`G`, where `H` is a bipartite subdivision of `K₄`.  Then either `G` is a line graph, or `G`
admits a proper 2-join, or `G` admits a balanced skew partition.  In particular, 1.8.1
holds."* -/
theorem thm_5_1 (G : SimpleGraph V) (hG : Berge G)
    (n : ℕ) (H : SimpleGraph (Fin n)) (K : Set V)
    (happ : IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K)
    (hnd : NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H) :
    IsLineGraphOfBipartite G ∨ AdmitsProper2Join G ∨ AdmitsBalancedSkewPartition G := by
  classical
  -- "Choose a 3-connected graph J maximal (under J-enlargement) such that there is a
  -- nondegenerate appearance of J in G."
  obtain ⟨⟨m, J⟩, ⟨hJ3, n₁, H₁, K₁, happ₁, hnd₁⟩, hmax⟩ :=
    Workspace.ProofLemmas.ExtremalChoice.exists_max_nat
      (fun x : (m : ℕ) × SimpleGraph (Fin m) =>
        IsKConnected x.2 3 ∧
          ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
            IsAppearance G x.2 H' K' ∧ NondegenerateAppearance x.2 H')
      (fun x => x.2.edgeSet.ncard) (Fintype.card V)
      (by
        rintro ⟨m', J'⟩ ⟨-, n', H', K', happ', -⟩
        exact edge_bound_of_appearance G J' H' K' happ')
      ⟨⟨4, (⊤ : SimpleGraph (Fin 4))⟩, k4_three_connected, n, H, K, happ, hnd⟩
  -- "then the hypotheses of 5.4 are satisfied"
  have hnoenl : ¬ ∃ (m' : ℕ) (J' : SimpleGraph (Fin m')),
      IsJEnlargement J J' ∧
      ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V),
        IsAppearance G J' H' K' ∧ NondegenerateAppearance J' H' := by
    rintro ⟨m', J', ⟨hJ'3, S, hSne, nD, Dg, hDsub, ⟨φ⟩⟩, n', H', K', happ', hnd'⟩
    have h1 : J.edgeSet.ncard ≤ Dg.edgeSet.ncard :=
      edgeSet_ncard_le_of_isSubdivision J Dg hDsub
    have h2 : Dg.edgeSet.ncard < J'.edgeSet.ncard :=
      edgeSet_ncard_lt_of_ne_top J' hJ'3 S hSne Dg φ
    have h3 := hmax ⟨m', J'⟩ ⟨hJ'3, n', H', K', happ', hnd'⟩
    simp only at h3
    omega
  -- "and the claim follows from 5.4"
  have h54 := thm_5_4 G hG m J hJ3 hnoenl n₁ H₁ K₁ happ₁ (fun hd => absurd hd hnd₁)
  rcases h54 with hiso | ⟨-, h2join⟩ | hskew
  · exact Or.inl ⟨n₁, H₁, happ₁.1.2, hiso⟩
  · exact Or.inr (Or.inl h2join)
  · exact Or.inr (Or.inr hskew)


end SPGT

end Workspace.Statements.S05
