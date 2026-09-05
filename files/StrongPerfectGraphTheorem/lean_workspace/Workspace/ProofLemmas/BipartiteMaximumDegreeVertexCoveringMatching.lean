import Mathlib
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Combinatorics.SimpleGraph.Subgraph

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

namespace KoenigAux


variable {W : Type*} [Fintype W] [DecidableEq W]

/-- A finset of edges of `G` that pairwise do not share a vertex. -/
def IsEdgeMatching (G : SimpleGraph W) (N : Finset (Sym2 W)) : Prop :=
  (∀ e ∈ N, e ∈ G.edgeSet) ∧ ∀ e ∈ N, ∀ f ∈ N, ∀ v : W, v ∈ e → v ∈ f → e = f

/-- The vertex `v` is an endpoint of an edge of `N`. -/
def CoveredBy (N : Finset (Sym2 W)) (v : W) : Prop := ∃ w, s(v, w) ∈ N

lemma coveredBy_iff {N : Finset (Sym2 W)} {v : W} :
    CoveredBy N v ↔ ∃ e ∈ N, v ∈ e := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨s(v, w), hw, Sym2.mem_mk_left v w⟩
  · rintro ⟨e, he, hv⟩
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.1 hv
    exact ⟨y, he⟩

/-- Hall's condition holds for any set of maximum-degree vertices. -/
lemma hall_condition (G : SimpleGraph W) [DecidableRel G.Adj] (Δ : ℕ) (hpos : 0 < Δ)
    (hle : ∀ v : W, G.degree v ≤ Δ) (S : Finset W) (hS : ∀ a ∈ S, G.degree a = Δ) :
    S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card := by
  classical
  set Nb := S.biUnion (fun a => G.neighborFinset a) with hNb
  have h2 : ∀ a ∈ S, G.degree a = ∑ b ∈ Nb, (if G.Adj a b then 1 else 0) := by
    intro a ha
    rw [← Finset.card_filter]
    have : Nb.filter (fun b => G.Adj a b) = G.neighborFinset a := by
      ext b
      simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, hNb, Finset.mem_biUnion]
      exact ⟨fun h => h.2, fun h => ⟨⟨a, ha, by simpa using h⟩, h⟩⟩
    rw [this]
    rfl
  have h1 : ∑ a ∈ S, G.degree a = Δ * S.card := by
    rw [Finset.sum_congr rfl hS, Finset.sum_const, smul_eq_mul, mul_comm]
  have h3 : ∑ a ∈ S, G.degree a = ∑ b ∈ Nb, (S.filter (fun a => G.Adj a b)).card := by
    rw [Finset.sum_congr rfl h2, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun b _ => (Finset.card_filter _ _).symm)
  have h4 : ∀ b ∈ Nb, (S.filter (fun a => G.Adj a b)).card ≤ G.degree b := by
    intro b _
    refine Finset.card_le_card ?_
    intro a ha
    simp only [Finset.mem_filter] at ha
    exact (SimpleGraph.mem_neighborFinset _ _ _).2 ha.2.symm
  have h5 : ∑ b ∈ Nb, (S.filter (fun a => G.Adj a b)).card ≤ Δ * Nb.card := by
    calc ∑ b ∈ Nb, (S.filter (fun a => G.Adj a b)).card
        ≤ ∑ b ∈ Nb, Δ := Finset.sum_le_sum (fun b hb => (h4 b hb).trans (hle b))
      _ = Δ * Nb.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  have : Δ * S.card ≤ Δ * Nb.card := by rw [← h1, h3]; exact h5
  exact Nat.le_of_mul_le_mul_left this hpos

/-- Hall's theorem produces an edge matching saturating `D`, when all edges leaving `D`'s
side `P` land in the disjoint side `Q`. -/
lemma exists_edgeMatching_of_hall (G : SimpleGraph W) [DecidableRel G.Adj]
    (D P Q : Finset W)
    (hDP : ∀ a ∈ D, a ∈ P)
    (hPQ : ∀ p ∈ P, ∀ w : W, G.Adj p w → w ∈ Q)
    (hdisj : ∀ x : W, x ∈ P → x ∈ Q → False)
    (hall : ∀ S : Finset W, S ⊆ D → S.card ≤ (S.biUnion (fun a => G.neighborFinset a)).card) :
    ∃ M : Finset (Sym2 W), IsEdgeMatching G M ∧ ∀ a ∈ D, CoveredBy M a := by
  classical
  obtain ⟨f, hfinj, hfmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective
      (fun a : {a : W // a ∈ D} => G.neighborFinset a.1)).1 (by
        intro s
        have himg : (s.image (fun a : {a : W // a ∈ D} => a.1)).card = s.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have hsub : (s.image (fun a : {a : W // a ∈ D} => a.1)) ⊆ D := by
          intro x hx
          obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
          exact a.2
        have hbi : s.biUnion (fun a : {a : W // a ∈ D} => G.neighborFinset a.1)
            = (s.image (fun a : {a : W // a ∈ D} => a.1)).biUnion
                (fun a => G.neighborFinset a) := by
          ext w
          simp only [Finset.mem_biUnion, Finset.mem_image]
          constructor
          · rintro ⟨a, ha, hw⟩
            exact ⟨a.1, ⟨a, ha, rfl⟩, hw⟩
          · rintro ⟨x, ⟨a, ha, rfl⟩, hw⟩
            exact ⟨a, ha, hw⟩
        rw [hbi, ← himg]
        exact hall _ hsub)
  refine ⟨(Finset.univ : Finset {a : W // a ∈ D}).image (fun a => s(a.1, f a)), ⟨?_, ?_⟩, ?_⟩
  · intro e he
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 he
    exact (SimpleGraph.mem_edgeSet G).2 ((SimpleGraph.mem_neighborFinset _ _ _).1 (hfmem a))
  · intro e he g hg u hue hug
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 he
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hg
    have hQmem : ∀ c : {a : W // a ∈ D}, f c ∈ Q := by
      intro c
      exact hPQ c.1 (hDP c.1 c.2) (f c) ((SimpleGraph.mem_neighborFinset _ _ _).1 (hfmem c))
    have hbad : ∀ c c' : {a : W // a ∈ D}, c.1 ≠ f c' := by
      intro c c' hcc
      refine hdisj c.1 (hDP c.1 c.2) ?_
      rw [hcc]
      exact hQmem c'
    rcases Sym2.mem_iff.1 hue with rfl | rfl
    · rcases Sym2.mem_iff.1 hug with h | h
      · rw [Subtype.ext (h : a.1 = a'.1)]
      · exact absurd h (hbad a a')
    · rcases Sym2.mem_iff.1 hug with h | h
      · exact absurd h.symm (hbad a' a)
      · rw [hfinj h]
  · intro a ha
    exact ⟨f ⟨a, ha⟩, Finset.mem_image.2 ⟨⟨a, ha⟩, Finset.mem_univ _, rfl⟩⟩

/-- Mendelsohn–Dulmage: a matching saturating `S` on one side and a matching saturating `T`
on the other side can be combined into a single matching saturating `S ∪ T`. -/
lemma exists_edgeMatching_covering_both (G : SimpleGraph W) [DecidableRel G.Adj]
    (P Q S T : Finset W)
    (hSP : ∀ a ∈ S, a ∈ P) (hTQ : ∀ b ∈ T, b ∈ Q)
    (hPQ : ∀ p ∈ P, ∀ w : W, G.Adj p w → w ∈ Q)
    (hQP : ∀ q ∈ Q, ∀ w : W, G.Adj q w → w ∈ P)
    (hdisj : ∀ x : W, x ∈ P → x ∈ Q → False)
    (M₁ M₂ : Finset (Sym2 W))
    (h₁ : IsEdgeMatching G M₁) (h₂ : IsEdgeMatching G M₂)
    (hS : ∀ a ∈ S, CoveredBy M₁ a) (hT : ∀ b ∈ T, CoveredBy M₂ b) :
    ∃ N : Finset (Sym2 W), IsEdgeMatching G N ∧ (∀ a ∈ S, CoveredBy N a) ∧
      (∀ b ∈ T, CoveredBy N b) := by
  classical
  set 𝓜 : Finset (Finset (Sym2 W)) :=
    (Finset.univ : Finset (Finset (Sym2 W))).filter
      (fun N => IsEdgeMatching G N ∧ ∀ b ∈ T, CoveredBy N b) with h𝓜
  have hM₂mem : M₂ ∈ 𝓜 := by
    simp only [h𝓜, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨h₂, hT⟩
  obtain ⟨N, hNmem, hNmax⟩ := Finset.exists_max_image 𝓜
    (fun N => (S.filter (fun w => CoveredBy N w)).card + (N ∩ M₁).card) ⟨M₂, hM₂mem⟩
  have hN : IsEdgeMatching G N ∧ ∀ b ∈ T, CoveredBy N b := by
    simpa only [h𝓜, Finset.mem_filter, Finset.mem_univ, true_and] using hNmem
  refine ⟨N, hN.1, ?_, hN.2⟩
  by_contra hcon
  obtain ⟨v, hvS, hvnc⟩ : ∃ v ∈ S, ¬ CoveredBy N v := by
    by_contra h2
    exact hcon (fun a ha => not_not.1 (fun hna => h2 ⟨a, ha, hna⟩))
  obtain ⟨b, hvb⟩ := hS v hvS
  have hadjvb : G.Adj v b := (SimpleGraph.mem_edgeSet G).1 (h₁.1 _ hvb)
  have hbQ : b ∈ Q := hPQ v (hSP v hvS) b hadjvb
  set Nrm : Finset (Sym2 W) := N.filter (fun e => b ∉ e) with hNrm
  set N' : Finset (Sym2 W) := insert s(v, b) Nrm with hN'
  have hNrmsub : Nrm ⊆ N := Finset.filter_subset _ _
  have hvbnotNrm : s(v, b) ∉ Nrm := by
    simp only [hNrm, Finset.mem_filter, not_and, not_not]
    intro _
    exact Sym2.mem_mk_right v b
  -- `N'` is again a matching
  have hkey : ∀ x ∈ Nrm, ∀ u : W, u ∈ x → u ∈ s(v, b) → False := by
    intro x hx u hux hu2
    rcases Sym2.mem_iff.1 hu2 with rfl | rfl
    · exact hvnc (coveredBy_iff.2 ⟨x, hNrmsub hx, hux⟩)
    · exact (Finset.mem_filter.1 hx).2 hux
  have hN'match : IsEdgeMatching G N' := by
    constructor
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact (SimpleGraph.mem_edgeSet G).2 hadjvb
      · exact hN.1.1 e (hNrmsub he)
    · intro e he g hg u hue hug
      rcases Finset.mem_insert.1 he with rfl | he'
      · rcases Finset.mem_insert.1 hg with rfl | hg'
        · rfl
        · exact (hkey g hg' u hug hue).elim
      · rcases Finset.mem_insert.1 hg with rfl | hg'
        · exact (hkey e he' u hue hug).elim
        · exact hN.1.2 e (hNrmsub he') g (hNrmsub hg') u hue hug
  -- `N'` still covers `T`
  have hN'T : ∀ t ∈ T, CoveredBy N' t := by
    intro t ht
    obtain ⟨e, heN, hte⟩ := coveredBy_iff.1 (hN.2 t ht)
    by_cases hbe : b ∈ e
    · have htb : t = b := by
        obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hbe
        rw [hx] at hte heN
        rcases Sym2.mem_iff.1 hte with h | h
        · exact h
        · exfalso
          subst h
          have hadjbx : G.Adj b t := (SimpleGraph.mem_edgeSet G).1 (hN.1.1 _ heN)
          exact hdisj t (hQP b hbQ t hadjbx) (hTQ t ht)
      subst htb
      exact ⟨v, by rw [Sym2.eq_swap]; exact Finset.mem_insert_self _ _⟩
    · exact coveredBy_iff.2
        ⟨e, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨heN, hbe⟩), hte⟩
  -- the score on `S` does not go down
  have hvX' : v ∈ S.filter (fun w => CoveredBy N' w) := by
    refine Finset.mem_filter.2 ⟨hvS, ⟨b, ?_⟩⟩
    exact Finset.mem_insert_self _ _
  have hvX : v ∉ S.filter (fun w => CoveredBy N w) := fun h => hvnc (Finset.mem_filter.1 h).2
  have hYcard : ((S.filter (fun w => CoveredBy N w)).filter
      (fun w => ¬ CoveredBy N' w)).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha c hc
    have step : ∀ z ∈ (S.filter (fun w => CoveredBy N w)).filter (fun w => ¬ CoveredBy N' w),
        ∃ e ∈ N, z ∈ e ∧ b ∈ e := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.1 hz
      obtain ⟨e, heN, hze⟩ := coveredBy_iff.1 (Finset.mem_filter.1 hz1).2
      refine ⟨e, heN, hze, ?_⟩
      by_contra hbe
      exact hz2 (coveredBy_iff.2
        ⟨e, Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨heN, hbe⟩), hze⟩)
    obtain ⟨e, heN, hae, hbe⟩ := step a ha
    obtain ⟨g, hgN, hcg, hbg⟩ := step c hc
    have heg : e = g := hN.1.2 e heN g hgN b hbe hbg
    subst heg
    have haP : a ∈ P := hSP a (Finset.mem_filter.1 (Finset.mem_filter.1 ha).1).1
    have hcP : c ∈ P := hSP c (Finset.mem_filter.1 (Finset.mem_filter.1 hc).1).1
    have hab : a ≠ b := fun h => hdisj a haP (by rw [h]; exact hbQ)
    have hcb : c ≠ b := fun h => hdisj c hcP (by rw [h]; exact hbQ)
    obtain ⟨x, hx⟩ := Sym2.mem_iff_exists.1 hbe
    rw [hx] at hae hcg
    have hax : a = x := by
      rcases Sym2.mem_iff.1 hae with h | h
      · exact absurd h hab
      · exact h
    have hcx : c = x := by
      rcases Sym2.mem_iff.1 hcg with h | h
      · exact absurd h hcb
      · exact h
    rw [hax, hcx]
  have hXsub : S.filter (fun w => CoveredBy N w) ⊆
      ((S.filter (fun w => CoveredBy N' w)).erase v) ∪
        ((S.filter (fun w => CoveredBy N w)).filter (fun w => ¬ CoveredBy N' w)) := by
    intro w hw
    by_cases hc : CoveredBy N' w
    · refine Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, ?_⟩)
      · rintro rfl
        exact hvX hw
      · exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hw).1, hc⟩
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hw, hc⟩)
  have hscore : (S.filter (fun w => CoveredBy N w)).card
      ≤ (S.filter (fun w => CoveredBy N' w)).card := by
    have hc1 := Finset.card_le_card hXsub
    have hc2 := Finset.card_union_le ((S.filter (fun w => CoveredBy N' w)).erase v)
      ((S.filter (fun w => CoveredBy N w)).filter (fun w => ¬ CoveredBy N' w))
    have hc3 : ((S.filter (fun w => CoveredBy N' w)).erase v).card
        = (S.filter (fun w => CoveredBy N' w)).card - 1 := Finset.card_erase_of_mem hvX'
    have hc4 : 1 ≤ (S.filter (fun w => CoveredBy N' w)).card :=
      Finset.card_pos.2 ⟨v, hvX'⟩
    omega
  -- the count of `M₁`-edges goes up by exactly one
  have hinter : Nrm ∩ M₁ = N ∩ M₁ := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro e he
      obtain ⟨h1, h2⟩ := Finset.mem_inter.1 he
      exact Finset.mem_inter.2 ⟨hNrmsub h1, h2⟩
    · intro e he
      obtain ⟨heN, heM⟩ := Finset.mem_inter.1 he
      refine Finset.mem_inter.2 ⟨Finset.mem_filter.2 ⟨heN, ?_⟩, heM⟩
      intro hbe
      have hev : e = s(v, b) := h₁.2 e heM _ hvb b hbe (Sym2.mem_mk_right v b)
      exact hvnc ⟨b, hev ▸ heN⟩
  have haux : (N' ∩ M₁).card = (N ∩ M₁).card + 1 := by
    have hins : N' ∩ M₁ = insert s(v, b) (Nrm ∩ M₁) := by
      rw [hN', Finset.insert_inter_of_mem hvb]
    rw [hins, Finset.card_insert_of_notMem, hinter]
    intro hmem
    exact hvbnotNrm (Finset.mem_of_mem_inter_left hmem)
  have hN'mem : N' ∈ 𝓜 := by
    simp only [h𝓜, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hN'match, hN'T⟩
  have hkeymax : (S.filter (fun w => CoveredBy N' w)).card + (N' ∩ M₁).card
      ≤ (S.filter (fun w => CoveredBy N w)).card + (N ∩ M₁).card := hNmax N' hN'mem
  omega

/-- Turn an edge matching into a matching subgraph. -/
def toSubgraph (G : SimpleGraph W) (N : Finset (Sym2 W)) (h : IsEdgeMatching G N) :
    G.Subgraph where
  verts := {v | CoveredBy N v}
  Adj u v := s(u, v) ∈ N
  adj_sub := fun h' => (SimpleGraph.mem_edgeSet G).1 (h.1 _ h')
  edge_vert := fun {u v} h' => ⟨v, h'⟩
  symm := fun u v h' => by
    show s(v, u) ∈ N
    rwa [Sym2.eq_swap]

lemma toSubgraph_isMatching (G : SimpleGraph W) (N : Finset (Sym2 W))
    (h : IsEdgeMatching G N) : (toSubgraph G N h).IsMatching := by
  intro v hv
  obtain ⟨w, hw⟩ := hv
  refine ⟨w, hw, ?_⟩
  intro y hy
  exact Sym2.congr_right.1
    (h.2 _ hy _ hw v (Sym2.mem_mk_left v y) (Sym2.mem_mk_left v w))

end KoenigAux

open KoenigAux in
/-- A positive-degree finite bipartite graph has a matching covering every
maximum-degree vertex. -/
theorem BipartiteMaximumDegreeVertexCoveringMatching
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hG : G.IsBipartite) (hDegree : 0 < G.maxDegree) :
    ∃ M : G.Subgraph,
      M.IsMatching ∧
        ∀ v : W, G.degree v = G.maxDegree → v ∈ M.verts := by
  classical
  obtain ⟨A, B, hAB⟩ := SimpleGraph.isBipartite_iff_exists_isBipartiteWith.1 hG
  set Δ := G.maxDegree with hΔ
  set P : Finset W := Finset.univ.filter (fun x => x ∈ A) with hP
  set Q : Finset W := Finset.univ.filter (fun x => x ∈ B) with hQ
  set S : Finset W := P.filter (fun a => G.degree a = Δ) with hS
  set T : Finset W := Q.filter (fun b => G.degree b = Δ) with hT
  have hPQ : ∀ p ∈ P, ∀ w : W, G.Adj p w → w ∈ Q := by
    intro p hp w hw
    simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hAB.mem_of_mem_adj (by simpa only [hP, Finset.mem_filter, Finset.mem_univ,
      true_and] using hp) hw
  have hQP : ∀ q ∈ Q, ∀ w : W, G.Adj q w → w ∈ P := by
    intro q hq w hw
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hAB.symm.mem_of_mem_adj (by simpa only [hQ, Finset.mem_filter, Finset.mem_univ,
      true_and] using hq) hw
  have hdisj : ∀ x : W, x ∈ P → x ∈ Q → False := by
    intro x hx1 hx2
    simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hx1
    simp only [hQ, Finset.mem_filter, Finset.mem_univ, true_and] at hx2
    exact Set.disjoint_left.1 hAB.disjoint hx1 hx2
  have hdeg : ∀ v : W, G.degree v ≤ Δ := fun v => SimpleGraph.degree_le_maxDegree G v
  obtain ⟨M₁, hM₁, hM₁cov⟩ := exists_edgeMatching_of_hall G S P Q
    (fun a ha => (Finset.mem_filter.1 ha).1) hPQ hdisj
    (fun S' hS' => hall_condition G Δ hDegree hdeg S'
      (fun a ha => (Finset.mem_filter.1 (hS' ha)).2))
  obtain ⟨M₂, hM₂, hM₂cov⟩ := exists_edgeMatching_of_hall G T Q P
    (fun b hb => (Finset.mem_filter.1 hb).1) hQP (fun x h1 h2 => hdisj x h2 h1)
    (fun S' hS' => hall_condition G Δ hDegree hdeg S'
      (fun a ha => (Finset.mem_filter.1 (hS' ha)).2))
  obtain ⟨N, hN, hNS, hNT⟩ := exists_edgeMatching_covering_both G P Q S T
    (fun a ha => (Finset.mem_filter.1 ha).1) (fun b hb => (Finset.mem_filter.1 hb).1)
    hPQ hQP hdisj M₁ M₂ hM₁ hM₂ hM₁cov hM₂cov
  refine ⟨toSubgraph G N hN, toSubgraph_isMatching G N hN, ?_⟩
  intro v hv
  have hpos : 0 < G.degree v := by rw [hv]; exact hDegree
  obtain ⟨w, hw⟩ := (SimpleGraph.degree_pos_iff_exists_adj G v).1 hpos
  have hmem : v ∈ A ∪ B :=
    SimpleGraph.isBipartiteWith_support_subset hAB ((SimpleGraph.mem_support G).2 ⟨w, hw⟩)
  rcases hmem with h | h
  · exact hNS v (Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hv⟩)
  · exact hNT v (Finset.mem_filter.2
      ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩, hv⟩)

end Workspace.ProofLemmas
