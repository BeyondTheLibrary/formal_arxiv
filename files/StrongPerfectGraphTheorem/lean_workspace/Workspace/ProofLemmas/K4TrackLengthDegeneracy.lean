import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.K4AppearanceEightVertices
import Workspace.ProofLemmas.BranchClassification

/-!
# Four branch-to-branch edges force a degenerate `K₄`

Let `H` be a **bipartite subdivision of `K₄`**.  Write `bedges H` for the set of edges of `H`
both of whose ends are branch-vertices — equivalently, the tracks of `H` of length `1`.

The two results of this file are:

* `degenerate_of_four_branch_edges` — if `4 ≤ (bedges H).ncard` then `H` is a *degenerate*
  appearance of `K₄`, i.e. there is a four-cycle of `H` through all four branch-vertices;
* `no_long_odd_branch_of_four_branch_edges` — under the same hypothesis no branch of `H` has
  odd length `≥ 3`.

## The mathematics

A subdivision of `K₄` replaces each of the six edges `uv` of `K₄` by a track `T u v` of length
`ℓ_uv ≥ 1` joining the branch-vertices `ι u`, `ι v`.  An edge of `H` has both ends
branch-vertices exactly when it is the whole of a track of length `1`
(`key` below: an edge of a longer track has an interior vertex as an end, and interior vertices
of tracks are not branch-vertices).  So `bedges H` is the set of the `s(ι u, ι v)` over the
`K₄`-edges with `ℓ_uv = 1`, and `h4` says at least four of the six such tracks are single edges.

`H` is bipartite; fix a 2-colouring `col` and put `c u := col (ι u)`.  The colour alternates
along a track (`DegenerateK4Tracks.track_color`), so reading it at the far end of `T u v` gives

```
ℓ_uv ≡ c u + c v   (mod 2).
```

Hence a `K₄`-edge whose two ends get the *same* colour has **even** `ℓ`, so is not a single
edge and contributes nothing to `bedges H`.

If some three of the four branch-vertices had the same colour, only the three `K₄`-edges at the
fourth vertex could be single edges, so `(bedges H).ncard ≤ 3` — contradiction (`BAD`).  So the
colouring splits the four branch-vertices into two pairs `{p,q}`, `{r,s}` of equal colour, and
the four *cross* edges `pr, ps, qr, qs` are the only candidates.  Being at least four in number
they are **all** present (`KEY`), i.e. `ι p ι r`, `ι p ι s`, `ι q ι r`, `ι q ι s` are edges of
`H`.  The four-cycle `ι p - ι r - ι q - ι s - ι p` passes through all four branch-vertices; that
is exactly `DegenerateK4Appearance H`.

For the second theorem: every branch of `H` is one of the six tracks
(`BranchClassification.exists_trackEdges_eq_of_isBranch`), and a track has as many edges as its
length (`K4AppearanceEightVertices.trackEdges_ncard`), so the branch lengths are exactly the
`ℓ_uv`.  A cross `K₄`-edge has `ℓ = 1 < 3`, and a same-colour `K₄`-edge has `ℓ` even; so no
branch has odd length `≥ 3`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K4TrackLengthDegeneracy

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

/-- The edges of `H` both of whose ends are branch-vertices. -/
def bedges {W : Type*} (H : SimpleGraph W) : Set (Sym2 W) :=
  {e ∈ H.edgeSet | ∀ x ∈ e, x ∈ branchVertices H}

theorem mem_bedges {W : Type*} {H : SimpleGraph W} {e : Sym2 W} :
    e ∈ bedges H ↔ e ∈ H.edgeSet ∧ ∀ x ∈ e, x ∈ branchVertices H := Iff.rfl

/-- A four-element list of pairwise distinct entries has no duplicates. -/
private theorem nodup4 {α : Type*} {w x y z : α} (h1 : w ≠ x) (h2 : w ≠ y) (h3 : w ≠ z)
    (h4 : x ≠ y) (h5 : x ≠ z) (h6 : y ≠ z) : [w, x, y, z].Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

/-- **The common core.**  A bipartite subdivision of `K₄` with at least four branch-to-branch
edges is degenerate, and has no branch of odd length `≥ 3`. -/
theorem structure_of_four_branch_edges {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (h4 : 4 ≤ (bedges H).ncard) :
    DegenerateK4Appearance H ∧
      ∀ q : List (Fin n), IsBranch H q → ¬ (Odd (trackLength q) ∧ 3 ≤ trackLength q) := by
  classical
  obtain ⟨hsub, hbip⟩ := hH
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  obtain ⟨col⟩ := hbip
  -- Adjacency in `K₄` is just distinctness.
  have hA : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v h; rw [SimpleGraph.top_adj]; exact h
  have hdeg4 : ∀ u : Fin 4, 3 ≤ ((⊤ : SimpleGraph (Fin 4)).neighborSet u).ncard :=
    SubdivisionCounting.three_le_degree_of_three_connected _ SubdivisionCounting.k4_three_connected
  -- `branchVertices H = Set.range ι`.
  have hbv1 : Set.range ι ⊆ branchVertices H :=
    SubdivisionCounting.range_subset_branchVertices hι htrack hlen hdisjint hnew hdeg4
  have hbv2 : branchVertices H ⊆ Set.range ι :=
    SubdivisionCounting.branchVertices_subset_range htrack hrev hdisjint hcover hedges
  have hne : ∀ x y : Fin 4, x ≠ y → ι x ≠ ι y := fun x y h hc => h (hι hc)
  have hlen2 : ∀ u v : Fin 4, u ≠ v → 2 ≤ (T u v).length := by
    intro u v huv
    have := hlen u v (hA u v huv)
    simp only [trackLength] at this
    omega
  -- ### The 2-colouring, as a `ℕ`-valued function on the four branch-vertices
  obtain ⟨c, hcdef⟩ : ∃ c : Fin 4 → ℕ, ∀ u : Fin 4, c u = ((col (ι u) : Fin 2) : ℕ) :=
    ⟨fun u => ((col (ι u) : Fin 2) : ℕ), fun _ => rfl⟩
  have hc2 : ∀ u : Fin 4, c u < 2 := by
    intro u; rw [hcdef]; exact (col (ι u)).isLt
  -- **Parity.**  The colour alternates along `T u v`, whose ends are `ι u` and `ι v`.
  have hpar : ∀ u v : Fin 4, u ≠ v → trackLength (T u v) % 2 = (c u + c v) % 2 := by
    intro u v huv
    have ht := htrack u v (hA u v huv)
    have h2 := hlen2 u v huv
    have hcc := DegenerateK4Tracks.track_color col ht.1 ((T u v).length - 1) (by omega) (by omega)
    rw [DegenerateK4Tracks.track_getLast ht (by omega),
      SubdivisionCounting.track_head ht (by omega)] at hcc
    have b1 := (col (ι u)).isLt
    have b2 := (col (ι v)).isLt
    simp only [hcdef, trackLength]
    omega
  have heven : ∀ u v : Fin 4, u ≠ v → c u = c v → Even (trackLength (T u v)) := by
    intro u v huv h
    have := hpar u v huv
    rw [Nat.even_iff]
    omega
  have hoddc : ∀ u v : Fin 4, u ≠ v → trackLength (T u v) % 2 = 1 → c u ≠ c v := by
    intro u v huv h hc
    have := hpar u v huv
    omega
  -- ### Every branch-to-branch edge is a length-one track
  have key : ∀ e ∈ bedges H,
      ∃ u v : Fin 4, u ≠ v ∧ trackLength (T u v) = 1 ∧ e = s(ι u, ι v) := by
    intro e he
    obtain ⟨heE, hebv⟩ := he
    rw [hedges] at heE
    simp only [Set.mem_iUnion] at heE
    obtain ⟨u, v, huv, hein⟩ := heE
    obtain ⟨i, hi, rfl⟩ := hein
    have huv' : u ≠ v := huv.ne
    have h1 : (T u v)[i]'(by omega) ∉ trackInterior (T u v) := by
      intro hc
      exact hnew u v huv _ hc (hbv2 (hebv _ (by simp)))
    have h2 : (T u v)[i + 1]'hi ∉ trackInterior (T u v) := by
      intro hc
      exact hnew u v huv _ hc (hbv2 (hebv _ (by simp)))
    have hl2 := SubdivisionCounting.track_edge_len_two (T u v) i hi h1 h2
    have hi0 : i = 0 := by omega
    have e0 : (T u v)[i]'(by omega) = ι u := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq (T u v) hi0 (by omega) (by omega)]
      exact SubdivisionCounting.track_head (htrack u v huv) (by omega)
    have e1 : (T u v)[i + 1]'hi = ι v := by
      rw [SubdivisionCounting.getElem_eq_of_index_eq (T u v) (show i + 1 = 1 by omega) hi
        (by omega)]
      exact SubdivisionCounting.track_last (htrack u v huv) hl2
    exact ⟨u, v, huv', by simp only [trackLength, hl2], by rw [e0, e1]⟩
  -- ### `bedges H` cannot be covered by three edges
  have hbound3 : ∀ x y z : Sym2 (Fin n),
      (∀ e ∈ bedges H, e = x ∨ e = y ∨ e = z) → False := by
    intro x y z hs
    have hss : bedges H ⊆ ({x, y, z} : Set (Sym2 (Fin n))) := by
      intro e he
      rcases hs e he with h | h | h <;> simp [h]
    have hfin : ({x, y, z} : Set (Sym2 (Fin n))).Finite :=
      ((Set.finite_singleton z).insert y).insert x
    have hb1 : (bedges H).ncard ≤ ({x, y, z} : Set (Sym2 (Fin n))).ncard :=
      Set.ncard_le_ncard hss hfin
    have hb2 : ({x, y, z} : Set (Sym2 (Fin n))).ncard ≤ ({y, z} : Set (Sym2 (Fin n))).ncard + 1 :=
      Set.ncard_insert_le _ _
    have hb3 : ({y, z} : Set (Sym2 (Fin n))).ncard ≤ ({z} : Set (Sym2 (Fin n))).ncard + 1 :=
      Set.ncard_insert_le _ _
    have hb4 : ({z} : Set (Sym2 (Fin n))).ncard = 1 := Set.ncard_singleton z
    omega
  -- ### Four candidate edges covering `bedges H` are all present
  have hone : ∀ A B C D : Sym2 (Fin n),
      (∀ e ∈ bedges H, e = A ∨ e = B ∨ e = C ∨ e = D) → A ∈ bedges H := by
    intro A B C D hs
    by_contra hA
    refine hbound3 B C D ?_
    intro e he
    rcases hs e he with h | h | h | h
    · exact absurd (h ▸ he) hA
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hfour : ∀ A B C D : Sym2 (Fin n),
      (∀ e ∈ bedges H, e = A ∨ e = B ∨ e = C ∨ e = D) →
      A ∈ bedges H ∧ B ∈ bedges H ∧ C ∈ bedges H ∧ D ∈ bedges H := by
    intro A B C D hs
    exact ⟨hone A B C D hs, hone B A C D (fun e he => by have := hs e he; tauto),
      hone C A B D (fun e he => by have := hs e he; tauto),
      hone D A B C (fun e he => by have := hs e he; tauto)⟩
  -- an edge between two branch-vertices belongs to `bedges H`
  have hmem : ∀ u v : Fin 4, H.Adj (ι u) (ι v) → s(ι u, ι v) ∈ bedges H := by
    intro u v hadj
    refine ⟨(SimpleGraph.mem_edgeSet _).mpr hadj, ?_⟩
    intro x hx
    rcases Sym2.mem_iff.mp hx with rfl | rfl
    · exact hbv1 ⟨u, rfl⟩
    · exact hbv1 ⟨v, rfl⟩
  -- four pairwise distinct elements of `Fin 4` are all of `Fin 4`
  have hall : ∀ p q r s : Fin 4, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      ∀ x : Fin 4, x = p ∨ x = q ∨ x = r ∨ x = s := by decide
  -- ### Three branch-vertices of the same colour are impossible
  have BAD : ∀ p q r s : Fin 4, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      c p = c q → c q = c r → False := by
    intro p q r s hpq hpr hps hqr hqs hrs h1 h2
    have hallx := hall p q r s hpq hpr hps hqr hqs hrs
    refine hbound3 s(ι p, ι s) s(ι q, ι s) s(ι r, ι s) ?_
    intro e he
    obtain ⟨u, v, huv, hl, rfl⟩ := key e he
    have hcuv : c u ≠ c v := hoddc u v huv (by omega)
    rcases hallx u with rfl | rfl | rfl | rfl <;> rcases hallx v with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl huv
        | omega
        | simp
  -- ### The balanced case: all four cross edges are edges of `H`
  have KEY : ∀ p q r s : Fin 4, p ≠ q → p ≠ r → p ≠ s → q ≠ r → q ≠ s → r ≠ s →
      c p = c q → c r = c s → c p ≠ c r →
      ∀ u v : Fin 4, u ≠ v → c u ≠ c v → H.Adj (ι u) (ι v) := by
    intro p q r s hpq hpr hps hqr hqs hrs h1 h2 h3
    have hallx := hall p q r s hpq hpr hps hqr hqs hrs
    have hsub4 : ∀ e ∈ bedges H,
        e = s(ι p, ι r) ∨ e = s(ι p, ι s) ∨ e = s(ι q, ι r) ∨ e = s(ι q, ι s) := by
      intro e he
      obtain ⟨u, v, huv, hl, rfl⟩ := key e he
      have hcuv : c u ≠ c v := hoddc u v huv (by omega)
      rcases hallx u with rfl | rfl | rfl | rfl <;> rcases hallx v with rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl huv
          | omega
          | simp
    obtain ⟨mpr, mps, mqr, mqs⟩ := hfour _ _ _ _ hsub4
    have apr : H.Adj (ι p) (ι r) := (SimpleGraph.mem_edgeSet _).mp mpr.1
    have aps : H.Adj (ι p) (ι s) := (SimpleGraph.mem_edgeSet _).mp mps.1
    have aqr : H.Adj (ι q) (ι r) := (SimpleGraph.mem_edgeSet _).mp mqr.1
    have aqs : H.Adj (ι q) (ι s) := (SimpleGraph.mem_edgeSet _).mp mqs.1
    intro u v huv hcuv
    rcases hallx u with rfl | rfl | rfl | rfl <;> rcases hallx v with rfl | rfl | rfl | rfl <;>
      first
        | exact absurd rfl huv
        | omega
        | assumption
        | exact apr.symm
        | exact aps.symm
        | exact aqr.symm
        | exact aqs.symm
  -- ### The colouring is balanced
  have hcases : ∀ u : Fin 4, c u = 0 ∨ c u = 1 := by
    intro u; have := hc2 u; omega
  obtain ⟨p, q, r, s, hpq, hpr, hps, hqr, hqs, hrs, e1, e2, e3⟩ :
      ∃ p q r s : Fin 4, p ≠ q ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧ r ≠ s ∧
        c p = c q ∧ c r = c s ∧ c p ≠ c r := by
    rcases hcases 0 with h0 | h0 <;> rcases hcases 1 with h1 | h1 <;>
      rcases hcases 2 with h2 | h2 <;> rcases hcases 3 with h3 | h3 <;>
      first
        | exact ⟨0, 1, 2, 3, by decide, by decide, by decide, by decide, by decide, by decide,
            by omega, by omega, by omega⟩
        | exact ⟨0, 2, 1, 3, by decide, by decide, by decide, by decide, by decide, by decide,
            by omega, by omega, by omega⟩
        | exact ⟨0, 3, 1, 2, by decide, by decide, by decide, by decide, by decide, by decide,
            by omega, by omega, by omega⟩
        | exact (BAD 0 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by omega) (by omega)).elim
        | exact (BAD 0 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by omega) (by omega)).elim
        | exact (BAD 0 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by omega) (by omega)).elim
        | exact (BAD 1 2 3 0 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by omega) (by omega)).elim
  have hadj : ∀ u v : Fin 4, u ≠ v → c u ≠ c v → H.Adj (ι u) (ι v) :=
    KEY p q r s hpq hpr hps hqr hqs hrs e1 e2 e3
  have hallx := hall p q r s hpq hpr hps hqr hqs hrs
  -- ### The two conclusions
  constructor
  · -- the four-cycle `ι p - ι r - ι q - ι s - ι p`
    refine ⟨ι p, ι r, ι q, ι s, nodup4 (hne p r hpr) (hne p q hpq) (hne p s hps)
      (hne r q (Ne.symm hqr)) (hne r s hrs) (hne q s hqs), hadj p r hpr e3,
      (hadj q r hqr (by omega)).symm, hadj q s hqs (by omega),
      (hadj p s hps (by omega)).symm, ?_⟩
    intro x hx
    obtain ⟨y, rfl⟩ := hbv2 hx
    rcases hallx y with rfl | rfl | rfl | rfl <;> simp
  · rintro qq hqq ⟨hodd, h3⟩
    have hq2 : 2 ≤ qq.length := by
      simp only [trackLength] at h3
      omega
    obtain ⟨u, v, huv, heq⟩ := BranchClassification.exists_trackEdges_eq_of_isBranch
      hι htrack hlen hrev hdisjint hnew hcover hedges hdeg4 hqq hq2
    have hcard1 : (trackEdges qq).ncard = trackLength qq :=
      K4AppearanceEightVertices.trackEdges_ncard qq hqq.1.2.1
    have hcard2 : (trackEdges (T u v)).ncard = trackLength (T u v) :=
      K4AppearanceEightVertices.trackEdges_ncard _ (htrack u v huv).1.2.1
    have hll : trackLength qq = trackLength (T u v) := by rw [← hcard1, ← hcard2, heq]
    have huv' : u ≠ v := huv.ne
    by_cases hcc : c u = c v
    · have hev := heven u v huv' hcc
      rw [hll] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) hev
    · have hb := hmem u v (hadj u v huv' hcc)
      obtain ⟨a, b, hab, hl1, heq2⟩ := key _ hb
      have hone1 : trackLength (T u v) = 1 := by
        rcases Sym2.eq_iff.mp heq2 with ⟨ha, hb'⟩ | ⟨ha, hb'⟩
        · have k1 : u = a := hι ha
          have k2 : v = b := hι hb'
          rw [k1, k2]
          exact hl1
        · have k1 : u = b := hι ha
          have k2 : v = a := hι hb'
          have hr := hrev a b (hA a b hab)
          rw [k1, k2]
          simp only [trackLength, hr, List.length_reverse]
          simpa only [trackLength] using hl1
      omega

/-- **Four branch-to-branch edges make the `K₄`-subdivision degenerate.** -/
theorem degenerate_of_four_branch_edges {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (h4 : 4 ≤ (bedges H).ncard) : DegenerateK4Appearance H :=
  (structure_of_four_branch_edges hH h4).1

/-- **With four branch-to-branch edges, no branch has odd length `≥ 3`.** -/
theorem no_long_odd_branch_of_four_branch_edges {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H)
    (h4 : 4 ≤ (bedges H).ncard)
    (q : List (Fin n)) (hq : IsBranch H q) : ¬ (Odd (trackLength q) ∧ 3 ≤ trackLength q) :=
  (structure_of_four_branch_edges hH h4).2 q hq

end Workspace.ProofLemmas.K4TrackLengthDegeneracy
