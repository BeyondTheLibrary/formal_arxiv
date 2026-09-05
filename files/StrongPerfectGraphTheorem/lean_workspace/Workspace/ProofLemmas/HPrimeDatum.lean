import Mathlib
import Workspace.Types.Tracks
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.SubdivisionDatum
import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.DegenerateK4Tracks
import Workspace.ProofLemmas.HPrimeTracks

/-!
# The second `K₄`-subdivision `H'` of 5.3, as a datum

> *"The subgraph `H'` formed by the edges `E(P) ∪ E(Q) ∪ E(R) ∪ {p₁q_n, p_mq₁, p_mq_n}` (and the
> vertices of `H` incident with them) is a subdivision of `K₄`."*

`HPrimeTracks` supplied the five tracks besides `R`, with their endpoints, lengths and decoders.
This module assembles them into a `SubdivisionDatum.IsK4Datum`, which
`SubdivisionDatumRealize.exists_subgraph_isSubdivision_of_hasK4Datum` then turns into an honest
`S : H.Subgraph` with `IsSubdivision K₄ S.coe`.

## How the interior-disjointness clause is discharged

`IsK4Datum`'s fifth clause quantifies over **four** `Fin 4` indices, so the naive case analysis
has `4⁴ = 256` branches, each needing its own argument.  That is avoided completely by the
following observation, which is the real structure of `H'`:

> each of the six tracks is exactly *its two endpoints together with its own private zone*,

where the six zones are

| pair | zone | code |
|---|---|---|
| `{r₁, r_t}` | `trackInterior R` | 1 |
| `{r₁, p_m}` | `{P[k] : i < k < m-1}` | 2 |
| `{r₁, q_n}` | `{P[k] : k < i}` | 3 |
| `{r_t, p_m}` | `{Q[k] : k < j}` | 4 |
| `{r_t, q_n}` | `{Q[k] : j < k < n-1}` | 5 |
| `{p_m, q_n}` | `∅` | 6 |

and the zones are pairwise disjoint and miss the four branch-vertices.  So we build a single
`zid : W → ℕ` sending each vertex to the code of the zone containing it (`0` if none), prove
`zid` agrees with the code on each interior, and reduce the whole clause to

```
u ≠ v → u' ≠ v' → s(u,v) ≠ s(u',v') → code u v ≠ code u' v'
```

which is a closed statement about `Fin 4` and falls to **one `decide`** — kernel computation, no
per-branch elaboration.  The same `zid` discharges the sixth clause (interiors miss `range ι`)
for free, since branch-vertices have `zid = 0` and every interior has `zid ≠ 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HPrimeDatum

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.TrackSlice
open Workspace.ProofLemmas.HPrimeTracks

variable {W : Type*}

/-- **`H'` is a `K₄`-subdivision datum.**  The branch-vertices are `ι 0 = r₁ = P[i]`,
`ι 1 = r_t = Q[j]`, `ι 2 = p_m`, `ι 3 = q_n`, and the six track lengths are returned so that
`CrossTrackEndgame.cross_track_indices` can consume them. -/
theorem exists_hprime_datum {H : SimpleGraph W} {P Q R : List W} {i j : ℕ}
    (hP : IsTrackList H P) (hQ : IsTrackList H Q)
    (hm : 3 ≤ P.length) (hn : 3 ≤ Q.length)
    (hi : i ≤ P.length - 2) (hj : j ≤ Q.length - 2)
    (hPQ : ∀ x ∈ P, x ∉ Q)
    (hR : IsTrackFrom H R (P[i]'(by omega)) (Q[j]'(by omega)))
    (hRlen : 2 ≤ R.length)
    (hRint : ∀ w ∈ trackInterior R, w ∉ P ∧ w ∉ Q)
    (e1n : H.Adj (P[0]'(by omega)) (Q[Q.length - 1]'(by omega)))
    (em1 : H.Adj (P[P.length - 1]'(by omega)) (Q[0]'(by omega)))
    (emn : H.Adj (P[P.length - 1]'(by omega)) (Q[Q.length - 1]'(by omega))) :
    ∃ (ι : Fin 4 → W) (T : Fin 4 → Fin 4 → List W),
      IsK4Datum H ι T ∧
      ι 0 = P[i]'(by omega) ∧ ι 1 = Q[j]'(by omega) ∧
      ι 2 = P[P.length - 1]'(by omega) ∧ ι 3 = Q[Q.length - 1]'(by omega) ∧
      (T 0 1).length = R.length ∧ (T 0 2).length = P.length - i ∧
      (T 0 3).length = i + 2 ∧ (T 1 2).length = j + 2 ∧
      (T 1 3).length = Q.length - j ∧ (T 2 3).length = 2 := by
  classical
  have hPlen : P.length - 1 < P.length := by omega
  have hQlen : Q.length - 1 < Q.length := by omega
  have hiP : i < P.length := by omega
  have hjQ : j < Q.length := by omega
  obtain ⟨A02, A03, A12, A13, A23, t02, t03, t12, t13, t23,
    l02, l03, l12, l13, l23, m02, m03, m12, m13, m23,
    n02, n03, n12, n13, n23⟩ :=
    exists_hprime_tracks hP hQ hm hn hi hj hPQ e1n em1 emn
  -- index injectivity on `P` and `Q`, and `R ∩ P = {P[i]}`, `R ∩ Q = {Q[j]}`
  have hPinj : ∀ (a b : ℕ) (ha : a < P.length) (hb : b < P.length),
      (P[a]'ha) = (P[b]'hb) → a = b := fun _ _ _ _ h => hP.2.1.getElem_inj_iff.mp h
  have hQinj : ∀ (a b : ℕ) (ha : a < Q.length) (hb : b < Q.length),
      (Q[a]'ha) = (Q[b]'hb) → a = b := fun _ _ _ _ h => hQ.2.1.getElem_inj_iff.mp h
  have hR0 : 0 < R.length := by omega
  have hRP : ∀ (k : ℕ) (h : k < P.length), (P[k]'h) ∈ R → k = i := by
    intro k h hmemR
    have hnotint : (P[k]'h) ∉ trackInterior R := fun hc => (hRint _ hc).1 (List.getElem_mem h)
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hmemR hnotint hR0 with he | he
    · exact hPinj _ _ _ _ (he.trans (track_head hR hR0))
    · exact absurd (List.getElem_mem h)
        (by rw [he.trans (DegenerateK4Tracks.track_getLast hR hR0)]
            exact fun hc => hPQ _ hc (List.getElem_mem hjQ))
  have hRQ : ∀ (k : ℕ) (h : k < Q.length), (Q[k]'h) ∈ R → k = j := by
    intro k h hmemR
    have hnotint : (Q[k]'h) ∉ trackInterior R := fun hc => (hRint _ hc).2 (List.getElem_mem h)
    rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hmemR hnotint hR0 with he | he
    · exact absurd (List.getElem_mem h)
        (by rw [he.trans (track_head hR hR0)]
            exact hPQ _ (List.getElem_mem hiP))
    · exact hQinj _ _ _ _ (he.trans (DegenerateK4Tracks.track_getLast hR hR0))
  -- the branch-vertex embedding
  obtain ⟨ι, hι0, hι1, hι2, hι3⟩ : ∃ f : Fin 4 → W,
      f 0 = P[i]'hiP ∧ f 1 = Q[j]'hjQ ∧
      f 2 = P[P.length - 1]'hPlen ∧ f 3 = Q[Q.length - 1]'hQlen :=
    ⟨![P[i]'hiP, Q[j]'hjQ, P[P.length - 1]'hPlen, Q[Q.length - 1]'hQlen], rfl, rfl, rfl, rfl⟩
  -- the six tracks
  obtain ⟨T, hT01, hT02, hT03, hT12, hT13, hT23, hTrev⟩ : ∃ T : Fin 4 → Fin 4 → List W,
      T 0 1 = R ∧ T 0 2 = A02 ∧ T 0 3 = A03 ∧ T 1 2 = A12 ∧ T 1 3 = A13 ∧ T 2 3 = A23 ∧
      ∀ u v : Fin 4, T v u = (T u v).reverse := by
    refine ⟨![![[], R, A02, A03], ![R.reverse, [], A12, A13],
      ![A02.reverse, A12.reverse, [], A23], ![A03.reverse, A13.reverse, A23.reverse, []]],
      rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro u v
    fin_cases u <;> fin_cases v <;> simp
  have hswap_mem : ∀ (u v : Fin 4) (x : W), x ∈ T v u ↔ x ∈ T u v := by
    intro u v x; rw [hTrev u v, List.mem_reverse]
  have hswap_int : ∀ (u v : Fin 4) (x : W),
      x ∈ trackInterior (T v u) ↔ x ∈ trackInterior (T u v) := by
    intro u v x; rw [hTrev u v, trackInterior_reverse, List.mem_reverse]
  -- the zone codes
  obtain ⟨code, hc01, hc02, hc03, hc12, hc13, hc23, hcsymm, hcdist⟩ :
      ∃ c : Fin 4 → Fin 4 → ℕ,
        c 0 1 = 1 ∧ c 0 2 = 2 ∧ c 0 3 = 3 ∧ c 1 2 = 4 ∧ c 1 3 = 5 ∧ c 2 3 = 6 ∧
        (∀ u v : Fin 4, c u v = c v u) ∧
        (∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' →
          ¬((u = u' ∧ v = v') ∨ (u = v' ∧ v = u')) → c u v ≠ c u' v') :=
    ⟨![![0, 1, 2, 3], ![1, 0, 4, 5], ![2, 4, 0, 6], ![3, 5, 6, 0]],
      rfl, rfl, rfl, rfl, rfl, rfl, by decide, by decide⟩
  -- the zone of a vertex
  obtain ⟨zid, zR, zP2, zP3, zQ4, zQ5, zbr⟩ : ∃ f : W → ℕ,
      (∀ x ∈ trackInterior R, f x = 1) ∧
      (∀ (k : ℕ) (h : k < P.length), i < k → k < P.length - 1 → f (P[k]'h) = 2) ∧
      (∀ (k : ℕ) (h : k < P.length), k < i → f (P[k]'h) = 3) ∧
      (∀ (k : ℕ) (h : k < Q.length), k < j → f (Q[k]'h) = 4) ∧
      (∀ (k : ℕ) (h : k < Q.length), j < k → k < Q.length - 1 → f (Q[k]'h) = 5) ∧
      (∀ u : Fin 4, f (ι u) = 0) := by
    refine ⟨fun x =>
      if x ∈ trackInterior R then 1
      else if ∃ (k : ℕ) (h : k < P.length), i < k ∧ k < P.length - 1 ∧ P[k]'h = x then 2
      else if ∃ (k : ℕ) (h : k < P.length), k < i ∧ P[k]'h = x then 3
      else if ∃ (k : ℕ) (h : k < Q.length), k < j ∧ Q[k]'h = x then 4
      else if ∃ (k : ℕ) (h : k < Q.length), j < k ∧ k < Q.length - 1 ∧ Q[k]'h = x then 5
      else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    -- the two "wrong list" refutations, and the two "wrong index range" ones
    · intro x hx; dsimp only; rw [if_pos hx]
    · intro k h h1 h2
      dsimp only
      rw [if_neg (fun hc => (hRint _ hc).1 (List.getElem_mem h)), if_pos ⟨k, h, h1, h2, rfl⟩]
    · intro k h h1
      dsimp only
      rw [if_neg (fun hc => (hRint _ hc).1 (List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', ha, hb, hc⟩; have := hPinj _ _ _ _ hc; omega),
        if_pos ⟨k, h, h1, rfl⟩]
    · intro k h h1
      dsimp only
      rw [if_neg (fun hc => (hRint _ hc).2 (List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', -, -, hc⟩
                   exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', -, hc⟩
                   exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem h)),
        if_pos ⟨k, h, h1, rfl⟩]
    · intro k h h1 h2
      dsimp only
      rw [if_neg (fun hc => (hRint _ hc).2 (List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', -, -, hc⟩
                   exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', -, hc⟩
                   exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem h)),
        if_neg (by rintro ⟨k', h', ha, hc⟩; have := hQinj _ _ _ _ hc; omega),
        if_pos ⟨k, h, h1, h2, rfl⟩]
    · intro u
      have hnP : ∀ (a : ℕ) (ha : a < P.length), (P[a]'ha) ∉ trackInterior R :=
        fun a ha hc => (hRint _ hc).1 (List.getElem_mem ha)
      have hnQ : ∀ (a : ℕ) (ha : a < Q.length), (Q[a]'ha) ∉ trackInterior R :=
        fun a ha hc => (hRint _ hc).2 (List.getElem_mem ha)
      fin_cases u <;>
        simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, hι0, hι1, hι2, hι3]
      · rw [if_neg (hnP i hiP),
          if_neg (by rintro ⟨k', h', ha, hb, hc⟩; have := hPinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', ha, hc⟩; have := hPinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', -, hc⟩
                     exact hPQ _ (List.getElem_mem hiP) (hc ▸ List.getElem_mem h')),
          if_neg (by rintro ⟨k', h', -, -, hc⟩
                     exact hPQ _ (List.getElem_mem hiP) (hc ▸ List.getElem_mem h'))]
      · rw [if_neg (hnQ j hjQ),
          if_neg (by rintro ⟨k', h', -, -, hc⟩
                     exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem hjQ)),
          if_neg (by rintro ⟨k', h', -, hc⟩
                     exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem hjQ)),
          if_neg (by rintro ⟨k', h', ha, hc⟩; have := hQinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', ha, hb, hc⟩; have := hQinj _ _ _ _ hc; omega)]
      · rw [if_neg (hnP (P.length - 1) hPlen),
          if_neg (by rintro ⟨k', h', ha, hb, hc⟩; have := hPinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', ha, hc⟩; have := hPinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', -, hc⟩
                     exact hPQ _ (List.getElem_mem hPlen) (hc ▸ List.getElem_mem h')),
          if_neg (by rintro ⟨k', h', -, -, hc⟩
                     exact hPQ _ (List.getElem_mem hPlen) (hc ▸ List.getElem_mem h'))]
      · rw [if_neg (hnQ (Q.length - 1) hQlen),
          if_neg (by rintro ⟨k', h', -, -, hc⟩
                     exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem hQlen)),
          if_neg (by rintro ⟨k', h', -, hc⟩
                     exact hPQ _ (List.getElem_mem h') (hc ▸ List.getElem_mem hQlen)),
          if_neg (by rintro ⟨k', h', ha, hc⟩; have := hQinj _ _ _ _ hc; omega),
          if_neg (by rintro ⟨k', h', ha, hb, hc⟩; have := hQinj _ _ _ _ hc; omega)]
  -- interiors carry their zone code
  have hint0 : ∀ u v : Fin 4, u < v →
      ∀ x ∈ trackInterior (T u v), zid x = code u v ∧ code u v ≠ 0 := by
    intro u v huv x hx
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at huv hx ⊢
    · exact absurd huv (by decide)
    · rw [hT01] at hx; rw [zR x hx, hc01]; exact ⟨rfl, by omega⟩
    · rw [hT02] at hx
      obtain ⟨k, h, h1, h2, rfl⟩ := (n02 x).mp hx
      rw [zP2 k h h1 h2, hc02]; exact ⟨rfl, by omega⟩
    · rw [hT03] at hx
      obtain ⟨k, h, h1, rfl⟩ := (n03 x).mp hx
      rw [zP3 k h h1, hc03]; exact ⟨rfl, by omega⟩
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT12] at hx
      obtain ⟨k, h, h1, rfl⟩ := (n12 x).mp hx
      rw [zQ4 k h h1, hc12]; exact ⟨rfl, by omega⟩
    · rw [hT13] at hx
      obtain ⟨k, h, h1, h2, rfl⟩ := (n13 x).mp hx
      rw [zQ5 k h h1 h2, hc13]; exact ⟨rfl, by omega⟩
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT23, n23] at hx; simp at hx
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
  have hint : ∀ u v : Fin 4, u ≠ v →
      ∀ x ∈ trackInterior (T u v), zid x = code u v ∧ code u v ≠ 0 := by
    intro u v huv x hx
    rcases lt_or_gt_of_ne huv with h | h
    · exact hint0 u v h x hx
    · have hh := hint0 v u h x ((hswap_int u v x).mpr hx)
      rw [← hcsymm u v] at hh
      exact hh
  -- each track is its two ends together with its zone
  have hmem0 : ∀ u v : Fin 4, u < v →
      ∀ x ∈ T u v, x = ι u ∨ x = ι v ∨ zid x = code u v := by
    intro u v huv x hx
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at huv hx ⊢
    · exact absurd huv (by decide)
    · rw [hT01] at hx
      by_cases hc : x ∈ trackInterior R
      · exact Or.inr (Or.inr (by rw [zR x hc, hc01]))
      · rcases DegenerateK4Tracks.mem_ends_of_notMem_interior hx hc hR0 with he | he
        · exact Or.inl (by rw [hι0, he]; exact track_head hR hR0)
        · exact Or.inr (Or.inl (by rw [hι1, he]
                                   exact DegenerateK4Tracks.track_getLast hR hR0))
    · rw [hT02] at hx
      obtain ⟨k, h, h1, rfl⟩ := (m02 x).mp hx
      rcases eq_or_lt_of_le h1 with rfl | h2
      · exact Or.inl (by rw [hι0])
      · by_cases h3 : k < P.length - 1
        · exact Or.inr (Or.inr (by rw [zP2 k h h2 h3, hc02]))
        · exact Or.inr (Or.inl (by rw [hι2]
                                   exact getElem_eq_of_index_eq P (by omega) h hPlen))
    · rw [hT03] at hx
      rcases (m03 x).mp hx with ⟨k, h, h1, rfl⟩ | rfl
      · rcases eq_or_lt_of_le h1 with rfl | h2
        · exact Or.inl (by rw [hι0])
        · exact Or.inr (Or.inr (by rw [zP3 k h h2, hc03]))
      · exact Or.inr (Or.inl hι3.symm)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT12] at hx
      rcases (m12 x).mp hx with ⟨k, h, h1, rfl⟩ | rfl
      · rcases eq_or_lt_of_le h1 with rfl | h2
        · exact Or.inl (by rw [hι1])
        · exact Or.inr (Or.inr (by rw [zQ4 k h h2, hc12]))
      · exact Or.inr (Or.inl hι2.symm)
    · rw [hT13] at hx
      obtain ⟨k, h, h1, rfl⟩ := (m13 x).mp hx
      rcases eq_or_lt_of_le h1 with rfl | h2
      · exact Or.inl (by rw [hι1])
      · by_cases h3 : k < Q.length - 1
        · exact Or.inr (Or.inr (by rw [zQ5 k h h2 h3, hc13]))
        · exact Or.inr (Or.inl (by rw [hι3]
                                   exact getElem_eq_of_index_eq Q (by omega) h hQlen))
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT23] at hx
      rcases (m23 x).mp hx with rfl | rfl
      · exact Or.inl hι2.symm
      · exact Or.inr (Or.inl hι3.symm)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
  have hmem : ∀ u v : Fin 4, u ≠ v → ∀ x ∈ T u v, x = ι u ∨ x = ι v ∨ zid x = code u v := by
    intro u v huv x hx
    rcases lt_or_gt_of_ne huv with h | h
    · exact hmem0 u v h x hx
    · rcases hmem0 v u h x ((hswap_mem u v x).mpr hx) with hh | hh | hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inl hh
      · exact Or.inr (Or.inr (by rw [← hcsymm u v] at hh; exact hh))
  -- the six clauses of `IsK4Datum`
  have hinj : Function.Injective ι := by
    have d01 : ι 0 ≠ ι 1 := by
      rw [hι0, hι1]; exact fun h => hPQ _ (List.getElem_mem hiP) (h ▸ List.getElem_mem hjQ)
    have d02 : ι 0 ≠ ι 2 := by
      rw [hι0, hι2]; exact fun h => absurd (hPinj _ _ _ _ h) (by omega)
    have d03 : ι 0 ≠ ι 3 := by
      rw [hι0, hι3]; exact fun h => hPQ _ (List.getElem_mem hiP) (h ▸ List.getElem_mem hQlen)
    have d12 : ι 1 ≠ ι 2 := by
      rw [hι1, hι2]
      exact fun h => hPQ _ (List.getElem_mem hPlen) (h ▸ List.getElem_mem hjQ)
    have d13 : ι 1 ≠ ι 3 := by
      rw [hι1, hι3]; exact fun h => absurd (hQinj _ _ _ _ h) (by omega)
    have d23 : ι 2 ≠ ι 3 := by
      rw [hι2, hι3]; exact fun h => hPQ _ (List.getElem_mem hPlen) (h ▸ List.getElem_mem hQlen)
    intro a b hab
    fin_cases a <;> fin_cases b <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hab ⊢ <;>
      first
        | rfl
        | exact absurd hab d01 | exact absurd hab d02 | exact absurd hab d03
        | exact absurd hab d12 | exact absurd hab d13 | exact absurd hab d23
        | exact absurd hab.symm d01 | exact absurd hab.symm d02 | exact absurd hab.symm d03
        | exact absurd hab.symm d12 | exact absurd hab.symm d13 | exact absurd hab.symm d23
  have htrack0 : ∀ u v : Fin 4, u < v → IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at huv ⊢
    · exact absurd huv (by decide)
    · rw [hT01, hι0, hι1]; exact hR
    · rw [hT02, hι0, hι2]; exact t02
    · rw [hT03, hι0, hι3]; exact t03
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT12, hι1, hι2]; exact t12
    · rw [hT13, hι1, hι3]; exact t13
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT23, hι2, hι3]; exact t23
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
  have htrack : ∀ u v : Fin 4, u ≠ v → IsTrackFrom H (T u v) (ι u) (ι v) := by
    intro u v huv
    rcases lt_or_gt_of_ne huv with h | h
    · exact htrack0 u v h
    · rw [hTrev v u]
      exact isTrackFrom_reverse (htrack0 v u h)
  have hlen0 : ∀ u v : Fin 4, u < v → 2 ≤ (T u v).length := by
    intro u v huv
    fin_cases u <;> fin_cases v <;>
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at huv ⊢
    · exact absurd huv (by decide)
    · rw [hT01]; omega
    · rw [hT02, l02]; omega
    · rw [hT03, l03]; omega
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT12, l12]; omega
    · rw [hT13, l13]; omega
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · rw [hT23, l23]
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
    · exact absurd huv (by decide)
  have hlen : ∀ u v : Fin 4, u ≠ v → 1 ≤ trackLength (T u v) := by
    intro u v huv
    have h2 : 2 ≤ (T u v).length := by
      rcases lt_or_gt_of_ne huv with h | h
      · exact hlen0 u v h
      · rw [hTrev v u, List.length_reverse]; exact hlen0 v u h
    simp only [trackLength]
    omega
  refine ⟨ι, T, ⟨hinj, htrack, hlen, fun u v _ => hTrev u v, ?_, ?_⟩,
    hι0, hι1, hι2, hι3, by rw [hT01], by rw [hT02, l02], by rw [hT03, l03],
    by rw [hT12, l12], by rw [hT13, l13], by rw [hT23, l23]⟩
  · -- interiors of distinct tracks miss the other track
    intro u v u' v' huv huv' hs w hw hmemw
    obtain ⟨hzw, hne0⟩ := hint u v huv w hw
    rcases hmem u' v' huv' w hmemw with hh | hh | hh
    · rw [hh, zbr] at hzw; exact hne0 hzw.symm
    · rw [hh, zbr] at hzw; exact hne0 hzw.symm
    · exact hcdist u v u' v' huv huv' (fun hcon => hs (Sym2.eq_iff.mpr hcon)) (hzw.symm.trans hh)
  · -- interiors miss the branch-vertices
    rintro u v huv w hw ⟨k, hk⟩
    obtain ⟨hzw, hne0⟩ := hint u v huv w hw
    rw [← hk, zbr] at hzw
    exact hne0 hzw.symm

end Workspace.ProofLemmas.HPrimeDatum
