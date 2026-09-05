import Mathlib
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.DegenerateK4Tracks

/-!
# An appearance of `K₄` forces `|V(G)| ≥ 8`

This module supplies the "consequently" of one sentence in the proof of 9.6 (printed p. 55):

> *"We may assume that there is an appearance of `K₄` in one of `G, Ḡ`, and consequently
> `|V(G)| ≥ 8`."*

The paper prints no argument.  Here is the one it means.

An appearance of `K₄` in `Gx` is a **bipartite** subdivision `H` of `K₄` together with a set
`K : Set V` and an isomorphism `L(H) ≃g Gx|K`.  The vertices of `L(H)` are the edges of `H`, so
`|K| = |E(H)|`.

Write `ℓ_{uv} := trackLength (T u v)` for the length (= number of edges) of the track of `H`
joining the branch-vertices `ι u`, `ι v`, one for each of the six edges `uv` of `K₄`.  The six
track edge-sets are pairwise disjoint (`SubdivisionCounting.trackEdges_disjoint`) and each has
exactly `ℓ_{uv}` elements (`trackEdges_ncard`), so `|E(H)| ≥ Σ_{uv} ℓ_{uv}`.

Because `H` is bipartite, fix a 2-colouring `col`.  `DegenerateK4Tracks.track_color` says the
colour alternates along a track, so reading it at the far end of `T u v` gives

```
ℓ_{uv} ≡ col(ι u) + col(ι v)   (mod 2).
```

Hence for each of the **four triangles** `{u,v,w}` of `K₄` the sum
`ℓ_{uv} + ℓ_{vw} + ℓ_{uw} ≡ 2(col u + col v + col w) ≡ 0 (mod 2)` is even; each `ℓ ≥ 1`, so each
triangle sum is `≥ 3` and even, hence `≥ 4`.  Summing over the four triangles counts each of the
six edges twice, so `2 Σ ℓ ≥ 16` and `|E(H)| ≥ Σ ℓ ≥ 8`.  (`omega` performs this last count
from the six parities, the six lower bounds `ℓ ≥ 1` and the four bounds `col < 2`; the four
triangle inequalities are exactly what it derives.)

Finally `K ⊆ V`, so `8 ≤ |E(H)| = K.ncard ≤ Nat.card V`.

**On `[Fintype V]`.**  The top-level statement genuinely needs a finiteness instance on `V`:
`Nat.card V = 0` when `V` is infinite, while `K` — being in bijection with the edge set of a
graph on `Fin n` — is always finite, so without it the conclusion `8 ≤ Nat.card V` is *false*.
`eight_le_ncard_of_isAppearance`, whose conclusion is about `K.ncard`, needs no instance.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K4AppearanceEightVertices

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.ProofLemmas.SubdivisionCounting
open Workspace.ProofLemmas.DegenerateK4Tracks

/-! ### The edge set of a track -/

/-- Every edge of a track of `H` is an edge of `H`. -/
theorem trackEdges_subset_edgeSet {W : Type*} {H : SimpleGraph W} {q : List W}
    (hq : IsTrackList H q) : trackEdges q ⊆ H.edgeSet := by
  rintro e ⟨i, hi, rfl⟩
  exact (SimpleGraph.mem_edgeSet _).mpr (hq.2.2 i hi)

/-- The edges of a track, enumerated by their position along it. -/
theorem trackEdges_eq_range {W : Type*} (q : List W) :
    trackEdges q = Set.range (fun i : Fin (q.length - 1) =>
      s(q[i.val]'(by have := i.isLt; omega), q[i.val + 1]'(by have := i.isLt; omega))) := by
  ext e
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, by omega⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    have hi := i.isLt
    exact ⟨i.val, by omega, rfl⟩

/-- **A track has exactly `trackLength q` edges.**  The enumeration above is injective because
the vertices of a track are distinct: `s(q[i], q[i+1]) = s(q[j], q[j+1])` forces either
`i = j`, or `i = j + 1` and `i + 1 = j`, which is absurd. -/
theorem trackEdges_ncard {W : Type*} (q : List W) (hnd : q.Nodup) :
    (trackEdges q).ncard = trackLength q := by
  classical
  have hinj : Function.Injective (fun i : Fin (q.length - 1) =>
      s(q[i.val]'(by have := i.isLt; omega), q[i.val + 1]'(by have := i.isLt; omega))) := by
    intro i j hij
    simp only at hij
    rcases Sym2.eq_iff.mp hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Fin.val_injective (hnd.getElem_inj_iff.mp h1)
    · have e1 := hnd.getElem_inj_iff.mp h1
      have e2 := hnd.getElem_inj_iff.mp h2
      exact Fin.val_injective (by omega)
  rw [trackEdges_eq_range q, ← Set.image_univ, Set.ncard_image_of_injective _ hinj,
    Set.ncard_univ]
  simp [trackLength]

/-! ### Six pairwise disjoint sets inside one finite set -/

/-- Six pairwise disjoint subsets of a set `E` in a finite type have total size at most
`E.ncard`.  (Specialised to six because that is the number of edges of `K₄`.) -/
private theorem ncard_six_le {α : Type*} [Finite α] {E s₁ s₂ s₃ s₄ s₅ s₆ : Set α}
    (h₁ : s₁ ⊆ E) (h₂ : s₂ ⊆ E) (h₃ : s₃ ⊆ E) (h₄ : s₄ ⊆ E) (h₅ : s₅ ⊆ E) (h₆ : s₆ ⊆ E)
    (d₁₂ : Disjoint s₁ s₂) (d₁₃ : Disjoint s₁ s₃) (d₁₄ : Disjoint s₁ s₄)
    (d₁₅ : Disjoint s₁ s₅) (d₁₆ : Disjoint s₁ s₆)
    (d₂₃ : Disjoint s₂ s₃) (d₂₄ : Disjoint s₂ s₄) (d₂₅ : Disjoint s₂ s₅) (d₂₆ : Disjoint s₂ s₆)
    (d₃₄ : Disjoint s₃ s₄) (d₃₅ : Disjoint s₃ s₅) (d₃₆ : Disjoint s₃ s₆)
    (d₄₅ : Disjoint s₄ s₅) (d₄₆ : Disjoint s₄ s₆) (d₅₆ : Disjoint s₅ s₆) :
    s₁.ncard + s₂.ncard + s₃.ncard + s₄.ncard + s₅.ncard + s₆.ncard ≤ E.ncard := by
  have u2 : (s₁ ∪ s₂).ncard = s₁.ncard + s₂.ncard := Set.ncard_union_eq d₁₂
  have u3 : (s₁ ∪ s₂ ∪ s₃).ncard = (s₁ ∪ s₂).ncard + s₃.ncard :=
    Set.ncard_union_eq (Set.disjoint_union_left.mpr ⟨d₁₃, d₂₃⟩)
  have u4 : (s₁ ∪ s₂ ∪ s₃ ∪ s₄).ncard = (s₁ ∪ s₂ ∪ s₃).ncard + s₄.ncard :=
    Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨d₁₄, d₂₄⟩, d₃₄⟩)
  have u5 : (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅).ncard = (s₁ ∪ s₂ ∪ s₃ ∪ s₄).ncard + s₅.ncard :=
    Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d₁₅, d₂₅⟩, d₃₅⟩, d₄₅⟩)
  have u6 : (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆).ncard
      = (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅).ncard + s₆.ncard :=
    Set.ncard_union_eq (Set.disjoint_union_left.mpr
      ⟨Set.disjoint_union_left.mpr
        ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨d₁₆, d₂₆⟩, d₃₆⟩, d₄₆⟩, d₅₆⟩)
  have hsub : s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆ ⊆ E :=
    Set.union_subset (Set.union_subset (Set.union_subset (Set.union_subset
      (Set.union_subset h₁ h₂) h₃) h₄) h₅) h₆
  calc s₁.ncard + s₂.ncard + s₃.ncard + s₄.ncard + s₅.ncard + s₆.ncard
      = (s₁ ∪ s₂ ∪ s₃ ∪ s₄ ∪ s₅ ∪ s₆).ncard := by rw [u6, u5, u4, u3, u2]
    _ ≤ E.ncard := Set.ncard_le_ncard hsub

/-! ### A bipartite subdivision of `K₄` has at least eight edges -/

private theorem six_lengths_at_least_eight
    (l01 l02 l03 l12 l13 l23 c0 c1 c2 c3 : ℕ)
    (hl01 : 1 ≤ l01) (hl02 : 1 ≤ l02) (hl03 : 1 ≤ l03)
    (hl12 : 1 ≤ l12) (hl13 : 1 ≤ l13) (hl23 : 1 ≤ l23)
    (hc0 : c0 < 2) (hc1 : c1 < 2) (hc2 : c2 < 2) (hc3 : c3 < 2)
    (hp01 : l01 % 2 = (c0 + c1) % 2)
    (hp02 : l02 % 2 = (c0 + c2) % 2)
    (hp03 : l03 % 2 = (c0 + c3) % 2)
    (hp12 : l12 % 2 = (c1 + c2) % 2)
    (hp13 : l13 % 2 = (c1 + c3) % 2)
    (hp23 : l23 % 2 = (c2 + c3) % 2) :
    8 ≤ l01 + l02 + l03 + l12 + l13 + l23 := by
  omega

/-- **The heart of the count.**  A bipartite subdivision of `K₄` has at least `8` edges.

The six tracks have lengths `ℓ_{uv} ≥ 1` and, `H` being bipartite,
`ℓ_{uv} ≡ col(ι u) + col(ι v) (mod 2)`; so each of the four triangle sums of `K₄` is even and
`≥ 3`, hence `≥ 4`, and `2 Σ ℓ ≥ 16`. -/
theorem eight_le_edgeSet_ncard {n : ℕ} {H : SimpleGraph (Fin n)}
    (hH : IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) H) : 8 ≤ H.edgeSet.ncard := by
  classical
  obtain ⟨hsub, hbip⟩ := hH
  obtain ⟨ι, T, hι, htrack, hlen, hrev, hdisjint, hnew, hcover, hedges⟩ := hsub
  obtain ⟨col⟩ := hbip
  -- Adjacency in `K₄` is just distinctness.
  have hA : ∀ u v : Fin 4, u ≠ v → (⊤ : SimpleGraph (Fin 4)).Adj u v := by
    intro u v h; rw [SimpleGraph.top_adj]; exact h
  -- Every track has at least two vertices.
  have hlen2 : ∀ u v : Fin 4, u ≠ v → 2 ≤ (T u v).length := by
    intro u v huv
    have := hlen u v (hA u v huv)
    simp only [trackLength] at this
    omega
  -- **Parity.**  The 2-colouring alternates along `T u v`, whose ends are `ι u` and `ι v`.
  have hpar : ∀ u v : Fin 4, u ≠ v →
      trackLength (T u v) % 2 = ((col (ι u) : ℕ) + (col (ι v) : ℕ)) % 2 := by
    intro u v huv
    have ht := htrack u v (hA u v huv)
    have h2 := hlen2 u v huv
    have hc := track_color col ht.1 ((T u v).length - 1) (by omega) (by omega)
    rw [track_getLast ht (by omega), track_head ht (by omega)] at hc
    have b1 := (col (ι u)).isLt
    have b2 := (col (ι v)).isLt
    simp only [trackLength]
    omega
  -- **The arithmetic.**  Four even triangle sums, each `≥ 4`, counting each edge twice.
  have key : 8 ≤ trackLength (T 0 1) + trackLength (T 0 2) + trackLength (T 0 3)
      + trackLength (T 1 2) + trackLength (T 1 3) + trackLength (T 2 3) := by
    apply six_lengths_at_least_eight
    · exact hlen 0 1 (hA 0 1 (by decide))
    · exact hlen 0 2 (hA 0 2 (by decide))
    · exact hlen 0 3 (hA 0 3 (by decide))
    · exact hlen 1 2 (hA 1 2 (by decide))
    · exact hlen 1 3 (hA 1 3 (by decide))
    · exact hlen 2 3 (hA 2 3 (by decide))
    · exact (col (ι 0)).isLt
    · exact (col (ι 1)).isLt
    · exact (col (ι 2)).isLt
    · exact (col (ι 3)).isLt
    · exact hpar 0 1 (by decide)
    · exact hpar 0 2 (by decide)
    · exact hpar 0 3 (by decide)
    · exact hpar 1 2 (by decide)
    · exact hpar 1 3 (by decide)
    · exact hpar 2 3 (by decide)
  -- Each track's edge set sits inside `E(H)` and has exactly `trackLength` elements.
  have hsubset : ∀ u v : Fin 4, u ≠ v → trackEdges (T u v) ⊆ H.edgeSet := fun u v huv =>
    trackEdges_subset_edgeSet (htrack u v (hA u v huv)).1
  have hcard : ∀ u v : Fin 4, u ≠ v →
      (trackEdges (T u v)).ncard = trackLength (T u v) := fun u v huv =>
    trackEdges_ncard (T u v) (htrack u v (hA u v huv)).1.2.1
  -- Distinct edges of `K₄` carry tracks with disjoint edge sets.
  have hdisj : ∀ u v u' v' : Fin 4, u ≠ v → u' ≠ v' → s(u, v) ≠ s(u', v') →
      Disjoint (trackEdges (T u v)) (trackEdges (T u' v')) := by
    intro u v u' v' huv hu'v' hne
    rw [Set.disjoint_left]
    intro a ha ha'
    exact hne (trackEdges_disjoint hι htrack hlen hdisjint u v u' v'
      (hA u v huv) (hA u' v' hu'v') a ha ha')
  have hle := ncard_six_le (E := H.edgeSet)
    (hsubset 0 1 (by decide)) (hsubset 0 2 (by decide)) (hsubset 0 3 (by decide))
    (hsubset 1 2 (by decide)) (hsubset 1 3 (by decide)) (hsubset 2 3 (by decide))
    (hdisj 0 1 0 2 (by decide) (by decide) (by decide))
    (hdisj 0 1 0 3 (by decide) (by decide) (by decide))
    (hdisj 0 1 1 2 (by decide) (by decide) (by decide))
    (hdisj 0 1 1 3 (by decide) (by decide) (by decide))
    (hdisj 0 1 2 3 (by decide) (by decide) (by decide))
    (hdisj 0 2 0 3 (by decide) (by decide) (by decide))
    (hdisj 0 2 1 2 (by decide) (by decide) (by decide))
    (hdisj 0 2 1 3 (by decide) (by decide) (by decide))
    (hdisj 0 2 2 3 (by decide) (by decide) (by decide))
    (hdisj 0 3 1 2 (by decide) (by decide) (by decide))
    (hdisj 0 3 1 3 (by decide) (by decide) (by decide))
    (hdisj 0 3 2 3 (by decide) (by decide) (by decide))
    (hdisj 1 2 1 3 (by decide) (by decide) (by decide))
    (hdisj 1 2 2 3 (by decide) (by decide) (by decide))
    (hdisj 1 3 2 3 (by decide) (by decide) (by decide))
  rw [hcard 0 1 (by decide), hcard 0 2 (by decide), hcard 0 3 (by decide),
    hcard 1 2 (by decide), hcard 1 3 (by decide), hcard 2 3 (by decide)] at hle
  omega

/-! ### The two statements 9.6 uses -/

variable {V : Type*}

/-- The vertex set `K` of an appearance of `K₄` in `Gx` has at least eight vertices: it is in
bijection (through the isomorphism `L(H) ≃g Gx|K`) with the edge set of `H`, and `H` — a
bipartite subdivision of `K₄` — has at least eight edges. -/
theorem eight_le_ncard_of_isAppearance {n : ℕ} {H : SimpleGraph (Fin n)} {K : Set V}
    (Gx : SimpleGraph V) (h : IsAppearance Gx (⊤ : SimpleGraph (Fin 4)) H K) : 8 ≤ K.ncard := by
  obtain ⟨hsub, ⟨φ⟩⟩ := h
  have hcard : H.edgeSet.ncard = K.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.toEquiv
  rw [← hcard]
  exact eight_le_edgeSet_ncard hsub

/-- **9.6, printed p. 55**: *"We may assume that there is an appearance of `K₄` in one of
`G, Ḡ`, and consequently `|V(G)| ≥ 8`."*

An appearance of `K₄` in `Gx` occupies at least eight vertices of `Gx`, so `Gx` has at least
eight vertices.  (Complementation does not change the vertex set, so the same bound follows from
an appearance in `Ḡ`.) -/
theorem eight_le_card_of_appears [Fintype V] (Gx : SimpleGraph V)
    (h : Appears Gx (⊤ : SimpleGraph (Fin 4))) : 8 ≤ Nat.card V := by
  obtain ⟨n, H, K, hK⟩ := h
  have h1 : 8 ≤ K.ncard := eight_le_ncard_of_isAppearance Gx hK
  have h2 : K.ncard ≤ (Set.univ : Set V).ncard :=
    Set.ncard_le_ncard (Set.subset_univ K) Set.finite_univ
  rw [Set.ncard_univ] at h2
  omega

end Workspace.ProofLemmas.K4AppearanceEightVertices
