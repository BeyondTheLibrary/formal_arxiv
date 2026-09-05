import Workspace.ProofLemmas.Thm58StarBranchStarTracks
import Workspace.ProofLemmas.Thm58StarBranchGeometry
import Workspace.ProofLemmas.Thm58StarBranchMixedHole

/-!
# The mixed-star link of 5.8 (6)

PAPER (proof of 5.8 (6), printed p. 28): *"Let `A` be the neighbours of `p₁` in `N_u` and
`B = N_u \ A`.  In `H` there is a cycle `C₂` using the branch between `v₁` and `v₂`, and using
an edge in `A` and an edge in `B`.  (To see this, divide `u` into two adjacent vertices, one
incident with the edges in `A` and the other with those in `B`, and use Menger's theorem to
deduce that there are two vertex-disjoint paths between these two vertices and `{v₁,v₂}`.)
Hence in `G`, there is a path between `N_{v₁}` and `N_{v₂}` using a unique edge of `N(u)`, and
that edge is between a vertex `a ∈ A` and some vertex in `B`.  Hence `a` can be linked onto the
triangle formed by `pₙ` and its two neighbours in `R_{v₁v₂}`, a contradiction."*

Deleting `a` from the path that the cycle `C₂` produces leaves two pieces, one reaching `r`
and one reaching `s`; together with `P` they are the three paths of the link, and `pₙ`, `r`,
`s` are their ends.  This file proves that the link follows from those two pieces
(`mixed_link_of_sectors`) and that the two pieces follow from the hole that the cycle `C₂`
induces in `G` (`exists_mixedSectors`).  The existence of that hole is the remaining gap, and
is stated in `Workspace.ProofLemmas.Thm58StarBranchMixedHole`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarBranchMixed

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT Workspace.Types.RousselRubio.SPGT
open Thm58StarBranchBasics

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V}
  {c : Fin n} {q : List (Fin n)}

/-- The two pieces of the cycle `C₂`, and the vertex `a ∈ A` between them.

`D₁` and `D₂` are the two regions of the appearance the two pieces live in; `T₁` and `T₂` are
the pieces themselves, ending at `pₙ`'s two neighbours `r` and `s`. -/
structure MixedSectors (G : SimpleGraph V) (K : Set V) (N : Fin n → Set V) (c : Fin n)
    (p₁ p₂ r s a : V) (D₁ D₂ : Set V) (T₁ T₂ : List V) : Prop where
  aStar : a ∈ N c
  aAdj : G.Adj p₁ a
  subK₁ : D₁ ⊆ K
  subK₂ : D₂ ⊆ K
  disj : ∀ x ∈ D₁, x ∉ D₂
  offStar₁ : ∀ x ∈ D₁, ¬ G.Adj p₁ x
  offStar₂ : ∀ x ∈ D₂, ¬ G.Adj p₁ x
  last₁ : ∀ x ∈ D₁, G.Adj p₂ x → x = r
  last₂ : ∀ x ∈ D₂, G.Adj p₂ x → x = s
  cross : ∀ x ∈ D₁, ∀ y ∈ D₂, G.Adj x y → x = r ∧ y = s
  path₁ : IsPathList G T₁
  path₂ : IsPathList G T₂
  sub₁ : ∀ x ∈ T₁, x ∈ D₁
  sub₂ : ∀ x ∈ T₂, x ∈ D₂
  end₁ : T₁.getLast? = some r
  end₂ : T₂.getLast? = some s
  nbr₁ : ∃ x ∈ T₁, G.Adj a x
  nbr₂ : ∃ x ∈ T₂, G.Adj a x

/-- With the two pieces in hand, the link onto the triangle `{pₙ, r, s}` is a bookkeeping
exercise: the only edges from `F` to the appearance run from `p₁` into the star at `c` and
from `pₙ` into the branch, and both regions avoid the star. -/
theorem mixed_link_of_sectors (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    {r s a : V} {D₁ D₂ : Set V} {T₁ T₂ : List V}
    (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : G.Adj r s) (hpr : G.Adj p₂ r) (hps : G.Adj p₂ s)
    (hM : MixedSectors G K N c p₁ p₂ r s a D₁ D₂ T₁ T₂) :
    VertexCanBeLinkedOntoTriangle G a p₂ r s := by
  classical
  have hdisjq : Disjoint (N c) (edgeImage φ (trackEdges q)) := star_disjoint_branch h hcq
  have hFK : F ⊆ Kᶜ := h.ready.2.2.2.2.1
  have hPF : ∀ x ∈ P, x ∉ K := by
    intro x hx
    have : x ∈ F := by rw [← vertices h]; exact hx
    exact hFK this
  -- the three paths and their sectors
  have hmain :=
    Thm101LinkOntoTriangle.canBeLinkedOntoTriangle_of_sectors G a
      ![p₂, r, s] ![P, T₁, T₂] ![{x : V | x ∈ P}, D₁, D₂] ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact hmain
  · -- the triangle
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;>
      first
        | exact hpr
        | exact hps
        | exact hpr.symm
        | exact hps.symm
        | exact hrs
        | exact hrs.symm
  · intro i
    fin_cases i
    · exact (path h).1
    · exact hM.path₁
    · exact hM.path₂
  · intro i
    fin_cases i
    · exact Or.inr (path h).2.2
    · exact Or.inr hM.end₁
    · exact Or.inr hM.end₂
  · intro i x hx
    fin_cases i
    · exact hx
    · exact hM.sub₁ x hx
    · exact hM.sub₂ x hx
  · -- pairwise disjointness of the sectors
    intro i j hij x hx hx'
    fin_cases i <;> fin_cases j <;> simp_all
    · exact hPF x hx (hM.subK₁ hx')
    · exact hPF x hx (hM.subK₂ hx')
    · exact hPF x hx' (hM.subK₁ hx)
    · exact hM.disj x hx hx'
    · exact hPF x hx' (hM.subK₂ hx)
    · exact hM.disj x hx' hx
  · -- the cross edges
    intro i j hij x hx y hy hadj
    have hPD : ∀ (D : Set V) (t : V), D ⊆ K → (∀ z ∈ D, ¬ G.Adj p₁ z) →
        (∀ z ∈ D, G.Adj p₂ z → z = t) → ∀ u ∈ P, ∀ v ∈ D, G.Adj u v → u = p₂ ∧ v = t := by
      intro D t hDK hDN hDt u hu v hv huv
      rcases edges_of_disjoint h hdisjq u hu v (hDK hv) huv with hh | hh
      · exact absurd (hh.1 ▸ huv) (hDN v hv)
      · exact ⟨hh.1, hDt v hv (hh.1 ▸ huv)⟩
    fin_cases i <;> fin_cases j <;> simp_all
    · exact hPD D₁ r hM.subK₁ hM.offStar₁ hM.last₁ x hx y hy hadj
    · exact hPD D₂ s hM.subK₂ hM.offStar₂ hM.last₂ x hx y hy hadj
    · exact (hPD D₁ r hM.subK₁ hM.offStar₁ hM.last₁ y hy x hx hadj.symm).symm
    · exact hM.cross x hx y hy hadj
    · exact (hPD D₂ s hM.subK₂ hM.offStar₂ hM.last₂ y hy x hx hadj.symm).symm
    · exact (hM.cross y hy x hx hadj.symm).symm
  · intro i
    fin_cases i
    · exact ⟨p₁, PathBasics.head_mem (path h).2.1, hM.aAdj.symm⟩
    · exact hM.nbr₁
    · exact hM.nbr₂

/-- **The two sectors of 5.8 (6).**  The rung of the cycle `C₂` of the paper is a hole `L` of
`G` inside the appearance (`Thm58StarBranchMixedHole.exists_mixed_hole`, the one remaining gap
of claim (6)).  Cutting `L` at the vertex `a` — the `A`-end of its unique edge in `N(u)` — and
at the edge `rs` leaves exactly the two arcs the link needs: one runs from a neighbour of `a`
to `r`, the other from the other neighbour of `a` to `s`.  Both arcs are induced paths because
`L` is a hole, they are disjoint and their only cross edge is `rs` for the same reason, and no
vertex of either is adjacent to `p₁` because `a` carried the only edge of `N(u)` on `L`. -/
theorem exists_mixedSectors (h : Context G m J n H K φ N F P p₁ p₂ c q) (hcq : c ∉ q)
    (r s : V) (hr : r ∈ edgeImage φ (trackEdges q)) (hs : s ∈ edgeImage φ (trackEdges q))
    (hrs : G.Adj r s) (hneighbors : ∀ x ∈ K, G.Adj p₂ x ↔ x = r ∨ x = s)
    (hA : ∃ a ∈ N c, G.Adj p₁ a) (hB : ∃ b ∈ N c, ¬ G.Adj p₁ b) :
    ∃ (a : V) (D₁ D₂ : Set V) (T₁ T₂ : List V),
      MixedSectors G K N c p₁ p₂ r s a D₁ D₂ T₁ T₂ := by
  classical
  obtain ⟨L, a, k, hL, hLK, hhead, haN, haAdj, hp1, hk1, hk2, hkr, hks⟩ :=
    Thm58StarBranchMixedHole.exists_mixed_hole h hcq r s hr hs hrs hneighbors hA hB
  have hn4 : 4 ≤ L.length := hL.1
  have hnd : L.Nodup := hL.2.1
  have hinj : ∀ (i j : ℕ) (hi : i < L.length) (hj : j < L.length),
      (L[i]'hi) = (L[j]'hj) → i = j := fun i j hi hj he =>
    (List.Nodup.getElem_inj_iff hnd).mp he
  have ha0 : (L[0]'(by omega)) = a := by
    rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < L.length by omega)] at hhead
    exact Option.some_injective _ hhead
  have hrk : (L[k]'(by omega)) = r := by
    rw [List.getElem?_eq_getElem (show k < L.length by omega)] at hkr
    exact Option.some_injective _ hkr
  have hsk : (L[k+1]'(by omega)) = s := by
    rw [List.getElem?_eq_getElem (show k + 1 < L.length by omega)] at hks
    exact Option.some_injective _ hks
  obtain ⟨T₁, T₂, hT₁, hT₂, hidx₁, hidx₂⟩ :=
    Thm58StarBranchMixedHole.arcs_of_hole hL hk1 hk2 a
  have hmem₁ : ∀ x ∈ T₁, x ∈ L := by
    intro x hx
    obtain ⟨i, _, _, hi, rfl⟩ := hidx₁ x hx
    exact List.getElem_mem hi
  have hmem₂ : ∀ x ∈ T₂, x ∈ L := by
    intro x hx
    obtain ⟨i, _, _, hi, rfl⟩ := hidx₂ x hx
    exact List.getElem_mem hi
  have hne₁ : ∀ x ∈ T₁, x ≠ a := by
    intro x hx hxa
    obtain ⟨i, hi1, hik, hi, hix⟩ := hidx₁ x hx
    have : i = 0 := hinj i 0 hi (by omega) (by rw [hix, hxa, ha0])
    omega
  have hne₂ : ∀ x ∈ T₂, x ≠ a := by
    intro x hx hxa
    obtain ⟨i, hi1, hik, hi, hix⟩ := hidx₂ x hx
    have : i = 0 := hinj i 0 hi (by omega) (by rw [hix, hxa, ha0])
    omega
  have hdisj : ∀ x ∈ T₁, x ∉ T₂ := by
    intro x hx hx'
    obtain ⟨i, hi1, hik, hi, hix⟩ := hidx₁ x hx
    obtain ⟨j, hj1, hjn, hj, hjx⟩ := hidx₂ x hx'
    have : i = j := hinj i j hi hj (by rw [hix, hjx])
    omega
  have hsT₂ : s ∈ T₂ := by
    have := PathBasics.getLast_mem hT₂.2.2
    rwa [hsk] at this
  refine ⟨a, {x : V | x ∈ T₁}, {x : V | x ∈ T₂}, T₁, T₂, ?_⟩
  refine
    { aStar := haN
      aAdj := haAdj
      subK₁ := fun x hx => hLK x (hmem₁ x hx)
      subK₂ := fun x hx => hLK x (hmem₂ x hx)
      disj := hdisj
      offStar₁ := fun x hx => hp1 x (hmem₁ x hx) (hne₁ x hx)
      offStar₂ := fun x hx => hp1 x (hmem₂ x hx) (hne₂ x hx)
      last₁ := ?_
      last₂ := ?_
      cross := ?_
      path₁ := hT₁.1
      path₂ := hT₂.1
      sub₁ := fun x hx => hx
      sub₂ := fun x hx => hx
      end₁ := by rw [hT₁.2.2, hrk]
      end₂ := by rw [hT₂.2.2, hsk]
      nbr₁ := ?_
      nbr₂ := ?_ }
  · intro x hx hadj
    rcases (hneighbors x (hLK x (hmem₁ x hx))).mp hadj with hxr | hxs
    · exact hxr
    · exact absurd (hxs ▸ hsT₂) (hdisj x hx)
  · intro x hx hadj
    rcases (hneighbors x (hLK x (hmem₂ x hx))).mp hadj with hxr | hxs
    · have hrT₁ : r ∈ T₁ := by
        have := PathBasics.getLast_mem hT₁.2.2
        rwa [hrk] at this
      exact absurd (hxr ▸ hx) (hdisj r hrT₁)
    · exact hxs
  · intro x hx y hy hadj
    obtain ⟨i, hi1, hik, hi, hix⟩ := hidx₁ x hx
    obtain ⟨j, hj1, hjn, hj, hjy⟩ := hidx₂ y hy
    have hadj' : G.Adj (L[i]'hi) (L[j]'hj) := by rw [hix, hjy]; exact hadj
    rcases (hL.2.2 i j hi hj).mp hadj' with hc | hc
    · rw [Nat.mod_eq_of_lt (show i + 1 < L.length by omega)] at hc
      have hik' : i = k := by omega
      have hjk' : j = k + 1 := by omega
      subst hik'
      subst hjk'
      exact ⟨by rw [← hix, hrk], by rw [← hjy, hsk]⟩
    · rcases Nat.lt_or_ge (j + 1) L.length with hjl | hjl
      · rw [Nat.mod_eq_of_lt hjl] at hc; omega
      · have hjn' : j + 1 = L.length := by omega
        rw [hjn', Nat.mod_self] at hc
        omega
  · refine ⟨L[1]'(by omega), PathBasics.head_mem hT₁.2.1, ?_⟩
    have := (hL.2.2 0 1 (by omega) (by omega)).mpr
      (Or.inl (by rw [Nat.mod_eq_of_lt (show 0 + 1 < L.length by omega)]))
    rwa [ha0] at this
  · refine ⟨L[L.length - 1]'(by omega), PathBasics.head_mem hT₂.2.1, ?_⟩
    have := (hL.2.2 0 (L.length - 1) (by omega) (by omega)).mpr
      (Or.inr (by rw [show L.length - 1 + 1 = L.length by omega, Nat.mod_self]))
    rwa [ha0] at this

end Workspace.ProofLemmas.Thm58StarBranchMixed
