import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction

/-!
# 12.3, the opening reduction: *"We may assume `F` is minimal … so `F` is the vertex set of a path"*

PAPER (printed p. 72, first sentence of the proof of 12.3): *"We may assume `F` is minimal
(possibly exchanging `A` and `B`); so `F` is the vertex set of a path `f₁`-…-`f_k`, where `f₁`
is the unique left-star in `F`, and `f_k` is the only vertex in `F` with a neighbour in
`B ∪ C`.  Since `f₁` is a left-star and `f_k` has a neighbour in `B ∪ C` it follows that
`k ≥ 2`."*

`Cand G A C B F` below is the property of `F` that 12.3 hypothesises — *"`F ⊆ V(G) \ V(S)` is
connected, containing a left-star and with an attachment in `B ∪ C`"* — and the reduction says
that a **minimal** such `F` is the vertex set of a path with the two uniqueness properties.

Since 12.3's conclusion is *"`F` **contains** either a major vertex or a banister"*, i.e. is
monotone in `F`, replacing `F` by a minimal subset with the same property is legitimate; that is
what *"we may assume `F` is minimal"* means.

The minimality itself is retained in the conclusion, because the printed proof appeals to it
again — most importantly in claim (1), where *"from the minimality of `F` (exchanging `A` and
`B`)"* is applied to the mirrored property (connected, containing a **right**-star, with an
attachment in `A ∪ C`).  The exchange is a choice of the orientation of the whole argument:
we minimize over the union of the displayed and mirrored candidate classes, then return the
path package in whichever orientation the chosen set satisfies.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm123Minimal

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas

/-! ### Index bookkeeping for the sub-paths `f₁-…-f_i` and `f_i-…-f_k`

The two uniqueness statements are proved by exhibiting a **shorter** set with 12.3's property,
namely the vertex set of an initial or a final stretch of the path.  `PathBasics` already has
`isPathList_slice`, `length_slice` and `getElem_slice'` for the stretch
`(p.drop i).take (j - i + 1)`; what is missing is the translation between membership in a
stretch and the range of indices it covers. -/

private theorem getElem_eq_of_idx {W : Type*} (p : List W) {i j : ℕ} (hi : i < p.length)
    (hj : j < p.length) (h : i = j) : (p[i]'hi) = (p[j]'hj) := by
  subst h; rfl

private theorem mem_slice {W : Type*} (p : List W) {i j m : ℕ}
    (him : i ≤ m) (hmj : m ≤ j) (hj : j < p.length) (hm : m < p.length) :
    (p[m]'hm) ∈ (p.drop i).take (j - i + 1) := by
  have hlen := PathBasics.length_slice p (show i ≤ j by omega) hj
  have hk : m - i < ((p.drop i).take (j - i + 1)).length := by omega
  have h1 := List.getElem_mem hk
  rwa [PathBasics.getElem_slice' p hk hm (by omega)] at h1

private theorem index_of_mem_slice {W : Type*} (p : List W) {i j : ℕ} (hij : i ≤ j)
    (hj : j < p.length) {x : W} (hx : x ∈ (p.drop i).take (j - i + 1)) :
    ∃ m, i ≤ m ∧ m ≤ j ∧ ∃ hm : m < p.length, (p[m]'hm) = x := by
  obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
  have hlen := PathBasics.length_slice p hij hj
  refine ⟨i + k, by omega, by omega, by omega, ?_⟩
  rw [PathBasics.getElem_slice' p hk (show i + k < p.length by omega) rfl] at hkx
  exact hkx

private theorem slice_subset {W : Type*} (p : List W) {i j : ℕ} {x : W}
    (hx : x ∈ (p.drop i).take (j - i + 1)) : x ∈ p :=
  (List.drop_sublist i p).subset ((List.take_sublist _ _).subset hx)

/-- The hypothesis 12.3 puts on `F`: *"`F ⊆ V(G) \ V(S)` … connected, containing a left-star
and with an attachment in `B ∪ C`"*.  (`V(S) = A ∪ B ∪ C`.) -/
def Cand {V : Type*} (G : SimpleGraph V) (A C B F : Set V) : Prop :=
  F ⊆ (A ∪ B ∪ C)ᶜ ∧ SPGT.ConnectedSet G F ∧
    (∃ u ∈ F, IsLeftStar G A C B u) ∧ (attachments G F (B ∪ C)).Nonempty

private theorem minimalPathPackage {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (F' : Set V) (hCand' : Cand G A C B F')
    (hmin : ∀ F'' ⊆ F', Cand G A C B F'' → F'' = F') :
    ∃ (f : List V) (f₁ fk : V),
      F' = {w : V | w ∈ f} ∧
      SPGT.IsPathFrom G f f₁ fk ∧ 2 ≤ f.length ∧
      IsLeftStar G A C B f₁ ∧
      (∀ w ∈ f, IsLeftStar G A C B w → w = f₁) ∧
      (∃ y ∈ B ∪ C, G.Adj fk y) ∧
      (∀ w ∈ f, (∃ y ∈ B ∪ C, G.Adj w y) → w = fk) := by
  classical
  obtain ⟨hFc1, hFc2, ⟨u, huF, hu⟩, hatt0⟩ := id hCand'
  obtain ⟨y, hyBC, w, hwF, hyw⟩ := hatt0
  -- *"so `F` is the vertex set of a path `f₁`-…-`f_k`"*: an induced path of `F'` from the
  -- left-star `u` to the vertex `w` carrying the attachment in `B ∪ C`.
  obtain ⟨p, hp, hpF⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hFc2 huF hwF
  have hpos : 0 < p.length := PathBasics.path_length_pos hp.1
  have hp0 : p[0]'hpos = u := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hplast : p[p.length - 1]'(by omega) = w :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  have hup : u ∈ p := List.mem_of_mem_head? (by rw [hp.2.1]; rfl)
  have hwp : w ∈ p := List.mem_of_mem_getLast? (by rw [hp.2.2]; rfl)
  have hPsub : {z : V | z ∈ p} ⊆ F' := fun z hz => hpF z hz
  have hPeq : {z : V | z ∈ p} = F' :=
    hmin _ hPsub
      ⟨hPsub.trans hFc1,
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.1,
        ⟨u, hup, hu⟩, ⟨y, hyBC, w, hwp, hyw⟩⟩
  -- *"Since `f₁` is a left-star and `f_k` has a neighbour in `B ∪ C` it follows that `k ≥ 2`."*
  have huw : u ≠ w := fun h => hu.2.2 y hyBC (by rw [h]; exact hyw.symm)
  have h2len : 2 ≤ p.length := by
    by_contra hc
    obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp (show p.length = 1 by omega)
    have h1' : p.head? = some a := by rw [ha]; rfl
    have h2' : p.getLast? = some a := by rw [ha]; rfl
    rw [hp.2.1] at h1'; rw [hp.2.2] at h2'
    exact huw ((Option.some_injective _ h1').trans (Option.some_injective _ h2').symm)
  -- *"`f₁` is the unique left-star in `F`"*.
  have hstaruniq : ∀ z ∈ p, IsLeftStar G A C B z → z = u := by
    intro z hz hzstar
    by_contra hzu
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hz
    have hzw : z ≠ w := fun h => hzstar.2.2 y hyBC (by rw [h]; exact hyw.symm)
    have hi0 : 1 ≤ i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exfalso
        apply hzu
        have hzz : z = p[0]'hpos := by rw [← hpi]; exact getElem_eq_of_idx p hi hpos h
        rw [hzz]; exact hp0
      · omega
    have hij : i < p.length - 1 := by
      rcases Nat.lt_or_ge i (p.length - 1) with h | h
      · exact h
      · exfalso
        apply hzw
        have hzz : z = p[p.length - 1]'(show p.length - 1 < p.length by omega) := by
          rw [← hpi]
          exact getElem_eq_of_idx p hi (show p.length - 1 < p.length by omega) (by omega)
        rw [hzz]; exact hplast
    -- the final stretch `f_i-…-f_k`, a strictly smaller set with the same property
    have hslice : SPGT.IsPathList G ((p.drop i).take (p.length - 1 - i + 1)) :=
      PathBasics.isPathList_slice hp.1 hij (by omega)
    have hssub : {t : V | t ∈ (p.drop i).take (p.length - 1 - i + 1)} ⊆ F' :=
      fun t ht => hpF t (slice_subset p ht)
    have hzs : z ∈ (p.drop i).take (p.length - 1 - i + 1) := by
      have := mem_slice p (le_refl i) (show i ≤ p.length - 1 by omega)
        (show p.length - 1 < p.length by omega) hi
      rwa [hpi] at this
    have hws : w ∈ (p.drop i).take (p.length - 1 - i + 1) := by
      have := mem_slice p (show i ≤ p.length - 1 by omega) (le_refl (p.length - 1))
        (show p.length - 1 < p.length by omega) (show p.length - 1 < p.length by omega)
      rwa [hplast] at this
    have hus : u ∉ (p.drop i).take (p.length - 1 - i + 1) := by
      intro hus
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ :=
        index_of_mem_slice p (show i ≤ p.length - 1 by omega)
          (show p.length - 1 < p.length by omega) hus
      have : (0 : ℕ) = m :=
        (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hp.1)).mp (by rw [hp0, hm4])
      omega
    have heq := hmin _ hssub
      ⟨hssub.trans hFc1,
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hslice,
        ⟨z, hzs, hzstar⟩, ⟨y, hyBC, w, hws, hyw⟩⟩
    have huin : u ∈ {t : V | t ∈ (p.drop i).take (p.length - 1 - i + 1)} := by
      rw [heq]; exact huF
    exact hus huin
  -- *"`f_k` is the only vertex in `F` with a neighbour in `B ∪ C`"*.
  have hattuniq : ∀ z ∈ p, (∃ x ∈ B ∪ C, G.Adj z x) → z = w := by
    rintro z hz ⟨x, hxBC, hzx⟩
    by_contra hzw
    obtain ⟨i, hi, hpi⟩ := List.mem_iff_getElem.mp hz
    have hzu : z ≠ u := fun h => hu.2.2 x hxBC (by rw [← h]; exact hzx)
    have hi0 : 0 < i := by
      rcases Nat.eq_zero_or_pos i with h | h
      · exfalso
        apply hzu
        have hzz : z = p[0]'hpos := by rw [← hpi]; exact getElem_eq_of_idx p hi hpos h
        rw [hzz]; exact hp0
      · exact h
    have hij : i < p.length - 1 := by
      rcases Nat.lt_or_ge i (p.length - 1) with h | h
      · exact h
      · exfalso
        apply hzw
        have hzz : z = p[p.length - 1]'(show p.length - 1 < p.length by omega) := by
          rw [← hpi]
          exact getElem_eq_of_idx p hi (show p.length - 1 < p.length by omega) (by omega)
        rw [hzz]; exact hplast
    -- the initial stretch `f₁-…-f_i`
    have hslice : SPGT.IsPathList G ((p.drop 0).take (i - 0 + 1)) :=
      PathBasics.isPathList_slice hp.1 hi0 hi
    have hssub : {t : V | t ∈ (p.drop 0).take (i - 0 + 1)} ⊆ F' :=
      fun t ht => hpF t (slice_subset p ht)
    have hus : u ∈ (p.drop 0).take (i - 0 + 1) := by
      have := mem_slice p (le_refl 0) (Nat.zero_le i) hi hpos
      rwa [hp0] at this
    have hzs : z ∈ (p.drop 0).take (i - 0 + 1) := by
      have := mem_slice p (Nat.zero_le i) (le_refl i) hi hi
      rwa [hpi] at this
    have hws : w ∉ (p.drop 0).take (i - 0 + 1) := by
      intro hws
      obtain ⟨m, hm1, hm2, hm3, hm4⟩ := index_of_mem_slice p (Nat.zero_le i) hi hws
      have : p.length - 1 = m :=
        (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hp.1)).mp (by rw [hplast, hm4])
      omega
    have heq := hmin _ hssub
      ⟨hssub.trans hFc1,
        InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hslice,
        ⟨u, hus, hu⟩, ⟨x, hxBC, z, hzs, hzx.symm⟩⟩
    have hwin : w ∈ {t : V | t ∈ (p.drop 0).take (i - 0 + 1)} := by
      rw [heq]; exact hwF
    exact hws hwin
  exact ⟨p, u, w, hPeq.symm, hp, h2len, hu, hstaruniq, ⟨y, hyBC, hyw.symm⟩, hattuniq⟩

/-- **12.3, opening reduction.**  *"We may assume `F` is minimal (possibly exchanging `A` and
`B`) …; so `F` is the vertex set of a path `f₁`-…-`f_k`."*  We choose a least-cardinality
subset satisfying the candidate property in either orientation.  The last disjunction records
the one selected orientation and its complete path package; the preceding quantified clause is
minimality in the union of the two candidate classes. -/
theorem thm123Minimal {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (F : Set V) (hF : Cand G A C B F) :
    ∃ (F' : Set V) (f : List V) (f₁ fk : V),
      F' ⊆ F ∧
      (∀ F'' ⊆ F', (Cand G A C B F'' ∨ Cand G B C A F'') → F'' = F') ∧
      F' = {w : V | w ∈ f} ∧
      SPGT.IsPathFrom G f f₁ fk ∧ 2 ≤ f.length ∧
      ((Cand G A C B F' ∧
          IsLeftStar G A C B f₁ ∧
          (∀ w ∈ f, IsLeftStar G A C B w → w = f₁) ∧
          (∃ y ∈ B ∪ C, G.Adj fk y) ∧
          (∀ w ∈ f, (∃ y ∈ B ∪ C, G.Adj w y) → w = fk)) ∨
        (Cand G B C A F' ∧
          IsLeftStar G B C A f₁ ∧
          (∀ w ∈ f, IsLeftStar G B C A w → w = f₁) ∧
          (∃ y ∈ A ∪ C, G.Adj fk y) ∧
          (∀ w ∈ f, (∃ y ∈ A ∪ C, G.Adj w y) → w = fk))) := by
  classical
  obtain ⟨F', ⟨hsub, horient⟩, hF'min⟩ :=
    Set.exists_min_image
      {X : Set V | X ⊆ F ∧ (Cand G A C B X ∨ Cand G B C A X)}
      Set.ncard (Set.toFinite _) ⟨F, Set.Subset.rfl, Or.inl hF⟩
  have hmin : ∀ F'' ⊆ F', (Cand G A C B F'' ∨ Cand G B C A F'') → F'' = F' :=
    fun F'' h2 h3 =>
      Set.eq_of_subset_of_ncard_le h2 (hF'min F'' ⟨h2.trans hsub, h3⟩) (Set.toFinite _)
  rcases horient with hCand' | hCand'
  · obtain ⟨f, f₁, fk, hFf, hpath, hlen, hstar, hstaruniq, hatt, hattuniq⟩ :=
      minimalPathPackage G A C B F' hCand' (fun F'' h2 h3 => hmin F'' h2 (Or.inl h3))
    exact ⟨F', f, f₁, fk, hsub, hmin, hFf, hpath, hlen,
      Or.inl ⟨hCand', hstar, hstaruniq, hatt, hattuniq⟩⟩
  · obtain ⟨f, f₁, fk, hFf, hpath, hlen, hstar, hstaruniq, hatt, hattuniq⟩ :=
      minimalPathPackage G B C A F' hCand' (fun F'' h2 h3 => hmin F'' h2 (Or.inr h3))
    exact ⟨F', f, f₁, fk, hsub, hmin, hFf, hpath, hlen,
      Or.inr ⟨hCand', hstar, hstaruniq, hatt, hattuniq⟩⟩

end Workspace.ProofLemmas.Thm123Minimal
