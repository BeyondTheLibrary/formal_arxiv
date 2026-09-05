import Workspace.ProofLemmas.TrackSlice
import Workspace.ProofLemmas.Connectivity58Concat
import Workspace.ProofLemmas.NoCrossTrackBranch
import Workspace.ProofLemmas.SubdivisionCompose

/-!
# Two internally disjoint tracks in a graph with no cutvertex

PAPER (proof of 5.8 (6), printed p. 28): *"… and use Menger's theorem to deduce that there are
two vertex-disjoint paths between these two vertices and `{v₁,v₂}`."*

Mathlib has no Menger theorem, so this file proves the case that 5.8 (6) needs: in a graph in
which deleting any single vertex leaves the rest connected, any two vertices are joined by two
tracks meeting only at those two vertices.  The proof is Whitney's induction on the distance
between the two vertices: the base case hangs one more vertex on a track avoiding the first
one, and the inductive step reroutes a track that leaves the cycle already built.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.TwoConnectedDisjointPaths

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.CyclicThreeConnectedAttachments

variable {W : Type*} [DecidableEq W] {Γ : SimpleGraph W}

/-- Deleting any one vertex leaves every pair of the remaining vertices joined. -/
def NoCutvertex (Γ : SimpleGraph W) : Prop :=
  ∀ z p r : W, p ≠ z → r ≠ z → RchIn Γ ({z}ᶜ : Set W) p r

/-- A track between two distinct vertices, avoiding a prescribed third vertex. -/
theorem exists_track_avoiding (h2 : NoCutvertex Γ) {z p r : W}
    (hp : p ≠ z) (hr : r ≠ z) :
    ∃ t : List W, IsTrackFrom Γ t p r ∧ z ∉ t := by
  obtain ⟨wlk, hwlk⟩ := NoCrossTrackBranch.walk_of_rchIn (h2 z p r hp hr)
  obtain ⟨R, hR, hRsupp, -⟩ := NoCrossTrackBranch.exists_track_of_walk wlk
  exact ⟨R, hR, fun hmem => (hwlk z (hRsupp z hmem)) rfl⟩

/-- The elements of a track are its two ends and its internal vertices. -/
private theorem mem_track_cases {t : List W} {a b x : W} (ht : IsTrackFrom Γ t a b)
    (hx : x ∈ t) (hxa : x ≠ a) (hxb : x ≠ b) : x ∈ trackInterior t := by
  by_contra hc
  rcases SubdivisionCompose.mem_ends_of_mem ht.2.1 ht.2.2 hx hc with h | h
  · exact hxa h
  · exact hxb h

/-- **The rerouting step.**  Two tracks from `u` to `w` meeting only at their ends, a neighbour
`v` of `w` off the second track, and a track from `v` to a vertex `z ≠ w` of the first track
which meets the two tracks only at `z` (and at `v`), assemble into two tracks from `u` to `v`
meeting only at their ends. -/
private theorem step {u v w z : W} {P₀ R₀ S : List W}
    (hP₀ : IsTrackFrom Γ P₀ u w) (hR₀ : IsTrackFrom Γ R₀ u w)
    (hdisj₀ : ∀ x ∈ P₀, x ∈ R₀ → x = u ∨ x = w)
    (hwv : Γ.Adj w v) (hvR : v ∉ R₀)
    (hS : IsTrackFrom Γ S v z) (hzP : z ∈ P₀) (hzw : z ≠ w)
    (hmeetP : ∀ x ∈ P₀, x ∈ S → x = z)
    (hmeetR : ∀ x ∈ R₀, x ∈ S → x = z ∨ x = v) :
    ∃ Pp Rr : List W, IsTrackFrom Γ Pp u v ∧ IsTrackFrom Γ Rr u v ∧
      (∀ x ∈ Pp, x ∈ Rr → x = u ∨ x = v) := by
  classical
  have hPne : 0 < P₀.length := List.length_pos_of_ne_nil hP₀.1.1
  have hP0 : P₀[0]'hPne = u := SubdivisionCounting.track_head hP₀ hPne
  have hPl : P₀[P₀.length - 1]'(by omega) = w := by
    have h' := hP₀.2.2
    rw [List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (by omega : P₀.length - 1 < P₀.length)] at h'
    exact Option.some_injective _ h'
  obtain ⟨i, hi, hzi⟩ := List.mem_iff_getElem.mp hzP
  have hilt : i < P₀.length - 1 := by
    rcases Nat.lt_or_ge i (P₀.length - 1) with hh | hh
    · exact hh
    · exact absurd (by rw [← hzi, SubdivisionCounting.getElem_eq_of_index_eq P₀
        (by omega : i = P₀.length - 1) hi (by omega), hPl]) hzw
  -- the first new track: `u` along `P₀` to `z`, then `S` backwards to `v`
  have hT₁ : IsTrackFrom Γ (TrackSlice.slice P₀ 0 i) u z := by
    have := TrackSlice.isTrackFrom_slice hP₀.1 hi (Nat.zero_le i)
    rwa [SubdivisionCounting.getElem_eq_of_index_eq P₀ (rfl : (0:ℕ) = 0) (by omega) hPne,
      hP0, hzi] at this
  have hT₂ : IsTrackFrom Γ S.reverse z v := TrackSlice.isTrackFrom_reverse hS
  have hslice_mem : ∀ x ∈ TrackSlice.slice P₀ 0 i, x ∈ P₀ :=
    fun x hx => TrackSlice.mem_of_mem_slice hx
  have hwslice : w ∉ TrackSlice.slice P₀ 0 i := by
    intro hw
    obtain ⟨k, hk, -, hki, hkw⟩ := (TrackSlice.mem_slice_iff hi (Nat.zero_le i)).mp hw
    have : k = P₀.length - 1 :=
      hP₀.1.2.1.getElem_inj_iff (hi := hk) (hj := (by omega)) |>.mp (by rw [hkw, hPl])
    omega
  have hPp : IsTrackFrom Γ (TrackSlice.slice P₀ 0 i ++ S.reverse.tail) u v := by
    refine Connectivity58Concat.isTrackFrom_append hT₁ hT₂ ?_
    intro x hx hx'
    exact hmeetP x (hslice_mem x hx) (List.mem_reverse.mp hx')
  -- the second new track: `R₀` with `v` hung on its end
  have hRr : IsTrackFrom Γ (R₀ ++ [v]) u v := TrackSlice.isTrackFrom_concat hR₀ hwv hvR
  refine ⟨_, _, hPp, hRr, ?_⟩
  intro x hx hx'
  have hx'' : x ∈ R₀ ∨ x = v := by
    rcases List.mem_append.mp hx' with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by simpa using hh)
  rcases List.mem_append.mp hx with hh | hh
  · -- `x` lies on the initial piece of `P₀`
    rcases hx'' with hxR | rfl
    · rcases hdisj₀ x (hslice_mem x hh) hxR with rfl | rfl
      · exact Or.inl rfl
      · exact absurd hh hwslice
    · exact Or.inr rfl
  · -- `x` lies on `S`, strictly after `z`
    have hxS : x ∈ S := List.mem_reverse.mp (List.mem_of_mem_tail hh)
    have hxz : x ≠ z := by
      intro hxz
      have hSne : 0 < S.reverse.length := by
        have := List.length_pos_of_ne_nil hS.1.1
        simpa using this
      have hz0 : S.reverse[0]'hSne = z := SubdivisionCounting.track_head hT₂ hSne
      obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hh
      rw [List.length_tail] at hk
      rw [List.getElem_tail] at hkx
      have := ((List.nodup_reverse).mpr hS.1.2.1).getElem_inj_iff
        (hi := (by omega : k + 1 < S.reverse.length)) (hj := hSne)
        |>.mp (by rw [hkx, hxz, hz0])
      omega
    rcases hx'' with hxR | rfl
    · rcases hmeetR x hxR hxS with hh2 | hh2
      · exact absurd hh2 hxz
      · exact Or.inr hh2
    · exact Or.inr rfl

/-- **Whitney's induction.**  If every vertex has two distinct neighbours and deleting any one
vertex leaves the rest connected, then any two distinct vertices joined by a track of at most
`nn` vertices are joined by two tracks meeting only at those two vertices. -/
theorem two_tracks (h2 : NoCutvertex Γ) (hdeg : ∀ x y : W, ∃ p : W, Γ.Adj x p ∧ p ≠ y) :
    ∀ (nn : ℕ) (u v : W) (t : List W), IsTrackFrom Γ t u v → t.length ≤ nn → u ≠ v →
      ∃ Pp Rr : List W, IsTrackFrom Γ Pp u v ∧ IsTrackFrom Γ Rr u v ∧
        (∀ x ∈ Pp, x ∈ Rr → x = u ∨ x = v) := by
  classical
  intro nn
  induction nn with
  | zero =>
    intro u v t ht hlen huv
    exact absurd (List.length_pos_of_ne_nil ht.1.1) (by omega)
  | succ nn ih =>
    intro u v t ht hlen huv
    rcases Nat.lt_or_ge t.length (nn + 1) with hlt | hge
    · exact ih u v t ht (by omega) huv
    have htlen : t.length = nn + 1 := by omega
    have htne : 0 < t.length := List.length_pos_of_ne_nil ht.1.1
    have ht0 : t[0]'htne = u := SubdivisionCounting.track_head ht htne
    have htl : t[t.length - 1]'(by omega) = v := by
      have h' := ht.2.2
      rw [List.getLast?_eq_getElem?,
        List.getElem?_eq_getElem (by omega : t.length - 1 < t.length)] at h'
      exact Option.some_injective _ h'
    have h2le : 2 ≤ t.length := by
      by_contra hc
      refine huv ?_
      rw [← ht0, ← htl]
      exact SubdivisionCounting.getElem_eq_of_index_eq t (by omega) _ _
    rcases Nat.eq_or_lt_of_le h2le with heq | hgt
    · -- the two vertices are adjacent: hang `u` on a track from a second neighbour
      have hadj : Γ.Adj u v := by
        have hh := ht.1.2.2 0 (by omega)
        rw [ht0] at hh
        rwa [SubdivisionCounting.getElem_eq_of_index_eq t
          (show (1 : ℕ) = t.length - 1 by omega) (by omega) (by omega), htl] at hh
      obtain ⟨pp, hup, hpv⟩ := hdeg u v
      obtain ⟨S, hS, huS⟩ := exists_track_avoiding h2 (z := u) (p := pp) (r := v)
        hup.ne' huv.symm
      refine ⟨u :: S, [u, v], ?_, ⟨⟨by simp, by simp [huv], ?_⟩, rfl, rfl⟩, ?_⟩
      · have h1 := TrackSlice.isTrackFrom_concat (TrackSlice.isTrackFrom_reverse hS)
          hup.symm (by simpa using huS)
        have h2' := TrackSlice.isTrackFrom_reverse h1
        simpa using h2'
      · intro k hk
        have hk0 : k = 0 := by simp at hk; omega
        subst hk0
        simpa using hadj
      · intro x hx hx'
        simpa using hx'
    · -- the general step
      have hwv : Γ.Adj (t[t.length - 2]'(by omega)) v := by
        have hh := ht.1.2.2 (t.length - 2) (by omega)
        rwa [SubdivisionCounting.getElem_eq_of_index_eq t
          (show t.length - 2 + 1 = t.length - 1 by omega) (by omega) (by omega), htl] at hh
      have hwu : (t[t.length - 2]'(by omega)) ≠ u := by
        intro hh
        have : t.length - 2 = 0 :=
          ht.1.2.1.getElem_inj_iff (hi := (by omega)) (hj := htne) |>.mp (by rw [hh, ht0])
        omega
      have ht' : IsTrackFrom Γ (TrackSlice.slice t 0 (t.length - 2)) u
          (t[t.length - 2]'(by omega)) := by
        have hh := TrackSlice.isTrackFrom_slice ht.1 (by omega : t.length - 2 < t.length)
          (Nat.zero_le _)
        rwa [SubdivisionCounting.getElem_eq_of_index_eq t (rfl : (0:ℕ) = 0) (by omega) htne,
          ht0] at hh
      have hlen' : (TrackSlice.slice t 0 (t.length - 2)).length ≤ nn := by
        rw [TrackSlice.length_slice t (by omega) (Nat.zero_le _)]; omega
      obtain ⟨P₀, R₀, hP₀, hR₀, hd₀⟩ := ih u _ _ ht' hlen' (Ne.symm hwu)
      have hd₀' : ∀ x ∈ R₀, x ∈ P₀ → x = u ∨ x = (t[t.length - 2]'(by omega)) :=
        fun x hx hx' => hd₀ x hx' hx
      have htriv : IsTrackFrom Γ [v] v v := ⟨⟨by simp, by simp, by intro k hk; simp at hk⟩, rfl, rfl⟩
      by_cases hvP : v ∈ P₀
      · have hvR : v ∉ R₀ := by
          intro hh
          rcases hd₀ v hvP hh with h1 | h1
          · exact huv h1.symm
          · exact hwv.ne' h1
        exact step hP₀ hR₀ hd₀ hwv hvR htriv hvP hwv.ne' (by simp) (by simp)
      by_cases hvR : v ∈ R₀
      · exact step hR₀ hP₀ hd₀' hwv hvP htriv hvR hwv.ne' (by simp) (by simp)
      -- `v` is on neither track: reroute along a track from `v` avoiding `w`
      obtain ⟨S, hSt, hwS⟩ := exists_track_avoiding h2
        (z := t[t.length - 2]'(by omega)) (p := v) (r := u) hwv.ne' (Ne.symm hwu)
      have hSne : 0 < S.length := List.length_pos_of_ne_nil hSt.1.1
      have hS0 : S[0]'hSne = v := SubdivisionCounting.track_head hSt hSne
      have hSl : S[S.length - 1]'(by omega) = u := by
        have h' := hSt.2.2
        rw [List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (by omega : S.length - 1 < S.length)] at h'
        exact Option.some_injective _ h'
      have hS2 : 2 ≤ S.length := by
        by_contra hc
        refine huv.symm ?_
        rw [← hS0, ← hSl]
        exact SubdivisionCounting.getElem_eq_of_index_eq S (by omega) _ _
      obtain ⟨S', a', z, hS', ha'A, hzB, hS'2, hS'clean, hS'sub⟩ :=
        TrackSlice.exists_clean_subtrack (A := ({v} : Set W))
          (B := {x : W | x ∈ P₀ ∨ x ∈ R₀}) hSt.1
          (i₀ := 0) (j₀ := S.length - 1) (by omega) (by omega)
          (by
            rw [SubdivisionCounting.getElem_eq_of_index_eq S (rfl : (0:ℕ) = 0) (by omega) hSne,
              hS0]
            rfl)
          (by
            rw [SubdivisionCounting.getElem_eq_of_index_eq S
              (rfl : S.length - 1 = S.length - 1) (by omega) (by omega), hSl]
            refine Or.inl ?_
            have hh := hP₀.2.1
            rw [List.head?_eq_getElem?,
              List.getElem?_eq_getElem (List.length_pos_of_ne_nil hP₀.1.1)] at hh
            exact (Option.some_injective _ hh) ▸ List.getElem_mem _)
      have ha'v : a' = v := ha'A
      subst ha'v
      have hzS' : z ∈ S' := by
        have hh := hS'.2.2
        rw [List.getLast?_eq_getElem?,
          List.getElem?_eq_getElem (by omega : S'.length - 1 < S'.length)] at hh
        exact (Option.some_injective _ hh) ▸ List.getElem_mem _
      have hzw : z ≠ t[t.length - 2]'(by omega) := by
        intro hh
        exact hwS (hh ▸ hS'sub z hzS')
      have hmeet : ∀ x : W, (x ∈ P₀ ∨ x ∈ R₀) → x ∈ S' → x = z := by
        intro x hx hx'
        by_cases hxz : x = z
        · exact hxz
        by_cases hxv : x = a'
        · subst hxv
          rcases hx with hh | hh
          · exact absurd hh hvP
          · exact absurd hh hvR
        exact absurd (show x ∈ {y : W | y ∈ P₀ ∨ y ∈ R₀} from hx)
          (hS'clean x (mem_track_cases hS' hx' hxv hxz)).2
      rcases hzB with hzP | hzR
      · exact step hP₀ hR₀ hd₀ hwv hvR hS' hzP hzw
          (fun x hx hx' => hmeet x (Or.inl hx) hx')
          (fun x hx hx' => Or.inl (hmeet x (Or.inr hx) hx'))
      · exact step hR₀ hP₀ hd₀' hwv hvP hS' hzR hzw
          (fun x hx hx' => hmeet x (Or.inr hx) hx')
          (fun x hx hx' => Or.inl (hmeet x (Or.inl hx) hx'))

/-- **Two internally disjoint tracks.**  A graph in which every vertex has two distinct
neighbours and in which deleting any one vertex leaves the rest connected has, for any two
distinct vertices, two tracks between them meeting only at those two vertices. -/
theorem exists_two_tracks (h2 : NoCutvertex Γ) (hdeg : ∀ x y : W, ∃ p : W, Γ.Adj x p ∧ p ≠ y)
    {u v : W} (huv : u ≠ v) :
    ∃ Pp Rr : List W, IsTrackFrom Γ Pp u v ∧ IsTrackFrom Γ Rr u v ∧
      (∀ x ∈ Pp, x ∈ Rr → x = u ∨ x = v) := by
  obtain ⟨pp, hup, hpv⟩ := hdeg u v
  obtain ⟨t, ht, -⟩ := exists_track_avoiding h2 (z := pp) (p := u) (r := v) hup.ne hpv.symm
  exact two_tracks h2 hdeg t.length u v t ht le_rfl huv

end Workspace.ProofLemmas.TwoConnectedDisjointPaths
