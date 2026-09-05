import Mathlib
import Workspace.Types.Core
import Workspace.ProofLemmas.PathBasics

/-!
# The case-1 replacement path of 5.8.2

PAPER (proof of 7.5, claim (2), printed p. 37): *"In case 1, let `R′` be the (unique) path from
`p₁` to `s₂` in `(V(P) ∪ V(Rb₁b₂)) \ {s₁}`."*

In case 1 of 5.8 (2) the path `P` attaches to the old appearance only at `Nb₁ \ {r₁}`, through
its first vertex `p₁`, and at the old rung, through its last vertex `p₂`.  The replacement path
is built by walking along `P` and then jumping onto the old rung at the **last** rung vertex
that `p₂` sees, and following the rung to its far end `r₂`.  Choosing the last such vertex is
what makes the result induced: any earlier jump would leave a chord from `p₂` to a later rung
vertex.

This module proves that construction, and packages the two facts the rung-replacement interface
`RungReplacementLabelled.rungReplacement` asks for: the spliced path meets the old appearance
only inside the old rung, and its attachments to the retained part of the appearance are exactly
`p₁` to `Nb₁ \ {r₁}` and `r₂` to `Nb₂ \ {r₂}`.

Everything here is stated for abstract sets `N₁, N₂` and an abstract rung `Q`; the only input
about the appearance is the rung boundary dictionary `hbdry`, proved in
`Thm75Claim2Five82RungBoundary`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm75Claim2Five82Splice

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.ProofLemmas.PathBasics

variable {V : Type*} {G : SimpleGraph V}

/-- Reading a list at two equal indices gives the same entry. -/
theorem idxeq (l : List V) (i j : ℕ) (hi : i < l.length) (hj : j < l.length) (h : i = j) :
    l[i]'hi = l[j]'hj := by subst h; rfl

/-- **Two induced paths joined at a single edge form an induced path.**

`A` ends at `a`, `B` starts at `b`, the two are vertex-disjoint, and the only edge of `G`
between them is `ab`.  Then `A ++ B` is again an induced path. -/
theorem isPathList_append {A B : List V} {a b : V}
    (hA : IsPathList G A) (hB : IsPathList G B)
    (hdisj : ∀ x ∈ A, x ∉ B)
    (ha : A.getLast? = some a) (hb : B.head? = some b)
    (hcross : ∀ x ∈ A, ∀ y ∈ B, (G.Adj x y ↔ (x = a ∧ y = b))) :
    IsPathList G (A ++ B) := by
  have hAne : A ≠ [] := hA.1
  have hBne : B ≠ [] := hB.1
  have hApos : 0 < A.length := List.length_pos_iff.mpr hAne
  have hBpos : 0 < B.length := List.length_pos_iff.mpr hBne
  have haA : A[A.length - 1]'(by omega) = a := getElem_last_of_getLast? ha hApos
  have hbB : B[0]'hBpos = b := getElem_zero_of_head? hb hBpos
  have hlen : (A ++ B).length = A.length + B.length := by simp
  refine ⟨by simp [hAne], ?_, ?_⟩
  · rw [List.nodup_append]
    exact ⟨hA.2.1, hB.2.1, by intro x hx y hy hxy; exact hdisj x hx (hxy ▸ hy)⟩
  · intro i j hi hj
    rw [hlen] at hi hj
    by_cases hiA : i < A.length
    · by_cases hjA : j < A.length
      · rw [List.getElem_append_left hiA, List.getElem_append_left hjA]
        exact hA.2.2 i j hiA hjA
      · push Not at hjA
        rw [List.getElem_append_left hiA, List.getElem_append_right hjA]
        rw [hcross _ (List.getElem_mem hiA) _ (List.getElem_mem (by omega))]
        constructor
        · rintro ⟨h1, h2⟩
          left
          have hi' : i = A.length - 1 := by
            have := hA.2.1.getElem_inj_iff (hi := hiA) (hj := show A.length - 1 < A.length by omega)
            exact this.mp (by rw [h1, haA])
          have hj' : j - A.length = 0 := by
            have := hB.2.1.getElem_inj_iff (hi := show j - A.length < B.length by omega)
              (hj := hBpos)
            exact this.mp (by rw [h2, hbB])
          omega
        · rintro (h | h)
          · have hj' : j = A.length := by omega
            constructor
            · rw [← haA]; congr 1; omega
            · rw [← hbB]; congr 1; omega
          · omega
    · push Not at hiA
      by_cases hjA : j < A.length
      · rw [List.getElem_append_right hiA, List.getElem_append_left hjA]
        rw [SimpleGraph.adj_comm]
        rw [hcross _ (List.getElem_mem hjA) _ (List.getElem_mem (by omega))]
        constructor
        · rintro ⟨h1, h2⟩
          right
          have hj' : j = A.length - 1 := by
            have := hA.2.1.getElem_inj_iff (hi := hjA) (hj := show A.length - 1 < A.length by omega)
            exact this.mp (by rw [h1, haA])
          have hi' : i - A.length = 0 := by
            have := hB.2.1.getElem_inj_iff (hi := show i - A.length < B.length by omega)
              (hj := hBpos)
            exact this.mp (by rw [h2, hbB])
          omega
        · rintro (h | h)
          · omega
          · have hi' : i = A.length := by omega
            constructor
            · rw [← haA]; congr 1; omega
            · rw [← hbB]; congr 1; omega
      · push Not at hjA
        rw [List.getElem_append_right hiA, List.getElem_append_right hjA]
        rw [hB.2.2 (i - A.length) (j - A.length) (by omega) (by omega)]
        omega

/-- **The case-1 splice.**

`Q` is the old rung, running from `r₁` to `r₂`, `P` is the connected set's path, running from
`p₁` to `p₂`, and the case-1 attachment pattern holds.  The conclusion is the replacement path
of the printed sentence, together with the two properties the rung-replacement interface needs:
it meets the old appearance only inside the old rung, and its attachments to the rest of the
appearance are exactly `p₁` to `N₁ \ {r₁}` and `r₂` to `N₂ \ {r₂}`. -/
theorem case_one_splice (K N₁ N₂ : Set V)
    (Q : List V) (r₁ r₂ : V) (hQ : IsPathFrom G Q r₁ r₂) (hQK : ∀ x ∈ Q, x ∈ K)
    (hr₁Q : N₁ ∩ {x : V | x ∈ Q} = {r₁})
    (hbdry : ∀ x ∈ Q, ∀ y ∈ K, y ∉ Q →
      (G.Adj x y ↔ (x = r₁ ∧ y ∈ N₁) ∨ (x = r₂ ∧ y ∈ N₂)))
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom G P p₁ p₂) (hPK : ∀ x ∈ P, x ∉ K)
    (hc1 : ∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x)
    (hc2 : ∃ x ∈ {y : V | y ∈ Q} \ {r₁}, G.Adj p₂ x)
    (hc3 : ∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ Q} \ {r₁})) :
    ∃ R' : List V, IsPathFrom G R' p₁ r₂ ∧ (∀ x ∈ R', x ∈ K → x ∈ Q) ∧
      p₁ ∈ R' ∧ r₂ ∈ R' ∧
      (∀ x ∈ R', ∀ y ∈ K, y ∉ Q →
        (G.Adj x y ↔ (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = r₂ ∧ y ∈ N₂ \ {r₂}))) := by
  classical
  have hQpos : 0 < Q.length := List.length_pos_iff.mpr hQ.1.1
  have hQ0 : Q[0]'hQpos = r₁ := getElem_zero_of_head? hQ.2.1 hQpos
  have hQlast : Q[Q.length - 1]'(by omega) = r₂ := getElem_last_of_getLast? hQ.2.2 (by omega)
  -- the index of a rung vertex, and the *last* one that `p₂` sees
  set Pred : ℕ → Prop := fun i => ∃ h : i < Q.length, G.Adj p₂ (Q[i]'h) with hPred
  obtain ⟨x₀, hx₀Q, hx₀adj⟩ := hc2
  obtain ⟨j₀, hj₀, hj₀x⟩ := List.mem_iff_getElem.mp hx₀Q.1
  have hj₀pos : 0 < j₀ := by
    rcases Nat.eq_zero_or_pos j₀ with rfl | h
    · exact absurd (hj₀x.symm.trans hQ0) hx₀Q.2
    · exact h
  have hPj₀ : Pred j₀ := ⟨hj₀, by rw [hj₀x]; exact hx₀adj⟩
  set k : ℕ := Nat.findGreatest Pred (Q.length - 1) with hk
  have hkP : Pred k := Nat.findGreatest_spec (m := j₀) (by omega) hPj₀
  have hkle : k ≤ Q.length - 1 := Nat.findGreatest_le _
  have hkpos : 0 < k := lt_of_lt_of_le hj₀pos (Nat.le_findGreatest (by omega) hPj₀)
  have hklt : k < Q.length := by omega
  have hkadj : G.Adj p₂ (Q[k]'hklt) := by
    obtain ⟨h, hadj⟩ := hkP
    exact hadj
  have hkmax : ∀ i : ℕ, k < i → ∀ h : i < Q.length, ¬ G.Adj p₂ (Q[i]'h) := by
    intro i hi h hadj
    exact Nat.findGreatest_is_greatest hi (by omega) ⟨h, hadj⟩
  -- the tail of the rung starting at that vertex
  have hBpath : IsPathList G (Q.drop k) := isPathList_drop hQ.1 hklt
  have hBhead : (Q.drop k).head? = some (Q[k]'hklt) := by
    rw [List.drop_eq_getElem_cons hklt]; rfl
  have hBsub : ∀ x ∈ Q.drop k, x ∈ Q := fun x hx => (List.drop_subset _ _) hx
  have hBmem : ∀ (i : ℕ) (h : i < Q.length), k ≤ i → (Q[i]'h) ∈ Q.drop k := by
    intro i h hki
    have : (Q.drop k)[i - k]'(by simp; omega) = Q[i]'h := by
      rw [List.getElem_drop]
      congr 1
      omega
    exact this ▸ List.getElem_mem _
  have hBidx : ∀ x ∈ Q.drop k, ∃ (i : ℕ) (h : i < Q.length), k ≤ i ∧ x = Q[i]'h := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    simp only [List.length_drop] at hi
    refine ⟨k + i, by omega, by omega, ?_⟩
    rw [← hix, List.getElem_drop]
  have hnotr₁ : r₁ ∉ Q.drop k := by
    intro hcon
    obtain ⟨i, hi, hki, hix⟩ := hBidx r₁ hcon
    have : (0 : ℕ) = i := hQ.1.2.1.getElem_inj_iff.mp (hQ0.trans hix)
    omega
  -- the two pieces are disjoint, because `P` avoids `K` and the rung lies inside `K`
  have hdisjAB : ∀ x ∈ P, x ∉ Q.drop k := fun x hx hcon => hPK x hx (hQK x (hBsub x hcon))
  -- the only edge between them is `p₂ Q[k]`
  have hcross : ∀ x ∈ P, ∀ y ∈ Q.drop k, (G.Adj x y ↔ (x = p₂ ∧ y = Q[k]'hklt)) := by
    intro x hx y hy
    constructor
    · intro hadj
      obtain ⟨i, hi, hki, rfl⟩ := hBidx y hy
      have hyner₁ : (Q[i]'hi) ≠ r₁ := by
        intro hcon
        have : i = 0 := hQ.1.2.1.getElem_inj_iff.mp (hcon.trans hQ0.symm)
        omega
      rcases hc3 x hx _ (hQK _ (List.getElem_mem hi)) hyner₁ hadj with ⟨hxp, hyN⟩ | ⟨hxp, -⟩
      · exact absurd (show (Q[i]'hi) = r₁ from by
          have : (Q[i]'hi) ∈ N₁ ∩ {z : V | z ∈ Q} := ⟨hyN.1, List.getElem_mem hi⟩
          rw [hr₁Q] at this; exact this) hyner₁
      · subst hxp
        have hik : i ≤ k := by
          by_contra hcon
          exact hkmax i (by omega) hi hadj
        have : i = k := by omega
        subst this
        exact ⟨rfl, rfl⟩
    · rintro ⟨rfl, rfl⟩
      exact hkadj
  -- the spliced path
  refine ⟨P ++ Q.drop k, ⟨isPathList_append hP.1 hBpath hdisjAB hP.2.2 hBhead hcross, ?_, ?_⟩,
    ?_, ?_, ?_, ?_⟩
  · obtain ⟨u, tl, hPcons⟩ : ∃ u tl, P = u :: tl := by
      cases P with
      | nil => exact absurd rfl hP.1.1
      | cons u tl => exact ⟨u, tl, rfl⟩
    have hhd : P.head? = some p₁ := hP.2.1
    rw [hPcons] at hhd ⊢
    simpa using hhd
  · have hdropne : Q.drop k ≠ [] := by
      rw [List.drop_eq_getElem_cons hklt]; exact List.cons_ne_nil _ _
    have hdlen : (Q.drop k).length = Q.length - k := by simp
    rw [List.getLast?_append_of_ne_nil P hdropne, List.getLast?_eq_getElem?,
      List.getElem?_eq_getElem (show (Q.drop k).length - 1 < (Q.drop k).length by omega)]
    have hval : (Q.drop k)[(Q.drop k).length - 1]'(by omega) = r₂ := by
      rw [List.getElem_drop, idxeq Q (k + ((Q.drop k).length - 1)) (Q.length - 1)
        (by omega) (by omega) (by omega)]
      exact hQlast
    rw [hval]
  · intro x hx hxK
    rcases List.mem_append.mp hx with h | h
    · exact absurd hxK (hPK x h)
    · exact hBsub x h
  · exact List.mem_append.mpr (Or.inl (head_mem hP.2.1))
  · refine List.mem_append.mpr (Or.inr ?_)
    have := hBmem (Q.length - 1) (by omega) (by omega)
    rwa [hQlast] at this
  · intro x hx y hyK hyQ
    have hyner₁ : y ≠ r₁ := fun hc => hyQ (hc ▸ head_mem hQ.2.1)
    have hyner₂ : y ≠ r₂ := fun hc => hyQ (hc ▸ getLast_mem hQ.2.2)
    rcases List.mem_append.mp hx with h | h
    · have hxK : x ∉ K := hPK x h
      constructor
      · intro hadj
        rcases hc3 x h y hyK hyner₁ hadj with hcase | hcase
        · exact Or.inl hcase
        · exact absurd hcase.2.1 hyQ
      · rintro (⟨hc, hy⟩ | ⟨hc, -⟩)
        · rw [hc]; exact hc1 y hy
        · exact absurd (hQK r₂ (getLast_mem hQ.2.2)) (hc ▸ hxK)
    · have hxQ : x ∈ Q := hBsub x h
      have hxner₁ : x ≠ r₁ := fun hc => hnotr₁ (hc ▸ h)
      have hxK : x ∈ K := hQK x hxQ
      rw [hbdry x hxQ y hyK hyQ]
      constructor
      · rintro (⟨hc, -⟩ | ⟨hc, hy⟩)
        · exact absurd hc hxner₁
        · exact Or.inr ⟨hc, hy, hyner₂⟩
      · rintro (⟨hc, -⟩ | ⟨hc, hy⟩)
        · exact absurd (hc ▸ hxK) (hPK p₁ (head_mem hP.2.1))
        · exact Or.inr ⟨hc, hy.1⟩

/-! ### The replacement input in the three cases where `R'` is `P` -/

/-- **Case 2 of 5.8.2**: `P` itself is the replacement path.  The two exceptional edges `p₁r₁`
and `p₂r₂` allowed by the case hypothesis disappear once the boundary condition is imposed only
against the retained part `K \ V(Q)` of the appearance. -/
theorem input_case_two (K N₁ N₂ : Set V) (Q : List V) (r₁ r₂ : V)
    (hQ : IsPathFrom G Q r₁ r₂)
    (P : List V) (p₁ p₂ : V) (hPK : ∀ x ∈ P, x ∉ K)
    (h1 : ∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x) (h2 : ∀ x ∈ N₂ \ {r₂}, G.Adj p₂ x)
    (h3 : ∀ x ∈ P, ∀ y ∈ K, G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂}) ∨
      (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) :
    (∀ x ∈ P, x ∈ K → x ∈ Q) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ∉ Q →
        (G.Adj x y ↔ (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂}))) := by
  have hr₁Q : r₁ ∈ Q := head_mem hQ.2.1
  have hr₂Q : r₂ ∈ Q := getLast_mem hQ.2.2
  refine ⟨fun x hx hxK => absurd hxK (hPK x hx), ?_⟩
  intro x hx y hyK hyQ
  constructor
  · intro hadj
    rcases h3 x hx y hyK hadj with h | h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h.2 ▸ hr₁Q) hyQ
    · exact absurd (h.2 ▸ hr₂Q) hyQ
  · rintro (⟨hc, hy⟩ | ⟨hc, hy⟩)
    · rw [hc]; exact h1 y hy
    · rw [hc]; exact h2 y hy

/-- **Case 3 of 5.8.2**: the path `P` is a single vertex, complete to both clique remainders. -/
theorem input_case_three (K N₁ N₂ : Set V) (Q : List V) (r₁ r₂ : V)
    (hQ : IsPathFrom G Q r₁ r₂)
    (P : List V) (p₁ : V) (hP : IsPathFrom G P p₁ p₁) (hPK : ∀ x ∈ P, x ∉ K)
    (h1 : ∀ x ∈ (N₁ ∪ N₂) \ {r₁, r₂}, G.Adj p₁ x)
    (h2 : ∀ y ∈ K, G.Adj p₁ y → y ∈ N₁ ∪ N₂ ∪ {z : V | z ∈ Q}) :
    P = [p₁] ∧ (∀ x ∈ P, x ∈ K → x ∈ Q) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ∉ Q →
        (G.Adj x y ↔ (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₁ ∧ y ∈ N₂ \ {r₂}))) := by
  have hr₁Q : r₁ ∈ Q := head_mem hQ.2.1
  have hr₂Q : r₂ ∈ Q := getLast_mem hQ.2.2
  have hlen : pathLength P = 0 := by
    by_contra hcon
    exact isPathFrom_ends_ne hP (by omega) rfl
  have hP1 : P.length = 1 := by
    have := length_eq_pathLength_add_one hP.1
    omega
  obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hP1
  have hup : u = p₁ := by
    have := hP.2.1
    rw [hu] at this
    simpa using this
  have hPeq : P = [p₁] := by rw [hu, hup]
  refine ⟨hPeq, fun x hx hxK => absurd hxK (hPK x hx), ?_⟩
  intro x hx y hyK hyQ
  have hxp : x = p₁ := by rw [hPeq] at hx; simpa using hx
  subst hxp
  have hyner₁ : y ≠ r₁ := fun hc => hyQ (hc ▸ hr₁Q)
  have hyner₂ : y ≠ r₂ := fun hc => hyQ (hc ▸ hr₂Q)
  constructor
  · intro hadj
    rcases h2 y hyK hadj with (hy | hy) | hy
    · exact Or.inl ⟨rfl, hy, hyner₁⟩
    · exact Or.inr ⟨rfl, hy, hyner₂⟩
    · exact absurd hy hyQ
  · rintro (⟨-, hy⟩ | ⟨-, hy⟩)
    · exact h1 y ⟨Or.inl hy.1, by rintro (hc | hc); exacts [hyner₁ hc, hyner₂ hc]⟩
    · exact h1 y ⟨Or.inr hy.1, by rintro (hc | hc); exacts [hyner₁ hc, hyner₂ hc]⟩

/-- **Case 4 of 5.8.2**: the two ends of the old rung coincide, so the old rung is a single
vertex and has even length. -/
theorem input_case_four (K N₁ N₂ : Set V) (Q : List V) (r₁ r₂ : V)
    (hQ : IsPathFrom G Q r₁ r₂) (hr : r₁ = r₂)
    (P : List V) (p₁ p₂ : V) (hPK : ∀ x ∈ P, x ∉ K)
    (h1 : ∀ x ∈ N₁ \ {r₁}, G.Adj p₁ x) (h2 : ∀ x ∈ N₂ \ {r₂}, G.Adj p₂ x)
    (h3 : ∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → G.Adj x y →
      (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂})) :
    Even (pathLength Q) ∧ (∀ x ∈ P, x ∈ K → x ∈ Q) ∧
      (∀ x ∈ P, ∀ y ∈ K, y ∉ Q →
        (G.Adj x y ↔ (x = p₁ ∧ y ∈ N₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N₂ \ {r₂}))) := by
  have hr₁Q : r₁ ∈ Q := head_mem hQ.2.1
  have hQlen : pathLength Q = 0 := by
    by_contra hcon
    exact isPathFrom_ends_ne hQ (by omega) hr
  refine ⟨by rw [hQlen]; exact Even.zero, fun x hx hxK => absurd hxK (hPK x hx), ?_⟩
  intro x hx y hyK hyQ
  have hyner₁ : y ≠ r₁ := fun hc => hyQ (hc ▸ hr₁Q)
  constructor
  · exact fun hadj => h3 x hx y hyK hyner₁ hadj
  · rintro (⟨hc, hy⟩ | ⟨hc, hy⟩)
    · rw [hc]; exact h1 y hy
    · rw [hc]; exact h2 y hy

end Workspace.ProofLemmas.Thm75Claim2Five82Splice
