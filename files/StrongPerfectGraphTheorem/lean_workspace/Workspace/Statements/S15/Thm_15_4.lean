/-  Proof attempt for statement 15.4 of Chudnovsky-Robertson-Seymour-Thomas,
    *The Strong Perfect Graph Theorem*.

    PRINTED PROOF (perfect.pdf, printed p. 94):

      "If `n` is even then `p_s-q_1-...-q_n-p_{s+1}` is an odd antipath, and `p_1, p_m`
       are complete to its interior; and hence `p_1, p_m` are both adjacent to one of
       `p_s, p_{s+1}`.  So `s = 2` and `m = s + 2`, and therefore `m = 4`.  Now assume
       `n` is odd; then `p_s-q_1-...-q_n-p_{s+1}` is an even antipath of length >= 4,
       contrary to 13.7 applied in `Gbar` to this antipath and the sets
       `{p_1,...,p_{s-1}}`, `{p_{s+2},...,p_n}`."                                     -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.ClassLemmas
import Workspace.Statements.S13.Thm_13_7

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace Workspace.Statements.S15

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A cyclically-free block of consecutive vertices of a path is a connected set. -/
private theorem block_connected {G : SimpleGraph V} {P : List V}
    (hP : IsPathList G P) (a b : ℕ) (S : Set V)
    (hSmem : ∀ w : V, w ∈ S ↔ ∃ k : ℕ, ∃ h : k < P.length, a ≤ k ∧ k ≤ b ∧ w = P[k]'h) :
    ConnectedSet G S := by
  have hmem : ∀ (k : ℕ) (hk : k < P.length), a ≤ k → k ≤ b → (P[k]'hk) ∈ S :=
    fun k hk h1 h2 => (hSmem _).mpr ⟨k, hk, h1, h2, rfl⟩
  have step : ∀ (d i : ℕ) (hi : i < P.length) (hid : i + d < P.length)
      (h1 : a ≤ i) (h2 : i + d ≤ b),
      (G.induce S).Reachable ⟨P[i]'hi, hmem i hi h1 (by omega)⟩
        ⟨P[i + d]'hid, hmem (i + d) hid (by omega) h2⟩ := by
    intro d
    induction d with
    | zero =>
        intro i hi hid h1 h2
        exact SimpleGraph.Reachable.refl _
    | succ d ih =>
        intro i hi hid h1 h2
        have hid' : i + d < P.length := by omega
        refine (ih i hi hid' h1 (by omega)).trans (SimpleGraph.Adj.reachable ?_)
        exact PathBasics.path_adj_succ hP hid
  intro x y
  obtain ⟨i, hi, hai, hib, hxi⟩ := (hSmem _).mp x.2
  obtain ⟨j, hj, haj, hjb, hyj⟩ := (hSmem _).mp y.2
  have hx : x = ⟨P[i]'hi, hmem i hi hai hib⟩ := Subtype.ext hxi
  have hy : y = ⟨P[j]'hj, hmem j hj haj hjb⟩ := Subtype.ext hyj
  rw [hx, hy]
  rcases le_total i j with hle | hle
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    exact step d i hi hj hai hjb
  · obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    exact (step d j hj hi haj hib).symm

theorem thm_15_4 (G : SimpleGraph V) (hG : InF6 G)
    (P : List V) (m : ℕ) (hP : IsPathList G P) (hPlen : P.length = m)
    (s : ℕ) (hs1 : 2 ≤ s) (hs2 : s ≤ m - 2)
    (Q : List V) (n : ℕ) (hQlen : Q.length = n + 2) (hn : 2 ≤ n)
    (hQ : IsAntipathFrom G Q P[s - 1] P[s])
    (hends : ∀ q ∈ SPGT.interior Q, G.Adj P[0] q ∧ G.Adj P[m - 1] q) :
    Even n ∧ m = 4 := by
  ---------------------------------------------------------------------------
  -- Bookkeeping: index bounds and the two index-level readings of `P`.
  ---------------------------------------------------------------------------
  have hm4 : 4 ≤ m := by omega
  have hb0 : 0 < P.length := by omega
  have hbm : m - 1 < P.length := by omega
  have hbs1 : s - 1 < P.length := by omega
  have hbs : s < P.length := by omega
  have hbsp : s + 1 < P.length := by omega
  have hbsm : s - 2 < P.length := by omega
  have hadjP : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length),
      (G.Adj (P[i]'hi) (P[j]'hj) ↔ (i + 1 = j ∨ j + 1 = i)) := hP.2.2
  have hneP : ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length),
      i ≠ j → (P[i]'hi) ≠ (P[j]'hj) :=
    fun i j hi hj hij => PathBasics.path_ne_of_ne_index hP hi hj hij
  have hBerge : Berge G := hG.1.1.1
  have hQ' : IsPathFrom Gᶜ Q (P[s - 1]'hbs1) (P[s]'hbs) := hQ
  ---------------------------------------------------------------------------
  -- The vertices of the antipath `Q` are its two ends together with `Q*`.
  ---------------------------------------------------------------------------
  have hQmem : ∀ u ∈ Q, u = (P[s - 1]'hbs1) ∨ u = (P[s]'hbs) ∨ u ∈ SPGT.interior Q := by
    intro u hu
    by_cases e1 : u = (P[s - 1]'hbs1)
    · exact Or.inl e1
    by_cases e2 : u = (P[s]'hbs)
    · exact Or.inr (Or.inl e2)
    · exact Or.inr (Or.inr ((PathBasics.mem_interior_iff_of_pathFrom hQ').mpr ⟨hu, e1, e2⟩))
  rcases Nat.even_or_odd n with hnE | hnO
  ---------------------------------------------------------------------------
  -- CASE `n` even.  `Q` is an odd antipath whose interior is complete to
  -- `p_1` and to `p_m`; a vertex complete to `Q*` and to neither end of `Q`
  -- would close `Q` into an odd hole of `Gbar`, i.e. an odd antihole of `G`.
  ---------------------------------------------------------------------------
  · refine ⟨hnE, ?_⟩
    have key : ∀ v : V, v ≠ (P[s - 1]'hbs1) → v ≠ (P[s]'hbs) →
        (∀ q ∈ SPGT.interior Q, G.Adj v q) →
        ¬ G.Adj v (P[s - 1]'hbs1) → ¬ G.Adj v (P[s]'hbs) → False := by
      intro v hv1 hv2 hvint hc1 hc2
      have hvQ : v ∉ Q := by
        intro hmem
        rcases hQmem v hmem with e | e | e
        · exact hv1 e
        · exact hv2 e
        · exact G.irrefl (hvint v e)
      have hsingle : IsPathFrom Gᶜ [v] v v :=
        ⟨PathBasics.isPathList_singleton Gᶜ v, rfl, rfl⟩
      have hdisj : ∀ x ∈ Q, x ∉ [v] := by
        intro x hx hxv
        simp only [List.mem_singleton] at hxv
        exact hvQ (hxv ▸ hx)
      have hcross : ∀ x ∈ Q, ∀ y ∈ [v],
          (Gᶜ.Adj x y ↔ (x = (P[s]'hbs) ∧ y = v) ∨ (x = (P[s - 1]'hbs1) ∧ y = v)) := by
        intro x hx y hy
        simp only [List.mem_singleton] at hy
        subst hy
        constructor
        · intro hadj
          rcases hQmem x hx with e | e | e
          · exact Or.inr ⟨e, rfl⟩
          · exact Or.inl ⟨e, rfl⟩
          · exact absurd (hvint x e).symm hadj.2
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact ⟨fun h => hv2 h.symm, fun h => hc2 h.symm⟩
          · exact ⟨fun h => hv1 h.symm, fun h => hc1 h.symm⟩
      have hhole : IsHoleList Gᶜ (Q ++ [v]) :=
        PathGlue.glue_hole hQ' hsingle hdisj hcross
          (by simp only [hQlen, List.length_cons, List.length_nil]; omega)
      have hev := hBerge.2 _ hhole
      simp only [holeLength, List.length_append, List.length_cons, List.length_nil,
        hQlen, Nat.even_add_one, Nat.even_iff] at hev
      rw [Nat.even_iff] at hnE
      omega
    -- `p_1` is adjacent to one of `p_s`, `p_{s+1}`.
    have h1 : G.Adj (P[0]'hb0) (P[s - 1]'hbs1) ∨ G.Adj (P[0]'hb0) (P[s]'hbs) := by
      by_cases c1 : G.Adj (P[0]'hb0) (P[s - 1]'hbs1)
      · exact Or.inl c1
      by_cases c2 : G.Adj (P[0]'hb0) (P[s]'hbs)
      · exact Or.inr c2
      · exact (key _ (hneP 0 (s - 1) hb0 hbs1 (by omega))
          (hneP 0 s hb0 hbs (by omega)) (fun q hq => (hends q hq).1) c1 c2).elim
    -- `p_m` is adjacent to one of `p_s`, `p_{s+1}`.
    have h2 : G.Adj (P[m - 1]'hbm) (P[s - 1]'hbs1) ∨ G.Adj (P[m - 1]'hbm) (P[s]'hbs) := by
      by_cases c1 : G.Adj (P[m - 1]'hbm) (P[s - 1]'hbs1)
      · exact Or.inl c1
      by_cases c2 : G.Adj (P[m - 1]'hbm) (P[s]'hbs)
      · exact Or.inr c2
      · exact (key _ (hneP (m - 1) (s - 1) hbm hbs1 (by omega))
          (hneP (m - 1) s hbm hbs (by omega)) (fun q hq => (hends q hq).2) c1 c2).elim
    -- `s = 2` and `m = s + 2`.
    have hseq : s = 2 := by
      rcases h1 with h1 | h1
      · have h := (hadjP 0 (s - 1) hb0 hbs1).mp h1; omega
      · have h := (hadjP 0 s hb0 hbs).mp h1; omega
    rcases h2 with h2 | h2
    · have h := (hadjP (m - 1) (s - 1) hbm hbs1).mp h2; omega
    · have h := (hadjP (m - 1) s hbm hbs).mp h2; omega
  ---------------------------------------------------------------------------
  -- CASE `n` odd.  `Q` is an even antipath of length `>= 4`; 13.7 applied in
  -- `Gbar` to it and the sets `{p_1,...,p_{s-1}}`, `{p_{s+2},...,p_m}` forces
  -- its length to be `2`.
  ---------------------------------------------------------------------------
  · exfalso
    obtain ⟨X, hXmem⟩ : ∃ X : Set V, ∀ w : V,
        (w ∈ X ↔ ∃ k : ℕ, ∃ h : k < P.length, s + 1 ≤ k ∧ k ≤ m - 1 ∧ w = P[k]'h) :=
      ⟨_, fun w => Iff.rfl⟩
    obtain ⟨Y, hYmem⟩ : ∃ Y : Set V, ∀ w : V,
        (w ∈ Y ↔ ∃ k : ℕ, ∃ h : k < P.length, 0 ≤ k ∧ k ≤ s - 2 ∧ w = P[k]'h) :=
      ⟨_, fun w => Iff.rfl⟩
    have hXY : Disjoint X Y := by
      rw [Set.disjoint_left]
      intro w hwX hwY
      obtain ⟨k1, hk1, ha1, hb1, rfl⟩ := (hXmem w).mp hwX
      obtain ⟨k2, hk2, ha2, hb2, he⟩ := (hYmem _).mp hwY
      exact hneP k1 k2 hk1 hk2 (by omega) he
    have hXne : X.Nonempty := ⟨_, (hXmem _).mpr ⟨s + 1, hbsp, le_refl _, by omega, rfl⟩⟩
    have hYne : Y.Nonempty := ⟨_, (hYmem _).mpr ⟨0, hb0, Nat.zero_le _, by omega, rfl⟩⟩
    have hXa : AnticonnectedSet Gᶜ X := by
      show ConnectedSet Gᶜᶜ X
      rw [compl_compl]
      exact block_connected hP (s + 1) (m - 1) X hXmem
    have hYa : AnticonnectedSet Gᶜ Y := by
      show ConnectedSet Gᶜᶜ Y
      rw [compl_compl]
      exact block_connected hP 0 (s - 2) Y hYmem
    have hcompl : Complete Gᶜ X Y := by
      intro x hx y hy
      obtain ⟨k1, hk1, ha1, hb1, rfl⟩ := (hXmem x).mp hx
      obtain ⟨k2, hk2, ha2, hb2, rfl⟩ := (hYmem y).mp hy
      exact ⟨hneP k1 k2 hk1 hk2 (by omega),
        PathBasics.path_not_adj_of_gap hP hk1 hk2 (by omega) (by omega)⟩
    have hEven : Even (pathLength Q) := by
      rw [pathLength, hQlen, Nat.even_iff]
      rcases hnO with ⟨t, ht⟩
      omega
    have hpos : 0 < pathLength Q := by rw [pathLength, hQlen]; omega
    have hXuniq : ∀ u ∈ Q, (VertexComplete Gᶜ u X ↔ u = (P[s - 1]'hbs1)) := by
      intro u hu
      constructor
      · intro hvc
        rcases hQmem u hu with e | e | e
        · exact e
        · exfalso
          subst e
          have hxin : (P[s + 1]'hbsp) ∈ X :=
            (hXmem _).mpr ⟨s + 1, hbsp, le_refl _, by omega, rfl⟩
          exact (hvc _ hxin).2 ((hadjP s (s + 1) hbs hbsp).mpr (Or.inl rfl))
        · exfalso
          have hxin : (P[m - 1]'hbm) ∈ X :=
            (hXmem _).mpr ⟨m - 1, hbm, by omega, le_refl _, rfl⟩
          exact (hvc _ hxin).2 ((hends u e).2.symm)
      · rintro rfl
        intro x hx
        obtain ⟨k, hk, ha, hb, rfl⟩ := (hXmem x).mp hx
        exact ⟨hneP (s - 1) k hbs1 hk (by omega),
          PathBasics.path_not_adj_of_gap hP hbs1 hk (by omega) (by omega)⟩
    have hYuniq : ∀ u ∈ Q, (VertexComplete Gᶜ u Y ↔ u = (P[s]'hbs)) := by
      intro u hu
      constructor
      · intro hvc
        rcases hQmem u hu with e | e | e
        · exfalso
          subst e
          have hyin : (P[s - 2]'hbsm) ∈ Y :=
            (hYmem _).mpr ⟨s - 2, hbsm, Nat.zero_le _, le_refl _, rfl⟩
          exact (hvc _ hyin).2 ((hadjP (s - 1) (s - 2) hbs1 hbsm).mpr (Or.inr (by omega)))
        · exact e
        · exfalso
          have hyin : (P[0]'hb0) ∈ Y :=
            (hYmem _).mpr ⟨0, hb0, Nat.zero_le _, by omega, rfl⟩
          exact (hvc _ hyin).2 ((hends u e).1.symm)
      · rintro rfl
        intro y hy
        obtain ⟨k, hk, ha, hb, rfl⟩ := (hYmem y).mp hy
        exact ⟨hneP s k hbs hk (by omega),
          PathBasics.path_not_adj_of_gap hP hbs hk (by omega) (by omega)⟩
    have h137 := _root_.Workspace.Statements.S13.SPGT.thm_13_7 Gᶜ
      (ClassLemmas.inF5_compl.mpr hG.1) X Y hXY hXne hYne hXa hYa hcompl
      Q (P[s - 1]'hbs1) (P[s]'hbs) hQ'.1 hEven hpos hQ'.2.1 hQ'.2.2 hXuniq hYuniq
    have hlen2 : pathLength Q = 2 := h137.1
    rw [pathLength, hQlen] at hlen2
    omega

end SPGT

end Workspace.Statements.S15
