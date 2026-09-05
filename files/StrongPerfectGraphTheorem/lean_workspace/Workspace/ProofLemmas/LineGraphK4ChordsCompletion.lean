import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Classes
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.LineGraphK4Chords

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LineGraphK4Chords

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT

/-! ## `Hg` is a subdivision of `K₄` -/

section SubDiv

variable {n P R Q : ℕ} [NeZero n]

variable (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)

include h0R hRP hPQ hQn

theorem iot_injective : Function.Injective (iot n P R Q) := by
  intro u v huv
  have h1 := iot_val h0R hRP hPQ hQn u
  have h2 := iot_val h0R hRP hPQ hQn v
  have hb : bp P R Q u = bp P R Q v := by rw [← h1, ← h2, huv]
  rcases fin4_cases u with rfl | rfl | rfl | rfl <;>
    rcases fin4_cases v with rfl | rfl | rfl | rfl <;>
    simp only [bp_zero, bp_one, bp_two, bp_three] at hb <;> first | rfl | omega

/-- Every vertex of `Hg` is a branch vertex or an interior vertex of a track. -/
theorem Hg_cover (w : Fin n) :
    (∃ u : Fin 4, w = iot n P R Q u) ∨
      ∃ u v : Fin 4, (⊤ : SimpleGraph (Fin 4)).Adj u v ∧
        w ∈ trackInterior (Tr n P R Q u v) := by
  have hw : w.val < n := w.isLt
  have hcy : ∀ k : ℕ, k < n → w.val = k → w = cyc n k := by
    intro k hk hwk
    apply Fin.val_injective
    rw [cyc_val, Nat.mod_eq_of_lt hk, hwk]
  rcases (by omega : w.val = 0 ∨ w.val = R ∨ w.val = P ∨ w.val = Q ∨
      (0 < w.val ∧ w.val < R) ∨ (R < w.val ∧ w.val < P) ∨ (P < w.val ∧ w.val < Q) ∨
      (Q < w.val ∧ w.val < n)) with h | h | h | h | h | h | h | h
  · exact Or.inl ⟨0, by rw [iot_zero]; exact hcy 0 (by omega) h⟩
  · exact Or.inl ⟨1, by rw [iot_one]; exact hcy R (by omega) h⟩
  · exact Or.inl ⟨2, by rw [iot_two]; exact hcy P (by omega) h⟩
  · exact Or.inl ⟨3, by rw [iot_three]; exact hcy Q (by omega) h⟩
  · refine Or.inr ⟨0, 1, by decide, ?_⟩
    rw [Tr_01, arc_interior_mem_iff]
    exact ⟨w.val, by omega, by omega, by rw [Nat.zero_add]; exact hcy w.val hw rfl⟩
  · refine Or.inr ⟨1, 2, by decide, ?_⟩
    rw [Tr_12, arc_interior_mem_iff]
    refine ⟨w.val - R, by omega, by omega, ?_⟩
    rw [show R + (w.val - R) = w.val from by omega]
    exact hcy w.val hw rfl
  · refine Or.inr ⟨2, 3, by decide, ?_⟩
    rw [Tr_23, arc_interior_mem_iff]
    refine ⟨w.val - P, by omega, by omega, ?_⟩
    rw [show P + (w.val - P) = w.val from by omega]
    exact hcy w.val hw rfl
  · refine Or.inr ⟨3, 0, by decide, ?_⟩
    rw [Tr_30, arc_interior_mem_iff]
    refine ⟨w.val - Q, by omega, by omega, ?_⟩
    rw [show Q + (w.val - Q) = w.val from by omega]
    exact hcy w.val hw rfl

/-- Every edge of `Hg` is either a cycle edge `w_k w_{k+1}` or one of the two chords. -/
theorem Hg_edge_cases {i j : Fin n} (hadj : (Hg n P R Q).Adj i j) :
    (∃ k : ℕ, k < n ∧ s(i, j) = s(cyc n k, cyc n (k + 1))) ∨
      s(i, j) = s(cyc n 0, cyc n P) ∨ s(i, j) = s(cyc n R, cyc n Q) := by
  obtain ⟨hne, hc⟩ := hadj
  have hself : ∀ x : Fin n, cyc n x.val = x := cyc_self n
  rcases hc with (h | h) | (h | h) | (h | h)
  · refine Or.inl ⟨i.val, i.isLt, ?_⟩
    have e1 : cyc n i.val = i := hself i
    have e2 : cyc n (i.val + 1) = j := by
      apply Fin.val_injective
      rw [cyc_val, ← h]
    rw [e1, e2]
  · refine Or.inl ⟨j.val, j.isLt, ?_⟩
    have e1 : cyc n j.val = j := hself j
    have e2 : cyc n (j.val + 1) = i := by
      apply Fin.val_injective
      rw [cyc_val, ← h]
    rw [e1, e2]
    exact Sym2.eq_swap
  · obtain ⟨h1, h2⟩ := h
    refine Or.inr (Or.inl ?_)
    have e1 : cyc n 0 = i := by apply Fin.val_injective; rw [cyc_val, Nat.zero_mod, h1]
    have e2 : cyc n P = j := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : P < n), h2]
    rw [e1, e2]
  · obtain ⟨h1, h2⟩ := h
    refine Or.inr (Or.inl ?_)
    have e1 : cyc n 0 = j := by apply Fin.val_injective; rw [cyc_val, Nat.zero_mod, h1]
    have e2 : cyc n P = i := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : P < n), h2]
    rw [e1, e2]
    exact Sym2.eq_swap
  · obtain ⟨h1, h2⟩ := h
    refine Or.inr (Or.inr ?_)
    have e1 : cyc n R = i := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : R < n), h1]
    have e2 : cyc n Q = j := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : Q < n), h2]
    rw [e1, e2]
  · obtain ⟨h1, h2⟩ := h
    refine Or.inr (Or.inr ?_)
    have e1 : cyc n R = j := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : R < n), h1]
    have e2 : cyc n Q = i := by
      apply Fin.val_injective; rw [cyc_val, Nat.mod_eq_of_lt (by omega : Q < n), h2]
    rw [e1, e2]
    exact Sym2.eq_swap

end SubDiv

section ArcEdges

variable {n : ℕ} [NeZero n]

theorem arc_edge_mem (s len k : ℕ) (hk : k < len) :
    s(cyc n (s + k), cyc n (s + k + 1)) ∈ trackEdges (arc n s len) := by
  refine ⟨k, by rw [arc_length]; omega, ?_⟩
  rw [arc_getElem n s len (by rw [arc_length]; omega),
    arc_getElem n s len (by rw [arc_length]; omega), Nat.add_assoc]

theorem arc_edge_mem' (s len k : ℕ) (h1 : s ≤ k) (h2 : k < s + len) :
    s(cyc n k, cyc n (k + 1)) ∈ trackEdges (arc n s len) := by
  have h := arc_edge_mem (n := n) s len (k - s) (by omega)
  rwa [show s + (k - s) = k from by omega] at h

end ArcEdges

section EdgeSet

variable {n P R Q : ℕ} [NeZero n]

variable (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)

include h0R hRP hPQ hQn

theorem Hg_edgeSet :
    (Hg n P R Q).edgeSet =
      ⋃ (u : Fin 4) (v : Fin 4) (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v),
        trackEdges (Tr n P R Q u v) := by
  have hmem : ∀ (u v : Fin 4), u ≠ v → ∀ e : Sym2 (Fin n), e ∈ trackEdges (Tr n P R Q u v) →
      e ∈ (⋃ (u : Fin 4) (v : Fin 4) (_ : (⊤ : SimpleGraph (Fin 4)).Adj u v),
        trackEdges (Tr n P R Q u v)) := by
    intro u v huv e he
    simp only [Set.mem_iUnion]
    exact ⟨u, v, by simpa using huv, he⟩
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    constructor
    · intro he
      have hadj : (Hg n P R Q).Adj i j := he
      rcases Hg_edge_cases h0R hRP hPQ hQn hadj with ⟨k, hk, hEq⟩ | hEq | hEq
      · rw [hEq]
        rcases (by omega : k < R ∨ (R ≤ k ∧ k < P) ∨ (P ≤ k ∧ k < Q) ∨ (Q ≤ k ∧ k < n))
          with h | h | h | h
        · exact hmem 0 1 (by decide) _ (by rw [Tr_01]; exact arc_edge_mem' 0 R k (by omega) (by omega))
        · exact hmem 1 2 (by decide) _
            (by rw [Tr_12]; exact arc_edge_mem' R (P - R) k (by omega) (by omega))
        · exact hmem 2 3 (by decide) _
            (by rw [Tr_23]; exact arc_edge_mem' P (Q - P) k (by omega) (by omega))
        · exact hmem 3 0 (by decide) _
            (by rw [Tr_30]; exact arc_edge_mem' Q (n - Q) k (by omega) (by omega))
      · rw [hEq]
        refine hmem 0 2 (by decide) _ ?_
        rw [Tr_02]
        exact ⟨0, by simp, rfl⟩
      · rw [hEq]
        refine hmem 1 3 (by decide) _ ?_
        rw [Tr_13]
        exact ⟨0, by simp, rfl⟩
    · intro he
      simp only [Set.mem_iUnion] at he
      obtain ⟨u, v, huv, k, hk, hEq⟩ := he
      rw [hEq, SimpleGraph.mem_edgeSet]
      exact (Tr_isTrackFrom h0R hRP hPQ hQn u v (by simpa using huv)).1.2.2 k hk

/-- **`Hg n P R Q` is a subdivision of `K₄`.** -/
theorem Hg_isSubdivision : IsSubdivision (⊤ : SimpleGraph (Fin 4)) (Hg n P R Q) := by
  refine ⟨iot n P R Q, Tr n P R Q, iot_injective h0R hRP hPQ hQn, ?_, ?_, ?_, ?_, ?_, ?_,
    Hg_edgeSet h0R hRP hPQ hQn⟩
  · intro u v huv
    exact Tr_isTrackFrom h0R hRP hPQ hQn u v (by simpa using huv)
  · intro u v huv
    have h2 := Tr_len2 h0R hRP hPQ hQn u v (by simpa using huv)
    unfold trackLength
    omega
  · intro u v huv
    exact Tr_rev h0R hRP hPQ hQn u v (by simpa using huv)
  · intro u v u' v' huv huv' hs w hw hmem
    have h1 : IntV n P R Q u v w.val :=
      Tr_int h0R hRP hPQ hQn u v (by simpa using huv) w hw
    rcases Tr_loc h0R hRP hPQ hQn u' v' (by simpa using huv') w hmem with h | h | h
    · exact IntV_ne_bp h0R hRP hPQ hQn h1 u' h
    · exact IntV_ne_bp h0R hRP hPQ hQn h1 v' h
    · exact hs ((IntV_which h0R hRP hPQ hQn h1).trans (IntV_which h0R hRP hPQ hQn h).symm)
  · rintro u v huv w hw ⟨x, hx⟩
    have h1 : IntV n P R Q u v w.val :=
      Tr_int h0R hRP hPQ hQn u v (by simpa using huv) w hw
    refine IntV_ne_bp h0R hRP hPQ hQn h1 x ?_
    rw [← hx, iot_val h0R hRP hPQ hQn x]
  · exact Hg_cover h0R hRP hPQ hQn

/-! ## `Hg` is bipartite -/

/-- The two-colouring `w ↦ w mod 2` shows that `Hg n P R Q` is bipartite, given that `n` is
even, that `P` is odd and that `Q - R` is odd. -/
theorem Hg_bipartite (hneven : Even n) (hPodd : ¬ Even P) (hRQodd : ¬ Even (R + (n - Q))) :
    (Hg n P R Q).IsBipartite := by
  have hn2 : n % 2 = 0 := Nat.even_iff.mp hneven
  have hP2 : P % 2 = 1 := Nat.not_even_iff.mp hPodd
  have hRQ2 : (R + (n - Q)) % 2 = 1 := Nat.not_even_iff.mp hRQodd
  have key : ∀ x y : ℕ, x < n → y < n → y = (x + 1) % n → x % 2 ≠ y % 2 := by
    intro x y hx hy hxy
    rcases Nat.lt_or_ge (x + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h] at hxy; omega
    · rw [show x + 1 = n from by omega, Nat.mod_self] at hxy; omega
  refine ⟨SimpleGraph.Coloring.mk (fun w : Fin n => (⟨w.val % 2, by omega⟩ : Fin 2)) ?_⟩
  intro u v huv
  obtain ⟨hne, hc⟩ := huv
  simp only [ne_eq, Fin.mk.injEq]
  rcases hc with (h | h) | ((h | h) | (h | h))
  · exact key u.val v.val u.isLt v.isLt h
  · exact (key v.val u.val v.isLt u.isLt h).symm
  · omega
  · omega
  · omega
  · omega

theorem Hg_isBipartiteSubdivision (hneven : Even n) (hPodd : ¬ Even P)
    (hRQodd : ¬ Even (R + (n - Q))) :
    IsBipartiteSubdivision (⊤ : SimpleGraph (Fin 4)) (Hg n P R Q) :=
  ⟨Hg_isSubdivision h0R hRP hPQ hQn, Hg_bipartite h0R hRP hPQ hQn hneven hPodd hRQodd⟩

end EdgeSet

/-! ## The line-graph isomorphism -/

/-- **The rim plus the two extra vertices induce `L(Hg n P R Q)`.**

The rim vertex `D t` corresponds to the cycle edge `w_t w_{t+1}`, `a` to the chord `w₀ w_P`
and `b` to the chord `w_R w_Q`. -/
theorem exists_iso_lineGraph {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {C : List V} {n P R Q : ℕ} {D : ℕ → V} {a b : V}
    (hC : IsHoleList G C) (hnn : C.length = n)
    (hD : ∀ t : ℕ, C[t % C.length]? = some (D t))
    (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)
    (haC : a ∉ C) (hbC : b ∉ C) (hne : a ≠ b) (hab : ¬ G.Adj a b)
    (ha : ∀ t, t < n → (G.Adj a (D t) ↔ (t = 0 ∨ t = n - 1 ∨ t = P - 1 ∨ t = P)))
    (hb : ∀ t, t < n → (G.Adj b (D t) ↔ (t = R - 1 ∨ t = R ∨ t = Q - 1 ∨ t = Q))) :
    Nonempty (G.induce ({w : V | w ∈ C} ∪ {a, b}) ≃g (Hg n P R Q).lineGraph) := by
  haveI : NeZero n := ⟨by omega⟩
  have hn4 : 4 ≤ n := by omega
  -- `D t` is the `t`-th entry of `C`.
  have hDC : ∀ (t : ℕ) (h : t < C.length), D t = C[t]'h := by
    intro t h
    have h1 := hD t
    rw [Nat.mod_eq_of_lt h, List.getElem?_eq_getElem h] at h1
    exact (Option.some.inj h1).symm
  have hcases : ∀ i : Fin (n + 2), i.val < n ∨ i.val = n ∨ i.val = n + 1 := by
    intro i; have := i.isLt; omega
  -- The indexing of `V(C) ∪ {a,b}` by `Fin (n+2)`.
  obtain ⟨φ, hφr, hφa, hφb⟩ : ∃ φ : Fin (n + 2) → V,
      (∀ i : Fin (n + 2), i.val < n → φ i = D i.val) ∧
      (∀ i : Fin (n + 2), i.val = n → φ i = a) ∧
      (∀ i : Fin (n + 2), i.val = n + 1 → φ i = b) := by
    refine ⟨fun i => if i.val < n then D i.val else if i.val = n then a else b, ?_, ?_, ?_⟩
    · intro i hi; simp only [if_pos hi]
    · intro i hi; simp [hi]
    · intro i hi; simp [hi]
  -- The matching indexing of `E(Hg)` by `Fin (n+2)`.
  obtain ⟨ψ, hψr, hψa, hψb⟩ : ∃ ψ : Fin (n + 2) → Sym2 (Fin n),
      (∀ i : Fin (n + 2), i.val < n → ψ i = s(cyc n i.val, cyc n (i.val + 1))) ∧
      (∀ i : Fin (n + 2), i.val = n → ψ i = s(cyc n 0, cyc n P)) ∧
      (∀ i : Fin (n + 2), i.val = n + 1 → ψ i = s(cyc n R, cyc n Q)) := by
    refine ⟨fun i => if i.val < n then s(cyc n i.val, cyc n (i.val + 1))
      else if i.val = n then s(cyc n 0, cyc n P) else s(cyc n R, cyc n Q), ?_, ?_, ?_⟩
    · intro i hi; simp only [if_pos hi]
    · intro i hi; simp [hi]
    · intro i hi; simp [hi]
  -- Arithmetic toolbox.
  have hce : ∀ x y : ℕ, x < n → y < n → (cyc n x = cyc n y ↔ x = y) :=
    fun x y hx hy => ⟨cyc_inj_of_lt n hx hy, fun h => by rw [h]⟩
  have hsucclt : ∀ x : ℕ, (x + 1) % n < n := fun x => Nat.mod_lt _ (by omega)
  have hstep : ∀ x y : ℕ, x < n → y < n →
      (y = (x + 1) % n ↔ (x + 1 = y ∨ (x = n - 1 ∧ y = 0))) := by
    intro x y hx hy
    rcases Nat.lt_or_ge (x + 1) n with h | h
    · rw [Nat.mod_eq_of_lt h]
      constructor
      · intro hh; exact Or.inl hh.symm
      · rintro (hh | ⟨hh1, hh2⟩) <;> omega
    · rw [show x + 1 = n from by omega, Nat.mod_self]
      constructor
      · intro hh; exact Or.inr ⟨by omega, hh⟩
      · rintro (hh | ⟨hh1, hh2⟩) <;> omega
  have hcycsucc : ∀ x : ℕ, cyc n (x + 1) = cyc n ((x + 1) % n) := by
    intro x
    apply Fin.val_injective
    rw [cyc_val, cyc_val, Nat.mod_eq_of_lt (hsucclt x)]
  have hex : ∀ x y z w : Fin n, (∃ v : Fin n, v ∈ s(x, y) ∧ v ∈ s(z, w)) ↔
      (x = z ∨ x = w ∨ y = z ∨ y = w) := by
    intro x y z w
    constructor
    · rintro ⟨v, hv1, hv2⟩
      rw [Sym2.mem_iff] at hv1 hv2
      rcases hv1 with rfl | rfl <;> rcases hv2 with h | h <;> tauto
    · rintro (h | h | h | h)
      · exact ⟨x, by simp, by simp [h]⟩
      · exact ⟨x, by simp, by simp [h]⟩
      · exact ⟨y, by simp, by simp [h]⟩
      · exact ⟨y, by simp, by simp [h]⟩
  -- The four "distinctness" facts about the `n + 2` edges of `Hg`.
  have hneRR : ∀ s t : ℕ, s < n → t < n → s ≠ t →
      s(cyc n s, cyc n (s + 1)) ≠ s(cyc n t, cyc n (t + 1)) := by
    intro s t hs ht hst
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' = (t + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have ht'lt : t' < n := by rw [ht']; exact hsucclt t
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    have Ht : t + 1 = t' ∨ (t = n - 1 ∧ t' = 0) := (hstep t t' ht ht'lt).mp ht'
    intro heq
    rw [hcycsucc s, hcycsucc t, ← hs', ← ht'] at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hst ((hce s t hs ht).mp h1)
    · have e1 := (hce s t' hs ht'lt).mp h1
      have e2 := (hce s' t hs'lt ht).mp h2
      omega
  have hneRA : ∀ s : ℕ, s < n → s(cyc n s, cyc n (s + 1)) ≠ s(cyc n 0, cyc n P) := by
    intro s hs
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    intro heq
    rw [hcycsucc s, ← hs'] at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := (hce s 0 hs (by omega)).mp h1
      have e2 := (hce s' P hs'lt (by omega)).mp h2
      omega
    · have e1 := (hce s P hs (by omega)).mp h1
      have e2 := (hce s' 0 hs'lt (by omega)).mp h2
      omega
  have hneRB : ∀ s : ℕ, s < n → s(cyc n s, cyc n (s + 1)) ≠ s(cyc n R, cyc n Q) := by
    intro s hs
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    intro heq
    rw [hcycsucc s, ← hs'] at heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := (hce s R hs (by omega)).mp h1
      have e2 := (hce s' Q hs'lt (by omega)).mp h2
      omega
    · have e1 := (hce s Q hs (by omega)).mp h1
      have e2 := (hce s' R hs'lt (by omega)).mp h2
      omega
  have hneAB : s(cyc n 0, cyc n P) ≠ s(cyc n R, cyc n Q) := by
    intro heq
    rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have e1 := (hce 0 R (by omega) (by omega)).mp h1
      omega
    · have e1 := (hce 0 Q (by omega) (by omega)).mp h1
      omega
  -- The three "meeting" facts.
  have hLR : ∀ s t : ℕ, s < n → t < n →
      ((s(cyc n s, cyc n (s + 1)) ≠ s(cyc n t, cyc n (t + 1)) ∧
        ∃ v : Fin n, v ∈ s(cyc n s, cyc n (s + 1)) ∧ v ∈ s(cyc n t, cyc n (t + 1))) ↔
       (t = (s + 1) % n ∨ s = (t + 1) % n)) := by
    intro s t hs ht
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    obtain ⟨t', ht'⟩ : ∃ t', t' = (t + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have ht'lt : t' < n := by rw [ht']; exact hsucclt t
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    have Ht : t + 1 = t' ∨ (t = n - 1 ∧ t' = 0) := (hstep t t' ht ht'lt).mp ht'
    rw [hcycsucc s, hcycsucc t, ← hs', ← ht', hex,
      hce s t hs ht, hce s t' hs ht'lt, hce s' t hs'lt ht,
      hce s' t' hs'lt ht'lt]
    constructor
    · rintro ⟨hne, h | h | h | h⟩
      · exfalso
        apply hne
        have he : s' = t' := by omega
        rw [h, he]
      · exact Or.inr h
      · exact Or.inl h.symm
      · exfalso
        apply hne
        have he : s = t := by omega
        rw [he, h]
    · rintro (h | h)
      · refine ⟨?_, Or.inr (Or.inr (Or.inl h.symm))⟩
        intro heq
        have : s = t := by
          rcases Sym2.eq_iff.mp heq with ⟨e1, -⟩ | ⟨e1, e2⟩
          · exact (hce s t hs ht).mp e1
          · have e1' := (hce s t' hs ht'lt).mp e1
            have e2' := (hce s' t hs'lt ht).mp e2
            omega
        omega
      · refine ⟨?_, Or.inr (Or.inl h)⟩
        intro heq
        have : s = t := by
          rcases Sym2.eq_iff.mp heq with ⟨e1, -⟩ | ⟨e1, e2⟩
          · exact (hce s t hs ht).mp e1
          · have e1' := (hce s t' hs ht'lt).mp e1
            have e2' := (hce s' t hs'lt ht).mp e2
            omega
        omega
  have hmeetRA : ∀ s : ℕ, s < n →
      ((∃ v : Fin n, v ∈ s(cyc n s, cyc n (s + 1)) ∧ v ∈ s(cyc n 0, cyc n P)) ↔
        (s = 0 ∨ s = n - 1 ∨ s = P - 1 ∨ s = P)) := by
    intro s hs
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    rw [hcycsucc s, ← hs', hex, hce s 0 hs (by omega), hce s P hs (by omega),
      hce s' 0 hs'lt (by omega), hce s' P hs'lt (by omega)]
    omega
  have hmeetRB : ∀ s : ℕ, s < n →
      ((∃ v : Fin n, v ∈ s(cyc n s, cyc n (s + 1)) ∧ v ∈ s(cyc n R, cyc n Q)) ↔
        (s = R - 1 ∨ s = R ∨ s = Q - 1 ∨ s = Q)) := by
    intro s hs
    obtain ⟨s', hs'⟩ : ∃ s', s' = (s + 1) % n := ⟨_, rfl⟩
    have hs'lt : s' < n := by rw [hs']; exact hsucclt s
    have Hs : s + 1 = s' ∨ (s = n - 1 ∧ s' = 0) := (hstep s s' hs hs'lt).mp hs'
    rw [hcycsucc s, ← hs', hex, hce s R hs (by omega), hce s Q hs (by omega),
      hce s' R hs'lt (by omega), hce s' Q hs'lt (by omega)]
    omega
  have hmeetAB : ¬ ∃ v : Fin n, v ∈ s(cyc n 0, cyc n P) ∧ v ∈ s(cyc n R, cyc n Q) := by
    rw [hex, hce 0 R (by omega) (by omega), hce 0 Q (by omega) (by omega),
      hce P R (by omega) (by omega), hce P Q (by omega) (by omega)]
    omega
  -- The adjacency correspondence.
  have hsymm : ∀ i j : Fin (n + 2),
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) →
      ((ψ j ≠ ψ i ∧ ∃ v : Fin n, v ∈ ψ j ∧ v ∈ ψ i) ↔ G.Adj (φ j) (φ i)) := by
    intro i j h
    rw [SimpleGraph.adj_comm, ← h]
    constructor
    · rintro ⟨h1, v, h2, h3⟩; exact ⟨h1.symm, v, h3, h2⟩
    · rintro ⟨h1, v, h2, h3⟩; exact ⟨h1.symm, v, h3, h2⟩
  have kAA : ∀ i j : Fin (n + 2), i.val = j.val →
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j hij
    have hh : i = j := Fin.val_injective hij
    subst hh
    constructor
    · rintro ⟨h1, -⟩; exact absurd rfl h1
    · intro h; exact absurd rfl h.ne
  have kRR : ∀ i j : Fin (n + 2), i.val < n → j.val < n →
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j hi hj
    have hadj : G.Adj (φ i) (φ j) ↔
        (j.val = (i.val + 1) % C.length ∨ i.val = (j.val + 1) % C.length) := by
      rw [hφr i hi, hφr j hj, hDC i.val (by omega), hDC j.val (by omega)]
      exact hC.2.2 i.val j.val (by omega) (by omega)
    rw [hnn] at hadj
    rw [hψr i hi, hψr j hj, hadj]
    exact hLR i.val j.val hi hj
  have kRA : ∀ i j : Fin (n + 2), i.val < n → j.val = n →
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j hi hj
    rw [hψr i hi, hψa j hj, hφr i hi, hφa j hj,
      show G.Adj (D i.val) a ↔ G.Adj a (D i.val) from G.adj_comm (D i.val) a,
      ha i.val hi]
    constructor
    · rintro ⟨-, hm⟩; exact (hmeetRA i.val hi).mp hm
    · intro h; exact ⟨hneRA i.val hi, (hmeetRA i.val hi).mpr h⟩
  have kRB : ∀ i j : Fin (n + 2), i.val < n → j.val = n + 1 →
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j hi hj
    rw [hψr i hi, hψb j hj, hφr i hi, hφb j hj,
      show G.Adj (D i.val) b ↔ G.Adj b (D i.val) from G.adj_comm (D i.val) b,
      hb i.val hi]
    constructor
    · rintro ⟨-, hm⟩; exact (hmeetRB i.val hi).mp hm
    · intro h; exact ⟨hneRB i.val hi, (hmeetRB i.val hi).mpr h⟩
  have kAB : ∀ i j : Fin (n + 2), i.val = n → j.val = n + 1 →
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j hi hj
    rw [hψa i hi, hψb j hj, hφa i hi, hφb j hj]
    constructor
    · rintro ⟨-, hm⟩; exact absurd hm hmeetAB
    · intro h; exact absurd h hab
  have hkey : ∀ i j : Fin (n + 2),
      ((ψ i ≠ ψ j ∧ ∃ v : Fin n, v ∈ ψ i ∧ v ∈ ψ j) ↔ G.Adj (φ i) (φ j)) := by
    intro i j
    rcases hcases i with hi | hi | hi <;> rcases hcases j with hj | hj | hj
    · exact kRR i j hi hj
    · exact kRA i j hi hj
    · exact kRB i j hi hj
    · exact hsymm j i (kRA j i hj hi)
    · exact kAA i j (by omega)
    · exact kAB i j hi hj
    · exact hsymm j i (kRB j i hj hi)
    · exact hsymm j i (kAB j i hj hi)
    · exact kAA i j (by omega)
  -- `φ` is a bijection onto `V(C) ∪ {a,b}`.
  have hrimC : ∀ i : Fin (n + 2), i.val < n → φ i ∈ C := by
    intro i h
    rw [hφr i h, hDC i.val (by omega)]
    exact List.getElem_mem _
  have hφmem : ∀ i : Fin (n + 2), φ i ∈ ({w : V | w ∈ C} ∪ {a, b} : Set V) := by
    intro i
    rcases hcases i with h | h | h
    · exact Or.inl (hrimC i h)
    · exact Or.inr (by simp [hφa i h])
    · exact Or.inr (by simp [hφb i h])
  have hφinj : Function.Injective φ := by
    intro i j hij
    apply Fin.val_injective
    rcases hcases i with hi | hi | hi <;> rcases hcases j with hj | hj | hj
    · have h1 : C[i.val]'(by omega) = C[j.val]'(by omega) := by
        rw [← hDC i.val (by omega), ← hDC j.val (by omega), ← hφr i hi, ← hφr j hj]; exact hij
      exact (List.Nodup.getElem_inj_iff hC.2.1).mp h1
    · exfalso; apply haC; have h := hrimC i hi; rw [hij, hφa j hj] at h; exact h
    · exfalso; apply hbC; have h := hrimC i hi; rw [hij, hφb j hj] at h; exact h
    · exfalso; apply haC; have h := hrimC j hj; rw [← hij, hφa i hi] at h; exact h
    · omega
    · exfalso; apply hne; rw [← hφa i hi, ← hφb j hj]; exact hij
    · exfalso; apply hbC; have h := hrimC j hj; rw [← hij, hφb i hi] at h; exact h
    · exfalso; apply hne; rw [← hφa j hj, ← hφb i hi]; exact hij.symm
    · omega
  have hφsurj : ∀ x : V, x ∈ ({w : V | w ∈ C} ∪ {a, b} : Set V) → ∃ i : Fin (n + 2), φ i = x := by
    intro x hx
    rcases hx with hx | hx
    · obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
      have hkn : k < n := by omega
      exact ⟨⟨k, by omega⟩, (hφr ⟨k, by omega⟩ hkn).trans ((hDC k hk).trans hkx)⟩
    · rcases hx with hx | hx
      · exact ⟨⟨n, by omega⟩, (hφa ⟨n, by omega⟩ rfl).trans hx.symm⟩
      · exact ⟨⟨n + 1, by omega⟩, (hφb ⟨n + 1, by omega⟩ rfl).trans
          (Set.mem_singleton_iff.mp hx).symm⟩
  -- `ψ` is a bijection onto `E(Hg)`.
  have hψE : ∀ i : Fin (n + 2), ψ i ∈ (Hg n P R Q).edgeSet := by
    intro i
    rcases hcases i with h | h | h
    · rw [hψr i h, SimpleGraph.mem_edgeSet]; exact cyc_adj_succ (by omega) i.val
    · rw [hψa i h, SimpleGraph.mem_edgeSet]; exact chord_one_adj h0R hRP hPQ hQn
    · rw [hψb i h, SimpleGraph.mem_edgeSet]; exact chord_two_adj h0R hRP hPQ hQn
  have hψinj : Function.Injective ψ := by
    intro i j hij
    apply Fin.val_injective
    rcases hcases i with hi | hi | hi <;> rcases hcases j with hj | hj | hj
    · by_contra hc
      rw [hψr i hi, hψr j hj] at hij
      exact hneRR i.val j.val hi hj hc hij
    · exfalso; rw [hψr i hi, hψa j hj] at hij; exact hneRA i.val hi hij
    · exfalso; rw [hψr i hi, hψb j hj] at hij; exact hneRB i.val hi hij
    · exfalso; rw [hψa i hi, hψr j hj] at hij; exact hneRA j.val hj hij.symm
    · omega
    · exfalso; rw [hψa i hi, hψb j hj] at hij; exact hneAB hij
    · exfalso; rw [hψb i hi, hψr j hj] at hij; exact hneRB j.val hj hij.symm
    · exfalso; rw [hψb i hi, hψa j hj] at hij; exact hneAB hij.symm
    · omega
  have hψsurj : ∀ e : Sym2 (Fin n), e ∈ (Hg n P R Q).edgeSet → ∃ i : Fin (n + 2), ψ i = e := by
    intro e
    induction e using Sym2.ind with
    | _ p q =>
      intro he
      rcases Hg_edge_cases h0R hRP hPQ hQn ((SimpleGraph.mem_edgeSet _).mp he) with
        ⟨k, hk, hEq⟩ | hEq | hEq
      · refine ⟨⟨k, by omega⟩, ?_⟩
        have hlt : (⟨k, by omega⟩ : Fin (n + 2)).val < n := hk
        exact (hψr _ hlt).trans hEq.symm
      · exact ⟨⟨n, by omega⟩, (hψa ⟨n, by omega⟩ rfl).trans hEq.symm⟩
      · exact ⟨⟨n + 1, by omega⟩, (hψb ⟨n + 1, by omega⟩ rfl).trans hEq.symm⟩
  -- Package the two indexings as bijections of the two vertex types.
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Fin (n + 2) → ({w : V | w ∈ C} ∪ {a, b} : Set V),
      ∀ i, (Φ i).val = φ i := ⟨fun i => ⟨φ i, hφmem i⟩, fun _ => rfl⟩
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : Fin (n + 2) → ((Hg n P R Q).edgeSet),
      ∀ i, (Ψ i).val = ψ i := ⟨fun i => ⟨ψ i, hψE i⟩, fun _ => rfl⟩
  have hΦbij : Function.Bijective Φ := by
    constructor
    · intro i j hij
      exact hφinj (by rw [← hΦ i, ← hΦ j, hij])
    · rintro ⟨x, hx⟩
      obtain ⟨i, hi⟩ := hφsurj x hx
      exact ⟨i, Subtype.ext (by rw [hΦ i]; exact hi)⟩
  have hΨbij : Function.Bijective Ψ := by
    constructor
    · intro i j hij
      exact hψinj (by rw [← hΨ i, ← hΨ j, hij])
    · rintro ⟨e, he⟩
      obtain ⟨i, hi⟩ := hψsurj e he
      exact ⟨i, Subtype.ext (by rw [hΨ i]; exact hi)⟩
  refine ⟨⟨(Equiv.ofBijective Φ hΦbij).symm.trans (Equiv.ofBijective Ψ hΨbij), ?_⟩⟩
  intro x y
  obtain ⟨i, rfl⟩ : ∃ i, Φ i = x := hΦbij.2 x
  obtain ⟨j, rfl⟩ : ∃ j, Φ j = y := hΦbij.2 y
  have hi : (Equiv.ofBijective Φ hΦbij).symm (Φ i) = i :=
    (Equiv.ofBijective Φ hΦbij).symm_apply_apply i
  have hj : (Equiv.ofBijective Φ hΦbij).symm (Φ j) = j :=
    (Equiv.ofBijective Φ hΦbij).symm_apply_apply j
  show (Hg n P R Q).lineGraph.Adj (Ψ ((Equiv.ofBijective Φ hΦbij).symm (Φ i)))
      (Ψ ((Equiv.ofBijective Φ hΦbij).symm (Φ j))) ↔ G.Adj ((Φ i : V)) ((Φ j : V))
  rw [hi, hj, hΦ i, hΦ j, SimpleGraph.lineGraph_adj_iff_exists]
  have hne' : (Ψ i ≠ Ψ j) ↔ (ψ i ≠ ψ j) := by
    constructor
    · intro h hc; exact h (Subtype.ext (by rw [hΨ i, hΨ j, hc]))
    · intro h hc; exact h (by rw [← hΨ i, ← hΨ j, hc])
  rw [hne', hΨ i, hΨ j]
  exact hkey i j

/-! ## The main export -/

/-- **A hole with these two "crossing" chord-pairs cannot occur in a graph of `F₃`.**

The last paragraph of the proof of 16.1 (printed p. 97): *"But then `G|(V(C) ∪ {v,y})` is the
line graph of a bipartite subdivision of `K₄`, a contradiction."* -/
theorem not_inF3_of_two_chord_config {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : Workspace.Types.Classes.SPGT.InF3 G)
    {C : List V} {n P R Q : ℕ} {D : ℕ → V} {a b : V}
    (hC : IsHoleList G C) (hnn : C.length = n) (hneven : Even n)
    (hD : ∀ t : ℕ, C[t % C.length]? = some (D t))
    (h0R : 0 < R) (hRP : R < P) (hPQ : P < Q) (hQn : Q < n)
    (hPodd : ¬ Even P) (hRQodd : ¬ Even (R + (n - Q)))
    (haC : a ∉ C) (hbC : b ∉ C) (hne : a ≠ b) (hab : ¬ G.Adj a b)
    (ha : ∀ t, t < n → (G.Adj a (D t) ↔ (t = 0 ∨ t = n - 1 ∨ t = P - 1 ∨ t = P)))
    (hb : ∀ t, t < n → (G.Adj b (D t) ↔ (t = R - 1 ∨ t = R ∨ t = Q - 1 ∨ t = Q))) :
    False := by
  haveI : NeZero n := ⟨by omega⟩
  refine (hG.2 n (Hg n P R Q)
    (Hg_isBipartiteSubdivision h0R hRP hPQ hQn hneven hPodd hRQodd)).1
      ⟨({w : V | w ∈ C} ∪ {a, b}), ?_⟩
  exact exists_iso_lineGraph hC hnn hD h0R hRP hPQ hQn haC hbC hne hab ha hb

end Workspace.ProofLemmas.LineGraphK4Chords
