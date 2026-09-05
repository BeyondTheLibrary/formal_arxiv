import Workspace.ProofLemmas.Thm125Case2LeftStar
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PathGlue
import Workspace.Statements.S03.Thm_3_2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# The 3.2 configuration in case (2) of Theorem 12.5

This isolates the list-heavy middle paragraph of the printed proof.  The final dependency on
the general statement 3.2 is temporary until its identical local proof is supplied; no other
part of the case uses 3.2.
-/

namespace Workspace.ProofLemmas.Thm125Case2Geometry

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas.Thm125Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem drop_pathFrom {G : SimpleGraph V} {p : List V} {u w : V}
    (hp : IsPathFrom G p u w) {k : ℕ} (hk : k < p.length) :
    IsPathFrom G (p.drop k) (p[k]'hk) w :=
  ⟨Workspace.ProofLemmas.PathBasics.isPathList_drop hp.1 hk,
   by rw [List.head?_drop, List.getElem?_eq_getElem hk],
   by rw [List.getLast?_drop, if_neg (by omega)]; exact hp.2.2⟩

private theorem getElem_mem_drop_take {alpha : Type*} (l : List alpha)
    {d r n : ℕ} (hdr : d ≤ r) (hrn : r - d < n) (hr : r < l.length) :
    l[r]'hr ∈ (l.drop d).take n := by
  have hk : r - d < ((l.drop d).take n).length := by
    simp only [List.length_take, List.length_drop]
    exact Nat.lt_min.mpr ⟨hrn, by omega⟩
  have hm := List.getElem_mem hk
  rw [List.getElem_take, List.getElem_drop] at hm
  have he : l[d + (r - d)]'(by omega) = l[r]'hr :=
    Workspace.ProofLemmas.Thm114Aux.getElem_eq_index l _ _ (Nat.add_sub_of_le hdr)
  rwa [he] at hm

/-- The output of the 3.2 application in case (2).  The vertices `t-u-b₀` are the
minimal terminal segment of the old banister. -/
theorem geometry
    (G : SimpleGraph V)
    (hG : Berge G)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : StronglyMaximalStaircase G A C B a₀ R₀ b₀)
    (q : List V) (q₁ qk : V) (hq : IsAntipathFrom G q q₁ qk)
    (hqint : ∀ w ∈ interior q,
      LeftDiagonal G A C B a₀ R₀ b₀ w ∧ RightDiagonal G A C B a₀ R₀ b₀ w)
    (hq₁ : LeftDiagonal G A C B a₀ R₀ b₀ q₁ ∧
      ¬ RightDiagonal G A C B a₀ R₀ b₀ q₁)
    (hqk : RightDiagonal G A C B a₀ R₀ b₀ qk ∧
      ¬ LeftDiagonal G A C B a₀ R₀ b₀ qk)
    (hleft : IsLeftStar G A C B q₁)
    (hqa₀ : G.Adj q₁ a₀)
    (hqodd : Odd q.length)
    (hcomplete : ∃ t ∈ interior R₀, VertexComplete G t {z : V | z ∈ q})
    (hqkb₀ : ¬ G.Adj qk b₀)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hqka₁ : G.Adj qk a₁) :
    ∃ t u : V,
      t ∈ interior R₀ ∧ u ∈ interior R₀ ∧ G.Adj t u ∧ G.Adj u b₀ ∧
      ¬ G.Adj t b₀ ∧ VertexComplete G t {z : V | z ∈ q} ∧
      VertexComplete G u {z : V | z ∈ q ∧ z ≠ q₁} ∧ ¬ G.Adj u q₁ ∧
      pathLength R₁ = 1 := by
  classical
  let Q : Set V := {z : V | z ∈ q}
  have hstair : IsStaircase G A C B a₀ R₀ b₀ := hK.1.1
  have hS := hstair.1
  have hban := hstair.2.1
  have hne : q₁ ≠ qk := endpoint_ne hq hq₁ hqk
  have hq2 : 2 ≤ q.length := by
    have hpos := Workspace.ProofLemmas.PathBasics.path_length_pos hq.1
    by_contra hc
    have hlen : q.length = 1 := by omega
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlen
    have h1 : x = q₁ := by simpa using hq.2.1
    have hk : x = qk := by simpa using hq.2.2
    exact hne (h1.symm.trans hk)

  -- Choose the last `Q`-complete position on `R₀`.
  obtain ⟨t', ht'int, ht'Q⟩ := hcomplete
  obtain ⟨it, hit, hitt⟩ := List.getElem_of_mem
    (Workspace.ProofLemmas.PathBasics.interior_subset ht'int)
  have hposComplete : ∃ k : ℕ, ∃ hk : k < R₀.length,
      VertexComplete G (R₀[k]'hk) Q := ⟨it, hit, by simpa [Q, hitt] using ht'Q⟩
  have hrevComplete : ∃ j : ℕ, ∃ hj : j < R₀.length,
      VertexComplete G (R₀[R₀.length - 1 - j]'(by omega)) Q := by
    refine ⟨R₀.length - 1 - it, by omega, ?_⟩
    have he : R₀.length - 1 - (R₀.length - 1 - it) = it := by omega
    simpa [he] using (show VertexComplete G (R₀[it]'hit) Q from
      (by simpa [Q, hitt] using ht'Q))
  let j : ℕ := Nat.find hrevComplete
  obtain ⟨hj, hjQ⟩ := Nat.find_spec hrevComplete
  let i : ℕ := R₀.length - 1 - j
  have hi : i < R₀.length := by omega
  have hiQ : VertexComplete G (R₀[i]'hi) Q := by simpa [i] using hjQ
  have hiMax : ∀ k : ℕ, ∀ hk : k < R₀.length, i < k →
      ¬ VertexComplete G (R₀[k]'hk) Q := by
    intro k hk hik hkQ
    refine Nat.find_min hrevComplete (m := R₀.length - 1 - k) (by simp [j, i] at hik; omega)
      ⟨by omega, ?_⟩
    have he : R₀.length - 1 - (R₀.length - 1 - k) = k := by omega
    simpa [he] using hkQ
  have hb₀notQ : ¬ VertexComplete G b₀ Q := by
    intro hbQ
    exact hqkb₀ (hbQ qk (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2)).symm
  have hiLast : i < R₀.length - 1 := by
    by_contra hc
    have hilast : i = R₀.length - 1 := by omega
    have hlast : R₀[R₀.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
    apply hb₀notQ
    simpa [hilast, hlast] using hiQ
  have hitPos : 0 < it := by
    by_contra hc
    have hi0 : it = 0 := by omega
    have hzero : R₀[0]'(by omega) = a₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
    have : t' = a₀ := by
      calc
        t' = R₀[it]'hit := hitt.symm
        _ = R₀[0]'(by omega) := by simp [hi0]
        _ = a₀ := hzero
    exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 ht'int |>.2.1 this
  have hitLe : it ≤ i := by
    by_contra hc
    exact hiMax it hit (by omega) (by simpa [Q, hitt] using ht'Q)
  have hiPos : 0 < i := lt_of_lt_of_le hitPos hitLe

  let t : V := R₀[i]'hi
  let T : List V := R₀.drop i
  have hT : IsPathFrom G T t b₀ := by
    dsimp [T, t]
    exact drop_pathFrom hban.1 hi
  have hTlen : T.length = R₀.length - i := by simp [T]
  have htint : t ∈ interior R₀ :=
    Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1 hi hiPos (by omega)
  have htQ : VertexComplete G t Q := by simpa [t] using hiQ
  have hTuniq : ∀ x ∈ T, VertexComplete G x Q → x = t := by
    intro x hx hxQ
    obtain ⟨k, hk, hkx⟩ := List.getElem_of_mem hx
    have hik : i + k < R₀.length := by
      have hk' : k < R₀.length - i := by simpa [T] using hk
      omega
    have hget : T[k]'hk = R₀[i + k]'hik := by simpa [T] using (List.getElem_drop (xs := R₀))
    by_cases hk0 : k = 0
    · subst k
      calc
        x = T[0]'hk := hkx.symm
        _ = R₀[i]'hi := by simpa using hget
        _ = t := rfl
    · exact (hiMax (i + k) hik (by omega) (by
        simpa [← hkx, ← hget] using hxQ)).elim
  have ha₀T : a₀ ∉ T := by
    intro haT
    have haQ := hTuniq a₀ haT (by
      intro z hz
      by_cases hz₁ : z = q₁
      · simpa [hz₁] using hqa₀.symm
      · exact ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hz hz₁).2 a₀
          (Or.inr rfl)).symm)
    exact (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban.1).1 htint |>.2.1
      haQ.symm

  have hR₁rev : IsPathFrom G R₁.reverse b₁ a₁ :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hstep.1.1
  have hform := Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step
    hban hstep
  have hcross₁₀ : ∀ y ∈ R₁, ∀ x ∈ R₀,
      (G.Adj y x ↔ (y = a₁ ∧ x = a₀) ∨ (y = b₁ ∧ x = b₀)) := by
    simpa using hform.2.2.2.2.2.2.2.1
  have hTRdisj : ∀ x ∈ T, x ∉ R₁.reverse := by
    intro x hxT hxR
    have hxR₀ : x ∈ R₀ := List.mem_of_mem_drop (by simpa [T] using hxT)
    have hxS := Workspace.ProofLemmas.Thm114Aux.rung_mem_strip hstep.1 x
      (List.mem_reverse.1 hxR)
    exact hban.2.1 x hxR₀ hxS
  have hTRcross : ∀ x ∈ T, ∀ y ∈ R₁.reverse,
      (G.Adj x y ↔ x = b₀ ∧ y = b₁) := by
    intro x hxT y hyR
    have hxR₀ : x ∈ R₀ := List.mem_of_mem_drop (by simpa [T] using hxT)
    have hyR₁ : y ∈ R₁ := List.mem_reverse.1 hyR
    rw [SimpleGraph.adj_comm, hcross₁₀ y hyR₁ x hxR₀]
    constructor
    · rintro (⟨-, hxa⟩ | h)
      · exfalso
        exact ha₀T (hxa ▸ hxT)
      · exact ⟨h.2, h.1⟩
    · rintro ⟨rfl, rfl⟩
      exact Or.inr ⟨rfl, rfl⟩
  let p : List V := T ++ R₁.reverse
  have hp : IsPathFrom G p t a₁ := by
    dsimp [p]
    exact Workspace.ProofLemmas.PathGlue.glue_path hT hR₁rev hTRdisj hTRcross
  let m := p.length
  let n := q.length
  let s := T.length
  have hR₁len2 : 2 ≤ R₁.length := by
    have hab : a₁ ≠ b₁ := fun he =>
      Set.disjoint_left.mp hS.1.1 hstep.1.2.1 (he ▸ hstep.1.2.2.1)
    exact Workspace.ProofLemmas.Thm114Aux.len_ge_two hstep.1.1 hab
  have hs1 : 2 ≤ s := by simp [s, hTlen]; omega
  have hs2 : s ≤ m - 2 := by simp [s, m, p]; omega
  have hpSm1 : p[s - 1]'(by simp [s, m, p]; omega) = b₀ := by
    have hl : T[T.length - 1]'(by omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hT.2.2 (by omega)
    simpa [p, s] using (show p[T.length - 1]'(by simp [p]; omega) = b₀ by
      rw [List.getElem_append_left (by omega)]
      exact hl)
  have hpS : p[s]'(by simp [s, m, p]; omega) = b₁ := by
    have h0 : R₁.reverse[0]'(by simp; omega) = b₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hR₁rev.2.1 (by simp; omega)
    dsimp [p, s]
    rw [List.getElem_append_right (le_refl T.length)]
    simpa only [Nat.sub_self] using h0

  let qr : List V := q.reverse
  have hqr : IsAntipathFrom G qr qk q₁ := by
    dsimp [qr]
    exact Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq
  have hb₀qkc : Gᶜ.Adj b₀ qk := (G.compl_adj b₀ qk).2
    ⟨fun he => outside_of_mem hq hqint hq₁.1 hqk.1
      (Workspace.ProofLemmas.PathBasics.getLast_mem hq.2.2)
      (Or.inl (he ▸ Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)),
      fun h => hqkb₀ h.symm⟩
  have hb₁q₁n : ¬ G.Adj b₁ q₁ := fun h =>
    hleft.2.2 b₁ (Or.inl hstep.1.2.2.1) h.symm
  have hb₁q₁ne : b₁ ≠ q₁ := fun he => hleft.1
    (Or.inl (Or.inr (he.symm ▸ hstep.1.2.2.1)))
  have hb₁q₁c : Gᶜ.Adj b₁ q₁ := (G.compl_adj b₁ q₁).2 ⟨hb₁q₁ne, hb₁q₁n⟩
  have hb₀b₁ : G.Adj b₀ b₁ := hban.2.2.2.1.2.1 b₁ hstep.1.2.2.1
  have hb₀qr : b₀ ∉ qr := by
    intro h
    have hqmem : b₀ ∈ q := List.mem_reverse.1 (by simpa [qr] using h)
    exact outside_of_mem hq hqint hq₁.1 hqk.1 hqmem
      (Or.inl (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2))
  have hb₁qr : b₁ ∉ qr := by
    intro h
    have hqmem : b₁ ∈ q := List.mem_reverse.1 (by simpa [qr] using h)
    exact outside_of_mem hq hqint hq₁.1 hqk.1 hqmem
      (Or.inr (Or.inl (Or.inr hstep.1.2.2.1)))
  have hb₀other : ∀ x ∈ qr, x ≠ qk → ¬ Gᶜ.Adj b₀ x := by
    intro x hx hxk hc
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact hc.2 ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hxq hxk).2 b₀
      (Or.inr rfl)).symm
  have hb₁other : ∀ x ∈ qr, x ≠ q₁ → ¬ Gᶜ.Adj b₁ x := by
    intro x hx hx₁ hc
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact hc.2 ((rightDiagonal_of_mem_ne_first hq hqint hqk.1 hxq hx₁).2 b₁
      (Or.inl hstep.1.2.2.1)).symm
  let anti : List V := b₀ :: (qr ++ [b₁])
  have hanti : IsAntipathFrom G anti b₀ b₁ := by
    dsimp [anti]
    exact Workspace.ProofLemmas.PathAttach.isPathFrom_cons_concat hqr hb₀qkc hb₁q₁c
      (fun hc => hc.2 hb₀b₁) hb₀b₁.ne hb₀qr hb₁qr hb₀other hb₁other
  have hantiIdx : IsAntipathFrom G
      (p[s - 1] :: (qr ++ [p[s]])) p[s - 1] p[s] := by
    simpa only [hpSm1, hpS] using hanti

  have ha₁Q : VertexComplete G a₁ Q := by
    intro z hz
    by_cases hzk : z = qk
    · simpa [hzk] using hqka₁.symm
    · exact ((leftDiagonal_of_mem_ne_last hq hqint hq₁.1 hz hzk).2 a₁
        (Or.inl hstep.1.2.1)).symm
  have htTake : t ∈ p.take (s - 1) := by
    have htakeHead : (p.take (s - 1)).head? = some t := by
      rw [List.head?_take, if_neg (by simp [s]; omega)]
      exact hp.2.1
    exact Workspace.ProofLemmas.PathBasics.head_mem htakeHead
  have ha₁Drop : a₁ ∈ p.drop (s + 1) := by
    have haRev : a₁ ∈ R₁.reverse.tail := by
      have haMem : a₁ ∈ R₁.reverse :=
        Workspace.ProofLemmas.PathBasics.getLast_mem hR₁rev.2.2
      have hhead : R₁.reverse.head? = some b₁ := hR₁rev.2.1
      have hbhead : b₁ ∈ R₁.reverse.head? := by rw [hhead]; simp
      have hcons : b₁ :: R₁.reverse.tail = R₁.reverse := List.cons_head?_tail hbhead
      have hcases : a₁ = b₁ ∨ a₁ ∈ R₁.reverse.tail := by
        rw [← hcons] at haMem
        simpa using haMem
      exact hcases.resolve_left (fun he =>
        Set.disjoint_left.mp hS.1.1 hstep.1.2.1 (he ▸ hstep.1.2.2.1))
    have hdropT : T.drop (T.length + 1) = [] :=
      List.drop_eq_nil_of_le (by omega)
    simpa [p, s, List.drop_append, hdropT] using haRev
  have hqleft : ∀ x ∈ qr, ∃ y ∈ p.take (s - 1), G.Adj x y := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact ⟨t, htTake, (htQ x hxq).symm⟩
  have hqright : ∀ x ∈ qr, ∃ y ∈ p.drop (s + 1), G.Adj x y := by
    intro x hx
    have hxq : x ∈ q := List.mem_reverse.1 (by simpa [qr] using hx)
    exact ⟨a₁, ha₁Drop, (ha₁Q x hxq).symm⟩
  have h32 := Workspace.Statements.S03.SPGT.thm_3_2 G hG m n s p qr hp.1 rfl hs1 hs2
    (by simp [n, qr]) (by simpa [n] using hq2) (by simpa [n] using hqodd)
    hantiIdx hqleft hqright

  -- The alternative extending two vertices into `R₁` would make `q₁` adjacent to an
  -- interior vertex of that rung, contrary to `q₁` being a left-star.
  rcases h32 with hfirst | hsecond
  · rcases hfirst with ⟨hs3, hrel⟩
    have hslt : s < p.length := by
      dsimp [m] at hs2
      omega
    have hsm3lt : s - 3 < p.length := by omega
    let x₀ : V := p[s - 3]'hsm3lt
    have hx₀win : x₀ ∈ (p.drop (s - 3)).take 5 := by
      dsimp [x₀]
      exact getElem_mem_drop_take p (le_refl _) (by omega) hsm3lt
    have hx₀Q : VertexComplete G x₀ Q := by
      intro z hzq
      have hzqr : z ∈ qr := by simpa [qr] using hzq
      by_contra hn
      rcases (hrel x₀ hx₀win z hzqr).1 hn with h | h | h
      · have he : p[s - 3]'hsm3lt = p[s - 2]'(by omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s - 3]'hsm3lt = p[s - 1]'(by omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s - 3]'hsm3lt = p[s]'hslt := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
    have hx₀T : x₀ ∈ T := by
      dsimp [x₀, p, s]
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem (by omega)
    have hx₀t : x₀ = t := hTuniq x₀ hx₀T hx₀Q
    have hp0 : p[0]'(by omega) = t :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hp.2.1 (by omega)
    have hsEq : s = 3 := by
      have he : p[s - 3]'hsm3lt = p[0]'(by omega) := hx₀t.trans hp0.symm
      have := hp.1.2.1.getElem_inj_iff.mp he
      omega

    have hs1lt : s + 1 < p.length := by omega
    let x₄ : V := p[s + 1]'hs1lt
    have hx₄win : x₄ ∈ (p.drop (s - 3)).take 5 := by
      dsimp [x₄]
      exact getElem_mem_drop_take p (by omega) (by omega) hs1lt
    have hx₄Q : VertexComplete G x₄ Q := by
      intro z hzq
      have hzqr : z ∈ qr := by simpa [qr] using hzq
      by_contra hn
      rcases (hrel x₄ hx₄win z hzqr).1 hn with h | h | h
      · have he : p[s + 1]'hs1lt = p[s - 2]'(by omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s + 1]'hs1lt = p[s - 1]'(by omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s + 1]'hs1lt = p[s]'hslt := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
    have hx₄rev : x₄ ∈ R₁.reverse := by
      have hRrev : 1 < R₁.reverse.length := by simpa using hR₁len2
      dsimp [x₄, p, s]
      rw [List.getElem_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using (List.getElem_mem hRrev)
    have hx₄R₁ : x₄ ∈ R₁ := List.mem_reverse.1 hx₄rev
    have hx₄b₁ : x₄ ≠ b₁ := by
      intro he
      have he' : p[s + 1]'hs1lt = p[s]'hslt := by simpa [x₄, hpS] using he
      have := hp.1.2.1.getElem_inj_iff.mp he'
      omega
    have hx₄a₁ : x₄ = a₁ := by
      by_contra hne₄
      have hxint : x₄ ∈ interior R₁ :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hstep.1.1).2
          ⟨hx₄R₁, hne₄, hx₄b₁⟩
      have hxC : x₄ ∈ C := hstep.1.2.2.2.2.2 x₄ hxint
      have hxq₁ : G.Adj x₄ q₁ := hx₄Q q₁
        (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)
      exact hleft.2.2 x₄ (Or.inr hxC) hxq₁.symm
    have hplast : p[p.length - 1]'(by omega) = a₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
    have hlastIdx : s + 1 = p.length - 1 := by
      apply hp.1.2.1.getElem_inj_iff.mp
      exact hx₄a₁.trans hplast.symm
    have hR₁len : R₁.length = 2 := by
      dsimp [p, s] at hlastIdx
      simp only [List.length_append, List.length_reverse] at hlastIdx
      omega

    have hsm2lt : s - 2 < p.length := by omega
    let u : V := p[s - 2]'hsm2lt
    have huwin : u ∈ (p.drop (s - 3)).take 5 := by
      dsimp [u]
      exact getElem_mem_drop_take p (by omega) (by omega) hsm2lt
    have hqrLast : qr[n - 1]'(by simp [qr, n]; omega) = q₁ := by
      have hl : qr[qr.length - 1]'(by simp [qr, n]; omega) = q₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hqr.2.2
          (by simp [qr, n]; omega)
      exact (Workspace.ProofLemmas.Thm114Aux.getElem_eq_index qr _ _
        (by simp [qr, n])).trans hl
    have hq₁qr : q₁ ∈ qr := by
      simpa [qr] using (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)
    have huq₁ : ¬ G.Adj u q₁ := by
      apply (hrel u huwin q₁ hq₁qr).2
      exact Or.inl ⟨rfl, hqrLast.symm⟩
    have huQ : VertexComplete G u {z : V | z ∈ q ∧ z ≠ q₁} := by
      intro z hz
      have hzqr : z ∈ qr := by simpa [qr] using hz.1
      by_contra hn
      rcases (hrel u huwin z hzqr).1 hn with h | h | h
      · exact hz.2 (h.2.trans hqrLast)
      · have he : p[s - 2]'hsm2lt = p[s - 1]'(by omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s - 2]'hsm2lt = p[s]'hslt := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
    have huT : u = T[1]'(by dsimp [s] at hsEq; omega) := by
      dsimp [u, p, s]
      rw [List.getElem_append_left (by omega)]
      exact Workspace.ProofLemmas.Thm114Aux.getElem_eq_index T _ _ (by omega)
    have hi1 : i + 1 < R₀.length := by
      dsimp [s] at hsEq
      omega
    have huR₀ : u = R₀[i + 1]'hi1 := by
      rw [huT]
      exact List.getElem_drop
    have huit : u ∈ interior R₀ := by
      rw [huR₀]
      apply Workspace.ProofLemmas.PathBasics.getElem_mem_interior hban.1.1 hi1
      · omega
      · dsimp [s] at hsEq
        omega
    have hT0 : T[0]'(by dsimp [s] at hsEq; omega) = t :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hT.2.1
        (by dsimp [s] at hsEq; omega)
    have hTlast : T[T.length - 1]'(by dsimp [s] at hsEq; omega) = b₀ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hT.2.2
        (by dsimp [s] at hsEq; omega)
    have hT2 : T[2]'(by dsimp [s] at hsEq; omega) = b₀ := by
      exact (Workspace.ProofLemmas.Thm114Aux.getElem_eq_index T _ _
        (by dsimp [s] at hsEq; omega)).trans hTlast
    have htu : G.Adj t u := by
      have ha := Workspace.ProofLemmas.PathBasics.path_adj_succ hT.1
        (i := 0) (by dsimp [s] at hsEq; omega)
      rw [hT0, ← huT] at ha
      simpa using ha
    have hub₀ : G.Adj u b₀ := by
      have ha := Workspace.ProofLemmas.PathBasics.path_adj_succ hT.1
        (i := 1) (by dsimp [s] at hsEq; omega)
      rw [← huT, hT2] at ha
      simpa using ha
    have htb₀ : ¬ G.Adj t b₀ := by
      have hn := Workspace.ProofLemmas.PathBasics.path_ends_not_adj hT.1
        (by dsimp [s] at hsEq; omega)
      simpa [hT0, hTlast] using hn
    have hlenR₁ : pathLength R₁ = 1 := by
      rw [Workspace.ProofLemmas.PathBasics.pathLength_eq, hR₁len]
    exact ⟨t, u, htint, huit, htu, hub₀, htb₀, by simpa [Q] using htQ,
      huQ, huq₁, hlenR₁⟩
  · rcases hsecond with ⟨hsm3, hrel⟩
    have hs1p : s + 1 < p.length := by
      dsimp [m] at hsm3
      omega
    let x : V := p[s + 1]'hs1p
    have hxwin : x ∈ (p.drop (s - 2)).take 5 := by
      dsimp [x]
      exact getElem_mem_drop_take p (by omega) (by omega) hs1p
    have hxrev : x ∈ R₁.reverse := by
      have hRrev : 1 < R₁.reverse.length := by
        dsimp [m, p, s] at hsm3
        simp only [List.length_append, List.length_reverse] at hsm3 ⊢
        omega
      dsimp [x, p, s]
      rw [List.getElem_append_right (by omega)]
      simpa only [Nat.add_sub_cancel_left] using (List.getElem_mem hRrev)
    have hxR₁ : x ∈ R₁ := List.mem_reverse.1 hxrev
    have hplast : p[p.length - 1]'(by omega) = a₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hp.2.2 (by omega)
    have hxb₁ : x ≠ b₁ := by
      intro he
      have he' : p[s + 1]'hs1p = p[s]'(by dsimp [m] at hsm3; omega) := by
        simpa [x, hpS] using he
      have := hp.1.2.1.getElem_inj_iff.mp he'
      omega
    have hxa₁ : x ≠ a₁ := by
      intro he
      have he' : p[s + 1]'hs1p = p[p.length - 1]'(by omega) := by
        exact he.trans hplast.symm
      have := hp.1.2.1.getElem_inj_iff.mp he'
      dsimp [m] at hsm3
      omega
    have hxint : x ∈ interior R₁ :=
      (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hstep.1.1).2
        ⟨hxR₁, hxa₁, hxb₁⟩
    have hxC : x ∈ C := hstep.1.2.2.2.2.2 x hxint
    have hq₁qr : q₁ ∈ qr := by
      simpa [qr] using (Workspace.ProofLemmas.PathBasics.head_mem hq.2.1)
    have hqr0 : qr[0]'(by simp [qr]; omega) = qk :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hqr.2.1 (by simp [qr]; omega)
    have hxq₁ : G.Adj x q₁ := by
      by_contra hn
      rcases (hrel x hxwin q₁ hq₁qr).1 hn with h | h | h
      · have he : p[s + 1]'hs1p = p[s - 1]'(by dsimp [m] at hsm3; omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · have he : p[s + 1]'hs1p = p[s]'(by dsimp [m] at hsm3; omega) := h.1
        have := hp.1.2.1.getElem_inj_iff.mp he
        omega
      · exact hne (h.2.trans hqr0)
    exact (hleft.2.2 x (Or.inr hxC) hxq₁.symm).elim

end Workspace.ProofLemmas.Thm125Case2Geometry
