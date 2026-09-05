import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.Statements.S18.Thm_18_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.Thm186Setup
import Workspace.ProofLemmas.Thm186HoleThroughF

/-!
# 18.6, closing paragraph

PAPER (`paper/proofs/18_6.md`, published page 114):

> *"Choose `b` with `1 ≤ b ≤ n` maximum such that `p_b` is `Y`-complete.  By (2), none of
> `p₂, …, p_{b−1}` are attachments of `F`, and since `F` is a counterexample, it follows that
> `p₁` is an attachment of `F` and also there exists `c` with `b ≤ c ≤ n` such that `p_c` is an
> attachment of `F`.  Choose `c` with `c` minimum, and let `Q` be a path between `p₁, p_c` with
> interior in `F`.  Then `p₁-⋯-p_c-Q-p₁` is a hole, and the `Y`-complete edges in it are
> precisely the `Y`-complete edges in `P`.  But there are an odd number of such edges and at
> least `3`, by 18.4, contrary to 2.3.  Thus there is no such `F`.  This proves 18.6."*

Gaps the paper leaves implicit and that are filled here:

* *"since `F` is a counterexample, it follows that `p₁` is an attachment"* — if it were not,
  every attachment would lie in `{p_b, …, p_n}` by (2) and the maximality of `b`, and
  `P' = p_b-⋯-p_n` would satisfy all three bullets (its interior `p_{b+1}, …, p_{n−1}` carries no
  `Y`-complete vertex by maximality of `b`, and `p_n ∈ V(P')`), so `F` would not be a
  counterexample;
* *"and also there exists `c` with `b ≤ c ≤ n`"* — otherwise every attachment is `p₁` and
  `P' = p₁` serves, with `V(P') = {p₁}`;
* *"the `Y`-complete edges in it are precisely the `Y`-complete edges in `P`"* — the edges of the
  hole inside `Q` have an end in `F`, and no vertex of `F` is `Y`-complete; and every
  `Y`-complete edge of `P` has both ends `Y`-complete, hence both of index `≤ b ≤ c`.

Tools for discharging the `sorry` below (kept out of the import list so that a statement-only
file stays cheap to elaborate; add them back when proving):
`Workspace.Statements.S18.Thm_18_4` (*"there are an odd number of such edges and at least 3, by
18.4"*), `Workspace.ProofLemmas.HoleYEdgeParity` (*"contrary to 2.3"* — see
`not_odd_ge_three_yEdges'`), `Workspace.ProofLemmas.Thm186HoleThroughF` (*"`p₁-⋯-p_c-Q-p₁` is a
hole"*), `Workspace.ProofLemmas.MinimalConnectedIsPath` (*"let `Q` be a path between `p₁, p_c`
with interior in `F`"* — see `exists_path_interior_attached`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm186Final

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm186Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Greatest index below `n` satisfying `Q`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ n : ℕ, (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  classical
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- Rewriting the index of a `getElem`.  Plain `rw` on the index equation gives
"motive is not type correct", because the bound proof mentions the index. -/
private theorem getElem_congr_idx (l : List V) {a b : ℕ} (h : a = b) (ha : a < l.length)
    (hb : b < l.length) : (l[a]'ha) = (l[b]'hb) := by
  subst h; rfl

/-- Every stretch of `p` is a contiguous block of `p`. -/
private theorem slice_infix (p : List V) (i m : ℕ) : (p.drop i).take m <:+: p := by
  refine ⟨p.take i, (p.drop i).drop m, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- **18.6, closing paragraph.**  Claim (2) plus the counterexample property produce the hole
`p₁-⋯-p_c-Q-p₁`, which carries an odd number `≥ 3` of `Y`-complete edges by 18.4 — contrary to
2.3. -/
theorem final_contradiction (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F)
    (hclaim2 : ¬ ∃ (a b : ℕ) (ha : a < P.length) (hb : b < P.length),
        0 < a ∧ a < b ∧ (P[a]'ha) ∈ attachments G F {w : V | w ∈ P} ∧
        VertexComplete G (P[b]'hb) Y) :
    False := by
  classical
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq, hq₁Y, hother, hq₂Y, hqₙY⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hBerge : Berge G := hG.1.1.1.1
  -- Orient these so that `subst` eliminates `q₁`/`qₙ` (the locally-obtained names) and keeps
  -- the theorem's own binders `p₁`/`pₙ`, which the rest of the argument refers to.
  have hq₁ : p₁ = q₁ := Option.some_injective _ (hhead.symm.trans hPfrom.2.1)
  have hqn : pₙ = qₙ := Option.some_injective _ (hlast.symm.trans hPfrom.2.2)
  subst q₁
  subst qₙ
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1 : P[1]'(show 1 < P.length by omega) = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hFP : ∀ f ∈ F, f ∉ P := fun f hf => (hmin.1.1 f hf).2
  have hFXY : ∀ f ∈ F, f ∉ X ∪ Y := fun f hf => (hmin.1.1 f hf).1
  have hFY : ∀ f ∈ F, ¬ VertexComplete G f Y := hmin.1.2.2
  -- ### *"Choose `b` with `1 ≤ b ≤ n` maximum such that `p_b` is `Y`-complete."*
  obtain ⟨v, hvP, hvne, hvY⟩ := hother
  obtain ⟨m, hm, hmv⟩ := List.getElem_of_mem hvP
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hvne (by rw [← hmv, hp0])
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact hq₂Y (by rw [← hp1, hmv]; exact hvY)
  obtain ⟨b, hblt, hbY', hbmax⟩ :=
    exists_greatest (Q := fun k => ∃ h : k < P.length, VertexComplete G (P[k]'h) Y)
      P.length ⟨m, hm, hm, by rw [hmv]; exact hvY⟩
  obtain ⟨hb', hbY⟩ := hbY'
  have hbm : m ≤ b := hbmax m hm ⟨hm, by rw [hmv]; exact hvY⟩
  have hb2 : 2 ≤ b := by omega
  have hbn : b ≠ P.length - 1 := by
    rintro rfl
    exact hqₙY (by rw [← hpn]; exact hbY)
  have hbn2 : b < P.length - 1 := by omega
  -- ### *"By (2), none of `p₂, …, p_{b−1}` are attachments of `F`."*
  have hnoatt_lt : ∀ (k : ℕ) (hk : k < P.length), 0 < k → k < b →
      (P[k]'hk) ∉ attachments G F {w : V | w ∈ P} := by
    intro k hk h1 h2 hcon
    exact hclaim2 ⟨k, b, hk, hb', h1, h2, hcon, hbY⟩
  -- ### *"it follows that `p₁` is an attachment of `F`"*
  have hp₁att : p₁ ∈ attachments G F {w : V | w ∈ P} := by
    by_contra hcon
    refine hmin.2.1 ⟨(P.drop b).take (P.length - 1 - b + 1),
      PathBasics.isPathList_slice hP hbn2 hnlt, slice_infix P _ _, ?_, ?_, ?_⟩
    · intro w hw
      obtain ⟨hwP, hwf⟩ := hw
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show w ∈ P from hwP)
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · exact absurd (by rw [← hp0]; exact ⟨hwP, hwf⟩) hcon
      · rcases Nat.lt_or_ge k b with hlt | hge
        · exact absurd ⟨hwP, hwf⟩ (hnoatt_lt k hk hkpos hlt)
        · exact (PathBasics.mem_slice_iff P (le_of_lt hbn2) hnlt).mpr ⟨k, hk, hge, by omega, rfl⟩
    · intro w hw hwY
      obtain ⟨k, hk, h1, h2, rfl⟩ := (PathBasics.mem_interior_slice_iff hP hbn2 hnlt).mp hw
      exact absurd (hbmax k hk ⟨hk, hwY⟩) (by omega)
    · intro _
      exact Or.inr ((PathBasics.mem_slice_iff P (le_of_lt hbn2) hnlt).mpr
        ⟨P.length - 1, hnlt, by omega, le_rfl, hpn⟩)
  -- ### *"and also there exists `c` with `b ≤ c ≤ n` such that `p_c` is an attachment of `F`"*
  have hexc : ∃ t : ℕ, ∃ h : b + t < P.length,
      (P[b + t]'h) ∈ attachments G F {w : V | w ∈ P} := by
    by_contra hcon
    push_neg at hcon
    refine hmin.2.1 ⟨[p₁], PathBasics.isPathList_singleton G p₁, ?_, ?_, ?_, ?_⟩
    · obtain ⟨s, t, hst⟩ := List.append_of_mem (PathBasics.head_mem hhead)
      exact ⟨s, t, by rw [hst]; simp⟩
    · intro w hw
      obtain ⟨hwP, hwf⟩ := hw
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show w ∈ P from hwP)
      rcases Nat.eq_zero_or_pos k with rfl | hkpos
      · rw [hp0]; simp
      · rcases Nat.lt_or_ge k b with hlt | hge
        · exact absurd ⟨hwP, hwf⟩ (hnoatt_lt k hk hkpos hlt)
        · exfalso
          have hcon' := hcon (k - b) (by omega)
          rw [getElem_congr_idx P (by omega : b + (k - b) = k) (by omega) hk] at hcon'
          exact hcon' ⟨hwP, hwf⟩
    · intro w hw
      simp [SPGT.interior] at hw
    · intro _
      exact Or.inl (by ext w; simp)
  obtain ⟨hclen, hcatt⟩ := Nat.find_spec hexc
  set c : ℕ := b + Nat.find hexc with hcdef
  have hcmin : ∀ (k : ℕ) (hk : k < P.length), b ≤ k → k < c →
      (P[k]'hk) ∉ attachments G F {w : V | w ∈ P} := by
    intro k hk h1 h2 hmem
    refine Nat.find_min hexc (m := k - b) (by omega) ?_
    refine ⟨by omega, ?_⟩
    rw [getElem_congr_idx P (by omega : b + (k - b) = k) (by omega) hk]
    exact hmem
  have hc2 : 2 ≤ c := by omega
  -- no attachment strictly between `p₁` and `p_c`
  have hnoatt : ∀ (k : ℕ) (hk : k < P.length), 0 < k → k < c →
      ∀ f ∈ F, ¬ G.Adj (P[k]'hk) f := by
    intro k hk h1 h2 f hf hadj
    rcases Nat.lt_or_ge k b with hlt | hge
    · exact hnoatt_lt k hk h1 hlt ⟨List.getElem_mem hk, f, hf, hadj⟩
    · exact hcmin k hk hge h2 ⟨List.getElem_mem hk, f, hf, hadj⟩
  -- ### *"let `Q` be a path between `p₁, p_c` with interior in `F`"*
  have hcne : p₁ ≠ (P[c]'hclen) := by
    rw [← hp0]
    exact PathBasics.path_ne_of_ne_index hP h0lt hclen (by omega)
  have hcnadj : ¬ G.Adj p₁ (P[c]'hclen) := by
    rw [← hp0]
    exact PathBasics.path_not_adj_of_gap hP h0lt hclen (by omega) (by omega)
  obtain ⟨Qp, hQfrom, hQ3, hQint, -, -, -⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hmin.1.2.1 hcne hcnadj
      (fun hcon => hFP p₁ hcon (PathBasics.head_mem hhead))
      (fun hcon => hFP _ hcon (List.getElem_mem hclen))
      (by obtain ⟨-, f, hf, hadj⟩ := hp₁att; exact ⟨f, hf, hadj⟩)
      (by obtain ⟨-, f, hf, hadj⟩ := hcatt; exact ⟨f, hf, hadj⟩)
  -- ### *"Then `p₁-⋯-p_c-Q-p₁` is a hole"*
  have hQfrom' : IsPathFrom G Qp (P[0]'h0lt) (P[c]'hclen) := by rw [hp0]; exact hQfrom
  have hCC : IsHoleList G (P.take (c + 1) ++ (SPGT.interior Qp).reverse) :=
    Thm186HoleThroughF.hole_through_F hP hFP hclen hc2 hQfrom' hQ3 hQint hnoatt
  have hCY : ∀ w ∈ P.take (c + 1) ++ (SPGT.interior Qp).reverse, w ∉ Y := by
    intro w hw
    rw [List.mem_append] at hw
    rcases hw with h | h
    · exact (hPXY w (List.mem_of_mem_take h)).2
    · rw [List.mem_reverse] at h
      exact fun hcon => hFXY _ (hQint _ h) (Set.mem_union_right _ hcon)
  -- ### *"the `Y`-complete edges in it are precisely the `Y`-complete edges in `P`"*
  have hyeq : HoleYEdgeParity.yEdges G Y (P.take (c + 1) ++ (SPGT.interior Qp).reverse)
      = HoleYEdgeParity.yEdges G Y P := by
    have hto : ∀ w ∈ P.take (c + 1) ++ (SPGT.interior Qp).reverse,
        VertexComplete G w Y → w ∈ P := by
      intro w hw hwY
      rw [List.mem_append] at hw
      rcases hw with h | h
      · exact List.mem_of_mem_take h
      · rw [List.mem_reverse] at h
        exact absurd hwY (hFY _ (hQint _ h))
    have hfrom : ∀ w ∈ P, VertexComplete G w Y →
        w ∈ P.take (c + 1) ++ (SPGT.interior Qp).reverse := by
      intro w hw hwY
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
      have hkb : k ≤ b := hbmax k hk ⟨hk, hwY⟩
      rw [List.mem_append]
      refine Or.inl ?_
      have hkl : k < (P.take (c + 1)).length := by rw [List.length_take]; omega
      have hget : (P.take (c + 1))[k]'hkl = P[k]'hk := by simp
      rw [← hget]
      exact List.getElem_mem hkl
    ext e
    constructor
    · rintro ⟨u, hu, w, hw, rfl, hadj, huY, hwY⟩
      exact ⟨u, hto u hu huY, w, hto w hw hwY, rfl, hadj, huY, hwY⟩
    · rintro ⟨u, hu, w, hw, rfl, hadj, huY, hwY⟩
      exact ⟨u, hfrom u hu huY, w, hfrom w hw hwY, rfl, hadj, huY, hwY⟩
  -- ### *"But there are an odd number of such edges and at least `3`, by 18.4, contrary to 2.3."*
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  refine HoleYEdgeParity.not_odd_ge_three_yEdges' hBerge hYanti hCC hCY ?_ ?_
  · rw [hyeq]; exact h184.1.1
  · rw [hyeq]; exact h184.1.2

end Workspace.ProofLemmas.Thm186Final
