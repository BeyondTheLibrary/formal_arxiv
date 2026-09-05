import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.StripSystems
import Workspace.ProofLemmas.Thm84BranchRungDictionaryAt
import Workspace.ProofLemmas.Thm84EveryChoiceFormsLineGraph

/-!
# 8.4, first paragraph: two choices of rungs differing on one edge, one saturated and one not

PAPER (printed p. 40, the proof of 8.4): *"Let us say that a choice of rungs `R_ij` forming a line
graph `L(H)` is saturated if `X` saturates `L(H)` … If every choice of rungs is saturated, then `X`
saturates the strip system as required, so we may therefore assume that there is some choice of
rungs that is not saturated.  **Hence there are two choices of rungs `R_ij` (`ij ∈ E(J)`) and
`R'_ij` (`ij ∈ E(J)`), so that the first is saturated and the second is not, differing only on one
edge of `J`.**  Let the line graphs made by `R_ij` and `R'_ij` be `L(H)` and `L(H')`
respectively."*

The printed word *"Hence"* hides a discrete interpolation: list the edges of `J` as
`e_1, …, e_m`, and let `F_k` be the family that uses `R'` on `e_1, …, e_k` and `R` on the rest.
Then `F_0 = R` is saturated and `F_m = R'` is not, so some consecutive pair `F_{k-1}, F_k` — which
differ only on the edge `e_k` — has the first saturated and the second not.

Two things have to be checked to make that run, and they are the mathematical content of the
lemma below:

* each hybrid `F_k` is again a choice of rungs (immediate: `F_k u v` is a `uv`-rung because both
  `R u v` and `R' u v` are, and the edge-indexing clause `F_k v u = (F_k u v).reverse` is
  inherited), and hence forms some line graph `L(H_k)` by
  `Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph`;
* *"saturated"* is a property of the **family of rungs alone**, not of the graph `H_k` or of the
  identification `φ_k` chosen to realise it.  By the rung-end dictionary
  (`Thm84RungEndDictionary.rungEndDictionary`, in the `∀ φ` form
  `Thm84RungEndDictionaryAt.rungEndDictionaryAt`), `δ_{H_k}(ι u)` is indexed by the `J`-neighbours
  `v` of `u`, and the edge indexed by `v` is carried by `φ_k` to the `u`-end of `F_k u v`.  So
  `X` saturates `L(H_k)` if and only if
  `∀ u, {v | J.Adj u v ∧ head (F_k u v) ∉ X}` is a subsingleton — a statement about `F_k` only.
  This is what lets the interpolation compare `F_{k-1}` with `F_k` at all.

## Proof attempt 1

Two ingredients:

* `saturates_iff` — **saturation is a property of the rung family alone**.  Via
  `Thm84BranchRungDictionaryAt.rungEndDictionaryAt` (the `∀ φ` form of the rung-end dictionary),
  `δ_H(ι u)` is indexed by the `J`-neighbours `v` of `u`, and `φ` carries the edge indexed by `v`
  to the `u`-end of `R u v`.  So `X` saturates `L(H)` iff for each `u` at most one `J`-neighbour
  `v` of `u` has the `u`-end of `R u v` outside `X` — a statement mentioning neither `H` nor `φ`.
  This is what makes the interpolation comparable at all.
* the interpolation itself: `F k` uses `R₁` on the first `k` entries of an enumeration `es` of
  `Sym2 U` and `R₀` elsewhere.  `F 0 = R₀` is saturated, `F |es| = R₁` is not, so some consecutive
  pair `F k`, `F (k+1)` straddles; they differ only at `es[k]`, which must be an edge of `J`
  (otherwise they would agree on every `J`-adjacent pair and be saturated together).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm84AdjacentChoices

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.StripSystems Workspace.Types.StripSystems.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Saturation of `L(H)` is a property of the choice of rungs alone.**

`X` saturates the line graph formed by the choice `R` if and only if, for every vertex `u` of `J`,
at most one `J`-neighbour `v` of `u` has the `u`-end of the rung `R u v` outside `X`.  Neither `H`
nor the identification `φ` occurs on the right-hand side. -/
theorem saturates_iff {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph V) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (H : SimpleGraph W) (R : U → U → List V) (hForms : FormsLineGraph G J S N R H)
    (φ : H.lineGraph ≃g G.induce (⋃ (a : U) (b : U) (_ : J.Adj a b), {x : V | x ∈ R a b}))
    (X : Set V) :
    SaturatesLineGraph H {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}
      ↔ ∀ u v v' : U, J.Adj u v → J.Adj u v' →
          (∀ s : V, (R u v).head? = some s → s ∉ X) →
          (∀ s : V, (R u v').head? = some s → s ∉ X) → v = v' := by
  classical
  obtain ⟨ι, E, hιinj, hrange, hEedge, hincid, hEinj, hEφ⟩ :=
    Thm84BranchRungDictionaryAt.rungEndDictionaryAt G J hJ S N hSN H R hForms φ
  -- `φ` sends the edge of `δ_H(ι u)` indexed by `v` to the head of the rung `R u v`
  have hφhead : ∀ (u v : U) (huv : J.Adj u v) (he : E u v ∈ H.edgeSet),
      (R u v).head? = some (↑(φ ⟨E u v, he⟩) : V) := by
    intro u v huv he
    obtain ⟨-, s, t, hp, -, -, -⟩ := hForms.1 u v huv
    rw [hEφ u v huv he s t hp]
    exact hp.2.1
  have hmemX : ∀ (u v : U), J.Adj u v →
      ((∀ s : V, (R u v).head? = some s → s ∉ X) ↔
        E u v ∉ {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X}) := by
    intro u v huv
    constructor
    · rintro hno ⟨he, hx⟩
      exact hno _ (hφhead u v huv he) hx
    · intro hno s hs hx
      refine hno ⟨hEedge u v huv, ?_⟩
      have hh := hφhead u v huv (hEedge u v huv)
      rw [hs] at hh
      have hseq : s = (↑(φ ⟨E u v, hEedge u v huv⟩) : V) := Option.some_injective _ hh
      rw [← hseq]
      exact hx
  constructor
  · intro hsat u v v' huv huv' hnv hnv'
    have hbr : ι u ∈ branchVertices H := by rw [← hrange]; exact ⟨u, rfl⟩
    have h1 : E u v ∈ incidentEdges H (ι u) \
        {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
      refine ⟨?_, (hmemX u v huv).mp hnv⟩
      rw [hincid u]; exact ⟨v, huv, rfl⟩
    have h2 : E u v' ∈ incidentEdges H (ι u) \
        {e : Sym2 W | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} := by
      refine ⟨?_, (hmemX u v' huv').mp hnv'⟩
      rw [hincid u]; exact ⟨v', huv', rfl⟩
    exact hEinj u v v' huv huv' (hsat (ι u) hbr h1 h2)
  · intro hfam w hw e₁ he₁ e₂ he₂
    obtain ⟨u, rfl⟩ : w ∈ Set.range ι := by rw [hrange]; exact hw
    have h1 := he₁.1
    rw [hincid u] at h1
    obtain ⟨v, huv, rfl⟩ := h1
    have h2 := he₂.1
    rw [hincid u] at h2
    obtain ⟨v', huv', rfl⟩ := h2
    rw [hfam u v v' huv huv' ((hmemX u v huv).mpr he₁.2) ((hmemX u v' huv').mpr he₂.2)]

/-- **"Hence there are two choices of rungs `R_ij` and `R'_ij`, so that the first is saturated and
the second is not, differing only on one edge of `J`."** -/
theorem adjacentChoices {U : Type*} [Fintype U]
    (G : SimpleGraph V) (hG : Berge G) (J : SimpleGraph U) (hJ : IsKConnected J 3)
    (S : U → U → Set V) (N : U → Set V) (hSN : IsJStripSystem G J S N)
    (X : Set V)
    (n₀ : ℕ) (H₀ : SimpleGraph (Fin n₀)) (R₀ : U → U → List V)
    (hForms₀ : FormsLineGraph G J S N R₀ H₀)
    (hsym₀ : ∀ u v : U, J.Adj u v → R₀ v u = (R₀ u v).reverse)
    (φ₀ : H₀.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₀ u v}))
    (hSat₀ : SaturatesLineGraph H₀
      {e : Sym2 (Fin n₀) | ∃ he : e ∈ H₀.edgeSet, (↑(φ₀ ⟨e, he⟩) : V) ∈ X})
    (n₁ : ℕ) (H₁ : SimpleGraph (Fin n₁)) (R₁ : U → U → List V)
    (hForms₁ : FormsLineGraph G J S N R₁ H₁)
    (hsym₁ : ∀ u v : U, J.Adj u v → R₁ v u = (R₁ u v).reverse)
    (φ₁ : H₁.lineGraph ≃g
      G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R₁ u v}))
    (hUnsat₁ : ¬ SaturatesLineGraph H₁
      {e : Sym2 (Fin n₁) | ∃ he : e ∈ H₁.edgeSet, (↑(φ₁ ⟨e, he⟩) : V) ∈ X}) :
    ∃ (a b : U) (n : ℕ) (H : SimpleGraph (Fin n)) (R : U → U → List V)
      (φ : H.lineGraph ≃g
        G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R u v}))
      (n' : ℕ) (H' : SimpleGraph (Fin n')) (R' : U → U → List V)
      (φ' : H'.lineGraph ≃g
        G.induce (⋃ (u : U) (v : U) (_ : J.Adj u v), {x : V | x ∈ R' u v})),
      J.Adj a b ∧
      FormsLineGraph G J S N R H ∧
      (∀ u v : U, J.Adj u v → R v u = (R u v).reverse) ∧
      FormsLineGraph G J S N R' H' ∧
      (∀ u v : U, J.Adj u v → R' v u = (R' u v).reverse) ∧
      SaturatesLineGraph H
        {e : Sym2 (Fin n) | ∃ he : e ∈ H.edgeSet, (↑(φ ⟨e, he⟩) : V) ∈ X} ∧
      ¬ SaturatesLineGraph H'
        {e : Sym2 (Fin n') | ∃ he : e ∈ H'.edgeSet, (↑(φ' ⟨e, he⟩) : V) ∈ X} ∧
      (∀ u v : U, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v) := by
  classical
  ---------------------------------------------------------------------------
  -- An enumeration of `Sym2 U`, along which to interpolate.
  ---------------------------------------------------------------------------
  obtain ⟨es, hesMem⟩ : ∃ l : List (Sym2 U), ∀ e : Sym2 U, e ∈ l :=
    ⟨(Finset.univ : Finset (Sym2 U)).toList, fun e => by simp⟩
  obtain ⟨F, hF⟩ : ∃ f : ℕ → U → U → List V,
      ∀ k u v, f k u v = if s(u, v) ∈ es.take k then R₁ u v else R₀ u v :=
    ⟨_, fun _ _ _ => rfl⟩
  have hFrung : ∀ k : ℕ, ∀ u v : U, J.Adj u v → IsUVRung G J S N u v (F k u v) := by
    intro k u v huv
    rw [hF]
    split_ifs
    · exact hForms₁.1 u v huv
    · exact hForms₀.1 u v huv
  have hFsym : ∀ k : ℕ, ∀ u v : U, J.Adj u v → F k v u = (F k u v).reverse := by
    intro k u v huv
    rw [hF, hF]
    have hswap : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [hswap]
    split_ifs
    · exact hsym₁ u v huv
    · exact hsym₀ u v huv
  have hF0 : ∀ u v : U, F 0 u v = R₀ u v := by
    intro u v
    rw [hF]
    exact if_neg (by simp)
  have hFm : ∀ u v : U, F es.length u v = R₁ u v := by
    intro u v
    rw [hF, List.take_length]
    exact if_pos (hesMem _)
  have hFstep : ∀ (k : ℕ) (hk : k < es.length) (u v : U),
      s(u, v) ≠ es[k]'hk → F k u v = F (k + 1) u v := by
    intro k hk u v hne
    rw [hF, hF]
    have hsplit : (s(u, v) ∈ es.take (k + 1)) ↔ (s(u, v) ∈ es.take k) := by
      rw [List.take_succ, List.mem_append]
      constructor
      · rintro (h | h)
        · exact h
        · exfalso
          rw [List.getElem?_eq_getElem hk] at h
          simp only [Option.toList_some, List.mem_singleton] at h
          exact hne h
      · intro h; exact Or.inl h
    by_cases hc : s(u, v) ∈ es.take k
    · rw [if_pos hc, if_pos (hsplit.mpr hc)]
    · rw [if_neg hc, if_neg (fun h => hc (hsplit.mp h))]
  ---------------------------------------------------------------------------
  -- Saturation as a property of the family.
  ---------------------------------------------------------------------------
  obtain ⟨Sat, hSatDef⟩ : ∃ P : ℕ → Prop, ∀ k : ℕ, P k ↔
      (∀ u v v' : U, J.Adj u v → J.Adj u v' →
        (∀ s : V, (F k u v).head? = some s → s ∉ X) →
        (∀ s : V, (F k u v').head? = some s → s ∉ X) → v = v') :=
    ⟨_, fun _ => Iff.rfl⟩
  have hfam₀ := (saturates_iff G J hJ S N hSN H₀ R₀ hForms₀ φ₀ X).mp hSat₀
  have hSat0 : Sat 0 := by
    rw [hSatDef]
    intro u v v' huv huv' h1 h2
    refine hfam₀ u v v' huv huv' ?_ ?_
    · rw [← hF0 u v]; exact h1
    · rw [← hF0 u v']; exact h2
  have hSatm : ¬ Sat es.length := by
    intro hc
    rw [hSatDef] at hc
    refine hUnsat₁ ((saturates_iff G J hJ S N hSN H₁ R₁ hForms₁ φ₁ X).mpr ?_)
    intro u v v' huv huv' h1 h2
    refine hc u v v' huv huv' ?_ ?_
    · rw [hFm u v]; exact h1
    · rw [hFm u v']; exact h2
  ---------------------------------------------------------------------------
  -- The straddling index.
  ---------------------------------------------------------------------------
  have hkey : ∀ m : ℕ, ¬ Sat m → ∃ k : ℕ, k < m ∧ Sat k ∧ ¬ Sat (k + 1) := by
    intro m
    induction m with
    | zero => intro h; exact absurd hSat0 h
    | succ n ih =>
      intro h
      by_cases hn : Sat n
      · exact ⟨n, by omega, hn, h⟩
      · obtain ⟨k, hk, h1, h2⟩ := ih hn
        exact ⟨k, by omega, h1, h2⟩
  obtain ⟨k, hklt, hSatk, hnSatk⟩ := hkey es.length hSatm
  obtain ⟨a, b, hab⟩ : ∃ a b : U, es[k]'hklt = s(a, b) := by
    have h : ∀ e : Sym2 U, ∃ a b : U, e = s(a, b) := by
      intro e
      induction e using Sym2.ind with
      | _ a b => exact ⟨a, b, rfl⟩
    exact h _
  -- the straddling entry must be an edge of `J`
  have hJab : J.Adj a b := by
    by_contra hnadj
    refine hnSatk ?_
    rw [hSatDef] at hSatk ⊢
    intro u v v' huv huv' h1 h2
    have hne : ∀ p q : U, J.Adj p q → s(p, q) ≠ es[k]'hklt := by
      intro p q hpq hcon
      rw [hab] at hcon
      rcases Sym2.eq_iff.mp hcon with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hnadj hpq
      · exact hnadj hpq.symm
    refine hSatk u v v' huv huv' ?_ ?_
    · rw [hFstep k hklt u v (hne u v huv)]; exact h1
    · rw [hFstep k hklt u v' (hne u v' huv')]; exact h2
  ---------------------------------------------------------------------------
  -- Both families form line graphs.
  ---------------------------------------------------------------------------
  obtain ⟨n, H, hFormsK⟩ :=
    Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph G hG J hJ S N hSN
      (F k) (hFrung k) (hFsym k)
  obtain ⟨φ⟩ := hFormsK.2.2
  obtain ⟨n', H', hFormsK'⟩ :=
    Thm84EveryChoiceFormsLineGraph.everyChoiceFormsLineGraph G hG J hJ S N hSN
      (F (k + 1)) (hFrung (k + 1)) (hFsym (k + 1))
  obtain ⟨φ'⟩ := hFormsK'.2.2
  refine ⟨a, b, n, H, F k, φ, n', H', F (k + 1), φ', hJab, hFormsK, hFsym k, hFormsK',
    hFsym (k + 1), ?_, ?_, ?_⟩
  · refine (saturates_iff G J hJ S N hSN H (F k) hFormsK φ X).mpr ?_
    rw [hSatDef] at hSatk
    exact hSatk
  · intro hc
    refine hnSatk ?_
    rw [hSatDef]
    exact (saturates_iff G J hJ S N hSN H' (F (k + 1)) hFormsK' φ' X).mp hc
  · intro u v huv hne
    exact hFstep k hklt u v (fun hcon => hne (by rw [← hab]; exact hcon))

end Workspace.ProofLemmas.Thm84AdjacentChoices
