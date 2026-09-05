import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.ProofLemmas.BipartiteClosedWalkEven
import Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
import Workspace.ProofLemmas.SubdivisionCounting
import Workspace.ProofLemmas.Thm57Setup

/-!
# The parity step in the endgame of 5.7

This is the sentence which joins two disjoint `X`-edges through
`H \ {c₁,c₂}` and uses the forbidden-even-track hypothesis.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameParity

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm57Setup

variable {W : Type*} [Fintype W] [DecidableEq W]

private theorem head_getElem {l : List W} {a : W} (h : l.head? = some a)
    (h0 : 0 < l.length) : l[0]'h0 = a := by
  cases l with
  | nil => simp at h0
  | cons x t => simp only [List.head?_cons, Option.some.injEq] at h; simpa using h

private theorem last_getElem {l : List W} {b : W} (h : l.getLast? = some b)
    (h0 : 0 < l.length) : l[l.length - 1]'(by omega) = b := by
  have hne : l ≠ [] := by intro hc; subst hc; simp at h0
  have h1 := List.getLast?_eq_some_getLast hne
  rw [h] at h1
  have h2 : b = l.getLast hne := Option.some_injective _ h1
  rw [h2]
  exact (List.getLast_eq_getElem hne).symm

private theorem getElem_idx_eq {l : List W} {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij
  rfl

/-- The paper's step *"Take a minimal track in `H \ {c₁,c₂}` between `a₁,a₂`;
then by the hypothesis of the theorem this track has odd length, and so `c₁,c₂` have
opposite biparity."* -/
theorem coverCentresDifferentBiparity (H : SimpleGraph W) (hbip : H.IsBipartite)
    (X : Set (Sym2 W)) (hXE : X ⊆ H.edgeSet) (hnotrack : NoEvenTrack57 H X)
    (c₁ c₂ : W) (hconn : ConnectedSet H (({c₁, c₂} : Set W)ᶜ))
    (hcover : X ⊆ incidentEdges H c₁ ∪ incidentEdges H c₂)
    (hdisj : TwoDisjointEdges H X) :
    DifferentBiparity H c₁ c₂ := by
  classical
  obtain ⟨e, heX, f, hfX, hef⟩ := hdisj
  obtain ⟨e₁, he₁, e₂, he₂, he₁e₂⟩ :
      ∃ e₁ ∈ incidentEdges H c₁ ∩ X, ∃ e₂ ∈ incidentEdges H c₂ ∩ X,
        DisjointEdges e₁ e₂ := by
    rcases hcover heX with he1 | he2
    · rcases hcover hfX with hf1 | hf2
      · exact False.elim (hef c₁ ⟨he1.2, hf1.2⟩)
      · exact ⟨e, ⟨he1, heX⟩, f, ⟨hf2, hfX⟩, hef⟩
    · rcases hcover hfX with hf1 | hf2
      · refine ⟨f, ⟨hf1, hfX⟩, e, ⟨he2, heX⟩, ?_⟩
        intro w hw
        exact hef w ⟨hw.2, hw.1⟩
      · exact False.elim (hef c₂ ⟨he2.2, hf2.2⟩)
  obtain ⟨a₁, he₁eq⟩ := Sym2.mem_iff_exists.mp he₁.1.2
  obtain ⟨a₂, he₂eq⟩ := Sym2.mem_iff_exists.mp he₂.1.2
  have hc₁a₁ : H.Adj c₁ a₁ := by
    apply H.mem_edgeSet.mp
    rw [← he₁eq]
    exact he₁.1.1
  have hc₂a₂ : H.Adj c₂ a₂ := by
    apply H.mem_edgeSet.mp
    rw [← he₂eq]
    exact he₂.1.1
  have ha₁c₂ : a₁ ≠ c₂ := by
    intro h
    apply he₁e₂ c₂
    constructor
    · rw [← h, he₁eq]
      simp
    · exact he₂.1.2
  have ha₂c₁ : a₂ ≠ c₁ := by
    intro h
    apply he₁e₂ c₁
    constructor
    · exact he₁.1.2
    · rw [← h, he₂eq]
      simp
  have ha₁a₂ : a₁ ≠ a₂ := by
    intro h
    apply he₁e₂ a₁
    constructor
    · rw [he₁eq]
      simp
    · rw [h, he₂eq]
      simp
  have hc₁c₂ : c₁ ≠ c₂ := by
    intro h
    apply he₁e₂ c₁
    exact ⟨he₁.1.2, h ▸ he₂.1.2⟩
  have ha₁S : a₁ ∈ (({c₁, c₂} : Set W)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hc₁a₁.ne', ha₁c₂⟩
  have ha₂S : a₂ ∈ (({c₁, c₂} : Set W)ᶜ) := by
    simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨ha₂c₁, hc₂a₂.ne'⟩
  obtain ⟨p₁, hp₁, p₂, hp₂, P, hP, hPS, -, -⟩ :=
    Workspace.ProofLemmas.ConnectedSetHasEndpointCleanTrack
      H (({c₁, c₂} : Set W)ᶜ) {a₁} {a₂} hconn
      ⟨a₁, rfl⟩ ⟨a₂, rfl⟩
      (Set.singleton_subset_iff.mpr ha₁S) (Set.singleton_subset_iff.mpr ha₂S)
  have hp₁eq : p₁ = a₁ := by simpa using hp₁
  have hp₂eq : p₂ = a₂ := by simpa using hp₂
  subst p₁
  subst p₂
  have hPne : P ≠ [] := hP.1.1
  have hPlen : 2 ≤ P.length := by
    have hpos : 0 < P.length := List.length_pos_of_ne_nil hPne
    by_contra h
    have hone : P.length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hone
    have hh := hP.2.1
    have hl := hP.2.2
    rw [hx] at hh hl
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at hh hl
    exact ha₁a₂ (hh.symm.trans hl)
  have hc₁P : c₁ ∉ P := by
    intro h
    exact (hPS c₁ h) (Or.inl rfl)
  have hc₂P : c₂ ∉ P := by
    intro h
    exact (hPS c₂ h) (Or.inr rfl)
  have hPchain : List.IsChain H.Adj P := List.isChain_iff_getElem.mpr hP.1.2.2
  have hPhead : (P ++ [c₂]).head? = some a₁ := by
    rw [List.head?_append, hP.2.1]
    rfl
  have hPlast : (P ++ [c₂]).getLast? = some c₂ := by
    rw [List.getLast?_append_of_ne_nil _ (by simp)]
    simp
  let Q : List W := c₁ :: (P ++ [c₂])
  have hQ : IsTrackFrom H Q c₁ c₂ := by
    refine ⟨⟨by simp [Q], ?_, ?_⟩, by simp [Q], ?_⟩
    · dsimp only [Q]
      refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨hP.1.2.1, by simp, ?_⟩⟩
      · intro h
        rcases List.mem_append.mp h with h | h
        · exact hc₁P h
        · exact hc₁c₂ (by simpa using h)
      · intro x hx y hy hxy
        have hyc : y = c₂ := by simpa using hy
        have hyP : y ∈ P := hxy ▸ hx
        have hcP : c₂ ∈ P := hyc ▸ hyP
        exact hc₂P hcP
    · dsimp only [Q]
      have hchainQ : List.IsChain H.Adj (c₁ :: (P ++ [c₂])) := by
        refine List.isChain_cons.mpr ⟨?_, ?_⟩
        · intro x hx
          rw [Option.mem_def, hPhead] at hx
          rw [← Option.some_injective _ hx]
          exact hc₁a₁
        · refine List.isChain_append.mpr ⟨hPchain, List.isChain_singleton _, ?_⟩
          intro x hx y hy
          rw [Option.mem_def, hP.2.2] at hx
          rw [Option.mem_def, List.head?_singleton] at hy
          rw [← Option.some_injective _ hx, ← Option.some_injective _ hy]
          exact hc₂a₂.symm
      exact List.isChain_iff_getElem.mp hchainQ
    · dsimp only [Q]
      rw [List.getLast?_cons_of_ne_nil (by simp), hPlast]
  have hQlen : Q.length = P.length + 2 := by simp [Q]
  have hP0 : P[0]'(by omega) = a₁ := head_getElem hP.2.1 (by omega)
  have hPl : P[P.length - 1]'(by omega) = a₂ := last_getElem hP.2.2 (by omega)
  have hQ0 : Q[0]'(by omega) = c₁ := by simp [Q]
  have hQ1 : Q[1]'(by omega) = a₁ := by
    simp only [Q, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega), hP0]
  have hQn2 : Q[Q.length - 2]'(by omega) = a₂ := by
    have hidx : Q.length - 2 = P.length := by omega
    rw [getElem_idx_eq hidx (by omega) (by omega)]
    have hidxP : P.length = (P.length - 1) + 1 := by omega
    rw [getElem_idx_eq hidxP (by omega) (by simp [Q])]
    simp only [Q, List.getElem_cons_succ]
    rw [List.getElem_append_left (by omega), hPl]
  have hQn1 : Q[Q.length - 1]'(by omega) = c₂ := last_getElem hQ.2.2 (by omega)
  have hfirstX : s(Q[0], Q[1]) ∈ X := by
    rw [hQ0, hQ1, ← he₁eq]
    exact he₁.2
  have hlastX : s(Q[Q.length - 2], Q[Q.length - 1]) ∈ X := by
    rw [hQn2, hQn1, Sym2.eq_swap, ← he₂eq]
    exact he₂.2
  have hclean : ∀ e ∈ trackEdges Q,
      e ≠ s(Q[0], Q[1]) → e ≠ s(Q[Q.length - 2], Q[Q.length - 1]) → e ∉ X := by
    intro d hd hd0 hdn hdX
    obtain ⟨i, hi, rfl⟩ := hd
    rcases hcover hdX with hc | hc
    · rcases Sym2.mem_iff.mp hc.2 with h | h
      · have hii : i = 0 := hQ.1.2.1.getElem_inj_iff.mp (h.symm.trans hQ0.symm)
        subst i
        exact hd0 rfl
      · have hii : i + 1 = 0 := hQ.1.2.1.getElem_inj_iff.mp (h.symm.trans hQ0.symm)
        omega
    · rcases Sym2.mem_iff.mp hc.2 with h | h
      · have hii : i = Q.length - 1 := hQ.1.2.1.getElem_inj_iff.mp
          (h.symm.trans hQn1.symm)
        omega
      · have hii : i + 1 = Q.length - 1 := hQ.1.2.1.getElem_inj_iff.mp
          (h.symm.trans hQn1.symm)
        have hieq : i = Q.length - 2 := by omega
        subst i
        apply hdn
        exact congrArg (fun z : W => s(Q[Q.length - 2], z))
          (getElem_idx_eq (by omega) (by omega) (by omega))
  have hQnotEven : ¬ Even (trackLength Q) := by
    intro heven
    have h5 : 5 ≤ Q.length := by
      obtain ⟨k, hk⟩ := heven
      simp only [trackLength] at hk
      omega
    exact hnotrack ⟨Q, h5, hQ.1, heven, hfirstX, hlastX, hclean⟩
  have hQodd : Odd (trackLength Q) := Nat.not_even_iff_odd.mp hQnotEven
  obtain ⟨col⟩ :=
    Workspace.ProofLemmas.BipartiteClosedWalkEven.exists_boolColoring_of_isBipartite hbip
  have hcolne : col c₁ ≠ col c₂ := by
    intro hsame
    exact hQnotEven
      ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hQ).mpr hsame)
  intro R hR
  apply Nat.not_even_iff_odd.mp
  intro hReven
  exact hcolne
    ((Workspace.ProofLemmas.BipartiteClosedWalkEven.even_trackLength_iff col hR).mp hReven)

end Workspace.ProofLemmas.Thm57EndgameParity
