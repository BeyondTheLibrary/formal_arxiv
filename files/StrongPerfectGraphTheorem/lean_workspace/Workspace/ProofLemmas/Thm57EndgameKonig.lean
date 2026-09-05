import Mathlib
import Workspace.Types.Tracks

/-! # The König step in the endgame of 5.7

The paper uses: "there is no 3-edge matching ... it follows from König's theorem that
there are two vertices ... such that every such edge is incident with one of them."
We obtain the bound two from Hall's theorem by adding dummy neighbours.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm57EndgameKonig

open Workspace.Types.Tracks.SPGT

/-- Hall's theorem with dummy neighbours gives a cover of size at most two when every
matching has size at most two. -/
theorem cover_of_matching_bound {L R : Type*} [Fintype L] [Fintype R]
    (t : L → Finset R)
    (hsmall : ∀ (P : L → Prop) [DecidablePred P] (f : {a // P a} → R),
      Function.Injective f → (∀ a, f a ∈ t a.1) → Fintype.card {a // P a} ≤ 2) :
    ∃ A : Finset L, ∃ B : Finset R, A.card + B.card ≤ 2 ∧
      ∀ a b, b ∈ t a → a ∈ A ∨ b ∈ B := by
  classical
  by_cases hL : Fintype.card L ≤ 2
  · exact ⟨Finset.univ, ∅, by simpa using hL, fun _ _ _ => Or.inl (Finset.mem_univ _)⟩
  let d := Fintype.card L - 3
  let t' : L → Finset (R ⊕ Fin d) := fun a => (t a).disjSum Finset.univ
  have hnot : ¬ ∃ f : L → R ⊕ Fin d, Function.Injective f ∧ ∀ a, f a ∈ t' a := by
    rintro ⟨f, hfi, hft⟩
    let P : L → Prop := fun a => (f a).isLeft
    let g : {a // P a} → R := fun a => (f a.1).getLeft a.2
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      apply hfi
      have hh := congrArg (Sum.inl : R → R ⊕ Fin d) hab
      simpa only [g, Sum.inl_getLeft] using hh
    have hgt : ∀ a, g a ∈ t a.1 := by
      intro a
      have hh := hft a.1
      rw [← Sum.inl_getLeft (f a.1) a.2] at hh
      simpa only [t', Finset.inl_mem_disjSum] using hh
    have hP := hsmall P g hg hgt
    have hQ : Fintype.card {a // ¬ P a} ≤ d := by
      let g' : {a // ¬ P a} → Fin d := fun a => (f a.1).getRight (by
        have := a.2
        cases h : f a.1 <;> simp_all [P])
      have hgi : Function.Injective g' := by
        intro a b hab
        apply Subtype.ext
        apply hfi
        have hh := congrArg (Sum.inr : Fin d → R ⊕ Fin d) hab
        simpa only [g', Sum.inr_getRight] using hh
      simpa using Fintype.card_le_of_injective g' hgi
    rw [Fintype.card_subtype_compl] at hQ
    dsimp [d] at hQ
    omega
  have hhall : ¬ ∀ s : Finset L, s.card ≤ (s.biUnion t').card := by
    intro h
    exact hnot ((Finset.all_card_le_biUnion_card_iff_exists_injective t').mp h)
  push Not at hhall
  obtain ⟨S, hS⟩ := hhall
  have hSne : S.Nonempty := by
    by_contra h
    simp only [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hS
  have hU : S.biUnion t' = (S.biUnion t).disjSum (Finset.univ : Finset (Fin d)) := by
    ext x
    cases x <;> simp [t', Finset.mem_biUnion, show ∃ a, a ∈ S from hSne]
  rw [hU, Finset.card_disjSum, Finset.card_univ, Fintype.card_fin] at hS
  refine ⟨Sᶜ, S.biUnion t, ?_, ?_⟩
  · rw [Finset.card_compl]
    have hSc := Finset.card_le_univ S
    dsimp [d] at hS
    omega
  · intro a b hab
    by_cases ha : a ∈ S
    · exact Or.inr (Finset.mem_biUnion.mpr ⟨a, ha, hab⟩)
    · exact Or.inl (Finset.mem_compl.mpr ha)

/-- A bipartite edge set with no three pairwise disjoint edges has a two-vertex cover. -/
theorem two_vertex_cover {W : Type*} [Fintype W] [Nonempty W]
    (H : SimpleGraph W) (hbip : H.IsBipartite) (X : Set (Sym2 W))
    (hXE : X ⊆ H.edgeSet)
    (hno : ¬ ∃ e ∈ X, ∃ f ∈ X, ∃ g ∈ X,
      DisjointEdges e f ∧ DisjointEdges e g ∧ DisjointEdges f g) :
    ∃ c₁ c₂ : W, ∀ e ∈ X, c₁ ∈ e ∨ c₂ ∈ e := by
  classical
  obtain ⟨col⟩ := hbip
  let L := {a : W // col a = 0}
  let R := {b : W // col b ≠ 0}
  let t : L → Finset R := fun a => Finset.univ.filter (fun b => s(a.1, b.1) ∈ X)
  have hcross : ∀ a : L, ∀ b : R, a.1 ≠ b.1 := by
    intro a b heq
    exact b.2 (heq ▸ a.2)
  obtain ⟨A, B, hcard, hcover⟩ := cover_of_matching_bound t (by
    intro P _ f hfi hft
    by_contra hn
    obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp (by omega :
      2 < Fintype.card {a // P a})
    have hmem : ∀ a, s(a.val.val, (f a).val) ∈ X := by
      intro a
      exact (Finset.mem_filter.mp (hft a)).2
    have hd : ∀ a b : {a // P a}, a ≠ b →
        DisjointEdges s(a.val.val, (f a).val) s(b.val.val, (f b).val) := by
      intro a b hab w hw
      rcases Sym2.mem_iff.mp hw.1 with hwa | hwa <;>
        rcases Sym2.mem_iff.mp hw.2 with hwb | hwb
      · exact hab (Subtype.ext (Subtype.ext (hwa.symm.trans hwb)))
      · exact hcross a.val (f b) (hwa.symm.trans hwb)
      · exact hcross b.val (f a) (hwb.symm.trans hwa)
      · exact hab (hfi (Subtype.ext (hwa.symm.trans hwb)))
    exact hno ⟨_, hmem a, _, hmem b, _, hmem c, hd a b hab, hd a c hac, hd b c hbc⟩)
  let C : Finset W := A.image Subtype.val ∪ B.image Subtype.val
  have hCcard : C.card ≤ 2 := by
    calc
      C.card ≤ (A.image Subtype.val).card + (B.image Subtype.val).card := Finset.card_union_le _ _
      _ ≤ A.card + B.card := Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
      _ ≤ 2 := hcard
  have hCcover : ∀ e ∈ X, ∃ w ∈ C, w ∈ e := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : H.Adj u v := hXE he
      have hcol := col.valid huv
      have hor : (col u = 0 ∧ col v ≠ 0) ∨ (col v = 0 ∧ col u ≠ 0) := by
        have hu := (col u).isLt
        have hv := (col v).isLt
        by_cases h : col u = 0
        · exact Or.inl ⟨h, fun hv => hcol (h.trans hv.symm)⟩
        · right
          refine ⟨?_, h⟩
          apply Fin.ext
          have hnu : (col u).val ≠ 0 := fun hh => h (Fin.ext hh)
          have hne : (col u).val ≠ (col v).val := fun hh => hcol (Fin.ext hh)
          omega
      rcases hor with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · rcases hcover ⟨u, hu⟩ ⟨v, hv⟩ (by simpa [t] using he) with h | h
        · exact ⟨u, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨u, hu⟩, h, rfl⟩), by simp⟩
        · exact ⟨v, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨v, hv⟩, h, rfl⟩), by simp⟩
      · rcases hcover ⟨v, hv⟩ ⟨u, hu⟩ (by simpa [t, Sym2.eq_swap] using he) with h | h
        · exact ⟨v, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨v, hv⟩, h, rfl⟩), by simp⟩
        · exact ⟨u, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨u, hu⟩, h, rfl⟩), by simp⟩
  have hp : ∃ c₁ c₂ : W, ∀ w ∈ C, w = c₁ ∨ w = c₂ := by
    by_cases htwo : C.card = 2
    · obtain ⟨c₁, c₂, _, hC⟩ := Finset.card_eq_two.mp htwo
      exact ⟨c₁, c₂, by simp [hC]⟩
    · have hsingle : (↑C : Set W).Subsingleton := Finset.card_le_one_iff_subsingleton.mp (by omega)
      by_cases hne : C.Nonempty
      · obtain ⟨c, hc⟩ := hne
        exact ⟨c, c, fun w hw => Or.inl (hsingle hw hc)⟩
      · exact ⟨Classical.arbitrary W, Classical.arbitrary W, fun w hw => (hne ⟨w, hw⟩).elim⟩
  obtain ⟨c₁, c₂, hp⟩ := hp
  refine ⟨c₁, c₂, ?_⟩
  intro e he
  obtain ⟨w, hw, hwe⟩ := hCcover e he
  rcases hp w hw with rfl | rfl
  · exact Or.inl hwe
  · exact Or.inr hwe

end Workspace.ProofLemmas.Thm57EndgameKonig
