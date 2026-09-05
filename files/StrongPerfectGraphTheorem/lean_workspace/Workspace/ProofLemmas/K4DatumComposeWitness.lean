import Workspace.ProofLemmas.SubdivisionCompose

/-!
# Composing a `K₄` datum with local subdivision witnesses

`SubdivisionCompose.hasK4Datum_of_subdivision` only needs the six local clauses of an
`IsSubdivision` witness.  This module exposes that slightly more general interface.  It is useful for
the suppression step in Dirac's theorem: the newly inserted edge is represented by a two-edge track
through the suppressed vertex, while irrelevant ambient edges and vertices need not be packaged into
an exact subdivision graph.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.K4DatumComposeWitness

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.SubdivisionCompose

variable {U W : Type*}

/-- A `K₄` datum composes with the six local clauses of a subdivision witness. -/
theorem hasK4Datum_of_subdivWitness {J : SimpleGraph U} {H : SimpleGraph W}
    {iota : U → W} {T : U → U → List W}
    (hdat : HasK4Datum J) (hS : SubdivWitness J H iota T) : HasK4Datum H := by
  obtain ⟨kappa, R, hkappa, hRtrack, hRlen, hRrev, hRdisj, hRnew⟩ := hdat
  have hRchain : ∀ a b : Fin 4, a ≠ b → List.IsChain J.Adj (R a b) := fun a b h ↦
    List.isChain_iff_getElem.mpr (hRtrack a b h).1.2.2
  have hRnd : ∀ a b : Fin 4, a ≠ b → (R a b).Nodup := fun a b h ↦
    (hRtrack a b h).1.2.1
  have hRne : ∀ a b : Fin 4, a ≠ b → R a b ≠ [] := fun a b h ↦
    (hRtrack a b h).1.1
  have hRhead : ∀ a b : Fin 4, a ≠ b → (R a b).head? = some (kappa a) := fun a b h ↦
    (hRtrack a b h).2.1
  have hRlast : ∀ a b : Fin 4, a ≠ b → (R a b).getLast? = some (kappa b) := fun a b h ↦
    (hRtrack a b h).2.2
  have hRlen2 : ∀ a b : Fin 4, a ≠ b → 2 ≤ (R a b).length := by
    intro a b h
    have h1 := hRlen a b h
    simp only [trackLength] at h1
    omega
  have hEhead : ∀ a b : Fin 4, a ≠ b →
      (expandTracks iota T (R a b)).head? = some (iota (kappa a)) := by
    intro a b h
    rw [expandTracks_head? hS (R a b) (hRchain a b h), hRhead a b h]
    rfl
  have hElast : ∀ a b : Fin 4, a ≠ b →
      (expandTracks iota T (R a b)).getLast? = some (iota (kappa b)) := by
    intro a b h
    rw [expandTracks_getLast? hS (R a b) (hRchain a b h), hRlast a b h]
    rfl
  have hEnd : ∀ a b : Fin 4, a ≠ b → (expandTracks iota T (R a b)).Nodup :=
    fun a b h ↦ expandTracks_nodup hS (R a b) (hRchain a b h) (hRnd a b h)
  have key : ∀ a b a' b' : Fin 4, a ≠ b → a' ≠ b' → s(a, b) ≠ s(a', b') →
      ∀ x y : U, x ≠ y → x ∈ R a b → y ∈ R a b → x ∈ R a' b' → y ∈ R a' b' → False := by
    intro a b a' b' hab ha'b' hs x y hxy hx hy hx' hy'
    have hxi : x ∉ trackInterior (R a b) := fun hc ↦ hRdisj a b a' b' hab ha'b' hs x hc hx'
    have hyi : y ∉ trackInterior (R a b) := fun hc ↦ hRdisj a b a' b' hab ha'b' hs y hc hy'
    have hxi' : x ∉ trackInterior (R a' b') := fun hc ↦
      hRdisj a' b' a b ha'b' hab (Ne.symm hs) x hc hx
    have hyi' : y ∉ trackInterior (R a' b') := fun hc ↦
      hRdisj a' b' a b ha'b' hab (Ne.symm hs) y hc hy
    have hx1 := mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hx hxi
    have hy1 := mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hy hyi
    have hx2 := mem_ends_of_mem (hRhead a' b' ha'b') (hRlast a' b' ha'b') hx' hxi'
    have hy2 := mem_ends_of_mem (hRhead a' b' ha'b') (hRlast a' b' ha'b') hy' hyi'
    have hc1 : (x = kappa a ∧ y = kappa b) ∨ (x = kappa b ∧ y = kappa a) := by
      rcases hx1 with h1 | h1 <;> rcases hy1 with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hxy
    have hc2 : (x = kappa a' ∧ y = kappa b') ∨ (x = kappa b' ∧ y = kappa a') := by
      rcases hx2 with h1 | h1 <;> rcases hy2 with h2 | h2
      · exact absurd (h1.trans h2.symm) hxy
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr ⟨h1, h2⟩
      · exact absurd (h1.trans h2.symm) hxy
    apply hs
    rcases hc1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hc2 with ⟨e3, e4⟩ | ⟨e3, e4⟩
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hkappa (e1.symm.trans e3), hkappa (e2.symm.trans e4)⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hkappa (e1.symm.trans e3), hkappa (e2.symm.trans e4)⟩)
    · exact Sym2.eq_iff.mpr (Or.inr ⟨hkappa (e2.symm.trans e4), hkappa (e1.symm.trans e3)⟩)
    · exact Sym2.eq_iff.mpr (Or.inl ⟨hkappa (e2.symm.trans e4), hkappa (e1.symm.trans e3)⟩)
  have hedge : ∀ a b a' b' : Fin 4, a ≠ b → a' ≠ b' → s(a, b) ≠ s(a', b') →
      ∀ x y x' y' : U, J.Adj x y → x ∈ R a b → y ∈ R a b →
        x' ∈ R a' b' → y' ∈ R a' b' → s(x, y) ≠ s(x', y') := by
    intro a b a' b' hab ha'b' hs x y x' y' hxy hx hy hx' hy' heq
    rcases Sym2.eq_iff.mp heq with ⟨p1, p2⟩ | ⟨p1, p2⟩
    · exact key a b a' b' hab ha'b' hs x y hxy.ne hx hy
        (by rw [p1]; exact hx') (by rw [p2]; exact hy')
    · exact key a b a' b' hab ha'b' hs x y hxy.ne hx hy
        (by rw [p1]; exact hy') (by rw [p2]; exact hx')
  refine ⟨fun a ↦ iota (kappa a), fun a b ↦ expandTracks iota T (R a b), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b hab
    exact hkappa (hS.inj hab)
  · intro a b hab
    refine ⟨⟨expandTracks_ne_nil hS (hRchain a b hab) (hRne a b hab), hEnd a b hab, ?_⟩,
      hEhead a b hab, hElast a b hab⟩
    exact List.isChain_iff_getElem.mp (expandTracks_isChain hS (R a b) (hRchain a b hab))
  · intro a b hab
    have h := two_le_expandTracks_length hS (hRchain a b hab) (hRlen2 a b hab)
    simp only [trackLength]
    omega
  · intro a b hab
    show expandTracks iota T (R b a) = (expandTracks iota T (R a b)).reverse
    rw [hRrev a b hab]
    exact expandTracks_reverse hS (R a b) (hRchain a b hab)
  · intro a b a' b' hab ha'b' hs w hw hmem
    have hwmem : w ∈ expandTracks iota T (R a b) := mem_of_mem_trackInterior hw
    have hwa : w ≠ iota (kappa a) :=
      ne_head_of_mem_trackInterior (hEnd a b hab) (hEhead a b hab) hw
    have hwb : w ≠ iota (kappa b) :=
      ne_getLast_of_mem_trackInterior (hEnd a b hab) (hElast a b hab) hw
    rcases mem_expandTracks hS (R a b) (hRchain a b hab) w hwmem with
      ⟨x, hxR, hxeq⟩ | ⟨x, y, hxR, hyR, hxy, hint⟩
    · rcases mem_expandTracks hS (R a' b') (hRchain a' b' ha'b') w hmem with
        ⟨x', hx'R, hx'eq⟩ | ⟨x', y', hx'R, hy'R, hx'y', hint'⟩
      · have hxx' : x = x' := hS.inj (hxeq.symm.trans hx'eq)
        have hxi : x ∉ trackInterior (R a b) := fun hc ↦
          hRdisj a b a' b' hab ha'b' hs x hc (by rw [hxx']; exact hx'R)
        rcases mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hxR hxi with h | h
        · exact hwa (by rw [hxeq, h])
        · exact hwb (by rw [hxeq, h])
      · exact hS.new x' y' hx'y' w hint' ⟨x, hxeq.symm⟩
    · rcases mem_expandTracks hS (R a' b') (hRchain a' b' ha'b') w hmem with
        ⟨x', hx'R, hx'eq⟩ | ⟨x', y', hx'R, hy'R, hx'y', hint'⟩
      · exact hS.new x y hxy w hint ⟨x', hx'eq.symm⟩
      · exact hS.disj x y x' y' hxy hx'y'
          (hedge a b a' b' hab ha'b' hs x y x' y' hxy hxR hyR hx'R hy'R) w hint
          (mem_of_mem_trackInterior hint')
  · intro a b hab w hw ⟨c, hc⟩
    have hwmem : w ∈ expandTracks iota T (R a b) := mem_of_mem_trackInterior hw
    have hwa : w ≠ iota (kappa a) :=
      ne_head_of_mem_trackInterior (hEnd a b hab) (hEhead a b hab) hw
    have hwb : w ≠ iota (kappa b) :=
      ne_getLast_of_mem_trackInterior (hEnd a b hab) (hElast a b hab) hw
    rcases mem_expandTracks hS (R a b) (hRchain a b hab) w hwmem with
      ⟨x, hxR, hxeq⟩ | ⟨x, y, hxR, hyR, hxy, hint⟩
    · have hxc : x = kappa c := hS.inj (hxeq.symm.trans hc.symm)
      by_cases hxi : x ∈ trackInterior (R a b)
      · exact hRnew a b hab x hxi ⟨c, hxc.symm⟩
      · rcases mem_ends_of_mem (hRhead a b hab) (hRlast a b hab) hxR hxi with h | h
        · exact hwa (by rw [hxeq, h])
        · exact hwb (by rw [hxeq, h])
    · exact hS.new x y hxy w hint ⟨kappa c, hc⟩

end Workspace.ProofLemmas.K4DatumComposeWitness
