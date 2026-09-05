import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_E7_lovasz_replication

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Replication.SPGT

private theorem inducedPerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y : Set W) (hK : IsPerfect K) :
    IsPerfect (K.induce Y) := by
  classical
  intro X
  let e : (K.induce Y).induce X ≃g K.induce (Subtype.val '' X) :=
    { Equiv.Set.image (Subtype.val : Y → W) X Subtype.val_injective with
      map_rel_iff' := by
        intro a b
        rfl }
  rw [IsoTransport.chromaticNumber_iso e, IsoTransport.cliqueNum_iso e]
  exact hK (Subtype.val '' X)

private abbrev Occ {W : Type*} (k : ℕ) (A : Fin k → Set W) :=
  {p : Fin k × W // p.2 ∈ A p.1}

private def occGraph {W : Type*} (K : SimpleGraph W) (k : ℕ)
    (A : Fin k → Set W) : SimpleGraph (Occ k A) :=
  { Adj := fun x y ↦ x ≠ y ∧
      (x.1.2 = y.1.2 ∨ K.Adj x.1.2 y.1.2)
    symm := by
      intro x y h
      exact ⟨h.1.symm, h.2.elim (fun hxy ↦ Or.inl hxy.symm)
        (fun hxy ↦ Or.inr hxy.symm)⟩
    loopless := by
      refine ⟨?_⟩
      intro x h
      exact h.1 rfl }

private theorem occurrencePerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (k : ℕ) (hk : 0 < k)
    (A : Fin k → Set W) (hK : IsPerfect K) :
    IsPerfect (occGraph K k A) := by
  classical
  let π : Occ k A → W := fun p ↦ p.1.2
  by_cases hinj : Function.Injective π
  · let f : Occ k A → {w : W // w ∈ Set.range π} :=
      fun x ↦ ⟨π x, x, rfl⟩
    have hfinj : Function.Injective f := fun x y h ↦ hinj (congrArg Subtype.val h)
    have hfsurj : Function.Surjective f := by
      rintro ⟨w, x, hx⟩
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact hx
    let e0 : Occ k A ≃ {w : W // w ∈ Set.range π} :=
      Equiv.ofBijective f ⟨hfinj, hfsurj⟩
    have hmap (x y : Occ k A) :
        K.Adj (π x) (π y) ↔ (occGraph K k A).Adj x y := by
      constructor
      · intro hadj
        refine ⟨?_, Or.inr hadj⟩
        intro hxy
        subst y
        exact K.irrefl hadj
      · rintro ⟨hxy, hs | hadj⟩
        · exact False.elim (hxy (hinj hs))
        · exact hadj
    let e : occGraph K k A ≃g K.induce (Set.range π) :=
      { e0 with
        map_rel_iff' := by
          intro x y
          simpa [e0, f] using hmap x y }
    exact IsoTransport.isPerfect_of_iso e.symm
      (inducedPerfect K (Set.range π) hK)
  · obtain ⟨x, y, hπ, hxy⟩ := Function.not_injective_iff.mp hinj
    let A' : Fin k → Set W := fun i ↦
      {w | w ∈ A i ∧ (i, w) ≠ x.1}
    let old : Occ k A' → Occ k A := fun z ↦ ⟨z.1, z.2.1⟩
    have hold_inj : Function.Injective old := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun z : Occ k A => z.1) h
    have hx_not_old : x ∉ Set.range old := by
      rintro ⟨z, hz⟩
      exact z.2.2 (congrArg (fun q : Occ k A => q.1) hz)
    have hsmallF : Fintype.card (Occ k A') < Fintype.card (Occ k A) :=
      Fintype.card_lt_of_injective_of_notMem old hold_inj hx_not_old
    have hsmall : Nat.card (Occ k A') < Nat.card (Occ k A) := by
      simpa only [Nat.card_eq_fintype_card] using hsmallF
    have hyval : y.1 ≠ x.1 := by
      intro h
      exact hxy (Subtype.ext h.symm)
    let y' : Occ k A' := ⟨y.1, y.2, hyval⟩
    have hperf' : IsPerfect (occGraph K k A') :=
      occurrencePerfect K k hk A' hK
    have hrepl : IsPerfect (replicateVertex (occGraph K k A') y') :=
      Workspace.MainTheorem.SPGT.thm_E7_lovasz_replication
        (occGraph K k A') y' hperf'
    let f : Occ k A' ⊕ Unit → Occ k A := fun z ↦
      match z with
      | Sum.inl a => old a
      | Sum.inr _ => x
    have hfinj : Function.Injective f := by
      rintro (a | u) (b | v) hab
      · exact congrArg Sum.inl (hold_inj hab)
      · exact False.elim (hx_not_old ⟨a, hab⟩)
      · exact False.elim (hx_not_old ⟨b, hab.symm⟩)
      · cases u
        cases v
        rfl
    have hfsurj : Function.Surjective f := by
      intro z
      by_cases hzx : z = x
      · exact ⟨Sum.inr (), hzx.symm⟩
      · have hzval : z.1 ≠ x.1 := by
          intro h
          exact hzx (Subtype.ext h)
        let z' : Occ k A' := ⟨z.1, z.2, hzval⟩
        exact ⟨Sum.inl z', rfl⟩
    let e0 : Occ k A' ⊕ Unit ≃ Occ k A :=
      Equiv.ofBijective f ⟨hfinj, hfsurj⟩
    have holdadj (a b : Occ k A') :
        (occGraph K k A).Adj (old a) (old b) ↔
          (occGraph K k A').Adj a b := by
      constructor
      · rintro ⟨hab, h⟩
        exact ⟨fun eab ↦ hab (congrArg old eab), h⟩
      · rintro ⟨hab, h⟩
        exact ⟨fun eab ↦ hab (hold_inj eab), h⟩
    have hpy : y'.1.2 = x.1.2 := hπ.symm
    have hcross (a : Occ k A') :
        (occGraph K k A).Adj (old a) x ↔
          (replicateVertex (occGraph K k A') y').Adj (Sum.inl a) (Sum.inr ()) := by
      change (old a ≠ x ∧
          ((old a).1.2 = x.1.2 ∨ K.Adj (old a).1.2 x.1.2)) ↔
        (a = y' ∨ (a ≠ y' ∧
          (a.1.2 = y'.1.2 ∨ K.Adj a.1.2 y'.1.2)))
      have haold : old a ≠ x := by
        intro h
        exact hx_not_old ⟨a, h⟩
      constructor
      · rintro ⟨-, hs | hadj⟩
        · by_cases hay : a = y'
          · exact Or.inl hay
          · exact Or.inr ⟨hay, Or.inl (hs.trans hpy.symm)⟩
        · by_cases hay : a = y'
          · exact Or.inl hay
          · exact Or.inr ⟨hay, Or.inr (hpy.symm ▸ hadj)⟩
      · intro h
        refine ⟨haold, ?_⟩
        rcases h with rfl | h
        · exact Or.inl hpy
        · rcases h.2 with hs | hadj
          · exact Or.inl (hs.trans hpy)
          · exact Or.inr (hpy ▸ hadj)
    let e : replicateVertex (occGraph K k A') y' ≃g occGraph K k A :=
      { e0 with
        map_rel_iff' := by
          rintro (a | ⟨⟩) (b | ⟨⟩)
          · simpa [e0, f] using holdadj a b
          · simpa [e0, f] using hcross a
          · simpa [e0, f, SimpleGraph.adj_comm] using hcross b
          · simp [e0, f, occGraph, replicateVertex] }
    exact IsoTransport.isPerfect_of_iso e hrepl
termination_by Nat.card (Occ k A)
decreasing_by exact hsmall

/-- Replacing each vertex of a perfect graph by an arbitrary finite clique of
occurrences, with the original adjacency between distinct fibers, preserves
perfection. Empty occurrence fibers simply omit their original vertex. -/
theorem OccurrenceIndexedCliqueReplicationPerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (k : ℕ) (hk : 0 < k)
    (A : Fin k → Set W) (hK : IsPerfect K) :
    let Ω := {p : Fin k × W // p.2 ∈ A p.1}
    let π : Ω → W := fun p ↦ p.1.2
    let KΩ : SimpleGraph Ω :=
      { Adj := fun x y ↦ x ≠ y ∧ (π x = π y ∨ K.Adj (π x) (π y))
        symm := by
          intro x y h
          exact ⟨h.1.symm, h.2.elim (fun hxy ↦ Or.inl hxy.symm)
            (fun hxy ↦ Or.inr hxy.symm)⟩
        loopless := by
          refine ⟨?_⟩
          intro x h
          exact h.1 rfl }
    IsPerfect KΩ := by
  simpa [Occ, occGraph] using occurrencePerfect K k hk A hK

end Workspace.ProofLemmas
