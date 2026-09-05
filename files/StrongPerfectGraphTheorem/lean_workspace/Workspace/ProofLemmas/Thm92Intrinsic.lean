import Mathlib

/-!
# Intrinsic forms of locality and saturation for 9.2

The line-graph notions in 9.2 do not depend on names for the four branch vertices.
This file records graph-only versions of them.  An edge is *flat* when it belongs to no
triangle.  The branches of a subdivision become the connected components of the flat edges
in its line graph, while the sets `incidentEdges H v` become its triangles.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm92Intrinsic

/-- Two adjacent vertices are flat when their edge belongs to no triangle. -/
def FlatAdj {A : Type*} (L : SimpleGraph A) (a b : A) : Prop :=
  L.Adj a b ∧ ¬ ∃ c : A, L.Adj a c ∧ L.Adj b c

/-- A set lies in one flat component.  The empty set is included explicitly. -/
def FlatLocal {A : Type*} (L : SimpleGraph A) (X : Set A) : Prop :=
  X = ∅ ∨ ∃ a ∈ X, ∀ b ∈ X, Relation.ReflTransGen (FlatAdj L) a b

/-- A set is contained in a triangle or in one flat component. -/
def IntrinsicLocal {A : Type*} (L : SimpleGraph A) (X : Set A) : Prop :=
  (∃ a b c : A, L.Adj a b ∧ L.Adj b c ∧ L.Adj c a ∧ X ⊆ {a, b, c}) ∨
  FlatLocal L X

/-- A set misses at most one vertex of every triangle. -/
def IntrinsicSaturates {A : Type*} (L : SimpleGraph A) (X : Set A) : Prop :=
  ∀ a b c : A, L.Adj a b → L.Adj b c → L.Adj c a →
    (({a, b, c} : Set A) \ X).Subsingleton

theorem flatAdj_symm {A : Type*} {L : SimpleGraph A} {a b : A}
    (h : FlatAdj L a b) : FlatAdj L b a := by
  refine ⟨h.1.symm, ?_⟩
  rintro ⟨c, hbc, hac⟩
  exact h.2 ⟨c, hac, hbc⟩

/-- Flat adjacency is preserved by a graph isomorphism. -/
theorem flatAdj_map_iff {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
    (φ : L ≃g M) (a b : A) : FlatAdj M (φ a) (φ b) ↔ FlatAdj L a b := by
  constructor
  · rintro ⟨hab, htri⟩
    refine ⟨φ.map_rel_iff.mp hab, ?_⟩
    rintro ⟨c, hac, hbc⟩
    exact htri ⟨φ c, φ.map_rel_iff.mpr hac, φ.map_rel_iff.mpr hbc⟩
  · rintro ⟨hab, htri⟩
    refine ⟨φ.map_rel_iff.mpr hab, ?_⟩
    rintro ⟨d, had, hbd⟩
    refine htri ⟨φ.symm d, ?_, ?_⟩
    · simpa using φ.symm.map_rel_iff.mpr had
    · simpa using φ.symm.map_rel_iff.mpr hbd

theorem flat_reflTransGen_map {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
    (φ : L ≃g M) {a b : A} (h : Relation.ReflTransGen (FlatAdj L) a b) :
    Relation.ReflTransGen (FlatAdj M) (φ a) (φ b) :=
  h.lift φ (fun x y hxy => (flatAdj_map_iff φ x y).mpr hxy)

theorem flat_reflTransGen_map_iff {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
    (φ : L ≃g M) (a b : A) :
    Relation.ReflTransGen (FlatAdj M) (φ a) (φ b) ↔
      Relation.ReflTransGen (FlatAdj L) a b := by
  constructor
  · intro h
    have h' := flat_reflTransGen_map φ.symm h
    simpa using h'
  · exact flat_reflTransGen_map φ

/-- Intrinsic locality is preserved by a graph isomorphism. -/
theorem intrinsicLocal_image_iff {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
    (φ : L ≃g M) (X : Set A) :
    IntrinsicLocal M (φ '' X) ↔ IntrinsicLocal L X := by
  constructor
  · rintro (⟨a, b, c, hab, hbc, hca, hsub⟩ | hflat)
    · refine Or.inl ⟨φ.symm a, φ.symm b, φ.symm c, ?_, ?_, ?_, ?_⟩
      · exact φ.symm.map_rel_iff.mpr hab
      · exact φ.symm.map_rel_iff.mpr hbc
      · exact φ.symm.map_rel_iff.mpr hca
      · intro x hx
        have hm := hsub ⟨x, hx, rfl⟩
        rcases hm with hm | hm | hm
        · exact Or.inl (φ.injective (by simpa using hm))
        · exact Or.inr (Or.inl (φ.injective (by simpa using hm)))
        · exact Or.inr (Or.inr (φ.injective (by simpa using hm)))
    · refine Or.inr ?_
      rcases hflat with hempty | ⟨a, ha, hreach⟩
      · left
        apply Set.image_eq_empty.mp
        exact hempty
      · obtain ⟨a₀, ha₀, rfl⟩ := ha
        right
        refine ⟨a₀, ha₀, ?_⟩
        intro b hb
        have hb' : φ b ∈ φ '' X := ⟨b, hb, rfl⟩
        exact (flat_reflTransGen_map_iff φ a₀ b).mp (hreach (φ b) hb')
  · rintro (⟨a, b, c, hab, hbc, hca, hsub⟩ | hflat)
    · refine Or.inl ⟨φ a, φ b, φ c, φ.map_rel_iff.mpr hab, φ.map_rel_iff.mpr hbc,
        φ.map_rel_iff.mpr hca, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      rcases hsub hx with h | h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (Or.inl (by rw [h]))
      · exact Or.inr (Or.inr (by simpa using congrArg φ (by simpa using h)))
    · refine Or.inr ?_
      rcases hflat with rfl | ⟨a, ha, hreach⟩
      · exact Or.inl (Set.image_empty φ)
      · right
        refine ⟨φ a, ⟨a, ha, rfl⟩, ?_⟩
        rintro y ⟨b, hb, rfl⟩
        exact flat_reflTransGen_map φ (hreach b hb)

/-- Intrinsic saturation is preserved by a graph isomorphism. -/
theorem intrinsicSaturates_image_iff {A B : Type*} {L : SimpleGraph A} {M : SimpleGraph B}
    (φ : L ≃g M) (X : Set A) :
    IntrinsicSaturates M (φ '' X) ↔ IntrinsicSaturates L X := by
  constructor
  · intro h a b c hab hbc hca x hx y hy
    have hs := h (φ a) (φ b) (φ c) (φ.map_rel_iff.mpr hab) (φ.map_rel_iff.mpr hbc)
      (φ.map_rel_iff.mpr hca)
    have hx' : φ x ∈ ({φ a, φ b, φ c} : Set B) \ φ '' X := by
      refine ⟨?_, ?_⟩
      · rcases hx.1 with rfl | rfl | rfl <;> simp
      · rintro ⟨z, hz, heq⟩
        exact hx.2 (φ.injective heq ▸ hz)
    have hy' : φ y ∈ ({φ a, φ b, φ c} : Set B) \ φ '' X := by
      refine ⟨?_, ?_⟩
      · rcases hy.1 with rfl | rfl | rfl <;> simp
      · rintro ⟨z, hz, heq⟩
        exact hy.2 (φ.injective heq ▸ hz)
    exact φ.injective (hs hx' hy')
  · intro h a b c hab hbc hca x hx y hy
    have hs := h (φ.symm a) (φ.symm b) (φ.symm c)
      (φ.symm.map_rel_iff.mpr hab) (φ.symm.map_rel_iff.mpr hbc)
      (φ.symm.map_rel_iff.mpr hca)
    have hx' : φ.symm x ∈ ({φ.symm a, φ.symm b, φ.symm c} : Set A) \ X := by
      refine ⟨?_, ?_⟩
      · rcases hx.1 with rfl | rfl | rfl <;> simp
      · intro hm
        exact hx.2 ⟨φ.symm x, hm, φ.apply_symm_apply x⟩
    have hy' : φ.symm y ∈ ({φ.symm a, φ.symm b, φ.symm c} : Set A) \ X := by
      refine ⟨?_, ?_⟩
      · rcases hy.1 with rfl | rfl | rfl <;> simp
      · intro hm
        exact hy.2 ⟨φ.symm y, hm, φ.apply_symm_apply y⟩
    have heq := hs hx' hy'
    simpa using congrArg φ heq

end Workspace.ProofLemmas.Thm92Intrinsic
