-- Cited from: Standard: the continuous image of a topologically finitely generated group is topologically finitely generated; L. Ribes and P. Zalesskii, Profinite Groups, 2nd ed., Springer, 2010.
-- Paper label: standard profinite fact (implicit in paper Step 2, tex 747-781)
-- NL statement: A quotient G/N of a topologically finitely generated topological group G by a closed normal subgroup N is again topologically finitely generated (the images of the generators topologically generate the quotient).
-- Proof: the quotient map QuotientGroup.mk' N is surjective and
-- continuous; push the finite topological generators through it via MonoidHom.map_closure
-- and image_closure_subset_closure_image.
import Mathlib
import Workspace.Types.ProPGroup

open Workspace.Types.ProPGroup

set_option maxHeartbeats 800000 in
theorem SublemmaTopFinGenQuotientClosed :
    ∀ (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (N : Subgroup G) [N.Normal],
      TopFinitelyGenerated G → TopFinitelyGenerated (G ⧸ N) := by
  intro G _ _ _ N _ hG
  classical
  obtain ⟨S, hS⟩ := hG
  refine ⟨S.image (QuotientGroup.mk' N), ?_⟩
  set π : G →* G ⧸ N := QuotientGroup.mk' N with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective N
  have hcont : Continuous π := QuotientGroup.continuous_mk
  unfold TopologicallyGenerates at hS ⊢
  -- rewrite the generated subgroup of the image of S as the image of the generated subgroup of S
  have hcoe : ((Subgroup.closure ((S.image π : Finset (G ⧸ N)) : Set (G ⧸ N)) : Subgroup (G ⧸ N)) : Set (G ⧸ N))
      = π '' ((Subgroup.closure (S : Set G) : Subgroup G) : Set G) := by
    rw [Finset.coe_image, ← MonoidHom.map_closure, Subgroup.coe_map]
  rw [hcoe]
  -- now: closure (π '' ↑(Subgroup.closure ↑S)) = univ
  apply Set.eq_univ_of_univ_subset
  have himg : π '' (Set.univ : Set G) = Set.univ := by
    rw [Set.image_univ, Set.range_eq_univ]; exact hsurj
  calc (Set.univ : Set (G ⧸ N))
      = π '' (Set.univ : Set G) := himg.symm
    _ = π '' (_root_.closure ((Subgroup.closure (S : Set G) : Subgroup G) : Set G)) := by rw [hS]
    _ ⊆ _root_.closure (π '' ((Subgroup.closure (S : Set G) : Subgroup G) : Set G)) :=
        image_closure_subset_closure_image hcont
