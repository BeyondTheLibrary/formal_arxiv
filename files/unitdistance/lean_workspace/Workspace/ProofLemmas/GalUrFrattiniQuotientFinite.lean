-- Cited from: unramified class field theory. For a number field F, the Artin reciprocity map of
-- the maximal everywhere-unramified abelian extension induces an isomorphism of the
-- abelianized Galois group Gal(F^{ur}/F)^{ab} with the ideal class group Cl_F (Hilbert class
-- field theory), and passing to the 3-part gives Gal(F^{ur,3}/F)^{ab}/3 ≅ Cl_F ⊗ Z/3Z. The
-- Frattini quotient galUr 3 F / Φ(galUr 3 F) of the pro-3 group G = Gal(F^{ur,3}/F) is the maximal
-- elementary-abelian-3 quotient of G, hence a quotient of G^{ab}/3 ≅ Cl_F ⊗ Z/3Z; since the class
-- group Cl_F is finite (Minkowski / NumberField.instFintypeClassGroup in Mathlib), the Frattini
-- quotient is finite. See: J. Neukirch, A. Schmidt, K. Wingberg, Cohomology of Number Fields, 2nd
-- ed., Springer, 2008, Ch. X (unramified extensions and class groups); H. Koch, Galois Theory of
-- p-Extensions, Springer, 2002, §11 (Golod–Shafarevich, generator rank of the class-field tower).
--
-- Paper label: [NSW08, Ch X] / [Koch §11] (Artin-map bridge, background to Prop A.10)
--
-- Classically (unramified class field theory) this follows from the Artin reciprocity
-- correspondence between the Frattini quotient of the unramified pro-3 Galois group and the 3-part
-- of the class group, which is not currently a Mathlib lemma: the Artin map gives
-- G^{ab}/3 ≅ Cl_F ⊗ Z/3Z, and Cl_F is finite via class-group finiteness
-- (NumberField.instFintypeClassGroup), so the Frattini quotient is finite.
--
-- NL statement: For every number field F, the topological Frattini quotient of the Galois group
-- G = galUr 3 F of the maximal everywhere-unramified pro-3 extension F^{ur,3}/F is finite:
-- Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)). Equivalently, the maximal elementary-abelian-3
-- quotient of G is finite, which by the unramified Artin map is a quotient of Cl_F ⊗ Z/3Z and hence
-- finite because the class group is finite.
--
-- The Artin-reciprocity route is not available in Mathlib; the proof instead uses the **Hermite**
-- route, which reaches the statement from Mathlib alone:
--   * every maximal proper open subgroup of `G = galUr 3 F` is normal of index 3 (pro-3-ness);
--   * `H ↦ fixedFieldOf 3 F H` is injective on them (infinite Galois correspondence, the already
--     proved `UnramifiedProPTowerCorrespondence_partA`);
--   * each such fixed field is a degree-3 everywhere-unramified extension of `F`
--     (`SublemmaSubextUnramified`), so its relative different ideal is trivial and the
--     different/discriminant tower formula gives `|D_E| = |D_F|³`;
--   * **Hermite's theorem** `NumberField.finite_of_discr_bdd` bounds the number of number fields of
--     bounded discriminant, so there are finitely many maximal open subgroups;
--   * therefore `Φ(G)` is open (a finite intersection of open subgroups) and `G` is compact, so
--     `G ⧸ Φ(G)` is finite.
-- The proof lives in `Workspace.ProofLemmas.GalUrFrattiniFinite`.
import Mathlib
import Workspace.Types.UnramifiedProPExtension
import Workspace.Types.ProPGroup
import Workspace.ProofLemmas.GalUrFrattiniFinite

open scoped NumberField
open Workspace.Types.UnramifiedProPExtension
open Workspace.Types.ProPGroup

/-- For a number field `F`, the topological Frattini quotient of `G = galUr 3 F` (the Galois group
of the maximal everywhere-unramified pro-`3` extension `F^{ur,3}/F`) is finite.

Proved from Mathlib via Hermite's finiteness theorem for number fields of bounded discriminant — see
`Workspace.ProofLemmas.GalUrFrattiniFinite`. -/
theorem GalUrFrattiniQuotientFinite :
    ∀ (F : Type) [Field F] [NumberField F],
      Finite (galUr 3 F ⧸ frattiniOpen (galUr 3 F)) :=
  fun F _ _ => Workspace.ProofLemmas.GalUrFrattiniFinite.galUrFrattiniQuotientFinite F
