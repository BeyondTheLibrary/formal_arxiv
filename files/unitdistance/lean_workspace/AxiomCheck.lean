/-
# Axiom audit

`lake env lean AxiomCheck.lean` prints, for the root theorem and for each prior-work statement the
formalization relies on, the axioms it depends on.  All but two are proved from Mathlib and show
`[propext, Classical.choice, Quot.sound]` (Mathlib's own axioms); these live under
`Workspace/ProofLemmas/`.  The two still admitted as axioms — `GolodShafarevichFiltration` and
`ShafarevichRelationRank`, both used by the main theorem — are under `Workspace/PriorWork/`.

Expected output for the root theorem:

`[GolodShafarevichFiltration, ShafarevichRelationRank, propext, Classical.choice, Quot.sound]`
-/
import Workspace.MainTheorem
import Workspace.ProofLemmas.ChebotarevManySplitPrimes
import Workspace.ProofLemmas.CompositumFamilyOddFinrank
import Workspace.ProofLemmas.CompositumFamilyUnramifiedAtFinitePrimes
import Workspace.ProofLemmas.ConductorMultiplicativeFamily
import Workspace.ProofLemmas.CutOutFieldEqCyclicCubic
import Workspace.ProofLemmas.CutOutFieldLevelInvariant
import Workspace.ProofLemmas.CyclicCubicSubfieldConductor
import Workspace.ProofLemmas.CyclicCubicSubfieldDegree
import Workspace.ProofLemmas.CyclicCubicSubfieldTotallyReal
import Workspace.ProofLemmas.FrobRepExistsMaxUnramified
import Workspace.ProofLemmas.GalUrFrattiniQuotientFinite
import Workspace.ProofLemmas.GalUrOpenNormalThreePowerIndex
import Workspace.ProofLemmas.GalUrTopFinGen
import Workspace.PriorWork.GolodShafarevichFiltration
import Workspace.ProofLemmas.GolodShafarevichInequality
import Workspace.ProofLemmas.IdealCountByNormBound
import Workspace.ProofLemmas.IdealCountDivisorTuple
import Workspace.ProofLemmas.PrimesOneModThreeLogSum
import Workspace.ProofLemmas.PrimesOneModThreePolyBound
import Workspace.ProofLemmas.ProPBurnsideBasis
import Workspace.ProofLemmas.ProPFrattiniQuotientRanks
import Workspace.ProofLemmas.ProPGeneratorRankFrattini
import Workspace.ProofLemmas.ProPMaximalOpenNormalIndexP
import Workspace.ProofLemmas.ProPRelationRankFrattiniQuotient
import Workspace.ProofLemmas.ProPTopologicalNakayama
import Workspace.PriorWork.ShafarevichRelationRank
import Workspace.ProofLemmas.SublemmaProPQuotientClosed
import Workspace.ProofLemmas.SublemmaSplittingTransitive
import Workspace.ProofLemmas.SublemmaSubextUnramified
import Workspace.ProofLemmas.SublemmaTopFinGenQuotientClosed
import Workspace.ProofLemmas.SublemmaTrivialFrobSplits
import Workspace.ProofLemmas.UnramifiedProPDescendingChain
import Workspace.ProofLemmas.UnramifiedProPTowerCorrespondence

#print axioms Workspace.MainTheorem.theorem_1_1_unit_distance

#print axioms ChebotarevManySplitPrimes
#print axioms CompositumFamilyOddFinrank
#print axioms CompositumFamilyUnramifiedAtFinitePrimes
#print axioms ConductorMultiplicativeFamily
#print axioms CutOutFieldEqCyclicCubic
#print axioms CutOutFieldLevelInvariant
#print axioms CyclicCubicSubfieldConductor
#print axioms CyclicCubicSubfieldDegree
#print axioms CyclicCubicSubfieldTotallyReal
#print axioms FrobRepExistsMaxUnramified
#print axioms GalUrFrattiniQuotientFinite
#print axioms GalUrOpenNormalThreePowerIndex
#print axioms GalUrTopFinGen
#print axioms GolodShafarevichFiltration
#print axioms GolodShafarevichInequality
#print axioms IdealCountByNormBound
#print axioms IdealCountDivisorTuple
#print axioms PrimesOneModThreeLogSum
#print axioms PrimesOneModThreePolyBound
#print axioms ProPBurnsideBasis
#print axioms ProPFrattiniQuotientRanks
#print axioms ProPGeneratorRankFrattini
#print axioms ProPMaximalOpenNormalIndexP
#print axioms ProPRelationRankFrattiniQuotient
#print axioms ProPTopologicalNakayama
#print axioms ShafarevichRelationRank
#print axioms SublemmaProPQuotientClosed
#print axioms SublemmaSplittingTransitive
#print axioms SublemmaSubextUnramified
#print axioms SublemmaTopFinGenQuotientClosed
#print axioms SublemmaTrivialFrobSplits
#print axioms UnramifiedProPDescendingChain
#print axioms UnramifiedProPTowerCorrespondence
