import Mathlib
import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.Types.BasicClasses
import Workspace.Types.Replication
import Workspace.Types.Classes
import Workspace.Types.Prisms
import Workspace.Statements.S01.Thm_1_1
import Workspace.Statements.S01.Thm_1_3
import Workspace.Statements.S01.Thm_1_5
import Workspace.Statements.S01.Thm_E2_no_proper_2_join_in_minimum_imperfect
import Workspace.Statements.S01.Thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect
import Workspace.Statements.S01.Thm_E4_basic_implies_perfect
import Workspace.Statements.S01.Thm_E5_perfect_implies_berge
import Workspace.ProofLemmas.IsoTransport

/-!
# The Strong Perfect Graph Theorem — the main statement file

The numbered results of Section 1 of Chudnovsky, Robertson, Seymour and Thomas,
*The Strong Perfect Graph Theorem* (`perfect.pdf`, June 20 2002 / revised July 19 2005,
printed pages 1–4), together with the external results that the paper's deduction of
**1.2** from **1.3** relies on, and the two external results used inside its proof of
**1.5**.

The centrepiece is `thm_1_2`: *a graph is perfect if and only if it is Berge.*

Contents, in the order printed in the paper:

* `thm_1_1` — Lovász [16]: the complement of every perfect graph is perfect;
* `thm_1_2` — **the Strong Perfect Graph Theorem**;
* `thm_1_3` — the structure theorem for Berge graphs (the contents of sections 2–24);
* `thm_1_4` — the same with the proper-homogeneous-pair alternative removed
  (Chudnovsky's PhD thesis [3, 4]; stated but not proved in this paper);
* `thm_1_5` — no minimum imperfect graph admits a balanced skew partition;

and the external ingredients of the proof of 1.2, printed page 4:

* `thm_E2_no_proper_2_join_in_minimum_imperfect` — Cornuéjols and Cunningham [13];
* `thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect` — Chvátal and Sbihi [7];
* `thm_E4_basic_implies_perfect` — König [15], Lovász [16], and "the reader";
* `thm_E5_perfect_implies_berge`;

and the two external ingredients of the proof of 1.5, printed pages 3–4:

* `thm_E6_no_star_cutset_in_minimum_imperfect` — Chvátal [6];
* `thm_E7_lovasz_replication` — Lovász [16].

and the twelve steps of the proof of 1.3, printed page 7:

* `thm_1_8_1`, …, `thm_1_8_12` — the twelve numbered statements of **1.8**
  *(The steps of the proof of 1.3)*, which the paper proves in 5.1, 5.2, 9.6, 10.6, 13.4,
  14.3, 16.3, 18.7, 23.2, 23.4, 23.5 and 24.1 respectively.  They quantify over the classes
  `F₁, …, F₁₁` of `Workspace.Types.Classes` (`InF1`, …, `InF11`), and 1.8(4) additionally
  uses `IsEvenPrism` of `Workspace.Types.Prisms`.
* `thm_1_8_4_F3` — **not printed in the paper**: the corrected form of 1.8(4), with hypothesis
  `G ∈ F₃` in place of the printed `G ∈ F₁` and the identical conclusion.  Printed 1.8(4) is
  false — see the erratum and countermodel in the doc-comment of `thm_1_8_4`, `AMBIGUITIES.md`
  §A2a and `FIXES.md` §F2 — while this form is what 10.6 proves and what the chain
  `1.8(3) → 1.8(4) → 1.8(5)` needs.  `thm_1_8_4` itself is left exactly as printed.

Every definition used below is imported: `Berge`, `IsPerfect`, `MinimumImperfect` from
`Workspace.Types.Core`; `AdmitsProper2Join`, `AdmitsProperHomogeneousPair`,
`AdmitsBalancedSkewPartition`, `AdmitsStarCutset` from `Workspace.Types.Decompositions`;
`IsBasic` from `Workspace.Types.BasicClasses`; `replicateVertex` from
`Workspace.Types.Replication`.  Nothing is restated here.

Ambient conventions (see `paper/spec/CONVENTIONS.md`): all graphs of the paper are finite
and simple, so the vertex type carries `[Fintype V]` (and `[DecidableEq V]`); the paper's
`Ḡ` is Mathlib's `Gᶜ`.
-/

namespace Workspace.MainTheorem

open Workspace.Types.Core Workspace.Types.Decompositions
open Workspace.Types.BasicClasses Workspace.Types.Replication
open Workspace.Types.Classes Workspace.Types.Prisms

namespace SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

-- `thm_1_2` is stated for a vertex type carrying both `[Fintype V]` and `[DecidableEq V]`
-- (the paper's ambient convention, see `paper/spec/CONVENTIONS.md`).  Its proof happens to
-- consume only `[Fintype V]`, because the paper's argument is run at the *minimum*
-- counterexample, which lives on `Fin n₀`, where decidable equality is automatic.  The
-- statement's binders are frozen, so the section variable stays and the linter is silenced.
set_option linter.unusedSectionVars false


/-- **The four printed sentences of the proof of 1.2** (printed p. 4, *"Proof of 1.2,
assuming 1.3"*), packaged as a standalone statement: *no graph on a finite vertex type
with decidable equality is a minimum imperfect graph.*

PAPER: *"Suppose that there is a minimum imperfect graph `G`.  Thus `G` is Berge and not
perfect.  Every basic graph is perfect, and so `G` is not basic.  It is shown in [13] that
`G` does not admit a proper 2-join.  From Lovász's theorem 1.1, it follows that `Ḡ` is also
a minimum imperfect graph, and therefore `Ḡ` also does not admit a proper 2-join.  It is
shown in [7] that `G` does not admit a proper homogeneous pair, and `G` does not admit a
balanced skew partition by 1.5.  It follows that `G` violates 1.3, and therefore there is
no such graph `G`."*

`[DecidableEq W]` is required, not decorative: the final step applies `thm_1_3` and
`thm_1_5`, both stated under `[Fintype V] [DecidableEq V]`.  It costs nothing, because this
  lemma is only ever applied at `W = Fin n₀`, where both instances are automatic. -/
theorem no_minimumImperfect {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) (hG : SPGT.MinimumImperfect G) : False := by
  -- *"Thus `G` is Berge and not perfect."*  (Page 1: *"in particular, any such graph is
  -- Berge and not perfect"*.)  Both follow from the first conjunct of `MinimumImperfect`
  -- together with E5, *"every perfect graph is Berge"*.
  have hnp : ¬ SPGT.IsPerfect G :=
    _root_.Workspace.ProofLemmas.IsoTransport.minimumImperfect_not_perfect hG
      (thm_E5_perfect_implies_berge G)
  have hb : SPGT.Berge G :=
    _root_.Workspace.ProofLemmas.IsoTransport.minimumImperfect_berge hG
      (thm_E5_perfect_implies_berge G)
  -- *"Every basic graph is perfect, and so `G` is not basic."*
  have hnotbasic : ¬ SPGT.IsBasic G := fun hbasic =>
    hnp (thm_E4_basic_implies_perfect G hbasic)
  -- *"It is shown in [13] that `G` does not admit a proper 2-join."*
  have hno2join : ¬ SPGT.AdmitsProper2Join G :=
    thm_E2_no_proper_2_join_in_minimum_imperfect G hG
  -- *"From Lovász's theorem 1.1, it follows that `Ḡ` is also a minimum imperfect graph …"*
  have hGc : SPGT.MinimumImperfect Gᶜ :=
    _root_.Workspace.ProofLemmas.IsoTransport.minimumImperfect_compl' hG
      (fun K hK => thm_1_1 K hK)
  -- *"… and therefore `Ḡ` also does not admit a proper 2-join."*
  have hno2joinc : ¬ SPGT.AdmitsProper2Join Gᶜ :=
    thm_E2_no_proper_2_join_in_minimum_imperfect Gᶜ hGc
  -- *"It is shown in [7] that `G` does not admit a proper homogeneous pair …"*
  have hnohp : ¬ SPGT.AdmitsProperHomogeneousPair G :=
    thm_E3_no_proper_homogeneous_pair_in_minimum_imperfect G hG
  -- *"… and `G` does not admit a balanced skew partition by 1.5."*
  have hnoskew : ¬ SPGT.AdmitsBalancedSkewPartition G := thm_1_5 G hG
  -- *"It follows that `G` violates 1.3, and therefore there is no such graph `G`."*
  rcases thm_1_3 G hb with h | (h | h) | h | h
  · exact hnotbasic h
  · exact hno2join h
  · exact hno2joinc h
  · exact hnohp h
  · exact hnoskew h


/-- **1.2** (printed p. 1) — **the Strong Perfect Graph Theorem**, the main theorem of the
paper and of this development.

PAPER: *"A graph is perfect if and only if it is Berge."*

*"The second conjecture has remained open until now; it was known as the strong perfect
graph conjecture, and the following is the main result of this paper."*

There is no hypothesis beyond the ambient one that the vertex type is finite: the assertion
is about *every* graph. -/
theorem thm_1_2 (G : SimpleGraph V) :
    SPGT.IsPerfect G ↔ SPGT.Berge G := by
  constructor
  · -- *"It is easy to see that every perfect graph is Berge, and so to prove 1.2 it
    -- remains to prove the converse."*  (printed p. 1)
    exact fun hp => thm_E5_perfect_implies_berge G hp
  · -- The converse.  Suppose it fails at `G`; then `G` is a counterexample to 1.2 …
    intro hB
    by_contra hnP
    have hcex : ¬ (SPGT.IsPerfect G ↔ SPGT.Berge G) := fun hiff => hnP (hiff.mpr hB)
    -- … and so, taking a counterexample *"with as few vertices as possible"*, there is a
    -- minimum imperfect graph.  This is the paper's *"Suppose that there is a minimum
    -- imperfect graph `G`."*
    obtain ⟨n₀, H₀, hH₀⟩ :=
      _root_.Workspace.ProofLemmas.IsoTransport.exists_minimumImperfect G hcex
    -- *"… and therefore there is no such graph `G`.  This proves 1.2."*
    exact no_minimumImperfect H₀ hH₀


end SPGT

end Workspace.MainTheorem
