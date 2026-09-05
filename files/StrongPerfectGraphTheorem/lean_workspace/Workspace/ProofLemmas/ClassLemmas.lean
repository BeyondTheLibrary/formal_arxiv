import Mathlib
import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.DoubleDiamond
import Workspace.Types.Appearances
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.PathBasics

/-!
# Bookkeeping lemmas about the classes `F₁ … F₁₁` and complementation

None of these lemmas has a counterpart in the paper: the paper uses them silently
whenever it writes *"and the same holds in `Ḡ`"*.

`InF3`, `InF5`, …, `InF10` are all complement-closed (`inF3_compl` … `inF10_compl`).
The only asymmetric conjunct in that chain is `InF6`'s *"no induced subgraph of `G` is
isomorphic to a double diamond"*, imposed on `G` alone; `doubleDiamond_self_compl`
repairs it by exhibiting the relabelling that makes the double diamond
self-complementary.

## What is deliberately absent, and why

Three complement-closure statements one might expect here are **false**, so they are
not stated.  Each is refuted by an explicit finite countermodel.

* **`InF4` is not complement-closed.**  `InF4 G = InF3 G ∧ (no even prism in G)` — the
  even-prism clause is imposed on `G` only and complementation does not preserve it.
  (`InF5` is defined from `InF3`, not from `InF4`, so nothing in the chain above needs
  it; see the printed quirk recorded in `AMBIGUITIES.md` §A2.)

* **`InF11` is not complement-closed.**  `InF11 G` bounds the *antiholes* of `G`,
  whereas `InF11 Gᶜ` bounds its *holes* — see `inF11_compl_iff`, which is the true
  statement in the neighbourhood.  Countermodel: `G = C₆`, the 6-cycle, whose
  complement is the triangular prism.  `InF11 C₆` holds (every clause of the chain
  `InF11 → InF10 → … → InF3` is satisfied, most of them vacuously: a double diamond
  needs 8 vertices, a pseudowheel needs 7, the smallest `L(H)` for a bipartite
  subdivision `H` of `K₄` has 8, a wheel needs a hole of length `≥ 6` *plus* a
  nonempty `Y` off that hole, and every hole of `C₆` uses all six vertices), while
  `InF11 (C₆)ᶜ` fails because `C₆` has a hole of length 6, not 4.  Taking `G` to be
  the prism instead refutes the reverse implication, so neither direction survives.

* **`AdmitsProper2Join` is not complement-closed.**  Countermodel on six vertices:
  let `G` be two triangles `{0,1,2}`, `{3,4,5}` plus the two edges `0-3` and `1-4`.
  Then `G` admits a proper 2-join — take `X₁ = {0,1,2}`, `X₂ = {3,4,5}`,
  `A₁ = {0}`, `B₁ = {1}`, `A₂ = {3}`, `B₂ = {4}`; the fourth bullet is vacuous because
  a triangle has no spanning induced path — whereas `Gᶜ` (which is `K₃,₃` minus the
  matching `{0-3, 1-4}`) admits none, checked exhaustively over all partitions and all
  choices of `A₁, B₁, A₂, B₂`.  Already for the natural partition the cross-edges of
  `Gᶜ` between `{0,1,2}` and `{3,4,5}` number 7, while `|A₁||A₂| + |B₁||B₂| ≤ 5` for
  any admissible choice, so the "no other edges between `X₁` and `X₂`" clause cannot
  be met.  This is expected, not a defect: the paper always writes *"one of `G`, `Ḡ`
  admits a proper 2-join"*, never transferring a 2-join across complementation.

`AdmitsProperHomogeneousPair` is likewise not complement-closed; that countermodel is
recorded in `proof_tree/_1_8_mapping.md` (item 5, **L10**).
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.ClassLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances.SPGT

/-! ## Isomorphism direction -/

section Iso

variable {α β : Type*} {A : SimpleGraph α} {B : SimpleGraph β}

/-- `Nonempty (· ≃g ·)` is symmetric.  `InF1`/`InF3` store
`Nonempty (G.induce K ≃g H.lineGraph)` while `IsAppearance` stores the reverse. -/
theorem nonempty_iso_symm : Nonempty (A ≃g B) ↔ Nonempty (B ≃g A) :=
  ⟨fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ => ⟨e.symm⟩⟩

end Iso

section IsoExists

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- The same flip, under the existential over the vertex set. -/
theorem exists_induce_iso_comm :
    (∃ K : Set V, Nonempty (G.induce K ≃g H)) ↔ (∃ K : Set V, Nonempty (H ≃g G.induce K)) := by
  constructor
  · rintro ⟨K, hK⟩; exact ⟨K, nonempty_iso_symm.mp hK⟩
  · rintro ⟨K, hK⟩; exact ⟨K, nonempty_iso_symm.mp hK⟩

end IsoExists

/-! ## Appearances of `K₄` -/

section Appearance

/-- For `J = K₄` the second branch of `DegenerateAppearance` is vacuous. -/
theorem degenerateAppearance_K4_iff {W : Type*} {H : SimpleGraph W} :
    DegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ↔ DegenerateK4Appearance H := by
  constructor
  · rintro (⟨-, h⟩ | ⟨hn, -, -⟩)
    · exact h
    · exact absurd ⟨SimpleGraph.Iso.refl⟩ hn
  · intro h
    exact Or.inl ⟨⟨SimpleGraph.Iso.refl⟩, h⟩

/-- **L8.** -/
theorem nondegenerateAppearance_K4_iff {W : Type*} {H : SimpleGraph W} :
    NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H ↔ ¬ DegenerateK4Appearance H :=
  not_congr degenerateAppearance_K4_iff

end Appearance

/-! ## The double diamond is self-complementary -/

section DoubleDiamond

variable {V : Type*} {G : SimpleGraph V}

/-- **L5.**  The double diamond is self-complementary, under the relabelling
`(a₁,a₂,a₃,a₄,b₁,b₂,b₃,b₄) ↦ (a₃,a₄,b₁,b₂,b₄,b₃,a₂,a₁)`. -/
theorem doubleDiamond_self_compl {a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V}
    (h : IsDoubleDiamond Gᶜ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) :
    IsDoubleDiamond G a₃ a₄ b₁ b₂ b₄ b₃ a₂ a₁ := by
  obtain ⟨hnd, ⟨ha12, ha13, ha14, ha23, ha24, hna34⟩,
    ⟨hb12, hb13, hb14, hb23, hb24, hnb34⟩,
    ⟨hab1, hab2, hab3, hab4⟩,
    ⟨hn12, hn13, hn14, hn21, hn23, hn24, hn31, hn32, hn34, hn41, hn42, hn43⟩⟩ := h
  have edge : ∀ x y : V, x ≠ y → ¬ Gᶜ.Adj x y → G.Adj x y := by
    intro x y hne hnc
    by_contra hg
    exact hnc ((SimpleGraph.compl_adj G x y).mpr ⟨hne, hg⟩)
  have nonedge : ∀ x y : V, Gᶜ.Adj x y → ¬ G.Adj x y := by
    intro x y hc
    exact ((SimpleGraph.compl_adj G x y).mp hc).2
  have d12 : a₃ ≠ a₄ := by rintro rfl; simp at hnd
  have d13 : a₃ ≠ b₁ := by rintro rfl; simp at hnd
  have d14 : a₃ ≠ b₂ := by rintro rfl; simp at hnd
  have d15 : a₃ ≠ b₄ := by rintro rfl; simp at hnd
  have d16 : a₃ ≠ b₃ := by rintro rfl; simp at hnd
  have d17 : a₃ ≠ a₂ := by rintro rfl; simp at hnd
  have d18 : a₃ ≠ a₁ := by rintro rfl; simp at hnd
  have d23 : a₄ ≠ b₁ := by rintro rfl; simp at hnd
  have d24 : a₄ ≠ b₂ := by rintro rfl; simp at hnd
  have d25 : a₄ ≠ b₄ := by rintro rfl; simp at hnd
  have d26 : a₄ ≠ b₃ := by rintro rfl; simp at hnd
  have d27 : a₄ ≠ a₂ := by rintro rfl; simp at hnd
  have d28 : a₄ ≠ a₁ := by rintro rfl; simp at hnd
  have d34 : b₁ ≠ b₂ := by rintro rfl; simp at hnd
  have d35 : b₁ ≠ b₄ := by rintro rfl; simp at hnd
  have d36 : b₁ ≠ b₃ := by rintro rfl; simp at hnd
  have d37 : b₁ ≠ a₂ := by rintro rfl; simp at hnd
  have d38 : b₁ ≠ a₁ := by rintro rfl; simp at hnd
  have d45 : b₂ ≠ b₄ := by rintro rfl; simp at hnd
  have d46 : b₂ ≠ b₃ := by rintro rfl; simp at hnd
  have d47 : b₂ ≠ a₂ := by rintro rfl; simp at hnd
  have d48 : b₂ ≠ a₁ := by rintro rfl; simp at hnd
  have d56 : b₄ ≠ b₃ := by rintro rfl; simp at hnd
  have d57 : b₄ ≠ a₂ := by rintro rfl; simp at hnd
  have d58 : b₄ ≠ a₁ := by rintro rfl; simp at hnd
  have d67 : b₃ ≠ a₂ := by rintro rfl; simp at hnd
  have d68 : b₃ ≠ a₁ := by rintro rfl; simp at hnd
  have d78 : a₂ ≠ a₁ := by rintro rfl; simp at hnd
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp [d12, d13, d14, d15, d16, d17, d18, d23, d24, d25, d26, d27, d28,
      d34, d35, d36, d37, d38, d45, d46, d47, d48, d56, d57, d58, d67, d68, d78]
  -- every two `Aᵢ`'s adjacent except `A₃A₄`
  · exact edge _ _ d12 hna34
  · exact edge _ _ d13 hn31
  · exact edge _ _ d14 hn32
  · exact edge _ _ d23 hn41
  · exact edge _ _ d24 hn42
  · exact nonedge _ _ hb12
  -- every two `Bᵢ`'s adjacent except `B₃B₄`
  · exact edge _ _ d56 fun hc => hnb34 hc.symm
  · exact edge _ _ d57 fun hc => hn24 hc.symm
  · exact edge _ _ d58 fun hc => hn14 hc.symm
  · exact edge _ _ d67 fun hc => hn23 hc.symm
  · exact edge _ _ d68 fun hc => hn13 hc.symm
  · exact nonedge _ _ ha12.symm
  -- the four edges `AᵢBᵢ`
  · exact edge _ _ d15 hn34
  · exact edge _ _ d26 hn43
  · exact edge _ _ d37 fun hc => hn21 hc.symm
  · exact edge _ _ d48 fun hc => hn12 hc.symm
  -- the twelve non-edges `AᵢBⱼ`, `i ≠ j`
  · exact nonedge _ _ hab3
  · exact nonedge _ _ ha23.symm
  · exact nonedge _ _ ha13.symm
  · exact nonedge _ _ hab4
  · exact nonedge _ _ ha24.symm
  · exact nonedge _ _ ha14.symm
  · exact nonedge _ _ hb14
  · exact nonedge _ _ hb13
  · exact nonedge _ _ hab1.symm
  · exact nonedge _ _ hb24
  · exact nonedge _ _ hb23
  · exact nonedge _ _ hab2.symm

/-- Consequently `G` contains a double diamond iff `Ḡ` does. -/
theorem exists_isDoubleDiamond_compl :
    (∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond Gᶜ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) ↔
      (∃ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : V, IsDoubleDiamond G a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄) := by
  constructor
  · rintro ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, hdd⟩
    exact ⟨_, _, _, _, _, _, _, _, doubleDiamond_self_compl hdd⟩
  · rintro ⟨a₁, a₂, a₃, a₄, b₁, b₂, b₃, b₄, hdd⟩
    have hdd' : IsDoubleDiamond Gᶜᶜ a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ := by rwa [compl_compl]
    exact ⟨_, _, _, _, _, _, _, _, doubleDiamond_self_compl hdd'⟩

end DoubleDiamond

/-! ## Complement closure of the classes -/

section Classes

variable {V : Type*} {G : SimpleGraph V}

/-- **L3.** -/
theorem inF3_compl : InF3 Gᶜ ↔ InF3 G := by
  simp only [InF3, compl_compl, HoleBasics.berge_compl]
  constructor
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun n H hs => ⟨(h n H hs).2, (h n H hs).1⟩⟩
  · rintro ⟨hb, h⟩
    exact ⟨hb, fun n H hs => ⟨(h n H hs).2, (h n H hs).1⟩⟩

/-- **L4.** -/
theorem inF5_compl : InF5 Gᶜ ↔ InF5 G := by
  simp only [InF5, compl_compl, inF3_compl]
  constructor <;> rintro ⟨x, y, z⟩ <;> exact ⟨x, z, y⟩

/-- **L6**, the substantive link: it holds because the double diamond is
self-complementary (`doubleDiamond_self_compl`). -/
theorem inF6_compl : InF6 Gᶜ ↔ InF6 G := by
  simp only [InF6, inF5_compl, exists_isDoubleDiamond_compl]

theorem inF7_compl : InF7 Gᶜ ↔ InF7 G := by
  simp only [InF7, compl_compl, inF6_compl]
  constructor <;> rintro ⟨x, y, z⟩ <;> exact ⟨x, z, y⟩

theorem inF8_compl : InF8 Gᶜ ↔ InF8 G := by
  simp only [InF8, compl_compl, inF7_compl]
  constructor <;> rintro ⟨x, y, z⟩ <;> exact ⟨x, z, y⟩

theorem inF9_compl : InF9 Gᶜ ↔ InF9 G := by
  simp only [InF9, compl_compl, inF8_compl]
  constructor <;> rintro ⟨x, y, z⟩ <;> exact ⟨x, z, y⟩

theorem inF10_compl : InF10 Gᶜ ↔ InF10 G := by
  simp only [InF10, compl_compl, inF9_compl]
  constructor <;> rintro ⟨x, y, z⟩ <;> exact ⟨x, z, y⟩

/-- `InF11` is **not** complement-closed; this records exactly what `InF11 Gᶜ` says
in terms of `G`.  The missing content is the second conjunct: `InF11 G` bounds the
*antiholes* of `G`, `InF11 Gᶜ` bounds its *holes*. -/
theorem inF11_compl_iff :
    InF11 Gᶜ ↔ (InF10 G ∧ ∀ c : List V, IsHoleList G c → holeLength c = 4) := by
  simp only [InF11, IsAntiholeList, compl_compl, inF10_compl]

end Classes

/-! ## Complementation of the balanced skew partition -/

section Balanced

variable {V : Type*} {G : SimpleGraph V} {p : List V} {u : V}

/-- A path whose two ends coincide is a single vertex, so it has length `0`.  This is
the degenerate case that the complementation of `Balanced` has to dispose of. -/
private theorem not_odd_pathLength_of_ends_eq (h : IsPathFrom G p u u) :
    ¬ Odd (pathLength p) := by
  have h1 : ¬ (1 ≤ pathLength p) := fun hl => PathBasics.isPathFrom_ends_ne h hl rfl
  have h0 : pathLength p = 0 := by omega
  rw [h0]
  simp

end Balanced

section Skew

variable {V : Type*} {G : SimpleGraph V} {A B : Set V}

/-- The two clauses of `Balanced` swap under complementation.  (`Balanced` has to be
written out in full: the root namespace has a different `Balanced`, for balanced sets
in a seminormed ring.) -/
theorem balanced_compl :
    Workspace.Types.Core.SPGT.Balanced Gᶜ B A ↔ Workspace.Types.Core.SPGT.Balanced G A B := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro u v q hu hv hadj hq hint
      rcases eq_or_ne u v with rfl | hne
      · exact not_odd_pathLength_of_ends_eq hq
      · exact h2 u v q hu hv ((SimpleGraph.compl_adj G u v).mpr ⟨hne, hadj⟩)
          (PathBasics.isAntipathFrom_compl.mpr hq) hint
    · intro u v q hu hv hadj hq hint
      exact h1 u v q hu hv (fun hc => ((SimpleGraph.compl_adj G u v).mp hc).2 hadj) hq hint
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro u v q hu hv hadj hq hint
      rcases eq_or_ne u v with rfl | hne
      · exact not_odd_pathLength_of_ends_eq hq
      · refine h2 u v q hu hv ?_ hq hint
        by_contra hg
        exact hadj ((SimpleGraph.compl_adj G u v).mpr ⟨hne, hg⟩)
    · intro u v q hu hv hadj hq hint
      exact h1 u v q hu hv ((SimpleGraph.compl_adj G u v).mp hadj).2
        (PathBasics.isAntipathFrom_compl.mp hq) hint

/-- A skew partition of `Ḡ` is a skew partition of `G` with the two sides swapped. -/
theorem isSkewPartition_compl : IsSkewPartition Gᶜ B A ↔ IsSkewPartition G A B := by
  simp only [IsSkewPartition, AnticonnectedSet, compl_compl]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [Set.union_comm]; exact h1, h2.symm, h4, h3⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [Set.union_comm]; exact h1, h2.symm, h4, h3⟩

theorem isBalancedSkewPartition_compl :
    IsBalancedSkewPartition Gᶜ B A ↔ IsBalancedSkewPartition G A B :=
  and_congr isSkewPartition_compl balanced_compl

/-- **L7.** -/
theorem admitsBalancedSkewPartition_compl :
    AdmitsBalancedSkewPartition Gᶜ ↔ AdmitsBalancedSkewPartition G := by
  constructor
  · rintro ⟨X, Y, h⟩
    exact ⟨Y, X, isBalancedSkewPartition_compl.mp h⟩
  · rintro ⟨X, Y, h⟩
    exact ⟨Y, X, isBalancedSkewPartition_compl.mpr h⟩

end Skew

end Workspace.ProofLemmas.ClassLemmas
