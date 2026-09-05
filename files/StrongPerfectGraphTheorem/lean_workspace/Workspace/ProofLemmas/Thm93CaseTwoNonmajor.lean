import Workspace.ProofLemmas.Thm93CaseTwoNonmajorDict
import Workspace.ProofLemmas.Thm93CaseOneLong
import Workspace.ProofLemmas.Thm93CaseOneEnlarge
import Workspace.ProofLemmas.Thm93CaseTwoNonmajorRepair
import Workspace.ProofLemmas.HoleBasics
import Workspace.Statements.S09.Thm_9_1

/-!
# Claim (2) of 9.3: the non-major vertex

PAPER (proof of 9.3, printed p. 49): *"(2) If there exists `f ∈ F` such that `f` is not major
with respect to `L(H)` in `G̅`, then the theorem holds."*

The caller has already applied 5.8 in `G̅` to the singleton `{f}`.  This module turns the
outcome of that application into the conclusion of 9.3.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm93CaseTwoNonmajor

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm93Infrastructure
open Workspace.ProofLemmas.Thm93CaseTwoSixOnePairs
open Workspace.ProofLemmas.Thm93CaseTwoNonmajorDict

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Two shapes of the conclusion of 9.3, for a one-vertex path `R = [f]` -/

/-- Statement 2 of 9.3 with the degenerate path `R = [f]`. -/
theorem conclusion_two {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K F : Set V} {f : V} (hfF : f ∈ F)
    {a a' : V} {P P' : List V}
    (hchoice : ((a, P, P') = (a₁, P₁, P₂) ∨ (a, P, P') = (b₁, P₁, P₂) ∨
      (a, P, P') = (a₂, P₂, P₁) ∨ (a, P, P') = (b₂, P₂, P₁)))
    (hsame : ∀ w ∈ ({v : V | v ∈ P'} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V),
      (G.Adj f w ↔ G.Adj a w))
    (ha'P : a' ∈ P) (ha'a : a' ≠ a) (hadj : G.Adj f a') :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  refine Or.inr (Or.inl ⟨a, P, P', hchoice, [f], f, f,
    ⟨PathBasics.isPathList_singleton G f, rfl, rfl⟩, ?_, hsame, ?_,
    ⟨a', ⟨ha'P, ha'a⟩, hadj⟩, ?_⟩)
  · intro v hv
    have hvf : v = f := by simpa using hv
    exact hvf ▸ hfF
  · rintro u ⟨hu, hu'⟩
    exact absurd (by simpa using hu) hu'
  · rintro u ⟨hu, hu'⟩
    exact absurd (by simpa using hu) hu'

/-- Statement 4 of 9.3. -/
theorem conclusion_four {G : SimpleGraph V} {P₁ P₂ Q₁ Q₂ : List V}
    {a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V} {K F : Set V} {f : V} (hfF : f ∈ F)
    {x y : V} {Q' : List V}
    (hchoice : ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
      (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)))
    (hsame : ∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
      (G.Adj f w ↔ G.Adj x w))
    (hwit : ∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F :=
  Or.inr (Or.inr (Or.inr ⟨x, y, Q', hchoice, f, hfF, hsame, hwit⟩))

/-- A track with at least two vertices has distinct ends. -/
theorem track_ends_ne {n : ℕ} {H : SimpleGraph (Fin n)} {q : List (Fin n)} {u v : Fin n}
    (hq : IsTrackFrom H q u v) (h2 : 2 ≤ q.length) : u ≠ v := by
  have h0 : q[0]'(by omega) = u := SubdivisionCounting.track_head hq (by omega)
  have hl : q[q.length - 1]'(by omega) = v := by
    have h' := hq.2.2
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h'
    exact Option.some_injective _ h'
  intro hne
  have hnd := hq.1.2.1
  have heq : q[0]'(by omega) = q[q.length - 1]'(by omega) := by rw [h0, hl, hne]
  have h0eq : (0 : ℕ) = q.length - 1 := (List.Nodup.getElem_inj_iff hnd).mp heq
  omega


/-! ### The four sub-alternatives of 5.8.2 -/

/-- The four sub-alternatives of 5.8.2, named.  This unfolds to the second disjunct of
`Thm93Infrastructure.FiveEightOutcome`. -/
abbrev Alt {n : ℕ} (D : SimpleGraph V) (K : Set V) (N : Fin n → Set V)
    (P : List V) (p₁ p₂ : V) (d₁ d₂ : Fin n) (R : List V) (r₁ r₂ : V) : Prop :=
  ((∀ x ∈ N d₁ \ {r₁}, D.Adj p₁ x) ∧
    (∃ x ∈ {y : V | y ∈ R} \ {r₁}, D.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → D.Adj x y →
      (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ {z : V | z ∈ R} \ {r₁}))) ∨
  ((∀ x ∈ N d₁ \ {r₁}, D.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, D.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, D.Adj x y →
      (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂}) ∨
      (x = p₁ ∧ y = r₁) ∨ (x = p₂ ∧ y = r₂)) ∧
    (Even (pathLength P) ↔ Even (pathLength R))) ∨
  (p₁ = p₂ ∧ (∀ x ∈ (N d₁ ∪ N d₂) \ {r₁, r₂}, D.Adj p₁ x) ∧
    (∀ y ∈ K, D.Adj p₁ y → y ∈ N d₁ ∪ N d₂ ∪ {z : V | z ∈ R}) ∧
    Even (pathLength R)) ∨
  (r₁ = r₂ ∧ (∀ x ∈ N d₁ \ {r₁}, D.Adj p₁ x) ∧ (∀ x ∈ N d₂ \ {r₂}, D.Adj p₂ x) ∧
    (∀ x ∈ P, ∀ y ∈ K, y ≠ r₁ → D.Adj x y →
      (x = p₁ ∧ y ∈ N d₁ \ {r₁}) ∨ (x = p₂ ∧ y ∈ N d₂ \ {r₂})) ∧
    Even (pathLength P))

/-- Reading off the unique vertex of a one-vertex branch image. -/
theorem inter_triple {N₁ : Set V} {Q : List V} {u v w : V} (hN : N₁ = ({u, v, w} : Set V))
    (hu : u ∉ Q) (hv : v ∉ Q) (hw : w ∈ Q) {r : V}
    (h : N₁ ∩ {x : V | x ∈ Q} = ({r} : Set V)) : r = w := by
  have hh : N₁ ∩ {x : V | x ∈ Q} = ({w} : Set V) := by
    rw [hN]
    ext z
    constructor
    · rintro ⟨hz, hzQ⟩
      rcases hz with rfl | rfl | rfl
      · exact absurd hzQ hu
      · exact absurd hzQ hv
      · rfl
    · intro hz
      have : z = w := hz
      subst this
      exact ⟨by simp, hw⟩
  rw [hh] at h
  exact (Set.singleton_eq_singleton_iff.mp h).symm

/-- **The one-edge branch case of 5.8.2.**  If the branch supplied by 5.8 is a single edge of
`J`, so that its image `R` is the single vertex `v` shared by the two triangles `N(d₁), N(d₂)`,
then the vertex `f` is complete to `(N(d₁) ∪ N(d₂)) \ {v}` and has no other neighbour in `K`.
This is the paper's *"`f, a₁` have the same neighbours in `K \ a₁`"*. -/
theorem square_sets {D : SimpleGraph V} {n : ℕ} {K : Set V} (N : Fin n → Set V)
    {P : List V} {p₁ p₂ f : V} (hp₁ : p₁ = f) (hp₂ : p₂ = f) (hfP : f ∈ P)
    (d₁ d₂ : Fin n) {R : List V} {r₁ r₂ v : V}
    (hRset : {x : V | x ∈ R} = ({v} : Set V))
    (hv₁ : v ∈ N d₁) (hv₂ : v ∈ N d₂)
    (hr₁ : N d₁ ∩ {x : V | x ∈ R} = ({r₁} : Set V))
    (hr₂ : N d₂ ∩ {x : V | x ∈ R} = ({r₂} : Set V))
    (halt : Alt D K N P p₁ p₂ d₁ d₂ R r₁ r₂) :
    (∀ w ∈ (N d₁ ∪ N d₂) \ ({v} : Set V), D.Adj f w) ∧
      (∀ w ∈ K, D.Adj f w → w ∈ N d₁ ∪ N d₂) := by
  rw [hp₁, hp₂] at halt
  have key : ∀ (M : Set V), v ∈ M → M ∩ {x : V | x ∈ R} = ({v} : Set V) := by
    intro M hM
    rw [hRset]
    ext z
    exact ⟨fun hz => hz.2, fun hz => ⟨(show z = v from hz) ▸ hM, hz⟩⟩
  have e₁ : r₁ = v := by
    have := (key (N d₁) hv₁).symm.trans hr₁
    exact (Set.singleton_eq_singleton_iff.mp this).symm
  have e₂ : r₂ = v := by
    have := (key (N d₂) hv₂).symm.trans hr₂
    exact (Set.singleton_eq_singleton_iff.mp this).symm
  rw [e₁, e₂] at halt
  rcases halt with ⟨-, ⟨z, hz, -⟩, -⟩ | ⟨hs₁, hs₂, hall, -⟩ | ⟨-, hs, hall, -⟩ |
    ⟨-, hs₁, hs₂, hall, -⟩
  · rw [hRset] at hz
    exact absurd (show z = v from hz.1) hz.2
  · refine ⟨?_, ?_⟩
    · rintro w ⟨hw, hwv⟩
      rcases hw with hw | hw
      · exact hs₁ w ⟨hw, hwv⟩
      · exact hs₂ w ⟨hw, hwv⟩
    · intro w hwK hadj
      rcases hall f hfP w hwK hadj with ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩ | ⟨-, hw⟩
      · exact Or.inl hw.1
      · exact Or.inr hw.1
      · exact Or.inl (hw ▸ hv₁)
      · exact Or.inl (hw ▸ hv₁)
  · refine ⟨?_, ?_⟩
    · rintro w ⟨hw, hwv⟩
      refine hs w ⟨hw, ?_⟩
      rintro (h | h)
      · exact hwv h
      · exact hwv h
    · intro w hwK hadj
      rcases hall w hwK hadj with hw | hw
      · exact hw
      · rw [hRset] at hw
        exact Or.inl ((show w = v from hw) ▸ hv₁)
  · refine ⟨?_, ?_⟩
    · rintro w ⟨hw, hwv⟩
      rcases hw with hw | hw
      · exact hs₁ w ⟨hw, hwv⟩
      · exact hs₂ w ⟨hw, hwv⟩
    · intro w hwK hadj
      by_cases hwr : w = v
      · exact Or.inl (hwr ▸ hv₁)
      · rcases hall f hfP w hwK hwr hadj with ⟨-, hw⟩ | ⟨-, hw⟩
        · exact Or.inl hw.1
        · exact Or.inr hw.1

/-- **The long branch case of 5.8.2.**  If the branch supplied by 5.8 is one of the two long
branches, whose image is the odd antipath `Q`, then only 5.8.2(a) survives, and `f` is complete
to `N(d₁) \ {r₁}` with no neighbours in `K` outside `N(d₁) ∪ V(Q)`. -/
theorem diagonal_sets {D : SimpleGraph V} {n : ℕ} {K : Set V} (N : Fin n → Set V)
    {P : List V} {p₁ p₂ f : V} (hp₁ : p₁ = f) (hp₂ : p₂ = f) (hfP : f ∈ P)
    (hPlen : pathLength P = 0)
    (d₁ d₂ : Fin n) {R Q : List V} {r₁ r₂ : V}
    (hRset : {x : V | x ∈ R} = {x : V | x ∈ Q})
    (hRlist : IsPathList D R) (hQlist : IsPathList D Q) (hQodd : Odd (pathLength Q))
    (hr12 : r₁ ≠ r₂)
    (halt : Alt D K N P p₁ p₂ d₁ d₂ R r₁ r₂) :
    (∀ w ∈ N d₁ \ ({r₁} : Set V), D.Adj f w) ∧
      (∀ w ∈ K, D.Adj f w → w ∈ (N d₁ \ ({r₁} : Set V)) ∪ ({r₁} ∪ {x : V | x ∈ Q})) := by
  rw [hp₁, hp₂] at halt
  have hRQ : pathLength R = pathLength Q :=
    Thm93CaseOneLong.pathLength_eq_of_support hQlist hRlist hRset
  have hnoteven : ¬ Even (pathLength R) := by
    rw [hRQ]
    exact Nat.not_even_iff_odd.mpr hQodd
  rcases halt with ⟨hs, -, hall⟩ | ⟨-, -, -, hpar⟩ | ⟨-, -, -, hev⟩ | ⟨heq, -⟩
  · refine ⟨hs, ?_⟩
    intro w hwK hadj
    by_cases hwr : w = r₁
    · exact Or.inr (Or.inl hwr)
    · rcases hall f hfP w hwK hwr hadj with ⟨-, hw⟩ | ⟨-, hw⟩
      · exact Or.inl hw
      · exact Or.inr (Or.inr (hRset ▸ hw.1))
  · exact absurd (hpar.mp (by simp [hPlen])) hnoteven
  · exact absurd hev hnoteven
  · exact absurd heq hr12



/-! ### Small set manipulations -/

/-- Trading a union description of the neighbour set for an `insert` description. -/
theorem sets_of_union {D : SimpleGraph V} {K M₁ M₂ S : Set V} {f v : V}
    (hsup : ∀ w ∈ (M₁ ∪ M₂) \ ({v} : Set V), D.Adj f w)
    (hsub : ∀ w ∈ K, D.Adj f w → w ∈ M₁ ∪ M₂)
    (hunion : M₁ ∪ M₂ = insert v S) (hvS : v ∉ S) :
    (∀ w ∈ S, D.Adj f w) ∧ (∀ w ∈ K, D.Adj f w → w ∈ insert v S) := by
  refine ⟨fun w hw => hsup w ⟨?_, ?_⟩, fun w hw hadj => hunion ▸ hsub w hw hadj⟩
  · rw [hunion]; exact Set.mem_insert_of_mem v hw
  · intro h
    exact hvS ((show w = v from h) ▸ hw)

/-- Removing the shared vertex from a triangle. -/
theorem triple_diff {u v w : V} (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v, w} : Set V) \ ({w} : Set V) = ({u, v} : Set V) := by
  ext z
  simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨(rfl | rfl | rfl), hz⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact absurd rfl hz
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, huw⟩
    · exact ⟨Or.inr (Or.inl rfl), hvw⟩

/-- The `T ∩ W ⊆ S` side condition of `same_of_sets`, for a one-edge branch. -/
theorem tw_square {W S : Set V} {v : V} (hv : v ∉ W) : ∀ z ∈ W, z ∈ insert v S → z ∈ S := by
  intro z hz hzT
  rcases hzT with h | h
  · exact absurd ((show z = v from h) ▸ hz) hv
  · exact h

/-- The `T ∩ W ⊆ S` side condition of `same_of_sets`, for a long branch. -/
theorem tw_diagonal {W S : Set V} {e : V} {Q : List V} (he : e ∉ W) (hQ : ∀ z ∈ Q, z ∉ W) :
    ∀ z ∈ W, z ∈ S ∪ (({e} : Set V) ∪ {x : V | x ∈ Q}) → z ∈ S := by
  intro z hz hzT
  rcases hzT with h | (h | h)
  · exact h
  · exact absurd ((show z = e from h) ▸ hz) he
  · exact absurd hz (hQ z h)

/-- A vertex outside `K` is `G`-adjacent to everything in `K` that it does not see in `G̅`. -/
theorem adj_of_not_mem {G : SimpleGraph V} {K T : Set V} {f w : V} (hfK : f ∉ K) (hwK : w ∈ K)
    (hsub : ∀ z ∈ K, Gᶜ.Adj f z → z ∈ T) (hwT : w ∉ T) : G.Adj f w := by
  by_contra hadj
  exact hwT (hsub w hwK ((G.compl_adj f w).mpr ⟨fun h => hfK (h ▸ hwK), hadj⟩))


/-- `N(c₁) ∪ N(c₂)` in the complement dictionary of 9.3. -/
theorem union_c12 (a₂ b₁ b₂ x₁ x₂ : V) :
    ({b₁, b₂, x₁} : Set V) ∪ ({b₁, a₂, x₂} : Set V) =
      insert b₁ ({a₂, b₂, x₁, x₂} : Set V) := by
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `N(c₂) ∪ N(c₃)` in the complement dictionary of 9.3. -/
theorem union_c23 (a₁ b₁ a₂ x₂ y₁ : V) :
    ({b₁, a₂, x₂} : Set V) ∪ ({a₁, a₂, y₁} : Set V) =
      insert a₂ ({a₁, b₁, y₁, x₂} : Set V) := by
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `N(c₃) ∪ N(c₄)` in the complement dictionary of 9.3. -/
theorem union_c34 (a₁ a₂ b₂ y₁ y₂ : V) :
    ({a₁, a₂, y₁} : Set V) ∪ ({a₁, b₂, y₂} : Set V) =
      insert a₁ ({a₂, b₂, y₁, y₂} : Set V) := by
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-- `N(c₄) ∪ N(c₁)` in the complement dictionary of 9.3. -/
theorem union_c41 (a₁ b₁ b₂ x₁ y₂ : V) :
    ({a₁, b₂, y₂} : Set V) ∪ ({b₁, b₂, x₁} : Set V) =
      insert b₂ ({a₁, b₁, x₁, y₂} : Set V) := by
  ext z
  simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-! ### The two remaining steps of the paper's sentence -/

/-- **Gap: outcome 5.8.1 in the complement lane of claim (2) of 9.3.**

PAPER (proof of 9.3, printed p. 48, invoked again on p. 49 through *"deduce, as before"*):
*"If 5.8.1 holds then there is an appearance in `G` of some `K₄`-enlargement, a
contradiction."*

Here `D` is the graph in which 5.8 was applied (in claim (2) it is `G̅`), `c₁, c₂` are the two
vertices of `H` supplied by 5.8.1, and `P` is the path of `F` it supplies. -/
theorem nonlocal_enlargement_gap
    (D : SimpleGraph V) (hD : Berge D)
    {n : ℕ} (H : SimpleGraph (Fin n)) (K : Set V) (phi : H.lineGraph ≃g D.induce K)
    (happ : IsAppearance D (⊤ : SimpleGraph (Fin 4)) H K)
    (N : Fin n → Set V)
    (hN : ∀ c : Fin n, N c =
      {v : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ incidentEdges H c ∧ v = (↑(phi ⟨e, he⟩) : V)})
    (P : List V) (p₁ p₂ : V) (hP : IsPathFrom D P p₁ p₂)
    (u₁ u₂ : Fin n)
    (hnobranch : ¬ ∃ q : List (Fin n), IsBranch H q ∧ u₁ ∈ q ∧ u₂ ∈ q)
    (hc₁ : ∀ x ∈ N u₁, D.Adj p₁ x) (hc₂ : ∀ x ∈ N u₂, D.Adj p₂ x)
    (hother : ∀ x ∈ P, ∀ y ∈ K, D.Adj x y → (x = p₁ ∧ y ∈ N u₁) ∨ (x = p₂ ∧ y ∈ N u₂)) :
    ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ Appears D J' :=
  Thm93CaseOneEnlarge.enlargement D hD H K phi happ N hN P p₁ p₂ hP u₁ u₂ hnobranch
    hc₁ hc₂ hother

/-- **The last clause of claim (2) of 9.3, in its repaired form.**

PAPER (proof of 9.3, printed p. 49): *"... or (up to symmetry) `f, x₁` have the same neighbours
in `V(P₁) ∪ V(P₂) ∪ V(Q₂)` (but then either statement 1 or statement 4 of the theorem
holds)."*

This used to be a `sorry` on a false statement: it asked for `¬ G.Adj f y`, with `y` the end
of the antipath of `x` other than `x`, and that is false when the antipath of `x` is long (a
twin of `x` is a counterexample; see the section "9.3, case 2: 9.3.4 is too strong" of
`REPORT.md`).  With the user-approved repair of outcome 9.3.4 the demand is the one the
argument actually meets: either the neighbour set of `f` in `K` resolves the knot (statement 1
of 9.3), or `f` has a non-neighbour on its own antipath other than `x`.  Since `Q₁` and `Q₂`
are disjoint and `Q'` is the antipath *not* containing `x`, the two conditions `w ∈ Q₁ ∨ w ∈ Q₂`
and `w ∉ Q'` say exactly that `w` lies on the antipath of `x`.

The proof is `Thm93CaseTwoNonmajorRepair.resolves_or_nonneighbour`, which is the dichotomy the
printed argument establishes; the only work here is to name the antipath of `x` in each of the
four symmetric positions and to convert `w ∈ Qx` into `w ∈ Q₁ ∨ w ∈ Q₂` together with
`w ∉ Q'`. -/
theorem statement_one_or_four_gap
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (f : V) (hfF : f ∈ F) (hfK : f ∉ K)
    (x y : V) (Q' : List V)
    (hchoice : ((x, y, Q') = (x₁, y₁, Q₂) ∨ (x, y, Q') = (y₁, x₁, Q₂) ∨
      (x, y, Q') = (x₂, y₂, Q₁) ∨ (x, y, Q') = (y₂, x₂, Q₁)))
    (hsame : ∀ w ∈ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q'} : Set V),
      (G.Adj f w ↔ G.Adj x w)) :
    (∃ g ∈ F, ResolvesKnot G P₁ P₂ Q₁ Q₂ (G.neighborSet g ∩ K)) ∨
      (∃ w, (w ∈ Q₁ ∨ w ∈ Q₂) ∧ w ∉ Q' ∧ w ≠ x ∧ ¬ G.Adj f w) := by
  -- The antipath of `x` is `Q₁` in the first two symmetric positions and `Q₂` in the last two.
  obtain ⟨-, -, -, -, -, hdisj, -⟩ := KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  rcases hchoice with h | h | h | h <;> simp only [Prod.mk.injEq] at h <;>
    obtain ⟨e1, e2, e3⟩ := h <;> subst e1 <;> subst e2 <;> subst e3
  · rcases Thm93CaseTwoNonmajorRepair.resolves_or_nonneighbour G P₁ P₂ Q₁ Q'
      a₁ b₁ a₂ b₂ x y x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK F f hfF x y Q' Q₁
      (Or.inl rfl) hsame with hres | ⟨w, hwQ, hwx, hwadj⟩
    · exact Or.inl hres
    · exact Or.inr ⟨w, Or.inl hwQ, hdisj w hwQ, hwx, hwadj⟩
  · rcases Thm93CaseTwoNonmajorRepair.resolves_or_nonneighbour G P₁ P₂ Q₁ Q'
      a₁ b₁ a₂ b₂ y x x₂ y₂ hknot hP₁ hP₂ hQ₁ hQ₂ K hK F f hfF x y Q' Q₁
      (Or.inr (Or.inl rfl)) hsame with hres | ⟨w, hwQ, hwx, hwadj⟩
    · exact Or.inl hres
    · exact Or.inr ⟨w, Or.inl hwQ, hdisj w hwQ, hwx, hwadj⟩
  · rcases Thm93CaseTwoNonmajorRepair.resolves_or_nonneighbour G P₁ P₂ Q' Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ x y hknot hP₁ hP₂ hQ₁ hQ₂ K hK F f hfF x y Q' Q₂
      (Or.inr (Or.inr (Or.inl rfl))) hsame with hres | ⟨w, hwQ, hwx, hwadj⟩
    · exact Or.inl hres
    · exact Or.inr ⟨w, Or.inr hwQ, fun hc => hdisj w hc hwQ, hwx, hwadj⟩
  · rcases Thm93CaseTwoNonmajorRepair.resolves_or_nonneighbour G P₁ P₂ Q' Q₂
      a₁ b₁ a₂ b₂ x₁ y₁ y x hknot hP₁ hP₂ hQ₁ hQ₂ K hK F f hfF x y Q' Q₂
      (Or.inr (Or.inr (Or.inr rfl))) hsame with hres | ⟨w, hwQ, hwx, hwadj⟩
    · exact Or.inl hres
    · exact Or.inr ⟨w, Or.inr hwQ, fun hc => hdisj w hc hwQ, hwx, hwadj⟩



/-- **Claim (2) of 9.3, after 5.8 has been applied in the complement.**

PAPER (proof of 9.3, printed p. 49): *"... so we can apply 5.8 (or, indeed, 5.7) in `G̅`, and
deduce, as before, that either there is a `K₄`-enlargement that appears in `G̅` (a
contradiction), or (up to symmetry) `f, a₁` have the same neighbours in `K \ a₁` (but then
statement 2 of the theorem holds), or (up to symmetry) `f, x₁` have the same neighbours in
`V(P₁) ∪ V(P₂) ∪ V(Q₂)` (but then either statement 1 or statement 4 of the theorem holds)."*

The branch of `H` supplied by 5.8.2 joins two of the four branch-vertices `c₁, c₂, c₃, c₄`.  If
they are consecutive on the square then the branch is a single edge, its image is one of
`a₁, b₁, a₂, b₂`, and the first alternative of the sentence above applies.  If they are
opposite then the branch is one of the two long ones, its image is `Q₁` or `Q₂`, which is odd,
and only 5.8.2(a) survives; that is the second alternative. -/
theorem endgame
    (G : SimpleGraph V) (hG : Berge G)
    (P₁ P₂ Q₁ Q₂ : List V) (a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ : V)
    (hknot : IsKnot G P₁ P₂ Q₁ Q₂)
    (hP₁ : IsPathFrom G P₁ a₁ b₁) (hP₂ : IsPathFrom G P₂ a₂ b₂)
    (hQ₁ : IsAntipathFrom G Q₁ x₁ y₁) (hQ₂ : IsAntipathFrom G Q₂ x₂ y₂)
    (hP₁len : pathLength P₁ = 1) (hP₂len : pathLength P₂ = 1)
    (K : Set V) (hK : KnotInduces P₁ P₂ Q₁ Q₂ K)
    (hnoenl : ¬ ∃ (m : ℕ) (J' : SimpleGraph (Fin m)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears G J' ∨ Appears Gᶜ J'))
    (hnoover : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g G.induce K'),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance G H' K' psi)
    (hnoovercompl : ¬ ∃ (n' : ℕ) (H' : SimpleGraph (Fin n')) (K' : Set V)
      (psi : H'.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H' K' ∧ IsOvershadowedAppearance Gᶜ H' K' psi)
    (F : Set V) (f : V) (hfF : f ∈ F) (hfK : f ∉ K)
    {n : ℕ} (H : SimpleGraph (Fin n)) (phi : H.lineGraph ≃g Gᶜ.induce K)
    (happ : IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K)
    (c₁ c₂ c₃ c₄ : Fin n) (N : Fin n → Set V)
    (hdict : KnotAppearanceDictionary Gᶜ H K phi Q₁ Q₂ x₁ y₁ x₂ y₂ b₁ a₁ b₂ a₂
      c₁ c₂ c₃ c₄ N)
    (h58 : FiveEightOutcome Gᶜ H K phi N ({f} : Set V)) :
    Conclusion G P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ K F := by
  classical
  have hGc : Berge Gᶜ := Workspace.ProofLemmas.HoleBasics.berge_compl.mpr hG
  have hL := labels_of_knot hknot hP₁ hP₂ hQ₁ hQ₂ hP₁len hP₂len hK
  obtain ⟨⟨nb₁, na₁, na₂, nb₂⟩, nx₁, ny₁, nx₂, ny₂⟩ :=
    knot_compl_neighbours hknot hP₁ hP₂ hQ₁ hQ₂ hL
  obtain ⟨⟨d1, d2, d3, d4, d5, d6, d7⟩, ⟨d8, d9, d10, d11, d12, d13⟩,
    ⟨d14, d15, d16, d17, d18⟩, ⟨d19, d20, d21, d22⟩,
    ⟨d23, d24, d25, d26, d27, d28⟩⟩ := all_ne hL
  obtain ⟨dP1P2, dP1Q1, dP1Q2, dP2Q1, dP2Q2, dQ1Q2, -⟩ :=
    KnotLabels.knot_labels hknot hP₁ hP₂ hQ₁ hQ₂
  obtain ⟨⟨-, -, hQ₁odd, hQ₂odd⟩, -⟩ :=
    Workspace.Statements.S09.SPGT.thm_9_1 G hG P₁ P₂ Q₁ Q₂ hknot
  have ha₁P : a₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have hb₁P : b₁ ∈ P₁ := by rw [hL.P₁_eq]; simp
  have ha₂P : a₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have hb₂P : b₂ ∈ P₂ := by rw [hL.P₂_eq]; simp
  have hKP₁ : ∀ w ∈ P₁, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inl (Or.inl hw))
  have hKP₂ : ∀ w ∈ P₂, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inl (Or.inr hw))
  have hKQ₁ : ∀ w ∈ Q₁, w ∈ K := by rw [hK]; exact fun w hw => Or.inl (Or.inr hw)
  have hKQ₂ : ∀ w ∈ Q₂, w ∈ K := by rw [hK]; exact fun w hw => Or.inr hw
  have hW₂K : ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) ⊆ K := by
    rintro z ((hz | hz) | hz)
    exacts [hKP₂ z hz, hKQ₁ z hz, hKQ₂ z hz]
  have hW₁K : ({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) ⊆ K := by
    rintro z ((hz | hz) | hz)
    exacts [hKP₁ z hz, hKQ₁ z hz, hKQ₂ z hz]
  have hWAK : ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V) ⊆ K := by
    rintro z ((hz | hz) | hz)
    exacts [hKP₁ z hz, hKP₂ z hz, hKQ₂ z hz]
  have hWBK : ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V) ⊆ K := by
    rintro z ((hz | hz) | hz)
    exacts [hKP₁ z hz, hKP₂ z hz, hKQ₁ z hz]
  have hb₁W₂ : b₁ ∉ ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
    rintro ((hz | hz) | hz)
    exacts [dP1P2 b₁ hb₁P hz, dP1Q1 b₁ hb₁P hz, dP1Q2 b₁ hb₁P hz]
  have ha₁W₂ : a₁ ∉ ({v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
    rintro ((hz | hz) | hz)
    exacts [dP1P2 a₁ ha₁P hz, dP1Q1 a₁ ha₁P hz, dP1Q2 a₁ ha₁P hz]
  have ha₂W₁ : a₂ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
    rintro ((hz | hz) | hz)
    exacts [dP1P2 a₂ hz ha₂P, dP2Q1 a₂ ha₂P hz, dP2Q2 a₂ ha₂P hz]
  have hb₂W₁ : b₂ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ Q₁} ∪ {v : V | v ∈ Q₂} : Set V) := by
    rintro ((hz | hz) | hz)
    exacts [dP1P2 b₂ hz hb₂P, dP2Q1 b₂ hb₂P hz, dP2Q2 b₂ hb₂P hz]
  have hQ₁WA : ∀ z ∈ Q₁, z ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V) := by
    rintro z hz ((h | h) | h)
    exacts [dP1Q1 z h hz, dP2Q1 z h hz, dQ1Q2 z hz h]
  have hQ₂WB : ∀ z ∈ Q₂, z ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V) := by
    rintro z hz ((h | h) | h)
    exacts [dP1Q2 z h hz, dP2Q2 z h hz, dQ1Q2 z h hz]
  have hx₁WA : x₁ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V) := hQ₁WA x₁ hL.x₁_mem
  have hy₁WA : y₁ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₂} : Set V) := hQ₁WA y₁ hL.y₁_mem
  have hx₂WB : x₂ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V) := hQ₂WB x₂ hL.x₂_mem
  have hy₂WB : y₂ ∉ ({v : V | v ∈ P₁} ∪ {v : V | v ∈ P₂} ∪ {v : V | v ∈ Q₁} : Set V) := hQ₂WB y₂ hL.y₂_mem
  have hb₁nQ₁ : b₁ ∉ Q₁ := dP1Q1 b₁ hb₁P
  have hb₂nQ₁ : b₂ ∉ Q₁ := dP2Q1 b₂ hb₂P
  have ha₁nQ₁ : a₁ ∉ Q₁ := dP1Q1 a₁ ha₁P
  have ha₂nQ₁ : a₂ ∉ Q₁ := dP2Q1 a₂ ha₂P
  have hb₁nQ₂ : b₁ ∉ Q₂ := dP1Q2 b₁ hb₁P
  have hb₂nQ₂ : b₂ ∉ Q₂ := dP2Q2 b₂ hb₂P
  have ha₁nQ₂ : a₁ ∉ Q₂ := dP1Q2 a₁ ha₁P
  have ha₂nQ₂ : a₂ ∉ Q₂ := dP2Q2 a₂ ha₂P
  have hQ₁list : IsPathList Gᶜ Q₁ := hQ₁.1
  have hQ₂list : IsPathList Gᶜ Q₂ := hQ₂.1
  obtain ⟨hN, hnd, h12, h23, h34, h41, hbv, hex₁, hex₂, hex₃, hex₄,
    hNc₁, hNc₂, hNc₃, hNc₄, hbr₁, hbr₂⟩ := hdict
  obtain ⟨he12, hi12⟩ := hex₁
  obtain ⟨he23, hi23⟩ := hex₂
  obtain ⟨he34, hi34⟩ := hex₃
  obtain ⟨he41, hi41⟩ := hex₄
  obtain ⟨q₁, hq₁br, hq₁from, hq₁img⟩ := hbr₁
  obtain ⟨q₂, hq₂br, hq₂from, hq₂img⟩ := hbr₂
  have hbc₁ : c₁ ∈ branchVertices H := by rw [hbv]; simp
  have hbc₂ : c₂ ∈ branchVertices H := by rw [hbv]; simp
  have hbc₃ : c₃ ∈ branchVertices H := by rw [hbv]; simp
  have hbc₄ : c₄ ∈ branchVertices H := by rw [hbv]; simp
  have hq₁2 : 2 ≤ q₁.length := by
    by_contra hc
    have hx : x₁ ∈ {v : V | v ∈ Q₁} := hL.x₁_mem
    rw [hq₁img] at hx
    obtain ⟨e, he, ⟨i, hi, -⟩, -⟩ := hx
    omega
  have hq₂2 : 2 ≤ q₂.length := by
    by_contra hc
    have hx : x₂ ∈ {v : V | v ∈ Q₂} := hL.x₂_mem
    rw [hq₂img] at hx
    obtain ⟨e, he, ⟨i, hi, -⟩, -⟩ := hx
    omega
  obtain ⟨P, p₁, p₂, hPfrom, hPF, houtcome⟩ := h58
  have hp₁ : p₁ = f := by
    simpa using hPF p₁ (PathBasics.isPathFrom_ends_mem hPfrom).1
  have hp₂ : p₂ = f := by
    simpa using hPF p₂ (PathBasics.isPathFrom_ends_mem hPfrom).2
  have hfP : f ∈ P := hp₁ ▸ (PathBasics.isPathFrom_ends_mem hPfrom).1
  have hPlen : pathLength P = 0 := by
    have hnd' : P.Nodup := hPfrom.1.2.1
    have hpos : 0 < P.length := List.length_pos_of_mem hfP
    have hlen : P.length = 1 := by
      by_contra hc
      have h2 : 1 < P.length := by omega
      have e0 : P[0]'(by omega) = f := by
        simpa using hPF _ (List.getElem_mem (by omega))
      have e1 : P[1]'(by omega) = f := by
        simpa using hPF _ (List.getElem_mem (by omega))
      have := (List.Nodup.getElem_inj_iff hnd').mp (e0.trans e1.symm)
      omega
    simp [pathLength, hlen]
  rcases houtcome with hnl | hbr
  · obtain ⟨u₁, u₂, hnb, hcc₁, hcc₂, hoth⟩ := hnl
    refine absurd ?_ hnoenl
    obtain ⟨m, J', hJ, hApp⟩ := nonlocal_enlargement_gap Gᶜ hGc H K phi happ N hN P p₁ p₂
      hPfrom u₁ u₂ hnb hcc₁ hcc₂ hoth
    exact ⟨m, J', hJ, Or.inr hApp⟩
  obtain ⟨d₁, d₂, q, R, r₁, r₂, hd₁, hd₂, hqbr, hqfrom, hRlist, hRset, hr₁, hr₂, halt⟩ := hbr
  have hq2 : 2 ≤ q.length := by
    by_contra hc
    have hr : r₁ ∈ N d₁ ∩ {x : V | x ∈ R} := by rw [hr₁]; rfl
    have hx := hr.2
    rw [hRset] at hx
    obtain ⟨e, he, ⟨i, hi, -⟩, -⟩ := hx
    omega
  have hdne : d₁ ≠ d₂ := track_ends_ne hqfrom hq2
  have hsq : ∀ (u v : Fin n) (huv : s(u, v) ∈ H.edgeSet),
      u ∈ branchVertices H → v ∈ branchVertices H →
      ((d₁ = u ∧ d₂ = v) ∨ (d₁ = v ∧ d₂ = u)) →
      {x : V | x ∈ R} = ({(↑(phi ⟨s(u, v), huv⟩) : V)} : Set V) := by
    intro u v huv hu hv hm
    obtain ⟨hBr, hFrom, hEd⟩ := isBranch_pair (show H.Adj u v from huv) hu hv
    have heq := branch_edges_eq SubdivisionCounting.k4_three_connected happ.1.1
      hqbr hq2 hqfrom hBr (by simp) hFrom hd₁ hd₂
      (by rcases hm with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
          · exact Or.inl ⟨hh1.symm, hh2.symm⟩
          · exact Or.inr ⟨hh2.symm, hh1.symm⟩)
    rw [hRset, heq, hEd]
    exact image_singleton_edge phi huv
  have hdg : ∀ (u v : Fin n) (qq : List (Fin n)) (QQ : List V),
      IsBranch H qq → IsTrackFrom H qq u v → 2 ≤ qq.length →
      {x : V | x ∈ QQ} = {x : V | ∃ (e : Sym2 (Fin n)) (he : e ∈ H.edgeSet),
        e ∈ trackEdges qq ∧ x = (↑(phi ⟨e, he⟩) : V)} →
      u ∈ branchVertices H → v ∈ branchVertices H →
      ((d₁ = u ∧ d₂ = v) ∨ (d₁ = v ∧ d₂ = u)) →
      {x : V | x ∈ R} = {x : V | x ∈ QQ} := by
    intro u v qq QQ hBr hFrom hlen himg hu hv hm
    have heq := branch_edges_eq SubdivisionCounting.k4_three_connected happ.1.1
      hqbr hq2 hqfrom hBr hlen hFrom hd₁ hd₂
      (by rcases hm with ⟨hh1, hh2⟩ | ⟨hh1, hh2⟩
          · exact Or.inl ⟨hh1.symm, hh2.symm⟩
          · exact Or.inr ⟨hh2.symm, hh1.symm⟩)
    rw [hRset, heq, ← himg]
  have hd₁' : d₁ = c₁ ∨ d₁ = c₂ ∨ d₁ = c₃ ∨ d₁ = c₄ := by
    rw [hbv] at hd₁; simpa using hd₁
  have hd₂' : d₂ = c₁ ∨ d₂ = c₂ ∨ d₂ = c₃ ∨ d₂ = c₄ := by
    rw [hbv] at hd₂; simpa using hd₂
  rcases hd₁' with e₁ | e₁ | e₁ | e₁ <;> rcases hd₂' with e₂ | e₂ | e₂ | e₂
  · -- d₁ = c₁, d₂ = c₁
    exact absurd (e₁.trans e₂.symm) hdne
  · -- d₁ = c₁, d₂ = c₂
    have hNd₁ : N d₁ = ({b₁, b₂, x₁} : Set V) := by rw [e₁]; exact hNc₁
    have hNd₂ : N d₂ = ({b₁, a₂, x₂} : Set V) := by rw [e₂]; exact hNc₂
    have hRs : {x : V | x ∈ R} = ({b₁} : Set V) := by
      rw [hsq c₁ c₂ he12 hbc₁ hbc₂ (Or.inl ⟨e₁, e₂⟩), hi12]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₂, b₂, x₁, x₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂]; exact union_c12 a₂ b₁ b₂ x₁ x₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨d8, d9, d10, d12⟩)
    exact conclusion_two hfF (Or.inr (Or.inl rfl))
      (same_of_sets hfK hsup hsub (tw_square hb₁W₂) nb₁ hW₂K hb₁W₂)
      ha₁P d1
      (adj_of_not_mem hfK (hKP₁ a₁ ha₁P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨d1, d2, d3, d4, d6⟩))
  · -- d₁ = c₁, d₂ = c₃
    have hNd₁ : N d₁ = ({b₁, b₂, x₁} : Set V) := by rw [e₁]; exact hNc₁
    have hNd₂ : N d₂ = ({a₁, a₂, y₁} : Set V) := by rw [e₂]; exact hNc₃
    have hRs : {x : V | x ∈ R} = {x : V | x ∈ Q₁} :=
      hdg c₁ c₃ q₁ Q₁ hq₁br hq₁from hq₁2 hq₁img hbc₁ hbc₃ (Or.inl ⟨e₁, e₂⟩)
    have hrr₁ : r₁ = x₁ := inter_triple hNd₁ hb₁nQ₁ hb₂nQ₁ hL.x₁_mem
      (by rw [← hRs]; exact hr₁)
    have hrr₂ : r₂ = y₁ := inter_triple hNd₂ ha₁nQ₁ ha₂nQ₁ hL.y₁_mem
      (by rw [← hRs]; exact hr₂)
    obtain ⟨hsupA, hsubA⟩ := diagonal_sets N hp₁ hp₂ hfP hPlen d₁ d₂ hRs hRlist hQ₁list hQ₁odd
      (by rw [hrr₁, hrr₂]; exact hL.x₁_ne_y₁) halt
    rw [hNd₁, hrr₁, triple_diff d10 d19] at hsupA hsubA
    have hsame := same_of_sets hfK hsupA hsubA (tw_diagonal hx₁WA hQ₁WA) nx₁ hWAK hx₁WA
    rcases statement_one_or_four_gap G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂
      hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover hnoovercompl F f hfF hfK x₁ y₁
      Q₂ (Or.inl rfl) hsame with hres | hnadj
    · exact Or.inl hres
    · exact conclusion_four hfF (Or.inl rfl) hsame hnadj
  · -- d₁ = c₁, d₂ = c₄
    have hNd₁ : N d₁ = ({b₁, b₂, x₁} : Set V) := by rw [e₁]; exact hNc₁
    have hNd₂ : N d₂ = ({a₁, b₂, y₂} : Set V) := by rw [e₂]; exact hNc₄
    have hRs : {x : V | x ∈ R} = ({b₂} : Set V) := by
      rw [hsq c₄ c₁ he41 hbc₄ hbc₁ (Or.inr ⟨e₁, e₂⟩), hi41]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₁, b₁, x₁, y₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂, Set.union_comm]; exact union_c41 a₁ b₁ b₂ x₁ y₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨(Ne.symm d3), (Ne.symm d9), d19, d22⟩)
    exact conclusion_two hfF (Or.inr (Or.inr (Or.inr rfl)))
      (same_of_sets hfK hsup hsub (tw_square hb₂W₁) nb₂ hW₁K hb₂W₁)
      ha₂P d14
      (adj_of_not_mem hfK (hKP₂ a₂ ha₂P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨d14, (Ne.symm d2), (Ne.symm d8), d15, d18⟩))
  · -- d₁ = c₂, d₂ = c₁
    have hNd₁ : N d₁ = ({b₁, a₂, x₂} : Set V) := by rw [e₁]; exact hNc₂
    have hNd₂ : N d₂ = ({b₁, b₂, x₁} : Set V) := by rw [e₂]; exact hNc₁
    have hRs : {x : V | x ∈ R} = ({b₁} : Set V) := by
      rw [hsq c₁ c₂ he12 hbc₁ hbc₂ (Or.inr ⟨e₁, e₂⟩), hi12]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₂, b₂, x₁, x₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂, Set.union_comm]; exact union_c12 a₂ b₁ b₂ x₁ x₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨d8, d9, d10, d12⟩)
    exact conclusion_two hfF (Or.inr (Or.inl rfl))
      (same_of_sets hfK hsup hsub (tw_square hb₁W₂) nb₁ hW₂K hb₁W₂)
      ha₁P d1
      (adj_of_not_mem hfK (hKP₁ a₁ ha₁P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨d1, d2, d3, d4, d6⟩))
  · -- d₁ = c₂, d₂ = c₂
    exact absurd (e₁.trans e₂.symm) hdne
  · -- d₁ = c₂, d₂ = c₃
    have hNd₁ : N d₁ = ({b₁, a₂, x₂} : Set V) := by rw [e₁]; exact hNc₂
    have hNd₂ : N d₂ = ({a₁, a₂, y₁} : Set V) := by rw [e₂]; exact hNc₃
    have hRs : {x : V | x ∈ R} = ({a₂} : Set V) := by
      rw [hsq c₂ c₃ he23 hbc₂ hbc₃ (Or.inl ⟨e₁, e₂⟩), hi23]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₁, b₁, y₁, x₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂]; exact union_c23 a₁ b₁ a₂ x₂ y₁)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨(Ne.symm d2), (Ne.symm d8), d16, d17⟩)
    exact conclusion_two hfF (Or.inr (Or.inr (Or.inl rfl)))
      (same_of_sets hfK hsup hsub (tw_square ha₂W₁) na₂ hW₁K ha₂W₁)
      hb₂P (Ne.symm d14)
      (adj_of_not_mem hfK (hKP₂ b₂ hb₂P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨(Ne.symm d14), (Ne.symm d3), (Ne.symm d9), d20, d21⟩))
  · -- d₁ = c₂, d₂ = c₄
    have hNd₁ : N d₁ = ({b₁, a₂, x₂} : Set V) := by rw [e₁]; exact hNc₂
    have hNd₂ : N d₂ = ({a₁, b₂, y₂} : Set V) := by rw [e₂]; exact hNc₄
    have hRs : {x : V | x ∈ R} = {x : V | x ∈ Q₂} :=
      hdg c₂ c₄ q₂ Q₂ hq₂br hq₂from hq₂2 hq₂img hbc₂ hbc₄ (Or.inl ⟨e₁, e₂⟩)
    have hrr₁ : r₁ = x₂ := inter_triple hNd₁ hb₁nQ₂ ha₂nQ₂ hL.x₂_mem
      (by rw [← hRs]; exact hr₁)
    have hrr₂ : r₂ = y₂ := inter_triple hNd₂ ha₁nQ₂ hb₂nQ₂ hL.y₂_mem
      (by rw [← hRs]; exact hr₂)
    obtain ⟨hsupA, hsubA⟩ := diagonal_sets N hp₁ hp₂ hfP hPlen d₁ d₂ hRs hRlist hQ₂list hQ₂odd
      (by rw [hrr₁, hrr₂]; exact hL.x₂_ne_y₂) halt
    rw [hNd₁, hrr₁, triple_diff d12 d17] at hsupA hsubA
    have hsame := same_of_sets hfK hsupA hsubA (tw_diagonal hx₂WB hQ₂WB) nx₂ hWBK hx₂WB
    rcases statement_one_or_four_gap G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂
      hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover hnoovercompl F f hfF hfK x₂ y₂
      Q₁ (Or.inr (Or.inr (Or.inl rfl))) hsame with hres | hnadj
    · exact Or.inl hres
    · exact conclusion_four hfF (Or.inr (Or.inr (Or.inl rfl))) hsame hnadj
  · -- d₁ = c₃, d₂ = c₁
    have hNd₁ : N d₁ = ({a₁, a₂, y₁} : Set V) := by rw [e₁]; exact hNc₃
    have hNd₂ : N d₂ = ({b₁, b₂, x₁} : Set V) := by rw [e₂]; exact hNc₁
    have hRs : {x : V | x ∈ R} = {x : V | x ∈ Q₁} :=
      hdg c₁ c₃ q₁ Q₁ hq₁br hq₁from hq₁2 hq₁img hbc₁ hbc₃ (Or.inr ⟨e₁, e₂⟩)
    have hrr₁ : r₁ = y₁ := inter_triple hNd₁ ha₁nQ₁ ha₂nQ₁ hL.y₁_mem
      (by rw [← hRs]; exact hr₁)
    have hrr₂ : r₂ = x₁ := inter_triple hNd₂ hb₁nQ₁ hb₂nQ₁ hL.x₁_mem
      (by rw [← hRs]; exact hr₂)
    obtain ⟨hsupA, hsubA⟩ := diagonal_sets N hp₁ hp₂ hfP hPlen d₁ d₂ hRs hRlist hQ₁list hQ₁odd
      (by rw [hrr₁, hrr₂]; exact (Ne.symm hL.x₁_ne_y₁)) halt
    rw [hNd₁, hrr₁, triple_diff d5 d16] at hsupA hsubA
    have hsame := same_of_sets hfK hsupA hsubA (tw_diagonal hy₁WA hQ₁WA) ny₁ hWAK hy₁WA
    rcases statement_one_or_four_gap G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂
      hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover hnoovercompl F f hfF hfK y₁ x₁
      Q₂ (Or.inr (Or.inl rfl)) hsame with hres | hnadj
    · exact Or.inl hres
    · exact conclusion_four hfF (Or.inr (Or.inl rfl)) hsame hnadj
  · -- d₁ = c₃, d₂ = c₂
    have hNd₁ : N d₁ = ({a₁, a₂, y₁} : Set V) := by rw [e₁]; exact hNc₃
    have hNd₂ : N d₂ = ({b₁, a₂, x₂} : Set V) := by rw [e₂]; exact hNc₂
    have hRs : {x : V | x ∈ R} = ({a₂} : Set V) := by
      rw [hsq c₂ c₃ he23 hbc₂ hbc₃ (Or.inr ⟨e₁, e₂⟩), hi23]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₁, b₁, y₁, x₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂, Set.union_comm]; exact union_c23 a₁ b₁ a₂ x₂ y₁)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨(Ne.symm d2), (Ne.symm d8), d16, d17⟩)
    exact conclusion_two hfF (Or.inr (Or.inr (Or.inl rfl)))
      (same_of_sets hfK hsup hsub (tw_square ha₂W₁) na₂ hW₁K ha₂W₁)
      hb₂P (Ne.symm d14)
      (adj_of_not_mem hfK (hKP₂ b₂ hb₂P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨(Ne.symm d14), (Ne.symm d3), (Ne.symm d9), d20, d21⟩))
  · -- d₁ = c₃, d₂ = c₃
    exact absurd (e₁.trans e₂.symm) hdne
  · -- d₁ = c₃, d₂ = c₄
    have hNd₁ : N d₁ = ({a₁, a₂, y₁} : Set V) := by rw [e₁]; exact hNc₃
    have hNd₂ : N d₂ = ({a₁, b₂, y₂} : Set V) := by rw [e₂]; exact hNc₄
    have hRs : {x : V | x ∈ R} = ({a₁} : Set V) := by
      rw [hsq c₃ c₄ he34 hbc₃ hbc₄ (Or.inl ⟨e₁, e₂⟩), hi34]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₂, b₂, y₁, y₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂]; exact union_c34 a₁ a₂ b₂ y₁ y₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨d2, d3, d5, d7⟩)
    exact conclusion_two hfF (Or.inl rfl)
      (same_of_sets hfK hsup hsub (tw_square ha₁W₂) na₁ hW₂K ha₁W₂)
      hb₁P (Ne.symm d1)
      (adj_of_not_mem hfK (hKP₁ b₁ hb₁P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨(Ne.symm d1), d8, d9, d11, d13⟩))
  · -- d₁ = c₄, d₂ = c₁
    have hNd₁ : N d₁ = ({a₁, b₂, y₂} : Set V) := by rw [e₁]; exact hNc₄
    have hNd₂ : N d₂ = ({b₁, b₂, x₁} : Set V) := by rw [e₂]; exact hNc₁
    have hRs : {x : V | x ∈ R} = ({b₂} : Set V) := by
      rw [hsq c₄ c₁ he41 hbc₄ hbc₁ (Or.inl ⟨e₁, e₂⟩), hi41]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₁, b₁, x₁, y₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂]; exact union_c41 a₁ b₁ b₂ x₁ y₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨(Ne.symm d3), (Ne.symm d9), d19, d22⟩)
    exact conclusion_two hfF (Or.inr (Or.inr (Or.inr rfl)))
      (same_of_sets hfK hsup hsub (tw_square hb₂W₁) nb₂ hW₁K hb₂W₁)
      ha₂P d14
      (adj_of_not_mem hfK (hKP₂ a₂ ha₂P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨d14, (Ne.symm d2), (Ne.symm d8), d15, d18⟩))
  · -- d₁ = c₄, d₂ = c₂
    have hNd₁ : N d₁ = ({a₁, b₂, y₂} : Set V) := by rw [e₁]; exact hNc₄
    have hNd₂ : N d₂ = ({b₁, a₂, x₂} : Set V) := by rw [e₂]; exact hNc₂
    have hRs : {x : V | x ∈ R} = {x : V | x ∈ Q₂} :=
      hdg c₂ c₄ q₂ Q₂ hq₂br hq₂from hq₂2 hq₂img hbc₂ hbc₄ (Or.inr ⟨e₁, e₂⟩)
    have hrr₁ : r₁ = y₂ := inter_triple hNd₁ ha₁nQ₂ hb₂nQ₂ hL.y₂_mem
      (by rw [← hRs]; exact hr₁)
    have hrr₂ : r₂ = x₂ := inter_triple hNd₂ hb₁nQ₂ ha₂nQ₂ hL.x₂_mem
      (by rw [← hRs]; exact hr₂)
    obtain ⟨hsupA, hsubA⟩ := diagonal_sets N hp₁ hp₂ hfP hPlen d₁ d₂ hRs hRlist hQ₂list hQ₂odd
      (by rw [hrr₁, hrr₂]; exact (Ne.symm hL.x₂_ne_y₂)) halt
    rw [hNd₁, hrr₁, triple_diff d7 d22] at hsupA hsubA
    have hsame := same_of_sets hfK hsupA hsubA (tw_diagonal hy₂WB hQ₂WB) ny₂ hWBK hy₂WB
    rcases statement_one_or_four_gap G hG P₁ P₂ Q₁ Q₂ a₁ b₁ a₂ b₂ x₁ y₁ x₂ y₂ hknot hP₁ hP₂
      hQ₁ hQ₂ hP₁len hP₂len K hK hnoenl hnoover hnoovercompl F f hfF hfK y₂ x₂
      Q₁ (Or.inr (Or.inr (Or.inr rfl))) hsame with hres | hnadj
    · exact Or.inl hres
    · exact conclusion_four hfF (Or.inr (Or.inr (Or.inr rfl))) hsame hnadj
  · -- d₁ = c₄, d₂ = c₃
    have hNd₁ : N d₁ = ({a₁, b₂, y₂} : Set V) := by rw [e₁]; exact hNc₄
    have hNd₂ : N d₂ = ({a₁, a₂, y₁} : Set V) := by rw [e₂]; exact hNc₃
    have hRs : {x : V | x ∈ R} = ({a₁} : Set V) := by
      rw [hsq c₃ c₄ he34 hbc₃ hbc₄ (Or.inr ⟨e₁, e₂⟩), hi34]
    obtain ⟨hsupA, hsubA⟩ := square_sets N hp₁ hp₂ hfP d₁ d₂ hRs (by rw [hNd₁]; simp)
      (by rw [hNd₂]; simp) hr₁ hr₂ halt
    obtain ⟨hsup, hsub⟩ := sets_of_union (S := ({a₂, b₂, y₁, y₂} : Set V)) hsupA hsubA
      (by rw [hNd₁, hNd₂, Set.union_comm]; exact union_c34 a₁ a₂ b₂ y₁ y₂)
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
          push_neg
          exact ⟨d2, d3, d5, d7⟩)
    exact conclusion_two hfF (Or.inl rfl)
      (same_of_sets hfK hsup hsub (tw_square ha₁W₂) na₁ hW₂K ha₁W₂)
      hb₁P (Ne.symm d1)
      (adj_of_not_mem hfK (hKP₁ b₁ hb₁P) hsub
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
            push_neg
            exact ⟨(Ne.symm d1), d8, d9, d11, d13⟩))
  · -- d₁ = c₄, d₂ = c₄
    exact absurd (e₁.trans e₂.symm) hdne

end Workspace.ProofLemmas.Thm93CaseTwoNonmajor
