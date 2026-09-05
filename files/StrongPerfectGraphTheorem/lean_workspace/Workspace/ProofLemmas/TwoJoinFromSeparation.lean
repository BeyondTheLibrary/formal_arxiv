import Mathlib
import Workspace.Types.Core
import Workspace.Types.DoubleDiamond
import Workspace.Types.Classes
import Workspace.Types.Decompositions
import Workspace.Types.Appearances
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.CubeClaimFour
import Workspace.ProofLemmas.CubeExtraction
import Workspace.Statements.S14.Thm_14_2

/-!
# A proper 2-join out of a separation

The closing paragraph of the printed proof of 14.3 (p. 91) opens

> *"Now if `Y = ∅`, then by (3) it follows that `G` admits a proper 2-join, a contradiction."*

and claim (2) of the printed proof of 13.4 (p. 85) has exactly the same shape:

> *"For assume that `N = ∅`.  Then the only edges between `V(S) ∪ D` and `A₀ ∪ B₀ ∪ M` are the
> edges from `A` to `A₀` and those from `B` to `B₀`; and since `R₀` is an odd path from `A₀` to
> `B₀` of length `≥ 3` … and both `A` and `B` contain at least two vertices, it follows that `G`
> admits a proper 2-join."*

In both places the authors exhibit a partition `(X₁, X₂)` of `V(G)` together with `A₁, B₁ ⊆ X₁`
and `A₂, B₂ ⊆ X₂` such that the only edges across are those from `A₁` to `A₂` and those from
`B₁` to `B₂`, and then leave the two remaining bullets of the definition of a *proper* 2-join —
*"every component of `G|Xᵢ` meets both `Aᵢ` and `Bᵢ`"* and the odd-path condition — to the
reader.  `admitsProper2Join_of_links` is that step, stated once:

* the component bullet is supplied in the shape it is always *available* in, namely
  **"every vertex of `Xᵢ` lies in a connected subset of `Xᵢ` that meets both `Aᵢ` and `Bᵢ`"**
  (`hlink₁`, `hlink₂`) — a component then swallows such a set by its own maximality;
* the odd-path bullet is taken verbatim, so §13 can discharge it with its path `R₀`, while §14
  gets it for free from `|A| ≥ 2` (`pathCond_of_nontrivial`).

The second half of the module is 14.3's instance,
`cube_admitsProper2Join_of_no_major`: with no major vertices, `V(G)` is the cube `K` together
with the components of `F`, each of which — by 14.2 and claim (3) of 14.3 — has its attachments
inside `A ∪ B` or inside `C ∪ D`, and *has an attachment in each of the two parts*.  Sorting the
components accordingly gives `X₁ = A ∪ B ∪ …`, `X₂ = C ∪ D ∪ …` with `A₁ = A`, `A₂ = C`,
`B₁ = B`, `B₂ = D`: the cube's own conditions (`A` complete to `C`, `B` to `D`, `A` anticomplete
to `D`, `B` to `C`) are exactly the 2-join's cross-edge condition.

Claim (3) of 14.3 is taken as a hypothesis (it lives in its own module); 14.2 is cited directly.

Nothing here corresponds to a numbered result of the paper.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.TwoJoinFromSeparation

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

variable {V : Type*}

/-! ### Bookkeeping -/

/-- A singleton is connected. -/
theorem connectedSet_singleton (G : SimpleGraph V) (v : V) :
    ConnectedSet G ({v} : Set V) := by
  intro a b
  exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)

/-- The fourth bullet of a proper 2-join — *"if `|Aᵢ| = |Bᵢ| = 1` and `G|Xᵢ` is a path joining
the members of `Aᵢ` and `Bᵢ`, then it has odd length `≥ 3`"* — is **vacuous** as soon as
`|Aᵢ| ≥ 2`.  This is how 13.4 and 14.3 both discharge it on the side carrying the cube's (or
the staircase's) `A` and `B`. -/
theorem pathCond_of_nontrivial (G : SimpleGraph V) (X A Bb : Set V) (h : A.Nontrivial) :
    ∀ a b : V, A = {a} → Bb = {b} → ∀ p : List V, IsPathFrom G p a b →
      {v : V | v ∈ p} = X → Odd (pathLength p) ∧ 3 ≤ pathLength p := by
  intro a b hA hB p hp hpX
  exfalso
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  rw [hA] at hx hy
  exact hxy ((hx : x = a).trans (hy : y = a).symm)

/-- **A component swallows any connected subset of the ambient set that meets it.**  So if every
vertex of `X` lies in a connected subset of `X` meeting `A`, then every component of `X` meets
`A`.  (`IsComponent` allows the empty set in general; here `A.Nonempty` rules it out.) -/
theorem meet_of_link {G : SimpleGraph V} {X A : Set V}
    (hAX : A ⊆ X) (hAne : A.Nonempty)
    (hlink : ∀ v ∈ X, ∃ S : Set V, S ⊆ X ∧ ConnectedSet G S ∧ v ∈ S ∧ (S ∩ A).Nonempty)
    {Cc : Set V} (hC : IsComponent G X Cc) : (Cc ∩ A).Nonempty := by
  obtain ⟨a₀, ha₀⟩ := hAne
  have hCne : Cc.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    subst hne
    have hsing := hC.2.2 ({a₀} : Set V) (Set.empty_subset _)
      (Set.singleton_subset_iff.mpr (hAX ha₀)) (connectedSet_singleton G a₀)
    exact absurd (hsing ▸ (rfl : a₀ ∈ ({a₀} : Set V))) (Set.notMem_empty a₀)
  obtain ⟨v, hv⟩ := hCne
  obtain ⟨S, hSX, hScon, hvS, hSA⟩ := hlink v (hC.1 hv)
  have hun : ConnectedSet G (Cc ∪ S) :=
    ConnectedSetUnionAttach.connectedSet_union hC.2.1 hScon (Or.inl ⟨v, hv, hvS⟩)
  have heq : Cc ∪ S = Cc :=
    hC.2.2 (Cc ∪ S) Set.subset_union_left (Set.union_subset hC.1 hSX) hun
  obtain ⟨x, hxS, hxA⟩ := hSA
  have hxC : x ∈ Cc := by rw [← heq]; exact Or.inr hxS
  exact ⟨x, hxC, hxA⟩

/-! ### The general construction -/

/-- **A proper 2-join from a separation.**  See the module doc-comment: this is the step that
13.4's claim (2) and the opening sentence of 14.3's closing paragraph both leave to the reader.
-/
theorem admitsProper2Join_of_links {G : SimpleGraph V} {X₁ X₂ A₁ B₁ A₂ B₂ : Set V}
    (hcover : X₁ ∪ X₂ = Set.univ) (hdisj : Disjoint X₁ X₂)
    (hA₁X : A₁ ⊆ X₁) (hB₁X : B₁ ⊆ X₁) (hA₂X : A₂ ⊆ X₂) (hB₂X : B₂ ⊆ X₂)
    (hA₁ne : A₁.Nonempty) (hB₁ne : B₁.Nonempty) (hA₂ne : A₂.Nonempty) (hB₂ne : B₂.Nonempty)
    (hdA₁B₁ : Disjoint A₁ B₁) (hdA₂B₂ : Disjoint A₂ B₂)
    (hcross : ∀ u ∈ X₁, ∀ v ∈ X₂, G.Adj u v ↔ ((u ∈ A₁ ∧ v ∈ A₂) ∨ (u ∈ B₁ ∧ v ∈ B₂)))
    (hlink₁ : ∀ v ∈ X₁, ∃ S : Set V, S ⊆ X₁ ∧ ConnectedSet G S ∧ v ∈ S ∧
      (S ∩ A₁).Nonempty ∧ (S ∩ B₁).Nonempty)
    (hlink₂ : ∀ v ∈ X₂, ∃ S : Set V, S ⊆ X₂ ∧ ConnectedSet G S ∧ v ∈ S ∧
      (S ∩ A₂).Nonempty ∧ (S ∩ B₂).Nonempty)
    (hpath₁ : ∀ a b : V, A₁ = {a} → B₁ = {b} → ∀ p : List V, IsPathFrom G p a b →
      {v : V | v ∈ p} = X₁ → Odd (pathLength p) ∧ 3 ≤ pathLength p)
    (hpath₂ : ∀ a b : V, A₂ = {a} → B₂ = {b} → ∀ p : List V, IsPathFrom G p a b →
      {v : V | v ∈ p} = X₂ → Odd (pathLength p) ∧ 3 ≤ pathLength p) :
    AdmitsProper2Join G := by
  have h3₁ : ∀ Cc : Set V, IsComponent G X₁ Cc → (Cc ∩ A₁).Nonempty ∧ (Cc ∩ B₁).Nonempty := by
    intro Cc hC
    constructor
    · refine meet_of_link hA₁X hA₁ne (fun v hv => ?_) hC
      obtain ⟨S, h1, h2, h3, h4, h5⟩ := hlink₁ v hv
      exact ⟨S, h1, h2, h3, h4⟩
    · refine meet_of_link hB₁X hB₁ne (fun v hv => ?_) hC
      obtain ⟨S, h1, h2, h3, h4, h5⟩ := hlink₁ v hv
      exact ⟨S, h1, h2, h3, h5⟩
  have h3₂ : ∀ Cc : Set V, IsComponent G X₂ Cc → (Cc ∩ A₂).Nonempty ∧ (Cc ∩ B₂).Nonempty := by
    intro Cc hC
    constructor
    · refine meet_of_link hA₂X hA₂ne (fun v hv => ?_) hC
      obtain ⟨S, h1, h2, h3, h4, h5⟩ := hlink₂ v hv
      exact ⟨S, h1, h2, h3, h4⟩
    · refine meet_of_link hB₂X hB₂ne (fun v hv => ?_) hC
      obtain ⟨S, h1, h2, h3, h4, h5⟩ := hlink₂ v hv
      exact ⟨S, h1, h2, h3, h5⟩
  exact ⟨X₁, X₂, hcover, hdisj, A₁, B₁, A₂, B₂, hA₁X, hB₁X, hA₂X, hB₂X,
    hA₁ne, hB₁ne, hA₂ne, hB₂ne, hdA₁B₁, hdA₂B₂, hcross, h3₁, h3₂, hpath₁, hpath₂⟩

/-! ### Squares as a source of cross edges -/

/-- The `(1,3)` diagonal of a square is a non-edge (`square_ends` is the `(0,2)` one). -/
theorem square_diag {G : SimpleGraph V} {A B : Set V} {a₁ b₁ b₂ a₂ : V}
    (h : IsSquare G A B a₁ b₁ b₂ a₂) : ¬ G.Adj b₁ a₂ := by
  obtain ⟨hhole, -, -, -, -⟩ := h
  have h2 := HoleBasics.hole_adj_iff hhole
    (show (1 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
    (show (3 : ℕ) < ([a₁, b₁, b₂, a₂] : List V).length by simp)
  simpa using h2

/-- Every vertex of `A` has a neighbour in `B` when `(A, B)` is square-connected: feed the
partition clause the trivial partition `({a}, A \ {a})` and read off the square's first edge. -/
theorem exists_adj_right {G : SimpleGraph V} {A B : Set V} (h : SquareConnected G A B)
    {a : V} (ha : a ∈ A) : ∃ b ∈ B, G.Adj a b := by
  obtain ⟨⟨hAnt, -⟩, h1, -⟩ := h
  obtain ⟨a', ha', hne⟩ := hAnt.exists_ne a
  obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, -⟩ :=
    h1 ({a} : Set V) (A \ ({a} : Set V)) (Set.union_diff_cancel (by simpa using ha))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨a, rfl⟩ ⟨a', ha', hne⟩
  have hm : a₁ = a := hm1
  refine ⟨b₁, hsq.2.2.2.1, ?_⟩
  rw [← hm]
  exact CubeClaimFour.square_adj hsq

/-- Every vertex of `B` has a neighbour in `A` when `(A, B)` is square-connected. -/
theorem exists_adj_left {G : SimpleGraph V} {A B : Set V} (h : SquareConnected G A B)
    {b : V} (hb : b ∈ B) : ∃ a ∈ A, G.Adj b a := by
  obtain ⟨⟨-, hBnt⟩, -, h2⟩ := h
  obtain ⟨b', hb', hne⟩ := hBnt.exists_ne b
  obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, -⟩ :=
    h2 ({b} : Set V) (B \ ({b} : Set V)) (Set.union_diff_cancel (by simpa using hb))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨b, rfl⟩ ⟨b', hb', hne⟩
  have hm : b₁ = b := hm1
  refine ⟨a₁, hsq.2.1, ?_⟩
  rw [← hm]
  exact (CubeClaimFour.square_adj hsq).symm

/-- Every vertex of `C` has a **`G`-neighbour** in `D` when `(C, D)` is antisquare-connected:
the antisquare `c₁`-`d₁`-`d₂`-`c₂` is a hole of `Gᶜ`, so its `(0,2)` diagonal `c₁d₂` is a
non-edge of `Gᶜ`, i.e. an edge of `G`. -/
theorem exists_adj_right_of_antisquare {G : SimpleGraph V} {C D : Set V}
    (hdisj : Disjoint C D) (h : AntisquareConnected G C D)
    {c : V} (hc : c ∈ C) : ∃ d ∈ D, G.Adj c d := by
  obtain ⟨⟨hCnt, -⟩, h1, -⟩ := h
  obtain ⟨c', hc', hne⟩ := hCnt.exists_ne c
  obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, -⟩ :=
    h1 ({c} : Set V) (C \ ({c} : Set V)) (Set.union_diff_cancel (by simpa using hc))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨c, rfl⟩ ⟨c', hc', hne⟩
  have hm : a₁ = c := hm1
  have hb₂ : b₂ ∈ D := hsq.2.2.2.2
  have hnc : ¬ Gᶜ.Adj a₁ b₂ := CubeClaimFour.square_ends hsq
  have hane : a₁ ≠ b₂ := by
    rw [hm]
    exact fun he => Set.disjoint_left.mp hdisj hc (he ▸ hb₂)
  refine ⟨b₂, hb₂, ?_⟩
  rw [← hm]
  by_contra hg
  exact hnc ⟨hane, hg⟩

/-- Every vertex of `D` has a **`G`-neighbour** in `C` when `(C, D)` is antisquare-connected:
here it is the `(1,3)` diagonal `d₁c₂` of the antisquare that is used. -/
theorem exists_adj_left_of_antisquare {G : SimpleGraph V} {C D : Set V}
    (hdisj : Disjoint C D) (h : AntisquareConnected G C D)
    {d : V} (hd : d ∈ D) : ∃ c ∈ C, G.Adj d c := by
  obtain ⟨⟨-, hDnt⟩, -, h2⟩ := h
  obtain ⟨d', hd', hne⟩ := hDnt.exists_ne d
  obtain ⟨a₁, b₁, b₂, a₂, hsq, hm1, -⟩ :=
    h2 ({d} : Set V) (D \ ({d} : Set V)) (Set.union_diff_cancel (by simpa using hd))
      (Set.disjoint_left.mpr (fun x hx hy => hy.2 hx)) ⟨d, rfl⟩ ⟨d', hd', hne⟩
  have hm : b₁ = d := hm1
  have ha₂ : a₂ ∈ C := hsq.2.2.1
  have hnc : ¬ Gᶜ.Adj b₁ a₂ := square_diag hsq
  have hane : b₁ ≠ a₂ := by
    rw [hm]
    exact fun he => Set.disjoint_left.mp hdisj (he ▸ ha₂) hd
  refine ⟨a₂, ha₂, ?_⟩
  rw [← hm]
  by_contra hg
  exact hnc ⟨hane, hg⟩

/-! ### 14.3: the case `Y = ∅` -/

/-- PAPER (printed p. 91): *"Now if `Y = ∅`, then by (3) it follows that `G` admits a proper
2-join, a contradiction."*

`(A, B, C, D)` is a maximal cube of `G ∈ F₅` forming `K`, `F` is the set of minor vertices and
`Y` the set of major ones; `hclaim3` is claim (3) of the printed proof, *"there is no component
of `F` such that its set of attachments in `K` is a subset of one of `A ∪ C`, `B ∪ D`"*.  It is
asked for only at **nonempty** components — `IsComponent` admits `∅` as a component of `∅`, for
which claim (3) is false, and `CubeClaimThree.cube_claim_three` wants `F.Nonempty` anyway, which
the caller reads off the component it is being applied to.

Claim (3) is load-bearing twice: it splits the components between the two sides, and it forces
each component to have an attachment in *each* of the two parts it attaches to, which is what
makes every component of `G|Xᵢ` meet both `Aᵢ` and `Bᵢ`.

The 2-join is `X₁ = A ∪ B ∪ (components of F attaching inside A ∪ B)`,
`X₂ = C ∪ D ∪ (the rest)`, with `A₁ = A`, `A₂ = C`, `B₁ = B`, `B₂ = D`. -/
theorem cube_admitsProper2Join_of_no_major [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {A B C D F Y : Set V}
    (hG : InF5 G) (hcube : MaximalCube G A B C D)
    (hFdef : F = {v : V | MinorForCube G A B C D v})
    (hYdef : Y = {v : V | MajorForCube G A B C D v})
    (hYempty : Y = ∅)
    (hclaim3 : ∀ F₁ : Set V, IsComponent G F F₁ → F₁.Nonempty →
        ¬ (attachments G F₁ (A ∪ B ∪ C ∪ D) ⊆ A ∪ C) ∧
        ¬ (attachments G F₁ (A ∪ B ∪ C ∪ D) ⊆ B ∪ D)) :
    AdmitsProper2Join G := by
  classical
  obtain ⟨⟨⟨dAB, dAC, dAD, dBC, dBD, dCD⟩, hAne, hBne, hCne, hDne⟩,
    ⟨cAC, cBD, aAD, aBC⟩, hsqAB, hsqCD⟩ := hcube.1
  obtain ⟨X₁, hX₁⟩ : ∃ S : Set V, S = (A ∪ B) ∪
      {v : V | ∃ P : Set V, IsComponent G F P ∧ v ∈ P ∧
        attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B} := ⟨_, rfl⟩
  obtain ⟨X₂, hX₂⟩ : ∃ S : Set V, S = (C ∪ D) ∪
      {v : V | ∃ P : Set V, IsComponent G F P ∧ v ∈ P ∧
        ¬ (attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B)} := ⟨_, rfl⟩
  -- basic memberships
  have hFmin : ∀ v ∈ F, MinorForCube G A B C D v := by intro v hv; rw [hFdef] at hv; exact hv
  have hFK : ∀ v ∈ F, v ∉ A ∪ B ∪ C ∪ D := fun v hv => (hFmin v hv).1
  -- the four inclusions into `X₁`, `X₂`
  have hAX₁ : A ⊆ X₁ := fun x hx => by rw [hX₁]; exact Or.inl (Or.inl hx)
  have hBX₁ : B ⊆ X₁ := fun x hx => by rw [hX₁]; exact Or.inl (Or.inr hx)
  have hCX₂ : C ⊆ X₂ := fun x hx => by rw [hX₂]; exact Or.inl (Or.inl hx)
  have hDX₂ : D ⊆ X₂ := fun x hx => by rw [hX₂]; exact Or.inl (Or.inr hx)
  have hPX₁ : ∀ P : Set V, IsComponent G F P →
      attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B → P ⊆ X₁ :=
    fun P hP hsub x hx => by rw [hX₁]; exact Or.inr ⟨P, hP, hx, hsub⟩
  have hPX₂ : ∀ P : Set V, IsComponent G F P →
      ¬ (attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B) → P ⊆ X₂ :=
    fun P hP hsub x hx => by rw [hX₂]; exact Or.inr ⟨P, hP, hx, hsub⟩
  -- 14.2 applied to a component of `F`, with claim (3) killing two of its four alternatives
  have h142 : ∀ P : Set V, IsComponent G F P → P.Nonempty →
      (attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B ∨
        attachments G P (A ∪ B ∪ C ∪ D) ⊆ C ∪ D) := by
    intro P hP hPne
    have h := _root_.Workspace.Statements.S14.SPGT.thm_14_2 G hG A B C D hcube P
      (fun v hv => hFK v (hP.1 hv)) hP.2.1 (fun v hv => hFmin v (hP.1 hv))
      (attachments G P (A ∪ B ∪ C ∪ D)) rfl
    rcases h.1 with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
    · exact absurd h1 (hclaim3 P hP hPne).1
    · exact absurd h1 (hclaim3 P hP hPne).2
  -- each component has an attachment in each of the two parts it attaches to
  have hattA : ∀ P : Set V, IsComponent G F P → P.Nonempty →
      attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B →
      ∃ a ∈ attachments G P (A ∪ B ∪ C ∪ D), a ∈ A := by
    intro P hP hPne hsub
    by_contra hcon
    push Not at hcon
    refine (hclaim3 P hP hPne).2 (fun w hw => ?_)
    rcases hsub hw with h | h
    · exact absurd h (hcon w hw)
    · exact Or.inl h
  have hattB : ∀ P : Set V, IsComponent G F P → P.Nonempty →
      attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B →
      ∃ b ∈ attachments G P (A ∪ B ∪ C ∪ D), b ∈ B := by
    intro P hP hPne hsub
    by_contra hcon
    push Not at hcon
    refine (hclaim3 P hP hPne).1 (fun w hw => ?_)
    rcases hsub hw with h | h
    · exact Or.inl h
    · exact absurd h (hcon w hw)
  have hattC : ∀ P : Set V, IsComponent G F P → P.Nonempty →
      attachments G P (A ∪ B ∪ C ∪ D) ⊆ C ∪ D →
      ∃ c ∈ attachments G P (A ∪ B ∪ C ∪ D), c ∈ C := by
    intro P hP hPne hsub
    by_contra hcon
    push Not at hcon
    refine (hclaim3 P hP hPne).2 (fun w hw => ?_)
    rcases hsub hw with h | h
    · exact absurd h (hcon w hw)
    · exact Or.inr h
  have hattD : ∀ P : Set V, IsComponent G F P → P.Nonempty →
      attachments G P (A ∪ B ∪ C ∪ D) ⊆ C ∪ D →
      ∃ d ∈ attachments G P (A ∪ B ∪ C ∪ D), d ∈ D := by
    intro P hP hPne hsub
    by_contra hcon
    push Not at hcon
    refine (hclaim3 P hP hPne).1 (fun w hw => ?_)
    rcases hsub hw with h | h
    · exact Or.inr h
    · exact absurd h (hcon w hw)
  -- the cover
  have hcover : X₁ ∪ X₂ = Set.univ := by
    refine Set.eq_univ_of_forall (fun v => ?_)
    by_cases hvK : v ∈ A ∪ B ∪ C ∪ D
    · rcases hvK with ((hv | hv) | hv) | hv
      · exact Or.inl (hAX₁ hv)
      · exact Or.inl (hBX₁ hv)
      · exact Or.inr (hCX₂ hv)
      · exact Or.inr (hDX₂ hv)
    · have hvF : v ∈ F := by
        rcases CubeExtraction.minor_or_major G hG hcube hvK with h | h
        · rw [hFdef]; exact h
        · exfalso
          have hvY : v ∈ Y := by rw [hYdef]; exact h
          rw [hYempty] at hvY
          exact Set.notMem_empty v hvY
      obtain ⟨P, hP, hvP⟩ := ComponentsOfSetBasics.exists_isComponent_mem G F hvF
      by_cases hsub : attachments G P (A ∪ B ∪ C ∪ D) ⊆ A ∪ B
      · exact Or.inl (hPX₁ P hP hsub hvP)
      · exact Or.inr (hPX₂ P hP hsub hvP)
  -- the two sides are disjoint
  have hdisjX : Disjoint X₁ X₂ := by
    refine Set.disjoint_left.mpr (fun x hx1 hx2 => ?_)
    rw [hX₁] at hx1
    rw [hX₂] at hx2
    rcases hx1 with h1 | ⟨P, hP, hxP, hsub⟩
    · rcases hx2 with h2 | ⟨Q, hQ, hxQ, hnsub⟩
      · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
        · exact Set.disjoint_left.mp dAC h1 h2
        · exact Set.disjoint_left.mp dAD h1 h2
        · exact Set.disjoint_left.mp dBC h1 h2
        · exact Set.disjoint_left.mp dBD h1 h2
      · exact hFK x (hQ.1 hxQ) (Or.inl (Or.inl h1))
    · rcases hx2 with h2 | ⟨Q, hQ, hxQ, hnsub⟩
      · refine hFK x (hP.1 hxP) ?_
        rcases h2 with h | h
        · exact Or.inl (Or.inr h)
        · exact Or.inr h
      · have hPQ : P = Q := by
          by_contra hne
          exact Set.disjoint_left.mp
            (ComponentsOfSetBasics.disjoint_of_isComponent G hP hQ hne) hxP hxQ
        rw [hPQ] at hsub
        exact hnsub hsub
  -- the cross-edge condition
  have hcross : ∀ u ∈ X₁, ∀ v ∈ X₂, G.Adj u v ↔ ((u ∈ A ∧ v ∈ C) ∨ (u ∈ B ∧ v ∈ D)) := by
    intro u hu v hv
    rw [hX₁] at hu
    rw [hX₂] at hv
    constructor
    · intro hadj
      rcases hu with hu | ⟨P, hP, huP, hsubP⟩
      · rcases hv with hv | ⟨Q, hQ, hvQ, hnsubQ⟩
        · rcases hu with hu | hu <;> rcases hv with hv | hv
          · exact Or.inl ⟨hu, hv⟩
          · exact absurd hadj (aAD u hu v hv)
          · exact absurd hadj (aBC u hu v hv)
          · exact Or.inr ⟨hu, hv⟩
        · exfalso
          have hatt : u ∈ attachments G Q (A ∪ B ∪ C ∪ D) := ⟨Or.inl (Or.inl hu), v, hvQ, hadj⟩
          rcases h142 Q hQ ⟨v, hvQ⟩ with h | h
          · exact hnsubQ h
          · rcases h hatt with h' | h' <;> rcases hu with hu | hu
            · exact Set.disjoint_left.mp dAC hu h'
            · exact Set.disjoint_left.mp dBC hu h'
            · exact Set.disjoint_left.mp dAD hu h'
            · exact Set.disjoint_left.mp dBD hu h'
      · rcases hv with hv | ⟨Q, hQ, hvQ, hnsubQ⟩
        · exfalso
          have hvK : v ∈ A ∪ B ∪ C ∪ D := by
            rcases hv with h | h
            · exact Or.inl (Or.inr h)
            · exact Or.inr h
          have hatt : v ∈ attachments G P (A ∪ B ∪ C ∪ D) := ⟨hvK, u, huP, hadj.symm⟩
          rcases hsubP hatt with h' | h' <;> rcases hv with hv | hv
          · exact Set.disjoint_left.mp dAC h' hv
          · exact Set.disjoint_left.mp dAD h' hv
          · exact Set.disjoint_left.mp dBC h' hv
          · exact Set.disjoint_left.mp dBD h' hv
        · exfalso
          have hPQ : P ≠ Q := fun he => hnsubQ (he ▸ hsubP)
          exact ComponentsOfSetBasics.anticomplete_of_isComponent G hP hQ hPQ u huP v hvQ hadj
    · rintro (⟨hu, hv⟩ | ⟨hu, hv⟩)
      · exact cAC u hu v hv
      · exact cBD u hu v hv
  -- every vertex of `X₁` lies in a connected subset of `X₁` meeting both `A` and `B`
  have hlink₁ : ∀ v ∈ X₁, ∃ S : Set V, S ⊆ X₁ ∧ ConnectedSet G S ∧ v ∈ S ∧
      (S ∩ A).Nonempty ∧ (S ∩ B).Nonempty := by
    intro v hv
    rw [hX₁] at hv
    rcases hv with hv | ⟨P, hP, hvP, hsub⟩
    · rcases hv with hv | hv
      · obtain ⟨b, hb, hadj⟩ := exists_adj_right hsqAB hv
        refine ⟨({v} : Set V) ∪ {b}, ?_, ?_, Or.inl rfl, ⟨v, Or.inl rfl, hv⟩, ⟨b, Or.inr rfl, hb⟩⟩
        · exact Set.union_subset (Set.singleton_subset_iff.mpr (hAX₁ hv))
            (Set.singleton_subset_iff.mpr (hBX₁ hb))
        · exact ConnectedSetUnionAttach.connectedSet_union_singleton
            (connectedSet_singleton G v) ⟨v, rfl, hadj.symm⟩
      · obtain ⟨a, ha, hadj⟩ := exists_adj_left hsqAB hv
        refine ⟨({v} : Set V) ∪ {a}, ?_, ?_, Or.inl rfl, ⟨a, Or.inr rfl, ha⟩, ⟨v, Or.inl rfl, hv⟩⟩
        · exact Set.union_subset (Set.singleton_subset_iff.mpr (hBX₁ hv))
            (Set.singleton_subset_iff.mpr (hAX₁ ha))
        · exact ConnectedSetUnionAttach.connectedSet_union_singleton
            (connectedSet_singleton G v) ⟨v, rfl, hadj.symm⟩
    · obtain ⟨a, hatta, haA⟩ := hattA P hP ⟨v, hvP⟩ hsub
      obtain ⟨b, hattb, hbB⟩ := hattB P hP ⟨v, hvP⟩ hsub
      obtain ⟨fa, hfaP, hadja⟩ := hatta.2
      obtain ⟨fb, hfbP, hadjb⟩ := hattb.2
      refine ⟨(P ∪ ({a} : Set V)) ∪ ({b} : Set V), ?_, ?_, Or.inl (Or.inl hvP),
        ⟨a, Or.inl (Or.inr rfl), haA⟩, ⟨b, Or.inr rfl, hbB⟩⟩
      · exact Set.union_subset (Set.union_subset (hPX₁ P hP hsub)
          (Set.singleton_subset_iff.mpr (hAX₁ haA))) (Set.singleton_subset_iff.mpr (hBX₁ hbB))
      · exact ConnectedSetUnionAttach.connectedSet_union_singleton
          (ConnectedSetUnionAttach.connectedSet_union_singleton hP.2.1 ⟨fa, hfaP, hadja⟩)
          ⟨fb, Or.inl hfbP, hadjb⟩
  have hlink₂ : ∀ v ∈ X₂, ∃ S : Set V, S ⊆ X₂ ∧ ConnectedSet G S ∧ v ∈ S ∧
      (S ∩ C).Nonempty ∧ (S ∩ D).Nonempty := by
    intro v hv
    rw [hX₂] at hv
    rcases hv with hv | ⟨P, hP, hvP, hnsub⟩
    · rcases hv with hv | hv
      · obtain ⟨d, hd, hadj⟩ := exists_adj_right_of_antisquare dCD hsqCD hv
        refine ⟨({v} : Set V) ∪ {d}, ?_, ?_, Or.inl rfl, ⟨v, Or.inl rfl, hv⟩, ⟨d, Or.inr rfl, hd⟩⟩
        · exact Set.union_subset (Set.singleton_subset_iff.mpr (hCX₂ hv))
            (Set.singleton_subset_iff.mpr (hDX₂ hd))
        · exact ConnectedSetUnionAttach.connectedSet_union_singleton
            (connectedSet_singleton G v) ⟨v, rfl, hadj.symm⟩
      · obtain ⟨c, hc, hadj⟩ := exists_adj_left_of_antisquare dCD hsqCD hv
        refine ⟨({v} : Set V) ∪ {c}, ?_, ?_, Or.inl rfl, ⟨c, Or.inr rfl, hc⟩, ⟨v, Or.inl rfl, hv⟩⟩
        · exact Set.union_subset (Set.singleton_subset_iff.mpr (hDX₂ hv))
            (Set.singleton_subset_iff.mpr (hCX₂ hc))
        · exact ConnectedSetUnionAttach.connectedSet_union_singleton
            (connectedSet_singleton G v) ⟨v, rfl, hadj.symm⟩
    · have hsub : attachments G P (A ∪ B ∪ C ∪ D) ⊆ C ∪ D := by
        rcases h142 P hP ⟨v, hvP⟩ with h | h
        · exact absurd h hnsub
        · exact h
      obtain ⟨c, hattc, hcC⟩ := hattC P hP ⟨v, hvP⟩ hsub
      obtain ⟨d, hattd, hdD⟩ := hattD P hP ⟨v, hvP⟩ hsub
      obtain ⟨fc, hfcP, hadjc⟩ := hattc.2
      obtain ⟨fd, hfdP, hadjd⟩ := hattd.2
      refine ⟨(P ∪ ({c} : Set V)) ∪ ({d} : Set V), ?_, ?_, Or.inl (Or.inl hvP),
        ⟨c, Or.inl (Or.inr rfl), hcC⟩, ⟨d, Or.inr rfl, hdD⟩⟩
      · exact Set.union_subset (Set.union_subset (hPX₂ P hP hnsub)
          (Set.singleton_subset_iff.mpr (hCX₂ hcC))) (Set.singleton_subset_iff.mpr (hDX₂ hdD))
      · exact ConnectedSetUnionAttach.connectedSet_union_singleton
          (ConnectedSetUnionAttach.connectedSet_union_singleton hP.2.1 ⟨fc, hfcP, hadjc⟩)
          ⟨fd, Or.inl hfdP, hadjd⟩
  exact admitsProper2Join_of_links hcover hdisjX hAX₁ hBX₁ hCX₂ hDX₂ hAne hBne hCne hDne
    dAB dCD hcross hlink₁ hlink₂ (pathCond_of_nontrivial G X₁ A B hsqAB.1.1)
    (pathCond_of_nontrivial G X₂ C D hsqCD.1.1)

end Workspace.ProofLemmas.TwoJoinFromSeparation
