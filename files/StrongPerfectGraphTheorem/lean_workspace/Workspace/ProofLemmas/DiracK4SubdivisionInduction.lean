import Workspace.ProofLemmas.DiracInductionBasics

/-!
# The finite induction in Dirac's `K₄`-subdivision theorem

For induction we allow one edge incident with the distinguished vertex to be counted twice.
Equivalently, when the flag is `some b`, `b` is allowed degree two while every vertex other
than the distinguished vertex and `b` has degree at least three.  This is the simple-graph
encoding of the single parallel edge in the standard textbook proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.DiracK4SubdivisionInduction

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.SubdivisionDatum
open Workspace.ProofLemmas.DiracSuppressionLift
open Workspace.ProofLemmas.DiracInductionBasics

variable {U : Type*} [Fintype U] [DecidableEq U]

def DegreeCondition (G : SimpleGraph U) (root : U) : Option U → Prop
  | none => ∀ x : U, x ≠ root → 3 ≤ (G.neighborSet x).ncard
  | some boosted =>
      G.Adj root boosted ∧
      2 ≤ (G.neighborSet boosted).ncard ∧
      ∀ x : U, x ≠ root → x ≠ boosted → 3 ≤ (G.neighborSet x).ncard

private def boostWeight {X : Type*} : Option X → ℕ
  | none => 0
  | some _ => 1

private noncomputable def inductionRank {X : Type*} [Fintype X]
    (G : SimpleGraph X) (boost : Option X) : ℕ × ℕ :=
  (Fintype.card X, 2 * G.edgeSet.ncard + boostWeight boost)

private abbrev RankRel : (ℕ × ℕ) → (ℕ × ℕ) → Prop :=
  Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)

private theorem inductionRank_lt_of_card_lt
    {X Y : Type*} [Fintype X] [Fintype Y]
    (G : SimpleGraph X) (boost : Option X) (H : SimpleGraph Y) (boost' : Option Y)
    (hcard : Fintype.card Y < Fintype.card X) :
    RankRel (inductionRank H boost') (inductionRank G boost) :=
  Prod.Lex.left _ _ hcard

private theorem inductionRank_none_lt_some (G : SimpleGraph U) (boosted : U) :
    RankRel (inductionRank G none) (inductionRank G (some boosted)) := by
  apply Prod.Lex.right
  simp [inductionRank, boostWeight]

private theorem inductionRank_deleteEdge_lt (G : SimpleGraph U) {a b : U}
    (hab : G.Adj a b) :
    RankRel (inductionRank (deleteEdge G a b) none) (inductionRank G none) := by
  apply Prod.Lex.right
  simp only [inductionRank, boostWeight, add_zero, deleteEdge,
    SimpleGraph.edgeSet_deleteEdges]
  have hlt : (G.edgeSet \ {s(a, b)}).ncard < G.edgeSet.ncard :=
    Set.ncard_diff_singleton_lt_of_mem hab
  omega

private theorem four_le_card_of_none {G : SimpleGraph U} {root : U}
    (hcard : 2 ≤ Fintype.card U) (h : DegreeCondition G root none) :
    4 ≤ Fintype.card U := by
  obtain ⟨x, hxr⟩ := Fintype.exists_ne_of_one_lt_card hcard root
  have hdeg := h x hxr
  have hlt := ncard_neighborSet_lt_card G x
  omega

private theorem three_le_card_of_some {G : SimpleGraph U} {root boosted : U}
    (h : DegreeCondition G root (some boosted)) : 3 ≤ Fintype.card U := by
  have hdeg := h.2.1
  have hlt := ncard_neighborSet_lt_card G boosted
  omega

private theorem neighbor_eq_of_ncard_le_one {G : SimpleGraph U} {root x y : U}
    (hcard : (G.neighborSet root).ncard ≤ 1) (hx : G.Adj root x) (hy : G.Adj root y) : x = y := by
  exact (Set.ncard_le_one (Set.toFinite _)).mp hcard x hx y hy

private theorem val_ne_of_subtype_ne {root : U} {x y : Without root} (h : x ≠ y) :
    (x : U) ≠ (y : U) := fun hxy ↦ h (Subtype.ext hxy)

private theorem not_adj_root_of_neighbor_pair {G : SimpleGraph U} {root a b x : U}
    (hneigh : G.neighborSet root = {a, b}) (hxa : x ≠ a) (hxb : x ≠ b) :
    ¬ G.Adj x root := by
  intro hxr
  have hxmem : x ∈ G.neighborSet root := hxr.symm
  rw [hneigh] at hxmem
  rcases hxmem with rfl | h
  · exact hxa rfl
  · exact hxb (by simpa using h)

private theorem not_adj_root_of_neighbor_triple {G : SimpleGraph U} {root a b c x : U}
    (hneigh : G.neighborSet root = {a, b, c})
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) : ¬ G.Adj x root := by
  intro hxr
  have hxmem : x ∈ G.neighborSet root := hxr.symm
  rw [hneigh] at hxmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxmem
  rcases hxmem with rfl | rfl | rfl
  · exact hxa rfl
  · exact hxb rfl
  · exact hxc rfl

private theorem degreeCondition_suppress_three {H : SimpleGraph U} {root a b c : U}
    (hregular : ∀ x : U, x ≠ root → 3 ≤ (H.neighborSet x).ncard)
    (hneigh : H.neighborSet root = {a, b, c})
    (hra : H.Adj root a) (hrb : H.Adj root b) (hrc : H.Adj root c)
    (hab : ¬ H.Adj a b) (habne : a ≠ b) :
    DegreeCondition
      (suppressVertexGraph H root a b hra.ne.symm hrb.ne.symm)
      (⟨c, hrc.ne.symm⟩ : Without root) none := by
  classical
  let a' : Without root := ⟨a, hra.ne.symm⟩
  let b' : Without root := ⟨b, hrb.ne.symm⟩
  let c' : Without root := ⟨c, hrc.ne.symm⟩
  have hInot : ¬ (H.induce ({root} : Set U)ᶜ).Adj a' b' := hab
  have habne' : a' ≠ b' := by
    intro h
    exact habne (congrArg Subtype.val h)
  change DegreeCondition
    (H.induce ({root} : Set U)ᶜ ⊔ SimpleGraph.edge a' b') c' none
  intro x hxc
  have hxroot : (x : U) ≠ root := x.property
  by_cases hxa : x = a'
  · subst x
    have hsup := ncard_neighborSet_sup_edge_left
      (H.induce ({root} : Set U)ᶜ) hInot habne'
    have hind := ncard_neighborSet_induce_compl_singleton_of_adj H root a' hra.symm
    dsimp only [a'] at hsup hind ⊢
    have hdeg := hregular a hra.ne.symm
    omega
  · by_cases hxb : x = b'
    · subst x
      have hsup := ncard_neighborSet_sup_edge_right
        (H.induce ({root} : Set U)ᶜ) hInot habne'
      have hind := ncard_neighborSet_induce_compl_singleton_of_adj H root b' hrb.symm
      dsimp only [b'] at hsup hind ⊢
      have hdeg := hregular b hrb.ne.symm
      omega
    · have hxaU : (x : U) ≠ a := by intro h; exact hxa (Subtype.ext h)
      have hxbU : (x : U) ≠ b := by intro h; exact hxb (Subtype.ext h)
      by_cases hxcEq : x = c'
      · exact (hxc hxcEq).elim
      · have hxcU : (x : U) ≠ c := by intro h; exact hxcEq (Subtype.ext h)
        have hxnot := not_adj_root_of_neighbor_triple hneigh hxaU hxbU hxcU
        have hsup := ncard_neighborSet_sup_edge_other
          (H.induce ({root} : Set U)ᶜ) hxa hxb
        have hind := ncard_neighborSet_induce_compl_singleton_of_not_adj H root x hxnot
        have hdeg := hregular (x : U) hxroot
        omega

private theorem hasK4Datum_of_root_triangle {G : SimpleGraph U} {root a b c : U}
    (habne : a ≠ b) (hacne : a ≠ c) (hbcne : b ≠ c)
    (hra : G.Adj root a) (hrb : G.Adj root b) (hrc : G.Adj root c)
    (hab : G.Adj a b) (hac : G.Adj a c) (hbc : G.Adj b c) : HasK4Datum G := by
  let kappa : Fin 4 → U := ![root, a, b, c]
  apply hasK4Datum_of_four_clique kappa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [kappa]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [kappa, SimpleGraph.adj_comm]

universe u

private def InductionStatement (p : ℕ × ℕ) : Prop :=
  ∀ {X : Type u} [Fintype X] [DecidableEq X]
    (G : SimpleGraph X) (root : X) (boost : Option X),
    inductionRank G boost = p →
    2 ≤ Fintype.card X → DegreeCondition G root boost → HasK4Datum G

private theorem hasK4Datum_induction (p : ℕ × ℕ) : InductionStatement p := by
  apply (wellFounded_lt.prod_lex wellFounded_lt).induction p
  intro p ih U instF instD G root boost hrank hcard hcond
  subst p
  classical
  cases boost with
  | some boosted =>
      have hrootBoost : G.Adj root boosted := hcond.1
      have hboostDeg : 2 ≤ (G.neighborSet boosted).ncard := hcond.2.1
      have hregular := hcond.2.2
      have hcard3 : 3 ≤ Fintype.card U := three_le_card_of_some hcond
      by_cases hrootSmall : (G.neighborSet root).ncard ≤ 1
      · -- Delete a leaf root; its unique neighbour becomes the new distinguished vertex.
        let boosted' : Without root := ⟨boosted, hrootBoost.ne.symm⟩
        let I : SimpleGraph (Without root) := G.induce ({root} : Set U)ᶜ
        have hIcard : 2 ≤ Fintype.card (Without root) := two_le_card_without root hcard3
        have hIcond : DegreeCondition I boosted' none := by
          intro x hxb
          have hxroot : (x : U) ≠ root := x.property
          have hxboost : (x : U) ≠ boosted := by
            intro h
            exact hxb (Subtype.ext h)
          have hxnot : ¬ G.Adj (x : U) root := by
            intro hxr
            exact hxboost (neighbor_eq_of_ncard_le_one hrootSmall hxr.symm hrootBoost)
          dsimp only [I]
          exact three_le_neighborSet_induce_compl_singleton_of_not_adj G root x hxnot
            (hregular (x : U) hxroot hxboost)
        have hlt : RankRel (inductionRank I none)
            (inductionRank G (some boosted)) := by
          apply inductionRank_lt_of_card_lt
          rw [card_without]
          omega
        exact hasK4Datum_of_induce_compl_singleton
          (ih (inductionRank I none) hlt I boosted' none rfl hIcard hIcond)
      · by_cases hrootTwo : (G.neighborSet root).ncard = 2
        · -- Suppress a degree-two root.  Its other neighbour is `a`.
          obtain ⟨a, haMem, habne⟩ :=
            Set.exists_ne_of_one_lt_ncard (by omega : 1 < (G.neighborSet root).ncard) boosted
          have hra : G.Adj root a := haMem
          have har : G.Adj a root := hra.symm
          have hneigh : G.neighborSet root = {a, boosted} := by
            apply Set.Subset.antisymm
            · intro z hz
              by_contra hzpair
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hzpair
              have hthree : 3 ≤ (G.neighborSet root).ncard := by
                have hsub : ({a, boosted, z} : Set U) ⊆ G.neighborSet root := by
                  intro w hw
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
                  rcases hw with rfl | rfl | rfl
                  · exact haMem
                  · exact hrootBoost
                  · exact hz
                calc
                  3 = ({a, boosted, z} : Set U).ncard := by
                    symm
                    exact Set.ncard_eq_three.mpr
                      ⟨a, boosted, z, habne,
                        (fun h ↦ hzpair.1 h.symm), (fun h ↦ hzpair.2 h.symm), rfl⟩
                  _ ≤ (G.neighborSet root).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
              omega
            · intro z hz
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact haMem
              · exact hrootBoost
          let a' : Without root := ⟨a, hra.ne.symm⟩
          let boosted' : Without root := ⟨boosted, hrootBoost.ne.symm⟩
          let K := suppressVertexGraph G root a boosted hra.ne.symm hrootBoost.ne.symm
          have hKcard : 2 ≤ Fintype.card (Without root) := two_le_card_without root hcard3
          by_cases hab : G.Adj a boosted
          · -- The old edge is the counted-twice edge after suppression.
            have hIab : (G.induce ({root} : Set U)ᶜ).Adj a' boosted' := hab
            have hKeq : K = G.induce ({root} : Set U)ᶜ := by
              dsimp only [K, suppressVertexGraph]
              exact SimpleGraph.sup_edge_of_adj _ hIab
            have hKcond : DegreeCondition K boosted' (some a') := by
              refine ⟨?_, ?_, ?_⟩
              · rw [hKeq]
                exact hab.symm
              · rw [hKeq]
                apply two_le_neighborSet_induce_compl_singleton_of_adj G root a' har
                simpa only [a'] using hregular a hra.ne.symm habne
              · intro x hxb hxa
                have hxroot : (x : U) ≠ root := x.property
                have hxboost : (x : U) ≠ boosted := by
                  intro h
                  exact hxb (Subtype.ext h)
                have hxa' : (x : U) ≠ a := by
                  intro h
                  exact hxa (Subtype.ext h)
                have hxnot := not_adj_root_of_neighbor_pair hneigh hxa' hxboost
                rw [hKeq]
                exact three_le_neighborSet_induce_compl_singleton_of_not_adj G root x hxnot
                  (hregular (x : U) hxroot hxboost)
            exact hasK4Datum_of_suppress_vertex_of_adj har hrootBoost hab
              (ih (inductionRank K (some a')) (by
                  apply inductionRank_lt_of_card_lt
                  rw [card_without]
                  omega) K boosted' (some a') rfl hKcard hKcond)
          · -- A genuinely new edge restores `a`'s degree; `boosted` is the sole exception.
            have hInot : ¬ (G.induce ({root} : Set U)ᶜ).Adj a' boosted' := hab
            have habne' : a' ≠ boosted' := by
              intro h
              exact habne (congrArg Subtype.val h)
            have hKcond : DegreeCondition K boosted' none := by
              change DegreeCondition
                (G.induce ({root} : Set U)ᶜ ⊔ SimpleGraph.edge a' boosted') boosted' none
              intro x hxb
              have hxroot : (x : U) ≠ root := x.property
              have hxboost : (x : U) ≠ boosted := by
                intro h
                exact hxb (Subtype.ext h)
              by_cases hxa : x = a'
              · subst x
                apply three_le_neighborSet_sup_edge_left_after_induce G root
                  hInot habne' har
                simpa only [a'] using hregular a hra.ne.symm habne
              · have hxaU : (x : U) ≠ a := by
                  intro h
                  exact hxa (Subtype.ext h)
                have hxnot := not_adj_root_of_neighbor_pair hneigh hxaU hxboost
                exact three_le_neighborSet_sup_edge_other_after_induce G root hxa hxb hxnot
                  (hregular (x : U) hxroot hxboost)
            exact hasK4Datum_of_suppress_vertex har hrootBoost hab
              (ih (inductionRank K none) (by
                  apply inductionRank_lt_of_card_lt
                  rw [card_without]
                  omega) K boosted' none rfl hKcard hKcond)
        · -- With degree at least three, discard the boost and distinguish its endpoint.
          have hroot3 : 3 ≤ (G.neighborSet root).ncard := by omega
          have hnone : DegreeCondition G boosted none := by
            intro x hxb
            by_cases hxr : x = root
            · simpa [hxr] using hroot3
            · exact hregular x hxr hxb
          exact ih (inductionRank G none) (inductionRank_none_lt_some G boosted)
            G boosted none rfl hcard hnone
  | none =>
      have hregular := hcond
      have hcard4 : 4 ≤ Fintype.card U := four_le_card_of_none hcard hcond
      by_cases hrootSmall : (G.neighborSet root).ncard ≤ 1
      · -- Remove an isolated/leaf distinguished vertex.
        by_cases hhas : ∃ b : U, G.Adj root b
        · obtain ⟨b, hrb⟩ := hhas
          let b' : Without root := ⟨b, hrb.ne.symm⟩
          let I : SimpleGraph (Without root) := G.induce ({root} : Set U)ᶜ
          have hIcard : 2 ≤ Fintype.card (Without root) :=
            two_le_card_without root (by omega)
          have hIcond : DegreeCondition I b' none := by
            intro x hxb
            have hxroot : (x : U) ≠ root := x.property
            have hxbU : (x : U) ≠ b := by
              intro h
              exact hxb (Subtype.ext h)
            have hxnot : ¬ G.Adj (x : U) root := by
              intro hxr
              exact hxbU (neighbor_eq_of_ncard_le_one hrootSmall hxr.symm hrb)
            dsimp only [I]
            exact three_le_neighborSet_induce_compl_singleton_of_not_adj G root x hxnot
              (hregular (x : U) hxroot)
          exact hasK4Datum_of_induce_compl_singleton
            (ih (inductionRank I none) (by
                apply inductionRank_lt_of_card_lt
                rw [card_without]
                omega) I b' none rfl hIcard hIcond)
        · obtain ⟨b, hbr⟩ := Fintype.exists_ne_of_one_lt_card (by omega) root
          let b' : Without root := ⟨b, hbr⟩
          let I : SimpleGraph (Without root) := G.induce ({root} : Set U)ᶜ
          have hIcard : 2 ≤ Fintype.card (Without root) :=
            two_le_card_without root (by omega)
          have hIcond : DegreeCondition I b' none := by
            intro x hxb
            have hxroot : (x : U) ≠ root := x.property
            have hxnot : ¬ G.Adj (x : U) root := fun hxr ↦ hhas ⟨x, hxr.symm⟩
            dsimp only [I]
            exact three_le_neighborSet_induce_compl_singleton_of_not_adj G root x hxnot
              (hregular (x : U) hxroot)
          exact hasK4Datum_of_induce_compl_singleton
            (ih (inductionRank I none) (by
                apply inductionRank_lt_of_card_lt
                rw [card_without]
                omega) I b' none rfl hIcard hIcond)
      · by_cases hrootTwo : (G.neighborSet root).ncard = 2
        · obtain ⟨a, b, habne, hneigh⟩ := Set.ncard_eq_two.mp hrootTwo
          have hra : G.Adj root a := by rw [← G.mem_neighborSet]; rw [hneigh]; simp
          have hrb : G.Adj root b := by rw [← G.mem_neighborSet]; rw [hneigh]; simp
          let a' : Without root := ⟨a, hra.ne.symm⟩
          let b' : Without root := ⟨b, hrb.ne.symm⟩
          let K := suppressVertexGraph G root a b hra.ne.symm hrb.ne.symm
          have hKcard : 2 ≤ Fintype.card (Without root) :=
            two_le_card_without root (by omega)
          by_cases hab : G.Adj a b
          · have hIab : (G.induce ({root} : Set U)ᶜ).Adj a' b' := hab
            have hKeq : K = G.induce ({root} : Set U)ᶜ := by
              dsimp only [K, suppressVertexGraph]
              exact SimpleGraph.sup_edge_of_adj _ hIab
            have hKcond : DegreeCondition K a' (some b') := by
              refine ⟨?_, ?_, ?_⟩
              · rw [hKeq]
                exact hab
              · rw [hKeq]
                apply two_le_neighborSet_induce_compl_singleton_of_adj G root b' hrb.symm
                simpa only [b'] using hregular b hrb.ne.symm
              · intro x hxa hxb
                have hxroot : (x : U) ≠ root := x.property
                have hxaU : (x : U) ≠ a := by intro h; exact hxa (Subtype.ext h)
                have hxbU : (x : U) ≠ b := by intro h; exact hxb (Subtype.ext h)
                have hxnot := not_adj_root_of_neighbor_pair hneigh hxaU hxbU
                rw [hKeq]
                exact three_le_neighborSet_induce_compl_singleton_of_not_adj G root x hxnot
                  (hregular (x : U) hxroot)
            exact hasK4Datum_of_suppress_vertex_of_adj hra.symm hrb hab
              (ih (inductionRank K (some b')) (by
                  apply inductionRank_lt_of_card_lt
                  rw [card_without]
                  omega) K a' (some b') rfl hKcard hKcond)
          · have hInot : ¬ (G.induce ({root} : Set U)ᶜ).Adj a' b' := hab
            have habne' : a' ≠ b' := by
              intro h
              exact habne (congrArg Subtype.val h)
            have hKcond : DegreeCondition K a' none := by
              change DegreeCondition
                (G.induce ({root} : Set U)ᶜ ⊔ SimpleGraph.edge a' b') a' none
              intro x hxa
              have hxroot : (x : U) ≠ root := x.property
              by_cases hxb : x = b'
              · subst x
                apply three_le_neighborSet_sup_edge_right_after_induce G root
                  hInot habne' hrb.symm
                simpa only [b'] using hregular b hrb.ne.symm
              · have hxaU : (x : U) ≠ a := by intro h; exact hxa (Subtype.ext h)
                have hxbU : (x : U) ≠ b := by intro h; exact hxb (Subtype.ext h)
                have hxnot := not_adj_root_of_neighbor_pair hneigh hxaU hxbU
                exact three_le_neighborSet_sup_edge_other_after_induce G root hxa hxb hxnot
                  (hregular (x : U) hxroot)
            exact hasK4Datum_of_suppress_vertex hra.symm hrb hab
              (ih (inductionRank K none) (by
                  apply inductionRank_lt_of_card_lt
                  rw [card_without]
                  omega) K a' none rfl hKcard hKcond)
        · by_cases hrootThree : (G.neighborSet root).ncard = 3
          · obtain ⟨a, b, c, habne, hacne, hbcne, hneigh⟩ :=
              Set.ncard_eq_three.mp hrootThree
            have hra : G.Adj root a := by rw [← G.mem_neighborSet]; rw [hneigh]; simp
            have hrb : G.Adj root b := by rw [← G.mem_neighborSet]; rw [hneigh]; simp
            have hrc : G.Adj root c := by rw [← G.mem_neighborSet]; rw [hneigh]; simp
            have degreeThreeSuppress : ∀ (a b c : U),
                G.neighborSet root = {a, b, c} →
                G.Adj root a → G.Adj root b → G.Adj root c →
                ¬ G.Adj a b → a ≠ b → HasK4Datum G := by
              intro a b c hneigh hra hrb hrc hab habne
              let a' : Without root := ⟨a, hra.ne.symm⟩
              let b' : Without root := ⟨b, hrb.ne.symm⟩
              let c' : Without root := ⟨c, hrc.ne.symm⟩
              let K := suppressVertexGraph G root a b hra.ne.symm hrb.ne.symm
              have hKcard : 2 ≤ Fintype.card (Without root) :=
                two_le_card_without root (by omega)
              have hKcond : DegreeCondition K c' none :=
                degreeCondition_suppress_three hregular hneigh hra hrb hrc hab habne
              apply hasK4Datum_of_suppress_vertex hra.symm hrb hab
              exact ih (inductionRank K none) (by
                  apply inductionRank_lt_of_card_lt
                  rw [card_without]
                  omega) K c' none rfl hKcard hKcond
            by_cases hab : G.Adj a b
            · by_cases hac : G.Adj a c
              · by_cases hbc : G.Adj b c
                · exact hasK4Datum_of_root_triangle habne hacne hbcne
                    hra hrb hrc hab hac hbc
                · exact degreeThreeSuppress b c a (by
                    rw [hneigh]
                    ext x
                    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
                    aesop) hrb hrc hra hbc hbcne
              · exact degreeThreeSuppress a c b (by
                  rw [hneigh]
                  ext x
                  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
                  aesop) hra hrc hrb hac hacne
            · exact degreeThreeSuppress a b c hneigh hra hrb hrc hab habne
          · -- Delete one edge at a root of degree at least four.
            have hroot4 : 4 ≤ (G.neighborSet root).ncard := by omega
            obtain ⟨b, hrb⟩ : ∃ b, G.Adj root b := by
              have hpos : 0 < (G.neighborSet root).ncard := by omega
              obtain ⟨b, hb⟩ := (Set.ncard_pos (Set.toFinite _)).mp hpos
              exact ⟨b, hb⟩
            let D := deleteEdge G root b
            have hDcond : DegreeCondition D b none := by
              intro x hxb
              by_cases hxr : x = root
              · subst x
                have hind := ncard_neighborSet_deleteEdge_left G hrb
                dsimp only [D]
                omega
              · have hind := ncard_neighborSet_deleteEdge_other G hxr hxb
                have hdeg := hregular x hxr
                dsimp only [D]
                omega
            exact hasK4Datum_mono (SimpleGraph.deleteEdges_le _)
              (ih (inductionRank D none) (inductionRank_deleteEdge_lt G hrb)
                D b none rfl hcard hDcond)


/-- The strengthened induction: all vertices except `root` have degree at least three, with an
optional doubled edge allowing its other endpoint to have ordinary degree two. -/
theorem hasK4Datum_of_degreeCondition (G : SimpleGraph U) (root : U) (boost : Option U)
    (hcard : 2 ≤ Fintype.card U) (hcond : DegreeCondition G root boost) : HasK4Datum G :=
  hasK4Datum_induction (inductionRank G boost) G root boost rfl hcard hcond

end Workspace.ProofLemmas.DiracK4SubdivisionInduction
