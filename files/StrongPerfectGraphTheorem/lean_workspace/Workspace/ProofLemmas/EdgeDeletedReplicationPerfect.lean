import Mathlib
import Workspace.Types.Core
import Workspace.Types.Replication
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.IsoTransport
import Workspace.Statements.S01.Thm_E7_lovasz_replication

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Replication.SPGT

/-- Any edge gives a clique of size two. -/
private lemma edrp_two_le_cliqueNum {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) {a b : α} (hab : G.Adj a b) : 2 ≤ G.cliqueNum := by
  classical
  have hclique : G.IsClique (↑({a, b} : Finset α) : Set α) := by
    rw [Finset.coe_insert, Finset.coe_singleton]
    intro x hx y hy hxy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact absurd rfl hxy
    · exact hab
    · exact hab.symm
    · exact absurd rfl hxy
  have h := SimpleGraph.IsClique.card_le_cliqueNum (tc := hclique)
  rwa [Finset.card_pair hab.ne] at h

/-- A graph with clique number at most one is edgeless, hence 1-colourable. -/
private lemma edrp_colorable_one {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (h : G.cliqueNum ≤ 1) : G.Colorable 1 := by
  refine ⟨SimpleGraph.Coloring.mk (fun _ => (0 : Fin 1)) ?_⟩
  intro a b hab
  exact absurd (edrp_two_le_cliqueNum G hab) (by omega)

/-- **§7.**  `K` perfect, `u v` adjacent with no common neighbour: replicating `v`
into a true twin `v' = Sum.inr ()` and then deleting *only* the edge `u v'` leaves a
perfect graph. -/
theorem EdgeDeletedReplicationPerfect
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (u v : W)
    (huv : K.Adj u v)
    (hnocommon : ∀ x : W, K.Adj x u → ¬ K.Adj x v)
    (hK : IsPerfect K) :
    IsPerfect ((replicateVertex K v).deleteEdges {s(Sum.inl u, Sum.inr ())}) := by
  classical
  obtain ⟨R, hRdef⟩ : ∃ R : SimpleGraph (W ⊕ Unit), R = replicateVertex K v := ⟨_, rfl⟩
  rw [← hRdef]
  obtain ⟨L, hLdef⟩ : ∃ L : SimpleGraph (W ⊕ Unit),
      L = R.deleteEdges {s((Sum.inl u : W ⊕ Unit), Sum.inr ())} := ⟨_, rfl⟩
  rw [← hLdef]
  -- basic dictionary for `R` and `L`
  have hRperf : IsPerfect R := by
    rw [hRdef]; exact Workspace.MainTheorem.SPGT.thm_E7_lovasz_replication K v hK
  have hLadj : ∀ a b : W ⊕ Unit,
      L.Adj a b ↔ (R.Adj a b ∧ s(a, b) ≠ s((Sum.inl u : W ⊕ Unit), Sum.inr ())) := by
    intro a b
    rw [hLdef]
    simp [SimpleGraph.deleteEdges_adj]
  have hLle : L ≤ R := by
    intro a b h
    exact ((hLadj a b).mp h).1
  have hRll : ∀ a b : W, R.Adj (Sum.inl a) (Sum.inl b) ↔ K.Adj a b := by
    intro a b; rw [hRdef]; exact Iff.rfl
  have hRlr : ∀ a : W, R.Adj (Sum.inl a) (Sum.inr ()) ↔ (a = v ∨ K.Adj a v) := by
    intro a; rw [hRdef]; exact Iff.rfl
  -- if one endpoint of the deleted edge is missing, `L` and `R` agree on `X`
  have hmiss : ∀ X : Set (W ⊕ Unit),
      ((Sum.inl u : W ⊕ Unit) ∉ X ∨ (Sum.inr () : W ⊕ Unit) ∉ X) →
      L.induce X = R.induce X := by
    intro X hX
    ext a b
    constructor
    · intro h; exact hLle h
    · intro h
      have hne : s((a : W ⊕ Unit), (b : W ⊕ Unit))
          ≠ s((Sum.inl u : W ⊕ Unit), Sum.inr ()) := by
        intro heq
        rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rcases hX with hx | hx
          · exact hx (h1 ▸ a.2)
          · exact hx (h2 ▸ b.2)
        · rcases hX with hx | hx
          · exact hx (h2 ▸ b.2)
          · exact hx (h1 ▸ a.2)
      exact (hLadj _ _).mpr ⟨h, hne⟩
  intro X
  by_cases hu : (Sum.inl u : W ⊕ Unit) ∈ X
  · by_cases hw : (Sum.inr () : W ⊕ Unit) ∈ X
    · -- the main case
      haveI : Fintype ↥X := Fintype.ofFinite _
      set u'' : ↥X := ⟨Sum.inl u, hu⟩ with hu''
      set w'' : ↥X := ⟨Sum.inr (), hw⟩ with hw''
      have hle : L.induce X ≤ R.induce X := by
        intro a b h; exact hLle h
      by_contra hne
      -- (C) part 1: ω(L*) < χ(L*)
      have hlt : ((L.induce X).cliqueNum : ℕ∞) < (L.induce X).chromaticNumber :=
        lt_of_le_of_ne SimpleGraph.cliqueNum_le_chromaticNumber (fun h => hne h.symm)
      -- (C) part 2: χ(L*) ≤ χ(K*) = ω(K*)
      have hRXcol : (R.induce X).Colorable (R.induce X).cliqueNum :=
        SimpleGraph.chromaticNumber_le_iff_colorable.mp (le_of_eq (hRperf X))
      have hLXcol : (L.induce X).Colorable (R.induce X).cliqueNum := by
        obtain ⟨cR⟩ := hRXcol
        exact ⟨SimpleGraph.Coloring.mk cR (fun {a b} hab => cR.valid (hle hab))⟩
      have hchile : (L.induce X).chromaticNumber ≤ (((R.induce X).cliqueNum : ℕ) : ℕ∞) :=
        SimpleGraph.chromaticNumber_le_iff_colorable.mpr hLXcol
      have hwlt : (L.induce X).cliqueNum < (R.induce X).cliqueNum := by
        have h := lt_of_lt_of_le hlt hchile
        exact_mod_cast h
      -- a maximum clique of `K*`
      obtain ⟨C, hCclique, hCcard⟩ :=
        SimpleGraph.exists_isNClique_cliqueNum (G := R.induce X)
      have hCnotL : ¬ (L.induce X).IsClique (↑C : Set ↥X) := by
        intro h
        have h2 := SimpleGraph.IsClique.card_le_cliqueNum (tc := h)
        omega
      have hex : ∃ a ∈ C, ∃ b ∈ C, a ≠ b ∧ ¬ (L.induce X).Adj a b := by
        by_contra hcon
        push_neg at hcon
        exact hCnotL fun a ha b hb hab =>
          hcon a (by simpa using ha) b (by simpa using hb) hab
      obtain ⟨a, haC, b, hbC, hab, hnadj⟩ := hex
      have hRab : (R.induce X).Adj a b :=
        hCclique (by simpa using haC) (by simpa using hbC) hab
      have hseq : s((a : W ⊕ Unit), (b : W ⊕ Unit))
          = s((Sum.inl u : W ⊕ Unit), Sum.inr ()) := by
        by_contra hcon
        exact hnadj ((hLadj _ _).mpr ⟨hRab, hcon⟩)
      have huC : u'' ∈ C ∧ w'' ∈ C := by
        rcases Sym2.eq_iff.mp hseq with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨(Subtype.ext h1 : a = u'') ▸ haC, (Subtype.ext h2 : b = w'') ▸ hbC⟩
        · exact ⟨(Subtype.ext h2 : b = u'') ▸ hbC, (Subtype.ext h1 : a = w'') ▸ haC⟩
      -- every vertex of the new clique lies in `{u, v, v'}`
      have hCsub : ∀ z ∈ C, (z : W ⊕ Unit) = Sum.inl u ∨ (z : W ⊕ Unit) = Sum.inl v ∨
          (z : W ⊕ Unit) = Sum.inr () := by
        intro z hz
        by_cases hzu : z = u''
        · exact Or.inl (by rw [hzu])
        by_cases hzw : z = w''
        · exact Or.inr (Or.inr (by rw [hzw]))
        have h1 : (R.induce X).Adj z u'' :=
          hCclique (by simpa using hz) (by simpa using huC.1) hzu
        have h2 : (R.induce X).Adj z w'' :=
          hCclique (by simpa using hz) (by simpa using huC.2) hzw
        have h1' : R.Adj (z : W ⊕ Unit) (Sum.inl u) := h1
        have h2' : R.Adj (z : W ⊕ Unit) (Sum.inr ()) := h2
        rcases hzc : (z : W ⊕ Unit) with y | t
        · rw [hzc] at h1' h2'
          have hyu : K.Adj y u := (hRll y u).mp h1'
          rcases (hRlr y).mp h2' with rfl | hyv
          · exact Or.inr (Or.inl (by first | rfl | exact hzc | simp [hzc]))
          · exact absurd hyv (hnocommon y hyu)
        · exfalso
          cases t
          rw [hzc] at h2'
          exact R.irrefl h2'
      -- so the new clique has at most three vertices
      have hCcard3 : C.card ≤ 3 := by
        have himg : C.image (Subtype.val) ⊆
            ({Sum.inl u, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)) := by
          intro x hx
          simp only [Finset.mem_image] at hx
          obtain ⟨z, hz, rfl⟩ := hx
          rcases hCsub z hz with h | h | h <;> simp [h]
        have h1 : (C.image (Subtype.val)).card = C.card :=
          Finset.card_image_of_injective _ Subtype.val_injective
        have h2 := Finset.card_le_card himg
        have h3 : ({Sum.inl u, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)).card ≤ 3 := by
          calc ({Sum.inl u, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)).card
              ≤ ({Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)).card + 1 :=
                Finset.card_insert_le _ _
            _ ≤ (({Sum.inr ()} : Finset (W ⊕ Unit)).card + 1) + 1 :=
                Nat.add_le_add_right (Finset.card_insert_le _ _) 1
            _ = 3 := by simp
        omega
      -- `w = ω(L*) = 2`
      have hw1 : 1 ≤ (L.induce X).cliqueNum := by
        have h := CliqueNumOfInducedSet.card_le_cliqueNum_induce L
          (X := X) (K := {(Sum.inl u : W ⊕ Unit)})
          (by simpa using hu)
          (by rw [Finset.coe_singleton]; exact Set.pairwise_singleton _ _)
        simpa using h
      have hwne1 : (L.induce X).cliqueNum ≠ 1 := by
        intro h1
        have hcol := edrp_colorable_one (L.induce X) (le_of_eq h1)
        have hle1 : (L.induce X).chromaticNumber ≤ ((1 : ℕ) : ℕ∞) :=
          SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol
        rw [h1] at hlt
        exact absurd (lt_of_lt_of_le hlt hle1) (by simp)
      have hw2 : (L.induce X).cliqueNum = 2 := by omega
      -- the third vertex of the new clique is `v`
      have hthird : ∃ z ∈ C, z ≠ u'' ∧ z ≠ w'' := by
        by_contra hcon
        push_neg at hcon
        have hsub : C ⊆ ({u'', w''} : Finset ↥X) := by
          intro z hz
          rcases eq_or_ne z u'' with h | h
          · simp [h]
          · simp [hcon z hz h]
        have h1 := Finset.card_le_card hsub
        have h2 : ({u'', w''} : Finset ↥X).card ≤ 2 := by
          calc ({u'', w''} : Finset ↥X).card ≤ ({w''} : Finset ↥X).card + 1 :=
                Finset.card_insert_le _ _
            _ = 2 := by simp
        omega
      obtain ⟨z, hzC, hzu, hzw⟩ := hthird
      have hvX : (Sum.inl v : W ⊕ Unit) ∈ X := by
        rcases hCsub z hzC with h | h | h
        · exact absurd (Subtype.ext h : z = u'') hzu
        · exact h ▸ z.2
        · exact absurd (Subtype.ext h : z = w'') hzw
      -- in `L*` the only neighbour of `v'` is `v`
      have honly : ∀ y : W, (Sum.inl y : W ⊕ Unit) ∈ X →
          L.Adj (Sum.inl y) (Sum.inr ()) → y = v := by
        intro y hyX hadj
        by_contra hyv
        have hyu : y ≠ u := by
          intro h
          subst h
          exact ((hLadj _ _).mp hadj).2 rfl
        have hKyv : K.Adj y v := by
          rcases (hRlr y).mp ((hLadj _ _).mp hadj).1 with h | h
          · exact absurd h hyv
          · exact h
        have e1 : L.Adj (Sum.inl y) (Sum.inl v) :=
          (hLadj _ _).mpr ⟨(hRll y v).mpr hKyv, by simp⟩
        have e3 : L.Adj (Sum.inl v) (Sum.inr ()) :=
          (hLadj _ _).mpr ⟨(hRlr v).mpr (Or.inl rfl), by simp [huv.ne']⟩
        have hclq : L.IsClique
            (↑({Sum.inl y, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)) : Set (W ⊕ Unit)) := by
          rw [Finset.coe_insert, Finset.coe_insert, Finset.coe_singleton]
          intro p hp q hq hpq
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp hq
          rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;>
            first
              | exact absurd rfl hpq
              | exact e1 | exact e1.symm | exact hadj | exact hadj.symm
              | exact e3 | exact e3.symm
        have hsubX : (↑({Sum.inl y, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)) : Set (W ⊕ Unit))
            ⊆ X := by
          intro p hp
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hp
          rcases hp with rfl | rfl | rfl
          · exact hyX
          · exact hvX
          · exact hw
        have hcard : ({Sum.inl y, Sum.inl v, Sum.inr ()} : Finset (W ⊕ Unit)).card = 3 := by
          rw [Finset.card_insert_of_notMem (by simp [hyv]),
            Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
        have h := CliqueNumOfInducedSet.card_le_cliqueNum_induce L hsubX hclq
        rw [hcard, hw2] at h
        omega
      -- two-colour `L*`
      have hX'eq : L.induce (X \ {(Sum.inr () : W ⊕ Unit)})
          = R.induce (X \ {(Sum.inr () : W ⊕ Unit)}) := hmiss _ (Or.inr (by simp))
      have hX'perf : (L.induce (X \ {(Sum.inr () : W ⊕ Unit)})).chromaticNumber
          = (((L.induce (X \ {(Sum.inr () : W ⊕ Unit)})).cliqueNum : ℕ) : ℕ∞) := by
        rw [hX'eq]; exact hRperf _
      have hX'w : (L.induce (X \ {(Sum.inr () : W ⊕ Unit)})).cliqueNum ≤ 2 := by
        have h := CliqueNumOfInducedSet.cliqueNum_induce_mono L
          (X := X \ {(Sum.inr () : W ⊕ Unit)}) (Y := X) Set.diff_subset
        omega
      have hX'col : (L.induce (X \ {(Sum.inr () : W ⊕ Unit)})).Colorable 2 := by
        apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
        rw [hX'perf]
        exact_mod_cast hX'w
      obtain ⟨c'⟩ := hX'col
      have hvX' : (Sum.inl v : W ⊕ Unit) ∈ X \ {(Sum.inr () : W ⊕ Unit)} := ⟨hvX, by simp⟩
      have hfin : ∀ x : Fin 2, x + 1 ≠ x := by decide
      set vv : ↥(X \ {(Sum.inr () : W ⊕ Unit)}) := ⟨Sum.inl v, hvX'⟩ with hvv
      have hcolor : (L.induce X).Colorable 2 := by
        refine ⟨SimpleGraph.Coloring.mk
          (fun a => if h : (a : W ⊕ Unit) = Sum.inr () then c' vv + 1
            else c' ⟨(a : W ⊕ Unit), ⟨a.2, h⟩⟩) ?_⟩
        intro p q hpq
        have hpq' : L.Adj (p : W ⊕ Unit) (q : W ⊕ Unit) := hpq
        by_cases hp : (p : W ⊕ Unit) = Sum.inr ()
        · by_cases hq : (q : W ⊕ Unit) = Sum.inr ()
          · exact absurd (hp.trans hq.symm ▸ hpq' : L.Adj (q : W ⊕ Unit) (q : W ⊕ Unit))
              (L.irrefl)
          · -- `q` is the unique neighbour `v`
            have hqadj : L.Adj (q : W ⊕ Unit) (Sum.inr ()) := by
              rw [← hp]; exact hpq'.symm
            have hqv : (q : W ⊕ Unit) = Sum.inl v := by
              rcases hqc : (q : W ⊕ Unit) with y | t
              · rw [hqc] at hqadj
                have hyX : (Sum.inl y : W ⊕ Unit) ∈ X := by rw [← hqc]; exact q.2
                rw [honly y hyX hqadj]
              · cases t; exact absurd hqc hq
            simp only [dif_pos hp, dif_neg hq]
            have : (⟨(q : W ⊕ Unit), ⟨q.2, hq⟩⟩ :
                ↥(X \ {(Sum.inr () : W ⊕ Unit)})) = vv := Subtype.ext hqv
            rw [this]
            exact hfin _
        · by_cases hq : (q : W ⊕ Unit) = Sum.inr ()
          · have hpadj : L.Adj (p : W ⊕ Unit) (Sum.inr ()) := by
              rw [← hq]; exact hpq'
            have hpv : (p : W ⊕ Unit) = Sum.inl v := by
              rcases hpc : (p : W ⊕ Unit) with y | t
              · rw [hpc] at hpadj
                have hyX : (Sum.inl y : W ⊕ Unit) ∈ X := by rw [← hpc]; exact p.2
                rw [honly y hyX hpadj]
              · cases t; exact absurd hpc hp
            simp only [dif_pos hq, dif_neg hp]
            have : (⟨(p : W ⊕ Unit), ⟨p.2, hp⟩⟩ :
                ↥(X \ {(Sum.inr () : W ⊕ Unit)})) = vv := Subtype.ext hpv
            rw [this]
            exact fun h => hfin _ h.symm
          · simp only [dif_neg hp, dif_neg hq]
            exact c'.valid (by exact hpq')
      have hchi2 : (L.induce X).chromaticNumber ≤ ((2 : ℕ) : ℕ∞) :=
        SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcolor
      rw [hw2] at hlt
      exact absurd (lt_of_lt_of_le hlt hchi2) (by simp)
    · rw [hmiss X (Or.inr hw)]; exact hRperf X
  · rw [hmiss X (Or.inl hu)]; exact hRperf X

end Workspace.ProofLemmas
