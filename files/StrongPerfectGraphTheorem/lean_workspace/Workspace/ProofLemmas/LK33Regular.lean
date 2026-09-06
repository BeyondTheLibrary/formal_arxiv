import Mathlib
import Workspace.ProofLemmas.K4AppearanceDegreeCriterion

/-!
# The line graph of `K₃,₃` is a 4-regular graph on nine vertices

`K₃,₃ = completeBipartiteGraph (Fin 3) (Fin 3)` has vertex type `Fin 3 ⊕ Fin 3` and nine edges,
one for each pair `(a, b)`, namely `s(Sum.inl a, Sum.inr b)`.  Its line graph `L33` therefore has
nine vertices, and each of them — the edge `s(inl a, inr b)` — is adjacent exactly to the two
other edges at `inl a` and the two other edges at `inr b`, so `L33` is 4-regular.

The payoff is `no_induced_L33_of_degree_criterion`: a graph in which every nine-element vertex
set contains a vertex with a number of neighbours inside the set different from `4` has no
induced copy of `L33`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.LK33Regular

open SimpleGraph

/-- `K₃,₃`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- The line graph of `K₃,₃`. -/
abbrev L33 : SimpleGraph K33.edgeSet := K33.lineGraph

/-! ## The nine edges of `K₃,₃` -/

/-- The edge of `K₃,₃` joining the left vertex `a` to the right vertex `b`. -/
def mkE (a b : Fin 3) : K33.edgeSet := ⟨s(Sum.inl a, Sum.inr b), by simp⟩

theorem mkE_injective : Function.Injective (fun p : Fin 3 × Fin 3 => mkE p.1 p.2) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  have h' : s(Sum.inl a, Sum.inr b) = (s(Sum.inl c, Sum.inr d) : Sym2 (Fin 3 ⊕ Fin 3)) :=
    congrArg Subtype.val h
  rcases Sym2.eq_iff.mp h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
    subst h1; subst h2; rfl
  · simp at h1

/-- Every edge of `K₃,₃` is of the form `mkE a b`. -/
theorem exists_mkE (e : K33.edgeSet) : ∃ a b : Fin 3, e = mkE a b := by
  obtain ⟨z, hz⟩ := e
  have hz' : z ∈ Set.range (fun x : Fin 3 × Fin 3 => s(Sum.inl x.1, Sum.inr x.2)) := by
    rwa [SimpleGraph.edgeSet_completeBipartiteGraph] at hz
  obtain ⟨⟨a, b⟩, hab⟩ := hz'
  exact ⟨a, b, Subtype.ext hab.symm⟩

/-- **`K₃,₃` has nine edges.** -/
theorem card_L33 : Nat.card (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet = 9 := by
  have hinj : Function.Injective
      (fun x : Fin 3 × Fin 3 => s(Sum.inl x.1, Sum.inr x.2) : Fin 3 × Fin 3 →
        Sym2 (Fin 3 ⊕ Fin 3)) := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [Sum.inl.injEq, Sum.inr.injEq] at h1 h2
      subst h1; subst h2; rfl
    · simp at h1
  rw [Nat.card_coe_set_eq, SimpleGraph.edgeSet_completeBipartiteGraph,
    Set.ncard_range_of_injective hinj]
  simp

/-! ## Adjacency in `L33` -/

/-- Two edges of `K₃,₃` are adjacent in the line graph exactly when they share precisely one
endpoint: same left end and different right ends, or different left ends and the same right end. -/
theorem L33_adj_mkE (a b c d : Fin 3) :
    L33.Adj (mkE a b) (mkE c d) ↔ (a = c ∧ b ≠ d) ∨ (a ≠ c ∧ b = d) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨hne, v, hv1, hv2⟩
    have hnead : ¬ (a = c ∧ b = d) := by
      rintro ⟨rfl, rfl⟩
      exact hne rfl
    have hshare : a = c ∨ b = d := by
      have hv1' : v = Sum.inl a ∨ v = Sum.inr b := Sym2.mem_iff.mp hv1
      have hv2' : v = Sum.inl c ∨ v = Sum.inr d := Sym2.mem_iff.mp hv2
      rcases hv1' with rfl | rfl
      · rcases hv2' with h | h
        · exact Or.inl (by simpa using h)
        · exact absurd h (by simp)
      · rcases hv2' with h | h
        · exact absurd h (by simp)
        · exact Or.inr (by simpa using h)
    rcases hshare with h | h
    · exact Or.inl ⟨h, fun hbd => hnead ⟨h, hbd⟩⟩
    · exact Or.inr ⟨fun hac => hnead ⟨hac, h⟩, h⟩
  · intro h
    have hne : mkE a b ≠ mkE c d := by
      intro heq
      have := mkE_injective (a₁ := (a, b)) (a₂ := (c, d)) heq
      rw [Prod.mk.injEq] at this
      rcases h with ⟨-, hbd⟩ | ⟨hac, -⟩
      · exact hbd this.2
      · exact hac this.1
    refine ⟨hne, ?_⟩
    rcases h with ⟨rfl, -⟩ | ⟨-, rfl⟩
    · exact ⟨Sum.inl a, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
    · exact ⟨Sum.inr b, Sym2.mem_mk_right _ _, Sym2.mem_mk_right _ _⟩

/-- The index set of the `L33`-neighbours of `mkE a b`. -/
def nbrIdx (a b : Fin 3) : Finset (Fin 3 × Fin 3) :=
  {p ∈ Finset.univ | (p.1 = a ∧ p.2 ≠ b) ∨ (p.1 ≠ a ∧ p.2 = b)}

theorem card_nbrIdx (a b : Fin 3) : (nbrIdx a b).card = 4 := by
  revert a b
  decide

theorem neighborSet_mkE (a b : Fin 3) :
    L33.neighborSet (mkE a b) = (fun p : Fin 3 × Fin 3 => mkE p.1 p.2) '' (nbrIdx a b) := by
  ext f
  constructor
  · intro hf
    obtain ⟨c, d, rfl⟩ := exists_mkE f
    have hadj : L33.Adj (mkE a b) (mkE c d) := hf
    refine ⟨(c, d), ?_, rfl⟩
    simp only [nbrIdx, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    rcases (L33_adj_mkE a b c d).mp hadj with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, fun h => h2 h.symm⟩
    · exact Or.inr ⟨fun h => h1 h.symm, h2.symm⟩
  · rintro ⟨⟨c, d⟩, hp, rfl⟩
    simp only [nbrIdx, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hp
    show L33.Adj (mkE a b) (mkE c d)
    refine (L33_adj_mkE a b c d).mpr ?_
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1.symm, fun h => h2 h.symm⟩
    · exact Or.inr ⟨fun h => h1 h.symm, h2.symm⟩

/-- **The line graph of `K₃,₃` is 4-regular.** -/
theorem L33_degree (e : (completeBipartiteGraph (Fin 3) (Fin 3)).edgeSet) :
    (L33.neighborSet e).ncard = 4 := by
  obtain ⟨a, b, rfl⟩ := exists_mkE e
  rw [neighborSet_mkE a b, Set.ncard_image_of_injective _ mkE_injective,
    Set.ncard_coe_finset, card_nbrIdx]

/-! ## The payoff -/

/-- **A degree criterion excluding an induced copy of `L(K₃,₃)`.**

If every nine-element vertex subset `K` of `Gx` contains a vertex whose number of neighbours
inside `K` differs from `4`, then `Gx` has no induced subgraph isomorphic to `L(K₃,₃)`. -/
theorem no_induced_L33_of_degree_criterion {V : Type*} [Fintype V] [DecidableEq V]
    (Gx : SimpleGraph V)
    (hcrit : ∀ K : Set V, K.ncard = 9 →
      ∃ v ∈ K, (Gx.neighborSet v ∩ K).ncard ≠ 4) :
    ¬ ∃ K : Set V, Nonempty (L33 ≃g Gx.induce K) := by
  rintro ⟨K, ⟨φ⟩⟩
  have hK : K.ncard = 9 := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_congr φ.toEquiv]
    exact card_L33
  obtain ⟨v, hvK, hbad⟩ := hcrit K hK
  set e : K33.edgeSet := φ.symm ⟨v, hvK⟩ with he
  have hφe : φ e = ⟨v, hvK⟩ := by rw [he]; simp
  have htrans : ((Gx.induce K).neighborSet ⟨v, hvK⟩).ncard = (L33.neighborSet e).ncard := by
    rw [← hφe, Workspace.ProofLemmas.SubdivisionCounting.neighborSet_image_of_iso φ e,
      Set.ncard_image_of_injective _ (EquivLike.injective φ)]
  rw [K4AppearanceDegreeCriterion.induce_neighborSet_ncard Gx hvK, L33_degree e] at htrans
  exact hbad htrans

end Workspace.ProofLemmas.LK33Regular
