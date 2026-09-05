import Mathlib
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.HoleBasics

/-!
# `L(K₃,₃)` is self-complementary

Infrastructure with no counterpart in the printed paper.

Several statements of the development — **1.8.2**, **5.2**, **9.6** and the class `F₂` of
`Workspace.Types.Classes` — carry a hypothesis of the shape

> *"no induced subgraph of `G` is isomorphic to `L(K₃,₃)`"*

imposed on `G` **only**.  A proof that needs to run the same argument in `Ḡ` (this came up while
proving `Workspace.ProofLemmas.NoK4EnlargementAppearance`, whose `Gᶜ` instantiation of 9.6 wants
the hypothesis for `Ḡ`) therefore has to know that the hypothesis for `G` already implies the one
for `Ḡ`.  It does, because `L(K₃,₃)` is **self-complementary**: `Ḡ|K ≅ L(K₃,₃)` iff
`G|K = (Ḡ|K)ᶜ ≅ L(K₃,₃)ᶜ ≅ L(K₃,₃)`.

## What is proved

* `rookIsoLine : rook33 ≃g K33.lineGraph` — the working model.  `L(K₃,₃)` is the `3 × 3`
  **rook's graph**: its nine vertices are the nine edges `xᵢyⱼ` of `K₃,₃`, i.e. the cells
  `(i, j)` of a `3 × 3` board, and two distinct edges share an end exactly when the two cells
  share a row or a column.
* `rookSelfCompl : rook33 ≃g rook33ᶜ` — the rook's graph is self-complementary.  Its complement
  is *"differ in both coordinates"*, and the invertible `𝔽₃`-linear `shear (i, j) = (i+j, i+2j)`
  carries one adjacency to the other: it sends the four rook directions `(±1,0), (0,±1)` to
  `(1,1), (2,2), (1,2), (2,1)`, which are exactly the four non-rook directions.  (The bare shear
  `(i,j) ↦ (i, i+j)` does **not** work — it fixes the direction `(0,1)`.)
* `l33SelfCompl` / `lineGraph_K33_self_compl` — the result, in `def` and `Nonempty` form.
* `no_L33_induced_compl` and friends — the corollary the callers want, in all four orientations.

`rook33` is the unique `SRG(9,4,1,2)`, i.e. the Paley graph of order `9`; `K₃,₃` and `L(K₃,₃)`
both have `9` edges resp. `18` edges, and `18 = 36 - 18`, as self-complementarity requires.

## Technique

Everything concrete is discharged by `decide`, following
`Workspace.ProofLemmas.NinePrismLineGraph` and `Workspace.ProofLemmas.LK33eAppearance`.  The one
extra ingredient here is a `DecidableRel` instance for Mathlib's `completeBipartiteGraph`, which
Mathlib does not provide; `inferInstanceAs` supplies it without inserting a propositional cast, so
kernel reduction inside `decide` still goes through.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.L33SelfComplementary

/-! ### `K₃,₃` and its nine edges -/

/-- `K₃,₃`, i.e. Mathlib's `completeBipartiteGraph (Fin 3) (Fin 3)`, on `Fin 3 ⊕ Fin 3`. -/
abbrev K33 : SimpleGraph (Fin 3 ⊕ Fin 3) := completeBipartiteGraph (Fin 3) (Fin 3)

/-- Mathlib does not register this; `decide` needs it (and, through
`SimpleGraph.fintypeEdgeSet`, so does `Fintype ↥K33.edgeSet`).

Written with `inferInstanceAs` rather than `by simp; infer_instance` on purpose: the latter
produces an `Eq.mpr` cast, which the kernel cannot reduce, and every `decide` below would get
stuck on it. -/
instance instDecidableK33Adj : DecidableRel K33.Adj := fun v w =>
  inferInstanceAs (Decidable ((v.isLeft ∧ w.isRight) ∨ (v.isRight ∧ w.isLeft)))

/-- The edge `xᵢyⱼ` of `K₃,₃`, as an element of `Sym2 (Fin 3 ⊕ Fin 3)`. -/
def psi (p : Fin 3 × Fin 3) : Sym2 (Fin 3 ⊕ Fin 3) := s(Sum.inl p.1, Sum.inr p.2)

theorem psi_mem (p : Fin 3 × Fin 3) : psi p ∈ K33.edgeSet := by revert p; decide

/-- The nine vertices of `L(K₃,₃)`, indexed by the cells of a `3 × 3` board. -/
def psiE (p : Fin 3 × Fin 3) : K33.edgeSet := ⟨psi p, psi_mem p⟩

theorem psiE_inj : Function.Injective psiE := by decide

theorem psiE_bij : Function.Bijective psiE :=
  (Fintype.bijective_iff_injective_and_card psiE).mpr ⟨psiE_inj, by decide⟩

/-! ### The `3 × 3` rook's graph -/

/-- Two distinct cells of a `3 × 3` board are a rook's move apart iff they share a row or a
column — equivalently, iff they agree in exactly one coordinate. -/
def rookAdj (p q : Fin 3 × Fin 3) : Prop := p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2)

instance instDecidableRookAdj : DecidableRel rookAdj :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ _))

/-- **The `3 × 3` rook's graph**, the unique `SRG(9,4,1,2)`. -/
def rook33 : SimpleGraph (Fin 3 × Fin 3) where
  Adj := rookAdj
  symm := by
    intro p q h
    exact ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr e.symm)⟩
  loopless := ⟨by decide⟩

instance instDecidableRook33Adj : DecidableRel rook33.Adj := inferInstanceAs (DecidableRel rookAdj)

theorem rook33_adj_iff (p q : Fin 3 × Fin 3) :
    rook33.Adj p q ↔ p ≠ q ∧ (p.1 = q.1 ∨ p.2 = q.2) := Iff.rfl

/-- The complement of the rook's graph is *"differ in both coordinates"*. -/
theorem rook33_compl_adj_iff (p q : Fin 3 × Fin 3) :
    rook33ᶜ.Adj p q ↔ (p.1 ≠ q.1 ∧ p.2 ≠ q.2) := by
  rw [SimpleGraph.compl_adj]
  revert p q
  decide

/-- **The `3 × 3` rook's graph is the line graph of `K₃,₃`.** -/
noncomputable def rookIsoLine : rook33 ≃g K33.lineGraph where
  toEquiv := Equiv.ofBijective psiE psiE_bij
  map_rel_iff' := by
    intro p q
    show K33.lineGraph.Adj (psiE p) (psiE q) ↔ _
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    revert p q
    decide

/-! ### Self-complementarity -/

/-- The invertible `𝔽₃`-linear map `(i, j) ↦ (i + j, i + 2j)` (determinant `2 - 1 = 1`).

It sends the four *rook* directions `(1,0), (2,0), (0,1), (0,2)` to `(1,1), (2,2), (1,2), (2,1)`,
which are exactly the four *non-rook* directions, so it carries `rook33` onto `rook33ᶜ`. -/
def shear (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (p.1 + p.2, p.1 + 2 * p.2)

theorem shear_bij : Function.Bijective shear := by decide

/-- **The `3 × 3` rook's graph is self-complementary.** -/
noncomputable def rookSelfCompl : rook33 ≃g rook33ᶜ where
  toEquiv := Equiv.ofBijective shear shear_bij
  map_rel_iff' := by
    intro p q
    show rook33ᶜ.Adj (shear p) (shear q) ↔ _
    simp only [SimpleGraph.compl_adj]
    revert p q
    decide

/-- **`L(K₃,₃)` is self-complementary.** -/
noncomputable def l33SelfCompl :
    (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g
      ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)ᶜ :=
  rookIsoLine.symm.trans (rookSelfCompl.trans (IsoTransport.Iso.compl rookIsoLine))

/-- **`L(K₃,₃)` is self-complementary**, in `Nonempty` form — this is the shape in which the
development states *"is isomorphic to"*. -/
theorem lineGraph_K33_self_compl :
    Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g
              ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)ᶜ) :=
  ⟨l33SelfCompl⟩

/-! ### Moving the complement across an appearance of `L(K₃,₃)`

`HoleBasics.induce_compl` says `(G|K)ᶜ = Ḡ|K`; combined with self-complementarity it turns an
appearance of `L(K₃,₃)` in `Ḡ` into one in `G` on the *same* vertex set `K`, and back. -/

variable {V : Type*} {G : SimpleGraph V}

/-- `(Ḡ|K)ᶜ = G|K`. -/
theorem induce_compl_compl (K : Set V) : (Gᶜ.induce K)ᶜ = G.induce K := by
  rw [← HoleBasics.induce_compl K, compl_compl]

/-- **The engine.**  An induced copy of `L(K₃,₃)` in `Ḡ` on the vertex set `K` gives one in `G`
on the *same* vertex set `K`. -/
noncomputable def isoInduceOfIsoInduceCompl {K : Set V}
    (e : (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g Gᶜ.induce K) :
    (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K := by
  have e2 := IsoTransport.Iso.compl e
  rw [induce_compl_compl] at e2
  exact l33SelfCompl.trans e2

/-- **The form 9.6 wants** (`hnoL33` there is literally the hypothesis below).  *"No induced
subgraph of `G` is isomorphic to `L(K₃,₃)`"* implies the same for `Ḡ`. -/
theorem no_L33_induced_compl
    (h : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) :
    ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g Gᶜ.induce K) := by
  rintro ⟨K, ⟨e⟩⟩
  exact h ⟨K, ⟨isoInduceOfIsoInduceCompl e⟩⟩

/-- The converse of `no_L33_induced_compl`. -/
theorem no_L33_induced_of_compl
    (h : ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g Gᶜ.induce K)) :
    ¬ ∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K) := by
  have h2 := no_L33_induced_compl (G := Gᶜ) h
  rwa [compl_compl] at h2

/-- The two hypotheses of `no_L33_induced_compl` are in fact equivalent. -/
theorem exists_L33_induced_compl_iff :
    (∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g Gᶜ.induce K)) ↔
    (∃ K : Set V,
      Nonempty ((completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph ≃g G.induce K)) := by
  constructor
  · intro hh
    by_contra hc
    exact no_L33_induced_compl hc hh
  · intro hh
    by_contra hc
    exact no_L33_induced_of_compl hc hh

/-! #### The same four statements with the isomorphism written the other way round

`Workspace.Types.Classes.InF2` phrases the clause as `Nonempty (G|K ≃g L(K₃,₃))`, so the
primed versions below are the ones that plug into it. -/

/-- `no_L33_induced_compl` in the `G|K ≃g L(K₃,₃)` orientation (the one `InF2` uses). -/
theorem no_L33_induced_compl'
    (h : ¬ ∃ K : Set V,
      Nonempty (G.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)) :
    ¬ ∃ K : Set V,
      Nonempty (Gᶜ.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph) := by
  rintro ⟨K, ⟨e⟩⟩
  refine no_L33_induced_compl (G := G) ?_ ⟨K, ⟨e.symm⟩⟩
  rintro ⟨K', ⟨e'⟩⟩
  exact h ⟨K', ⟨e'.symm⟩⟩

/-- The converse of `no_L33_induced_compl'`. -/
theorem no_L33_induced_of_compl'
    (h : ¬ ∃ K : Set V,
      Nonempty (Gᶜ.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)) :
    ¬ ∃ K : Set V,
      Nonempty (G.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph) := by
  have h2 := no_L33_induced_compl' (G := Gᶜ) h
  rwa [compl_compl] at h2

/-- `exists_L33_induced_compl_iff` in the `G|K ≃g L(K₃,₃)` orientation. -/
theorem exists_L33_induced_compl_iff' :
    (∃ K : Set V,
      Nonempty (Gᶜ.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)) ↔
    (∃ K : Set V,
      Nonempty (G.induce K ≃g (completeBipartiteGraph (Fin 3) (Fin 3)).lineGraph)) := by
  constructor
  · intro hh
    by_contra hc
    exact no_L33_induced_compl' hc hh
  · intro hh
    by_contra hc
    exact no_L33_induced_of_compl' hc hh

end Workspace.ProofLemmas.L33SelfComplementary
