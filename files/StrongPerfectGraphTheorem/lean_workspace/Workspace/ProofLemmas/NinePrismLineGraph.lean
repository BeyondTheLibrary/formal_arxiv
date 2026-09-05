import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.BasicClasses
import Workspace.ProofLemmas.PathBasics

/-!
# The nine-vertex even prism is the line graph of a bipartite graph

This module isolates the one auxiliary fact needed to discharge the escape clause of
**10.6** (printed p. 62):

> *"Let `G` be a Berge graph, such that there is no nondegenerate appearance of `K₄` in
> `G`.  If `G` contains an even prism, then either `G` **is an even prism with
> `|V(G)| = 9`**, or `G` admits a proper 2-join or a balanced skew partition."*

and likewise of **1.8.4** (printed p. 6, same escape clause).

When the paper writes, immediately after the definition of *recalcitrant* (printed p. 86),

> *"Certainly every recalcitrant graph belongs to `F₅`, by 10.6 and 9.7."*

the escape clause is disposed of silently: a graph that *is* an even prism on nine
vertices has all three of its paths of length `2`, hence is `L(H)` for `H` the theta
graph consisting of two vertices joined by three internally disjoint paths of length
`3` — and that `H` is bipartite.  So such a `G` is a line graph of a bipartite graph
and therefore is *not* recalcitrant (the second bullet of *recalcitrant* is
*"`G` and `Ḡ` are not line graphs"*, read as in `Workspace.Types.LongOddPrism` as
*line graphs of bipartite graphs*).

The hypothesis below is **byte-for-byte the first disjunct of `thm_10_6`'s conclusion**,
so the lemma plugs straight into that `rcases`.

## How the proof runs

* The three paths `R₁, R₂, R₃` of the prism are pairwise disjoint: a common vertex `u`
  of `Rᵢ` and `Rⱼ` has a neighbour on each of the two paths, and the prism's
  cross-condition *"the only edges between `V(Rᵢ)` and `V(Rⱼ)` are `aᵢaⱼ` and `bᵢbⱼ`"*
  then forces `u ∈ {aᵢ, bᵢ} ∩ {aⱼ, bⱼ}`, which is empty.
* Each `Rᵢ` has at least two vertices (its ends `aᵢ ≠ bᵢ` differ) and even length, so an
  odd number of vertices, hence at least three.  The three paths cover the nine vertices
  of `G` and are disjoint, so each has exactly three vertices, i.e. length `2`.
* So `G` is the prism on the nine vertices `(Rᵢ)ₖ` (`i, k ∈ {0,1,2}`), and its adjacency
  is exactly `prismAdj` below: within a path, consecutive positions; between two paths,
  only position `0` to position `0` and position `2` to position `2`.
* `prismAdj` is the line graph of the theta graph `theta` on `Fin 8`, checked by
  `decide`, and `theta` is bipartite.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.NinePrismLineGraph

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.BasicClasses.SPGT

/-! ### The theta graph `H` and its line graph

`H` is the graph consisting of two vertices `x, y` joined by three internally disjoint paths
of length `3`.  It is drawn on `Fin 8` as

```
0 = x,  1 = y,  2,3,4 = u₀,u₁,u₂,  5,6,7 = v₀,v₁,v₂
```

with edges `x uᵢ`, `uᵢ vᵢ`, `vᵢ y` for `i = 0,1,2`.  All its cycles have length `6`, so it is
bipartite (`x, v₀, v₁, v₂` against `y, u₀, u₁, u₂`), and `L(H)` is the nine-vertex even prism:
the nine edges `xuᵢ`, `uᵢvᵢ`, `vᵢy` are the nine vertices, the triangles are `{xu₀,xu₁,xu₂}`
and `{v₀y,v₁y,v₂y}`, and `xuᵢ - uᵢvᵢ - vᵢy` are the three paths of length `2`. -/

/-- The raw (asymmetric) edge relation of the theta graph. -/
def thetaRel (x y : Fin 8) : Bool :=
  (x == 0 && (y == 2 || y == 3 || y == 4)) ||
  (x == 2 && y == 5) || (x == 3 && y == 6) || (x == 4 && y == 7) ||
  ((x == 5 || x == 6 || x == 7) && y == 1)

/-- Its symmetrisation. -/
def thetaAdj (x y : Fin 8) : Prop := thetaRel x y = true ∨ thetaRel y x = true

instance : DecidableRel thetaAdj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

/-- The theta graph: two vertices joined by three internally disjoint paths of length `3`. -/
def theta : SimpleGraph (Fin 8) where
  Adj := thetaAdj
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

instance : DecidableRel theta.Adj := inferInstanceAs (DecidableRel thetaAdj)

/-- All cycles of the theta graph have length `6`; the two-colouring below witnesses it. -/
theorem theta_bipartite : theta.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk ![0, 1, 1, 1, 1, 0, 0, 0] ?_⟩
  intro u v h
  revert h
  revert u v
  decide

/-! ### The abstract nine-vertex prism

Its vertices are indexed by pairs `(i, k)` — `i` says which of the three paths, `k` says the
position `0,1,2` on that path, so `(i,0) = aᵢ`, `(i,1)` is the middle vertex, `(i,2) = bᵢ`. -/

/-- Adjacency of the nine-vertex prism. -/
def prismAdj (p q : Fin 3 × Fin 3) : Prop :=
  if p.1 = q.1 then ((p.2 : ℕ) + 1 = (q.2 : ℕ) ∨ (q.2 : ℕ) + 1 = (p.2 : ℕ))
  else (((p.2 : ℕ) = 0 ∧ (q.2 : ℕ) = 0) ∨ ((p.2 : ℕ) = 2 ∧ (q.2 : ℕ) = 2))

instance : DecidableRel prismAdj := fun p q => by unfold prismAdj; infer_instance

/-- The nine-vertex prism. -/
def prism9 : SimpleGraph (Fin 3 × Fin 3) where
  Adj := prismAdj
  symm := by
    intro p q h
    unfold prismAdj at h ⊢
    split_ifs at h ⊢ with h1 h2
    · omega
    · exact absurd h1.symm h2
    · tauto
    · tauto
  loopless := ⟨by decide⟩

instance : DecidableRel prism9.Adj := inferInstanceAs (DecidableRel prismAdj)

/-- The nine edges of `theta`, indexed by the nine vertices of the prism. -/
def psi (p : Fin 3 × Fin 3) : Sym2 (Fin 8) :=
  ![![s(0,2), s(2,5), s(5,1)],
    ![s(0,3), s(3,6), s(6,1)],
    ![s(0,4), s(4,7), s(7,1)]] p.1 p.2

theorem psi_mem (p : Fin 3 × Fin 3) : psi p ∈ theta.edgeSet := by revert p; decide

/-- The nine vertices of `L(theta)`. -/
def psiE (p : Fin 3 × Fin 3) : theta.edgeSet := ⟨psi p, psi_mem p⟩

theorem psiE_inj : Function.Injective psiE := by decide

theorem psiE_bij : Function.Bijective psiE :=
  (Fintype.bijective_iff_injective_and_card psiE).mpr ⟨psiE_inj, by decide⟩

/-- **The nine-vertex prism is the line graph of the theta graph.** -/
noncomputable def prismIsoLine : prism9 ≃g theta.lineGraph where
  toEquiv := Equiv.ofBijective psiE psiE_bij
  map_rel_iff' := by
    intro p q
    show theta.lineGraph.Adj (psiE p) (psiE q) ↔ _
    rw [SimpleGraph.lineGraph_adj_iff_exists]
    revert p q
    decide

/-! ### Two small facts about paths -/

variable {V : Type*}

/-- Every vertex of a path with at least two vertices has a neighbour on the path. -/
theorem has_neighbour {G : SimpleGraph V} {p : List V} (hp : IsPathList G p)
    (h2 : 2 ≤ p.length) {u : V} (hu : u ∈ p) : ∃ v ∈ p, G.Adj u v := by
  obtain ⟨k, hk, hku⟩ := List.getElem_of_mem hu
  by_cases hk1 : k + 1 < p.length
  · refine ⟨p[k + 1]'hk1, List.getElem_mem _, ?_⟩
    rw [← hku]
    exact PathBasics.path_adj_succ hp hk1
  · have hk0 : 1 ≤ k := by omega
    refine ⟨p[k - 1]'(by omega), List.getElem_mem _, ?_⟩
    rw [← hku, SimpleGraph.adj_comm]
    have := PathBasics.path_adj_succ (i := k - 1) hp (by omega)
    have he : k - 1 + 1 = k := by omega
    simpa [he] using this

/-! ### The lemma -/

/-- **Auxiliary to 10.6 / 1.8.4.**  A graph that *is* an even prism on nine vertices is
the line graph of a bipartite graph.

The hypothesis is verbatim the first disjunct of the conclusion of
`Workspace.Statements.S10.SPGT.thm_10_6`. -/
theorem ninePrism_isLineGraphOfBipartite {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (h : (∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃ ∧
            {v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} = Set.univ) ∧
          Fintype.card V = 9) :
    IsLineGraphOfBipartite G := by
  obtain ⟨⟨a, b, R₁, R₂, R₃, ⟨hform, hev1, hev2, hev3⟩, hcovset⟩, hcard⟩ := h
  obtain ⟨hAA, hBB, hAB, hp1, hp2, hp3, e12, e13, e23⟩ := hform
  -- Flip a cross-condition.
  have flipc : ∀ (P Q : List V) (x y z t : V),
      (∀ u ∈ P, ∀ v ∈ Q, (G.Adj u v ↔ (u = x ∧ v = y) ∨ (u = z ∧ v = t))) →
      ∀ u ∈ Q, ∀ v ∈ P, (G.Adj u v ↔ (u = y ∧ v = x) ∨ (u = t ∧ v = z)) := by
    intro P Q x y z t e u hu v hv
    rw [SimpleGraph.adj_comm, e v hv u hu]
    tauto
  -- Package the three paths as a single family.
  obtain ⟨R, hR0, hR1, hR2⟩ : ∃ R : Fin 3 → List V, R 0 = R₁ ∧ R 1 = R₂ ∧ R 2 = R₃ :=
    ⟨![R₁, R₂, R₃], by simp, by simp, by simp⟩
  have hpath : ∀ i : Fin 3, IsPathFrom G (R i) (a i) (b i) := by
    intro i
    fin_cases i
    · simpa [hR0] using hp1
    · simpa [hR1] using hp2
    · simpa [hR2] using hp3
  have hev : ∀ i : Fin 3, Even (pathLength (R i)) := by
    intro i
    fin_cases i
    · simpa [hR0] using hev1
    · simpa [hR1] using hev2
    · simpa [hR2] using hev3
  have hcross : ∀ i j : Fin 3, i ≠ j → ∀ u ∈ R i, ∀ v ∈ R j,
      (G.Adj u v ↔ (u = a i ∧ v = a j) ∨ (u = b i ∧ v = b j)) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · simpa [hR0, hR1] using e12
    · simpa [hR0, hR2] using e13
    · simpa [hR0, hR1] using flipc R₁ R₂ (a 0) (a 1) (b 0) (b 1) e12
    · exact absurd rfl hij
    · simpa [hR1, hR2] using e23
    · simpa [hR0, hR2] using flipc R₁ R₃ (a 0) (a 2) (b 0) (b 2) e13
    · simpa [hR1, hR2] using flipc R₂ R₃ (a 1) (a 2) (b 1) (b 2) e23
    · exact absurd rfl hij
  have hcov : ∀ v : V, ∃ i : Fin 3, v ∈ R i := by
    intro v
    have hmem : v ∈ ({v : V | v ∈ R₁} ∪ {v : V | v ∈ R₂} ∪ {v : V | v ∈ R₃} : Set V) := by
      rw [hcovset]; trivial
    rcases hmem with (hm | hm) | hm
    · exact ⟨0, by rw [hR0]; exact hm⟩
    · exact ⟨1, by rw [hR1]; exact hm⟩
    · exact ⟨2, by rw [hR2]; exact hm⟩
  -- Each path has at least two vertices, since its two ends differ.
  have hne2 : ∀ i : Fin 3, 2 ≤ (R i).length := by
    intro i
    by_contra hc
    have hpos : 0 < (R i).length := PathBasics.path_length_pos (hpath i).1
    have hl1 : (R i).length = 1 := by omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hl1
    have h2 := (hpath i).2.1
    have h3 := (hpath i).2.2
    rw [hx] at h2 h3
    simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at h2 h3
    exact hAB i i (h2.symm.trans h3)
  -- Paths of a prism are pairwise disjoint.
  have hdisj : ∀ (i j : Fin 3), i ≠ j → ∀ u ∈ R i, u ∉ R j := by
    intro i j hij u hu huj
    obtain ⟨v, hv, hadjv⟩ := has_neighbour (hpath j).1 (hne2 j) huj
    have h1 := (hcross i j hij u hu v hv).mp hadjv
    obtain ⟨v', hv', hadjv'⟩ := has_neighbour (hpath i).1 (hne2 i) hu
    have h2 := (hcross j i hij.symm u huj v' hv').mp hadjv'
    rcases h1 with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rcases h2 with ⟨he, -⟩ | ⟨he, -⟩
    · exact (hAA i j hij).ne he
    · exact hAB i j he
    · exact (hAB j i he.symm).elim
    · exact (hBB i j hij).ne he
  -- Each path has an odd number of vertices, hence at least three.
  have hge3 : ∀ i : Fin 3, 3 ≤ (R i).length := by
    intro i
    have h2 := hne2 i
    have hE := hev i
    rw [PathBasics.pathLength_eq, Nat.even_iff] at hE
    omega
  -- The three paths together enumerate `V`, so their lengths add up to `9`.
  have hnodupL : (R 0 ++ R 1 ++ R 2).Nodup := by
    rw [List.nodup_append, List.nodup_append]
    refine ⟨⟨(hpath 0).1.2.1, (hpath 1).1.2.1, ?_⟩, (hpath 2).1.2.1, ?_⟩
    · intro x hx y hy hxy
      exact hdisj 0 1 (by decide) x hx (hxy ▸ hy)
    · intro x hx y hy hxy
      rcases List.mem_append.mp hx with hx' | hx'
      · exact hdisj 0 2 (by decide) x hx' (hxy ▸ hy)
      · exact hdisj 1 2 (by decide) x hx' (hxy ▸ hy)
  have hmemL : ∀ v : V, v ∈ R 0 ++ R 1 ++ R 2 := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    fin_cases i
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl (by simpa using hi))))
    · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr (by simpa using hi))))
    · exact List.mem_append.mpr (Or.inr (by simpa using hi))
  have hlenL : (R 0 ++ R 1 ++ R 2).length = 9 := by
    have hu : (R 0 ++ R 1 ++ R 2).toFinset = Finset.univ :=
      Finset.eq_univ_iff_forall.mpr fun v => List.mem_toFinset.mpr (hmemL v)
    have hc := List.toFinset_card_of_nodup hnodupL
    rw [hu, Finset.card_univ, hcard] at hc
    omega
  have hsum : (R 0).length + (R 1).length + (R 2).length = 9 := by
    simp only [List.length_append] at hlenL
    omega
  have hL0 : (R 0).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hL1 : (R 1).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hL2 : (R 2).length = 3 := by have := hge3 0; have := hge3 1; have := hge3 2; omega
  have hlen3 : ∀ i : Fin 3, (R i).length = 3 := by
    intro i; fin_cases i
    · simpa using hL0
    · simpa using hL1
    · simpa using hL2
  -- The nine vertices, indexed by (path, position).
  obtain ⟨w, hw⟩ : ∃ w : Fin 3 × Fin 3 → V,
      ∀ (i k : Fin 3), w (i, k) = (R i)[(k : ℕ)]'(by rw [hlen3]; exact k.isLt) :=
    ⟨fun p => (R p.1).getD (p.2 : ℕ) (a 0), by
      intro i k
      exact List.getD_eq_getElem _ _ _⟩
  -- Ends of the paths, read off as entries of the lists.
  have hend0 : ∀ i : Fin 3, (R i)[(0 : ℕ)]'(by rw [hlen3]; omega) = a i := fun i =>
    PathBasics.getElem_zero_of_head? (hpath i).2.1 _
  have hend2 : ∀ i : Fin 3, (R i)[(2 : ℕ)]'(by rw [hlen3]; omega) = b i := by
    intro i
    have := PathBasics.getElem_last_of_getLast? (hpath i).2.2 (by rw [hlen3]; omega)
    have hl : (R i).length - 1 = 2 := by rw [hlen3]
    simpa [hl] using this
  -- `w` is injective.
  have hinj : Function.Injective w := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hkl
    rw [hw, hw] at hkl
    by_cases hij : i = j
    · subst hij
      have hkl' : (k : ℕ) = (l : ℕ) := by
        by_contra hne
        exact PathBasics.path_ne_of_ne_index (hpath i).1 _ _ hne hkl
      simp [Fin.ext_iff, hkl']
    · exfalso
      have hmi : (R i)[(k : ℕ)]'(by rw [hlen3]; exact k.isLt) ∈ R i := List.getElem_mem _
      have hmj : (R j)[(l : ℕ)]'(by rw [hlen3]; exact l.isLt) ∈ R j := List.getElem_mem _
      rw [hkl] at hmi
      exact hdisj j i (Ne.symm hij) _ hmj hmi
  -- `w` is surjective.
  have hsurj : Function.Surjective w := by
    intro v
    obtain ⟨i, hi⟩ := hcov v
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hi
    have hk3 : k < 3 := by rw [← hlen3 i]; exact hk
    refine ⟨(i, ⟨k, hk3⟩), ?_⟩
    rw [hw]
    exact hkv
  -- The adjacency of `G` is that of the prism.
  have hadj : ∀ p q : Fin 3 × Fin 3, G.Adj (w p) (w q) ↔ prismAdj p q := by
    rintro ⟨i, k⟩ ⟨j, l⟩
    rw [hw, hw]
    unfold prismAdj
    by_cases hij : i = j
    · subst hij
      simp only [if_pos rfl]
      exact PathBasics.path_adj_iff (hpath i).1 _ _
    · rw [if_neg hij]
      rw [hcross i j hij _ (List.getElem_mem _) _ (List.getElem_mem _)]
      have hA : ∀ (m : Fin 3) (n : Fin 3),
          ((R m)[(n : ℕ)]'(by rw [hlen3]; exact n.isLt) = a m) ↔ (n : ℕ) = 0 := by
        intro m n
        constructor
        · intro hn
          by_contra hne
          exact PathBasics.path_ne_of_ne_index (hpath m).1 _ _ hne (hn.trans (hend0 m).symm)
        · intro hn
          rw [← hend0 m]
          congr 1
      have hB : ∀ (m : Fin 3) (n : Fin 3),
          ((R m)[(n : ℕ)]'(by rw [hlen3]; exact n.isLt) = b m) ↔ (n : ℕ) = 2 := by
        intro m n
        constructor
        · intro hn
          by_contra hne
          exact PathBasics.path_ne_of_ne_index (hpath m).1 _ _ hne (hn.trans (hend2 m).symm)
        · intro hn
          rw [← hend2 m]
          congr 1
      rw [hA i k, hA j l, hB i k, hB j l]
  -- Assemble the isomorphism.
  refine ⟨8, theta, theta_bipartite, ⟨?_⟩⟩
  have hiso : prism9 ≃g G :=
    ⟨Equiv.ofBijective w ⟨hinj, hsurj⟩, fun {p q} => hadj p q⟩
  exact hiso.symm.trans prismIsoLine

end Workspace.ProofLemmas.NinePrismLineGraph
