import Mathlib
import Workspace.Types.Core
import Workspace.Types.Tracks
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.BasicClasses
import Workspace.Types.Decompositions
import Workspace.Types.Classes
import Workspace.Types.LongOddPrism
import Workspace.ProofLemmas.HoleBasics
import Workspace.ProofLemmas.ClassLemmas
import Workspace.ProofLemmas.NinePrismLineGraph
import Workspace.ProofLemmas.DoubleSplitSelfComplementary
import Workspace.Statements.S09.Thm_9_7
import Workspace.Statements.S10.Thm_10_6
import Workspace.Statements.S13.Thm_13_4

/-!
# Every recalcitrant graph belongs to `F₅`

PAPER (printed p. 86, immediately after 13.5):

> *"… for the remainder of the paper we shall only be concerned with Berge graphs `G`
> such that in both `G, Ḡ` there is no appearance of `K₄` and no long prism; that is,
> with the members of the class `F₅` introduced in section 1.  **Certainly every
> recalcitrant graph belongs to `F₅`, by 10.6 and 9.7.**"*

`Recalcitrant` (printed p. 86, transcribed in `Workspace.Types.LongOddPrism`) is

> *"`G` is Berge; `G` and `Ḡ` are not line graphs, and `G` is not a double split graph;
> `G` and `Ḡ` do not admit proper 2-joins; and `G` does not admit a proper homogeneous
> pair or balanced skew partition."*

## How the printed one-liner unfolds

* **`InF3`** — *"in both `G, Ḡ` there is no appearance of `K₄`"*.  This is **9.7**
  (*"Let `G` be a Berge graph, such that there is an appearance of `K₄` in `G`.  Then
  either one of `G,Ḡ` is a line graph, or `G` is a double split graph, or one of `G,Ḡ`
  admits a proper 2-join, or `G` admits a balanced skew partition"*), applied to `G`
  and then to `Ḡ`.  Each of the six alternatives is negated by a bullet of
  *recalcitrant* — for `Ḡ` after using that the class of double split graphs is
  self-complementary (the paper's own parenthetical on printed p. 2:
  *"(Note that if `G` is a double split graph then so is `Ḡ`.)"*, proved here as
  `isDoubleSplitGraph_compl`) and that balanced skew partitions are
  (`ClassLemmas.admitsBalancedSkewPartition_compl`).

* **no long prism in `G`, none in `Ḡ`** — a prism is either even or odd
  (`IsOddPrism` is by definition the negation of the parity condition of
  `IsEvenPrism`), so a long prism falls into one of two cases:
  * an **even** prism is disposed of by **10.6** (*"If `G` contains an even prism, then
    either `G` is an even prism with `|V(G)| = 9`, or `G` admits a proper 2-join or a
    balanced skew partition"*).  Its first escape clause is disposed of by
    `NinePrismLineGraph.ninePrism_isLineGraphOfBipartite`: a nine-vertex even prism is
    `L(H)` for a bipartite theta graph `H`, contradicting *"`G` is not a line graph"*.
  * a **long odd** prism is disposed of by **13.4** — the result printed immediately
    before the definition of *recalcitrant*, whose four alternatives (*proper 2-join in
    `G`*, *in `Ḡ`*, *balanced skew partition*, *proper homogeneous pair*) are precisely
    the last two bullets of *recalcitrant*.

  For `Ḡ` the odd case needs that proper homogeneous pairs are complement-invariant,
  which is exactly the reading of *"proper homogeneous pair"* recorded in
  `Workspace.Types.Decompositions` (*"it makes the notion invariant under
  complementation, which §13 requires"*); it is proved here as
  `isProperHomogeneousPair_compl`.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.RecalcitrantInF5

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.BasicClasses.SPGT
open Workspace.Types.Decompositions.SPGT
open Workspace.Types.Classes.SPGT
open Workspace.Types.LongOddPrism.SPGT

/-! ## The class of double split graphs is self-complementary

PAPER (printed p. 2, inside the definition of *basic*): *"(Note that if `G` is a double
split graph then so is `Ḡ`.)"*  Interchanging the two halves `(a,b)` and `(c,d)` of the
partition turns the presentation of `G` into a presentation of `Ḡ`. -/

section DoubleSplit

variable {V : Type*} {G : SimpleGraph V}

/-- The proof now lives in `Workspace.ProofLemmas.DoubleSplitSelfComplementary`, which imports
no numbered statement.  It had to be moved out of this module because this module cites **9.7**
and therefore imports `Workspace.Statements.S09.Thm_9_7`, which imports `Thm_9_6` — and the
proof of **9.6** needs exactly this lemma for its *"by taking complements"* steps.  This
re-export keeps every existing reference to `RecalcitrantInF5.isDoubleSplitGraph_compl`
working. -/
theorem isDoubleSplitGraph_compl (h : IsDoubleSplitGraph G) : IsDoubleSplitGraph Gᶜ :=
  DoubleSplitSelfComplementary.isDoubleSplitGraph_compl h

end DoubleSplit

/-! ## Proper homogeneous pairs are complement-invariant

The reading of *proper homogeneous pair* recorded in `Workspace.Types.Decompositions`
was chosen precisely so that this holds (see the note there: *"it makes the notion
invariant under complementation, which §13 requires"*). -/

section HomogeneousPair

variable {V : Type*} {G : SimpleGraph V}

theorem isProperHomogeneousPair_compl {A B : Set V} (h : IsProperHomogeneousPair G A B) :
    IsProperHomogeneousPair Gᶜ A B := by
  obtain ⟨hdisj, hAne, hBne, hUA, hUB, h11, h12, h21, h22⟩ := h
  -- Being `S`-complete in `Ḡ` is being outside `S` and `S`-anticomplete in `G`.
  have hVC : ∀ (S : Set V) (v : V),
      VertexComplete Gᶜ v S ↔ (v ∉ S ∧ VertexAnticomplete G v S) := by
    intro S v
    constructor
    · intro hv
      exact ⟨fun hvS => ((SimpleGraph.compl_adj G v v).mp (hv v hvS)).1 rfl,
             fun x hx hadj => ((SimpleGraph.compl_adj G v x).mp (hv x hx)).2 hadj⟩
    · rintro ⟨hvS, hv⟩ x hx
      exact (SimpleGraph.compl_adj G v x).mpr ⟨by rintro rfl; exact hvS hx, hv x hx⟩
  -- Being outside `S` and `S`-anticomplete in `Ḡ` is being `S`-complete in `G`.
  have hVA2 : ∀ (S : Set V) (v : V),
      (v ∉ S ∧ VertexAnticomplete Gᶜ v S) ↔ VertexComplete G v S := by
    intro S v
    constructor
    · rintro ⟨hvS, hv⟩ x hx
      by_contra hadj
      exact hv x hx ((SimpleGraph.compl_adj G v x).mpr ⟨by rintro rfl; exact hvS hx, hadj⟩)
    · intro hv
      refine ⟨fun hvS => G.irrefl (hv v hvS), fun x hx hadj => ?_⟩
      exact ((SimpleGraph.compl_adj G v x).mp hadj).2 (hv x hx)
  have hVAc : ∀ (S : Set V) (v : V), VertexComplete G v S → VertexAnticomplete Gᶜ v S :=
    fun S v hv x hx hadj => ((SimpleGraph.compl_adj G v x).mp hadj).2 (hv x hx)
  -- A vertex complete to `A` (resp. `B`) lies outside `A ∪ B`.
  have houtA : ∀ v : V, VertexComplete G v A → v ∉ A ∪ B := by
    intro v hv
    have hmem : v ∈ ({w : V | VertexComplete G w A} ∪
        {w : V | w ∉ A ∧ VertexAnticomplete G w A}) := Or.inl hv
    rw [hUA] at hmem
    exact hmem
  have houtB : ∀ v : V, VertexComplete G v B → v ∉ A ∪ B := by
    intro v hv
    have hmem : v ∈ ({w : V | VertexComplete G w B} ∪
        {w : V | w ∉ B ∧ VertexAnticomplete G w B}) := Or.inl hv
    rw [hUB] at hmem
    exact hmem
  -- A vertex anticomplete to both `A` and `B` also lies outside `A ∪ B`: a vertex of `A`
  -- has a neighbour in `B` and vice versa, which is what the two union clauses say.
  have hout : ∀ v : V, VertexAnticomplete G v A → VertexAnticomplete G v B → v ∉ A ∪ B := by
    intro v hvA hvB hmem
    rcases hmem with hA | hB
    · have h' : v ∈ ({w : V | VertexComplete G w B} ∪
          {w : V | w ∉ B ∧ VertexAnticomplete G w B}) :=
        Or.inr ⟨Set.disjoint_left.mp hdisj hA, hvB⟩
      rw [hUB] at h'
      exact h' (Or.inl hA)
    · have h' : v ∈ ({w : V | VertexComplete G w A} ∪
          {w : V | w ∉ A ∧ VertexAnticomplete G w A}) :=
        Or.inr ⟨Set.disjoint_right.mp hdisj hB, hvA⟩
      rw [hUA] at h'
      exact h' (Or.inr hB)
  refine ⟨hdisj, hAne, hBne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : {v : V | VertexComplete Gᶜ v A}
        = {v : V | v ∉ A ∧ VertexAnticomplete G v A} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVC A v
    have e2 : {v : V | v ∉ A ∧ VertexAnticomplete Gᶜ v A}
        = {v : V | VertexComplete G v A} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVA2 A v
    rw [e1, e2, Set.union_comm]
    exact hUA
  · have e1 : {v : V | VertexComplete Gᶜ v B}
        = {v : V | v ∉ B ∧ VertexAnticomplete G v B} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVC B v
    have e2 : {v : V | v ∉ B ∧ VertexAnticomplete Gᶜ v B}
        = {v : V | VertexComplete G v B} := by
      ext v; simp only [Set.mem_setOf_eq]; exact hVA2 B v
    rw [e1, e2, Set.union_comm]
    exact hUB
  · obtain ⟨w, hwA, hwB⟩ := h22
    have hw := hout w hwA hwB
    exact ⟨w, (hVC A w).mpr ⟨fun hc => hw (Or.inl hc), hwA⟩,
              (hVC B w).mpr ⟨fun hc => hw (Or.inr hc), hwB⟩⟩
  · obtain ⟨w, hwA, hwB⟩ := h21
    have hw := houtB w hwB
    exact ⟨w, (hVC A w).mpr ⟨fun hc => hw (Or.inl hc), hwA⟩, hVAc B w hwB⟩
  · obtain ⟨w, hwA, hwB⟩ := h12
    have hw := houtA w hwA
    exact ⟨w, hVAc A w hwA, (hVC B w).mpr ⟨fun hc => hw (Or.inr hc), hwB⟩⟩
  · obtain ⟨w, hwA, hwB⟩ := h11
    exact ⟨w, hVAc A w hwA, hVAc B w hwB⟩

theorem admitsProperHomogeneousPair_of_compl (h : AdmitsProperHomogeneousPair Gᶜ) :
    AdmitsProperHomogeneousPair G := by
  obtain ⟨A, B, hAB⟩ := h
  have h' := isProperHomogeneousPair_compl hAB
  rw [compl_compl] at h'
  exact ⟨A, B, h'⟩

end HomogeneousPair

/-! ## No long prism -/

section NoLongPrism

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The "no long prism" half of `F₅`, for a single graph.  The hypotheses are exactly the
bullets of *recalcitrant* that the two cited results consume. -/
theorem no_long_prism (G : SimpleGraph V) (hBerge : Berge G)
    (hlg : ¬ IsLineGraphOfBipartite G)
    (hK4G : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hK4Gc : ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)))
    (h2j : ¬ AdmitsProper2Join G) (h2jc : ¬ AdmitsProper2Join Gᶜ)
    (hphp : ¬ AdmitsProperHomogeneousPair G)
    (hbsp : ¬ AdmitsBalancedSkewPartition G) :
    ¬ ∃ (a b : Fin 3 → V) (P₁ P₂ P₃ : List V), IsLongPrism G a b P₁ P₂ P₃ := by
  rintro ⟨a, b, P₁, P₂, P₃, hform, hlong⟩
  by_cases heven : Even (pathLength P₁) ∧ Even (pathLength P₂) ∧ Even (pathLength P₃)
  · -- An even prism: 10.6.
    have hK4' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
        IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
          NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
      rintro ⟨n, H, K', happ, -⟩
      exact hK4G ⟨n, H, K', happ⟩
    rcases _root_.Workspace.Statements.S10.SPGT.thm_10_6 G hBerge hK4'
        ⟨a, b, P₁, P₂, P₃, hform, heven⟩ with h9 | h2 | hb
    · exact hlg (NinePrismLineGraph.ninePrism_isLineGraphOfBipartite G h9)
    · exact h2j h2
    · exact hbsp hb
  · -- A long odd prism: 13.4.
    rcases _root_.Workspace.Statements.S13.SPGT.thm_13_4 G hBerge hK4G hK4Gc
        ⟨a, b, P₁, P₂, P₃, ⟨hform, hlong⟩, ⟨hform, heven⟩⟩ with (h | h) | h | h
    · exact h2j h
    · exact h2jc h
    · exact hbsp h
    · exact hphp h

end NoLongPrism

/-! ## The corollary itself -/

section Main

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (printed p. 86): *"Certainly every recalcitrant graph belongs to `F₅`, by 10.6
and 9.7."* -/
theorem recalcitrant_inF5 (G : SimpleGraph V) (hG : Recalcitrant G) : InF5 G := by
  obtain ⟨hBerge, ⟨hlgG, hlgGc, hdsG⟩, ⟨h2jG, h2jGc⟩, hphpG, hbspG⟩ := hG
  have hBergeC : Berge Gᶜ := HoleBasics.berge_compl.mpr hBerge
  have hdsGc : ¬ IsDoubleSplitGraph Gᶜ := by
    intro hc
    have := isDoubleSplitGraph_compl hc
    rw [compl_compl] at this
    exact hdsG this
  have hbspGc : ¬ AdmitsBalancedSkewPartition Gᶜ := fun hc =>
    hbspG (ClassLemmas.admitsBalancedSkewPartition_compl.mp hc)
  have hphpGc : ¬ AdmitsProperHomogeneousPair Gᶜ := fun hc =>
    hphpG (admitsProperHomogeneousPair_of_compl hc)
  -- 9.7 applied to `G`: every alternative is a bullet of *recalcitrant*.
  have hK4G : ¬ Appears G (⊤ : SimpleGraph (Fin 4)) := by
    intro happ
    rcases _root_.Workspace.Statements.S09.SPGT.thm_9_7 G hBerge happ with
      (h | h) | h | (h | h) | h
    · exact hlgG h
    · exact hlgGc h
    · exact hdsG h
    · exact h2jG h
    · exact h2jGc h
    · exact hbspG h
  -- 9.7 applied to `Ḡ`.
  have hK4Gc : ¬ Appears Gᶜ (⊤ : SimpleGraph (Fin 4)) := by
    intro happ
    rcases _root_.Workspace.Statements.S09.SPGT.thm_9_7 Gᶜ hBergeC happ with
      (h | h) | h | (h | h) | h
    · exact hlgGc h
    · rw [compl_compl] at h; exact hlgG h
    · exact hdsGc h
    · exact h2jGc h
    · rw [compl_compl] at h; exact h2jG h
    · exact hbspGc h
  have hK4Gcc : ¬ Appears Gᶜᶜ (⊤ : SimpleGraph (Fin 4)) := by
    rw [compl_compl]; exact hK4G
  have h2jGcc : ¬ AdmitsProper2Join Gᶜᶜ := by rw [compl_compl]; exact h2jG
  refine ⟨⟨hBerge, ?_⟩, ?_, ?_⟩
  · -- `F₃`: no `L(H)` inside `G` or inside `Ḡ`, for `H` a bipartite subdivision of `K₄`.
    intro n H hsub
    constructor
    · rintro ⟨K, ⟨e⟩⟩
      exact hK4G ⟨n, H, K, hsub, ⟨e.symm⟩⟩
    · rintro ⟨K, ⟨e⟩⟩
      exact hK4Gc ⟨n, H, K, hsub, ⟨e.symm⟩⟩
  · exact no_long_prism G hBerge hlgG hK4G hK4Gc h2jG h2jGc hphpG hbspG
  · exact no_long_prism Gᶜ hBergeC hlgGc hK4Gc hK4Gcc h2jGc h2jGcc hphpGc hbspGc

end Main

end Workspace.ProofLemmas.RecalcitrantInF5
