import Mathlib
import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.Types.Appearances
import Workspace.Types.Decompositions
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.Thm123Minimal
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.ProofLemmas.Thm121C3PathCons
import Workspace.ProofLemmas.PathAttach
import Workspace.Statements.S10.Thm_10_1
import Workspace.Statements.S10.Thm_10_4
import Workspace.Statements.S02.Thm_2_4
import Workspace.Statements.S11.Thm_11_3
import Workspace.Statements.S12.Thm_12_1
import Workspace.Statements.S12.Thm_12_2
import Workspace.ProofLemmas.Thm123Claim3RungEdgeCharacterization

/-!
# 12.3, the body of the printed proof

PAPER (printed pp. 72–73).  After the opening reduction (`Workspace.ProofLemmas.Thm123Minimal`)
the proof runs:

*"We may assume there is no major vertex in `F`.*

*(1) We may assume that none of `f₁, …, f_k` is a right-star, and that `f_k` is not
`B`-complete.*

*For if there is a right-star in `F`, then it must be `f_k`; and then from the minimality of `F`
(exchanging `A` and `B`), no vertex of `F` different from `f₁` has a neighbour in `A ∪ C`, and so
`f₁`-…-`f_k` is a banister.  So we may assume that there is no right-star in `F`.  Since `f_k` is
neither major nor a right-star, by 12.1 it is not `B`-complete.  This proves (1).*

*(2) `F ∩ V(R₀) = ∅`, and there are no edges between `{f₂, …, f_k}` and `V(R₀ \ b₀)`.*

*For by (1), `b₀ ∉ F`.  Suppose that either `{f₂, …, f_k}` intersects `V(R₀ \ b₀)`, or there is
an edge joining these two sets.  Choose `i` with `2 ≤ i ≤ k` maximum such that either
`f_i ∈ V(R₀ \ b₀)` or `f_i` has a neighbour in `V(R₀ \ b₀)`.  We claim that `f_i ∉ V(R₀)`. …
Since `{f_i, …, f_k}` has attachments in `V(R₀ \ b₀)` and in `B ∪ C`, and contains no major
vertex or left- or right-star, this contradicts 12.2. …  This proves (2).*

*Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that `f_k` has a neighbour in `R₁ \ a₁` and
`f_k` is nonadjacent to `b₂`.  (To see that such a step exists … the required step exists since
the strip is step-connected.)*

*(3) `f₁a₂` is the only edge between `F` and `R₂`. …*

*(4) `b₀` has neighbours in `{f₁, …, f_{k−1}}`. …*

*Choose `i` with `1 ≤ i < k` minimum such that `b₀` is adjacent to `f_i`, and let `R₀'` be the
path `f₁`-…-`f_i`-`b₀`. …  But then by (2), `a₁` can be linked onto the triangle
`{b₀, b₁, f_k}`, via `a₁`-`a₀`-`R₀`-`b₀`, `a₁`-`R₁`-`b₁`, `a₁`-`f₂`-…-`f_k`, contrary to 2.4.
This proves 12.3."*

The results cited are 12.1, 12.2, 10.4, 11.3 and 2.4 (Roussel–Rubio).

Encoding notes.

* `{f₂, …, f_k}` is `{w | w ∈ f ∧ w ≠ f₁}` (the path list `f` is `Nodup`, so removing `f₁`
  removes exactly the first vertex), and `V(R₀ \ b₀)` is `{x | x ∈ R₀ ∧ x ≠ b₀}`.
* `Setup` bundles the data produced by `Thm123Minimal.thm123Minimal` together with the standing
  assumption *"we may assume there is no major vertex in `F`"*; each claim of the printed proof
  is stated below relative to it.
* The last paragraph derives a contradiction, so it is stated as `… → False`.

**Status:** the body below formalizes all four claims and the final linkage contradiction.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.Thm123Body

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases Workspace.Types.Staircases.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.ProofLemmas.Thm123Minimal

/-- The situation the printed proof works in after its opening reduction: one orientation has
been selected, `F` has 12.3's property in that orientation and is minimal among candidates in
either orientation; it is the vertex set of the path `f₁`-…-`f_k`, `f₁` is its unique
left-star, `f_k` is its only vertex with a neighbour in `B ∪ C`, `k ≥ 2`, and — *"We may assume
there is no major vertex in `F`"* — no vertex of `F` is major. -/
def Setup {V : Type*} (G : SimpleGraph V) (A C B : Set V) (a₀ : V) (R₀ : List V) (b₀ : V)
    (F : Set V) (f : List V) (f₁ fk : V) : Prop :=
  Cand G A C B F ∧
  (∀ F'' ⊆ F, (Cand G A C B F'' ∨ Cand G B C A F'') → F'' = F) ∧
  F = {w : V | w ∈ f} ∧
  SPGT.IsPathFrom G f f₁ fk ∧ 2 ≤ f.length ∧
  IsLeftStar G A C B f₁ ∧
  (∀ w ∈ f, IsLeftStar G A C B w → w = f₁) ∧
  (∃ y ∈ B ∪ C, G.Adj fk y) ∧
  (∀ w ∈ f, (∃ y ∈ B ∪ C, G.Adj w y) → w = fk) ∧
  (∀ w ∈ F, ¬ MajorForStaircase G A C B a₀ R₀ b₀ w)

variable {V : Type*}

/-- A step is symmetric in its two rungs: `a₁-R₁-b₁, a₂-R₂-b₂` is a step iff `a₂-R₂-b₂,
a₁-R₁-b₁` is.  (Used for the paper's silent *"say `f_k` has a neighbour in `R₁`"*.) -/
private theorem isStep_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ : V} {R₁ : List V} {b₁ : V} {a₂ : V} {R₂ : List V} {b₂ : V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) : IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h2, h1, fun v hv hv' => h3 v hv' hv, fun u hu v hv => ?_⟩
  constructor
  · intro hadj
    rcases (h4 v hv u hu).mp hadj.symm with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨e2, e1⟩
    · exact Or.inr ⟨e2, e1⟩
  · rintro (⟨e1, e2⟩ | ⟨e1, e2⟩)
    · exact ((h4 v hv u hu).mpr (Or.inl ⟨e2, e1⟩)).symm
    · exact ((h4 v hv u hu).mpr (Or.inr ⟨e2, e1⟩)).symm

private theorem claim3_rung_mem_ABC {G : SimpleGraph V} {A C B : Set V} {a b : V}
    {p : List V} (h : IsRungOfStrip G A C B a p b) :
    ∀ w ∈ p, w ∈ A ∪ B ∪ C := by
  intro w hw
  by_cases hwa : w = a
  · exact Or.inl (Or.inl (hwa ▸ h.2.1))
  by_cases hwb : w = b
  · exact Or.inl (Or.inr (hwb ▸ h.2.2.1))
  · exact Or.inr (h.2.2.2.2.2 w
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom h.1).mpr
        ⟨hw, hwa, hwb⟩))

private theorem claim3_rung_mem_BC_of_ne_left {G : SimpleGraph V} {A C B : Set V}
    {a b w : V} {p : List V} (h : IsRungOfStrip G A C B a p b)
    (hw : w ∈ p) (hwa : w ≠ a) : w ∈ B ∪ C := by
  rcases claim3_rung_mem_ABC h w hw with (hwA | hwB) | hwC
  · exact (hwa (h.2.2.2.1 w hw hwA)).elim
  · exact Or.inl hwB
  · exact Or.inr hwC

private theorem claim3_banister_rung_edges {G : SimpleGraph V} {A C B : Set V}
    {a₀ b₀ a b : V} {R₀ R : List V} (hban : IsBanister G A C B a₀ R₀ b₀)
    (hr : IsRungOfStrip G A C B a R b) :
    ∀ u ∈ R₀, ∀ w ∈ R,
      (G.Adj u w ↔ (u = a₀ ∧ w = a) ∨ (u = b₀ ∧ w = b)) := by
  obtain ⟨hR₀path, hR₀avoid, hLS, hRS, hR₀int⟩ := hban
  intro u hu w hw
  constructor
  · intro hadj
    have hwS := claim3_rung_mem_ABC hr w hw
    by_cases hua : u = a₀
    · subst u
      refine Or.inl ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact hr.2.2.2.1 w hw hwA
      · exact absurd hadj (hLS.2.2 w (Or.inl hwB))
      · exact absurd hadj (hLS.2.2 w (Or.inr hwC))
    by_cases hub : u = b₀
    · subst u
      refine Or.inr ⟨rfl, ?_⟩
      rcases hwS with (hwA | hwB) | hwC
      · exact absurd hadj (hRS.2.2 w (Or.inl hwA))
      · exact hr.2.2.2.2.1 w hw hwB
      · exact absurd hadj (hRS.2.2 w (Or.inr hwC))
    · exact absurd hadj (hR₀int u
        ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀path).mpr
          ⟨hu, hua, hub⟩) w hwS)
  · intro h
    rcases h with h | h
    · exact h.1 ▸ h.2 ▸ hLS.2.1 _ hr.2.1
    · exact h.1 ▸ h.2 ▸ hRS.2.1 _ hr.2.2.1

private theorem getElem_eq_of_index_eq {W : Type*} (p : List W) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hij : i = j) : p[i]'hi = p[j]'hj := by
  subst j
  rfl

/-- The last neighbour of `v` on a nonempty finite stretch of a path. -/
private theorem exists_max_adj_on_list {G : SimpleGraph V} (v : V) (p : List V)
    (k₀ : ℕ) (hk₀ : k₀ < p.length) (hadj₀ : G.Adj v (p[k₀]'hk₀)) :
    ∃ (k : ℕ) (hk : k < p.length), G.Adj v (p[k]'hk) ∧
      ∀ (j : ℕ) (hj : j < p.length), k < j → ¬ G.Adj v (p[j]'hj) := by
  classical
  let I : Finset ℕ := (Finset.range p.length).filter
    (fun k => ∃ hk : k < p.length, G.Adj v (p[k]'hk))
  have hk₀I : k₀ ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk₀, hk₀, hadj₀⟩
  have hI : I.Nonempty := ⟨k₀, hk₀I⟩
  have hkI := Finset.max'_mem I hI
  simp only [I, Finset.mem_filter, Finset.mem_range] at hkI
  obtain ⟨hk, hk', hadj⟩ := hkI
  refine ⟨I.max' hI, hk, hadj, ?_⟩
  intro j hj hkj hjadj
  have hjI : j ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hj, hjadj⟩
  exact (not_lt_of_ge (Finset.le_max' I j hjI)) hkj

/-- The first neighbour of `v` on a finite path list. -/
private theorem exists_min_adj_on_list {G : SimpleGraph V} (v : V) (p : List V)
    (k₀ : ℕ) (hk₀ : k₀ < p.length) (hadj₀ : G.Adj v (p[k₀]'hk₀)) :
    ∃ (k : ℕ) (hk : k < p.length), G.Adj v (p[k]'hk) ∧
      ∀ (j : ℕ) (hj : j < p.length), j < k → ¬ G.Adj v (p[j]'hj) := by
  classical
  let I : Finset ℕ := (Finset.range p.length).filter
    (fun k => ∃ hk : k < p.length, G.Adj v (p[k]'hk))
  have hk₀I : k₀ ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_range]
    exact ⟨hk₀, hk₀, hadj₀⟩
  have hI : I.Nonempty := ⟨k₀, hk₀I⟩
  have hkI := Finset.min'_mem I hI
  simp only [I, Finset.mem_filter, Finset.mem_range] at hkI
  obtain ⟨hk, hk', hadj⟩ := hkI
  refine ⟨I.min' hI, hk, hadj, ?_⟩
  intro j hj hjk hjadj
  have hjI : j ∈ I := by
    simp only [I, Finset.mem_filter, Finset.mem_range]
    exact ⟨hj, hj, hjadj⟩
  exact (not_lt_of_ge (Finset.min'_le I j hjI)) hjk

private theorem mem_drop_with_index {W : Type*} (p : List W) (i : ℕ) {x : W} :
    x ∈ p.drop i ↔ ∃ (j : ℕ) (hj : j < p.length), i ≤ j ∧ p[j]'hj = x := by
  constructor
  · intro hx
    obtain ⟨k, hk, hkx⟩ := List.mem_iff_getElem.mp hx
    rw [List.length_drop] at hk
    refine ⟨i + k, by omega, by omega, ?_⟩
    rw [← hkx, List.getElem_drop]
  · rintro ⟨j, hj, hij, rfl⟩
    have hk : j - i < (p.drop i).length := by
      rw [List.length_drop]
      omega
    have hm := List.getElem_mem hk
    have heq : (p.drop i)[j - i]'hk = p[j]'hj := by
      simp only [List.getElem_drop]
      congr 1
      omega
    rwa [heq] at hm

private theorem isPathFrom_drop_to_last {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (i : ℕ) (hi : i < p.length) :
    IsPathFrom G (p.drop i) (p[i]'hi) v := by
  refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_drop hp.1 hi, ?_, ?_⟩
  · rw [List.head?_drop, List.getElem?_eq_getElem hi]
  · rw [List.getLast?_drop, if_neg (by omega)]
    exact hp.2.2

private theorem isPathFrom_take_to_index {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (i : ℕ) (hi : i < p.length) :
    IsPathFrom G (p.take (i + 1)) u (p[i]'hi) := by
  refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hp.1 (by omega), ?_, ?_⟩
  · simpa [List.head?_take] using hp.2.1
  · have h := Workspace.ProofLemmas.PathBasics.getLast?_slice p
        (i := 0) (j := i) (by omega) hi
    simpa using h

/-- The path part of 10.4 needed in the last paragraph of 12.3.  The frozen statement of
10.4 records only its attachment-set corollary, so this lemma retains the witness path
supplied by 10.1.  With no attachment on the third rung, only 10.1.3 survives. -/
private theorem prismJumpPath {G : SimpleGraph V} [Fintype V] [DecidableEq V]
    (hG : Berge G) (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hform : FormPrism G a b (R 0) (R 1) (R 2))
    (hKeq : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hnonlocal : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hnomajor : ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (hnoR2 : ∀ x ∈ F, ∀ y ∈ R 2, ¬ G.Adj x y) :
    ∃ (q : List V) (s t : V),
      IsPathFrom G q s t ∧ 2 ≤ q.length ∧ (∀ x ∈ q, x ∈ F) ∧
      G.Adj s (a 0) ∧ G.Adj s (a 1) ∧
      G.Adj t (b 0) ∧ G.Adj t (b 1) ∧
      (∀ x ∈ q, ∀ z ∈ K, G.Adj x z →
        (x = s ∧ (z = a 0 ∨ z = a 1)) ∨
          (x = t ∧ (z = b 0 ∨ z = b 1))) := by
  have hform' := hform
  obtain ⟨-, -, -, hP0, hP1, hP2, -, -, -⟩ := hform
  have hamem : ∀ i : Fin 3, a i ∈ R i := by
    intro i
    fin_cases i
    · exact List.mem_of_mem_head? hP0.2.1
    · exact List.mem_of_mem_head? hP1.2.1
    · exact List.mem_of_mem_head? hP2.2.1
  have hbmem : ∀ i : Fin 3, b i ∈ R i := by
    intro i
    fin_cases i
    · exact List.mem_of_mem_getLast? hP0.2.2
    · exact List.mem_of_mem_getLast? hP1.2.2
    · exact List.mem_of_mem_getLast? hP2.2.2
  obtain ⟨q, s, t, hq, hqF, -, a', b', R', σ, hR', hab', hcase⟩ :=
    Workspace.Statements.S10.SPGT.thm_10_1 G hG a b R K F hform' hKeq hFK hFconn
      hnonlocal hnomajor
  have hsQ : s ∈ q := List.mem_of_mem_head? hq.2.1
  have htQ : t ∈ q := List.mem_of_mem_getLast? hq.2.2
  have hsF : s ∈ F := hqF s hsQ
  have htF : t ∈ F := hqF t htQ
  have ha'mem : ∀ i : Fin 3, a' i ∈ R (σ i) := by
    intro i
    rcases hab' with ⟨ha, -⟩ | ⟨ha, -⟩ <;> rw [ha]
    · exact hamem (σ i)
    · exact hbmem (σ i)
  have hR'mem : ∀ i : Fin 3, R' i = R (σ i) := by
    intro i
    rw [hR']
  rcases hcase with hcase1 | hcase2 | hcase3 | hcase4
  · obtain ⟨u, u', -, -, -, -, -, w, w', -, -, -, -, -, -, happ⟩ := hcase1
    exact (hK4 happ).elim
  · obtain ⟨-, hsa, -, -⟩ := hcase2
    have hm := ha'mem (σ.symm 2)
    have he : σ (σ.symm 2) = 2 := Equiv.apply_symm_apply σ 2
    rw [he] at hm
    exact (hnoR2 s hsF (a' (σ.symm 2)) hm (hsa (σ.symm 2))).elim
  · obtain ⟨hqlen, hsa0, hsa1, htb0, htb1, hcross⟩ := hcase3
    have hσ0 : σ 0 ≠ 2 := by
      intro he
      exact hnoR2 s hsF (a' 0) (he ▸ ha'mem 0) hsa0
    have hσ1 : σ 1 ≠ 2 := by
      intro he
      exact hnoR2 s hsF (a' 1) (he ▸ ha'mem 1) hsa1
    have hpair : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
      have hfin : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
      have h0 : σ 0 = 0 ∨ σ 0 = 1 := by
        rcases hfin (σ 0) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hσ0 h).elim
      have h1 : σ 1 = 0 ∨ σ 1 = 1 := by
        rcases hfin (σ 1) with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact (hσ1 h).elim
      rcases h0 with h00 | h01 <;> rcases h1 with h10 | h11
      · have hh := σ.injective (h00.trans h10.symm)
        omega
      · exact Or.inl ⟨h00, h11⟩
      · exact Or.inr ⟨h01, h10⟩
      · have hh := σ.injective (h01.trans h11.symm)
        omega
    rcases hab' with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rcases hpair with ⟨h00, h11⟩ | ⟨h01, h10⟩
      · refine ⟨q, s, t, hq, hqlen, hqF, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [ha, h00] using hsa0
        · simpa [ha, h11] using hsa1
        · simpa [hb, h00] using htb0
        · simpa [hb, h11] using htb1
        · intro x hx z hz hxz
          simpa [ha, hb, h00, h11] using hcross x hx z hz hxz
      · refine ⟨q, s, t, hq, hqlen, hqF, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [ha, h10] using hsa1
        · simpa [ha, h01] using hsa0
        · simpa [hb, h10] using htb1
        · simpa [hb, h01] using htb0
        · intro x hx z hz hxz
          simpa [ha, hb, h01, h10, or_comm] using hcross x hx z hz hxz
    · rcases hpair with ⟨h00, h11⟩ | ⟨h01, h10⟩
      · refine ⟨q.reverse, t, s,
            Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq, by simpa, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx
          exact hqF x (List.mem_reverse.mp hx)
        · simpa [hb, h00] using htb0
        · simpa [hb, h11] using htb1
        · simpa [ha, h00] using hsa0
        · simpa [ha, h11] using hsa1
        · intro x hx z hz hxz
          rcases hcross x (List.mem_reverse.mp hx) z hz hxz with hc | hc
          · exact Or.inr ⟨hc.1, by simpa [ha, h00, h11] using hc.2⟩
          · exact Or.inl ⟨hc.1, by simpa [hb, h00, h11] using hc.2⟩
      · refine ⟨q.reverse, t, s,
            Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hq, by simpa, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro x hx
          exact hqF x (List.mem_reverse.mp hx)
        · simpa [hb, h10] using htb1
        · simpa [hb, h01] using htb0
        · simpa [ha, h10] using hsa1
        · simpa [ha, h01] using hsa0
        · intro x hx z hz hxz
          rcases hcross x (List.mem_reverse.mp hx) z hz hxz with hc | hc
          · exact Or.inr ⟨hc.1, by simpa [ha, h01, h10, or_comm] using hc.2⟩
          · exact Or.inl ⟨hc.1, by simpa [hb, h01, h10, or_comm] using hc.2⟩
  · obtain ⟨hsa0, hsa1, ⟨y, hy, -, hty⟩, -⟩ := hcase4
    have he : σ (σ.symm 2) = 2 := Equiv.apply_symm_apply σ 2
    have hi : σ.symm 2 = 0 ∨ σ.symm 2 = 1 ∨ σ.symm 2 = 2 := by
      have hfin : ∀ z : Fin 3, z = 0 ∨ z = 1 ∨ z = 2 := by decide
      exact hfin (σ.symm 2)
    rcases hi with hi | hi | hi
    · have hs0 : σ 0 = 2 := by rw [← hi]; exact he
      exact (hnoR2 s hsF (a' 0) (hs0 ▸ ha'mem 0) hsa0).elim
    · have hs1 : σ 1 = 2 := by rw [← hi]; exact he
      exact (hnoR2 s hsF (a' 1) (hs1 ▸ ha'mem 1) hsa1).elim
    · rw [hi] at he
      have hyR2 : y ∈ R 2 := by rw [← he, ← hR'mem 2]; exact hy
      exact (hnoR2 t htF y hyR2 hty).elim

/-- **12.3 (1)**: *"We may assume that none of `f₁, …, f_k` is a right-star, and that `f_k` is
not `B`-complete."*  ("We may assume" because the alternative — a right-star in `F` — already
exhibits the banister `f₁`-…-`f_k` that 12.3 asks for.) -/
theorem claim1 [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk) :
    (∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G A C B u R v) ∨
      ((∀ w ∈ f, ¬ IsRightStar G A C B w) ∧ ¬ SPGT.VertexComplete G fk B) := by
  classical
  obtain ⟨hCand, hmin, hF, hpath, hlen, hleft, hleftuniq, hfkatt, hattuniq, hnomajor⟩ := hS
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? (by rw [hpath.2.1]; rfl)
  have hfkmem : fk ∈ f := List.mem_of_mem_getLast? (by rw [hpath.2.2]; rfl)
  have hf₁fk : f₁ ≠ fk := by
    rintro rfl
    obtain ⟨y, hy, hadj⟩ := hfkatt
    exact hleft.2.2 y hy hadj
  have hmemtail : ∀ z : V, z ∈ f.tail ↔ z ∈ f ∧ z ≠ f₁ := by
    intro z
    rcases f with _ | ⟨c, t⟩
    · exact (hpath.1.1 rfl).elim
    have hc : c = f₁ := by simpa using hpath.2.1
    subst c
    have hnotmem : f₁ ∉ t :=
      (List.nodup_cons.mp (Workspace.ProofLemmas.PathBasics.path_nodup hpath.1)).1
    simp only [List.tail_cons, List.mem_cons]
    constructor
    · intro hz
      exact ⟨Or.inr hz, fun h => hnotmem (h ▸ hz)⟩
    · rintro ⟨hz | hz, hne⟩
      · exact (hne hz).elim
      · exact hz
  by_cases hrs : ∃ w ∈ f, IsRightStar G A C B w
  · left
    obtain ⟨w, hwf, hwright⟩ := hrs
    obtain ⟨b, hbB⟩ := hK.1.1.2.1.2
    have hwfk : w = fk :=
      hattuniq w hwf ⟨b, Or.inl hbB, hwright.2.1 b hbB⟩
    subst w
    refine ⟨f₁, fk, f, ?_, hpath, ?_, hleft, hwright, ?_⟩
    · intro z hz
      rw [hF]
      exact hz
    · intro z hz
      exact hCand.1 (by rw [hF]; exact hz)
    · intro u hu x hx hux
      have huData := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hpath).mp hu
      obtain ⟨huf, huf₁, hufk⟩ := huData
      rcases hx with (hxA | hxB) | hxC
      · have hutail : u ∈ f.tail := (hmemtail u).2 ⟨huf, huf₁⟩
        have htailPath : SPGT.IsPathList G f.tail := by
          simpa only [List.drop_one] using
            (Workspace.ProofLemmas.PathBasics.isPathList_drop hpath.1
              (show 1 < f.length by omega))
        have htailSub : {z : V | z ∈ f.tail} ⊆ F := by
          intro z hz
          rw [hF]
          exact (hmemtail z).1 hz |>.1
        have hfkTail : fk ∈ f.tail := (hmemtail fk).2 ⟨hfkmem, hf₁fk.symm⟩
        have htailCand : Cand G B C A {z : V | z ∈ f.tail} := by
          refine ⟨?_,
            Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
              htailPath, ?_, ?_⟩
          · intro z hz
            have hzout := hCand.1 (htailSub hz)
            simp only [Set.mem_compl_iff, Set.mem_union] at hzout ⊢
            tauto
          · refine ⟨fk, hfkTail, ?_⟩
            simp only [IsLeftStar, IsRightStar, Set.mem_union] at hwright ⊢
            tauto
          · refine ⟨x, ?_⟩
            exact ⟨Or.inl hxA, u, hutail, hux.symm⟩
        have htailEq : {z : V | z ∈ f.tail} = F :=
          hmin _ htailSub (Or.inr htailCand)
        have hf₁Tail : f₁ ∈ f.tail := by
          have : f₁ ∈ F := by rw [hF]; exact hf₁mem
          rw [← htailEq] at this
          exact this
        exact ((hmemtail f₁).1 hf₁Tail).2 rfl
      · exact hufk (hattuniq u huf ⟨x, Or.inl hxB, hux⟩)
      · exact hufk (hattuniq u huf ⟨x, Or.inr hxC, hux⟩)
  · right
    have hnors : ∀ w ∈ f, ¬ IsRightStar G A C B w := by
      intro w hw hright
      exact hrs ⟨w, hw, hright⟩
    refine ⟨hnors, ?_⟩
    have hfkF : fk ∈ F := by rw [hF]; exact hfkmem
    have hnorFk : ¬ IsRightStar G A C B fk := hnors fk hfkmem
    have hban₀ := hK.1.2.1
    have hfka₀ : fk ≠ a₀ := by
      intro heq
      obtain ⟨y, hy, hadj⟩ := hfkatt
      exact hban₀.2.2.1.2.2 y hy (heq ▸ hadj)
    have hfkb₀ : fk ≠ b₀ := by
      intro heq
      apply hnorFk
      rw [heq]
      exact hban₀.2.2.2.1
    have hfkR₀ : fk ∉ R₀ := by
      intro hmem
      have hint : fk ∈ SPGT.interior R₀ :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hban₀.1).2
          ⟨hmem, hfka₀, hfkb₀⟩
      obtain ⟨y, hy, hadj⟩ := hfkatt
      have hyABC : y ∈ A ∪ B ∪ C := by
        rcases hy with hyB | hyC
        · exact Or.inl (Or.inr hyB)
        · exact Or.inr hyC
      exact hban₀.2.2.2.2 fk hint y hyABC hadj
    have hfkOutside : fk ∉ staircaseVertices A C B R₀ := by
      intro hmem
      rcases hmem with hR | hABC
      · exact hfkR₀ hR
      · exact hCand.1 hfkF hABC
    obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1
      G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK fk hfkOutside
    fin_cases i
    · exact hi.2.2.resolve_left hnorFk
    · exact (hnomajor fk hfkF hi.1).elim
    · rcases hi with hleftFk | hrightFk
      · obtain ⟨y, hy, hadj⟩ := hfkatt
        exact (hleftFk.1.2.2 y hy hadj).elim
      · exact (hnorFk hrightFk.1).elim

/-- **12.3 (2)**: *"`F ∩ V(R₀) = ∅`, and there are no edges between `{f₂, …, f_k}` and
`V(R₀ \ b₀)`."* -/
theorem claim2 [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk)
    (hnors : ∀ w ∈ f, ¬ IsRightStar G A C B w)
    (hnotB : ¬ SPGT.VertexComplete G fk B) :
    (∀ w ∈ f, w ∉ R₀) ∧
      SPGT.Anticomplete G {w : V | w ∈ f ∧ w ≠ f₁} {x : V | x ∈ R₀ ∧ x ≠ b₀} := by
  classical
  obtain ⟨⟨hFsub, -, -, -⟩, -, hFeq, hfpath, hflen, hf₁ls, hf₁uniq, ⟨y0, hy0BC, hfky0⟩,
    honly, hnomaj⟩ := hS
  have hban := hK.1.2.1
  obtain ⟨⟨hAB, hAC, -⟩, -, -, -, -⟩ := hK.1.1
  have hpos : 0 < f.length := by omega
  have hf0 : f[0]'hpos = f₁ := PathBasics.getElem_zero_of_head? hfpath.2.1 hpos
  have hflast : f[f.length - 1]'(by omega) = fk :=
    PathBasics.getElem_last_of_getLast? hfpath.2.2 hpos
  have hfnodup : f.Nodup := hfpath.1.2.1
  have hgetInj : ∀ (a b : ℕ) (ha : a < f.length) (hb : b < f.length),
      f[a]'ha = f[b]'hb → a = b := by
    intro a b ha hb h
    exact (List.Nodup.getElem_inj_iff hfnodup).mp h
  have hgetEq : ∀ (a b : ℕ) (ha : a < f.length) (hb : b < f.length),
      a = b → f[a]'ha = f[b]'hb := by
    intro a b ha hb h; subst h; rfl
  have hBCsub : ∀ z ∈ B ∪ C, z ∈ A ∪ B ∪ C := by
    intro z hz; rcases hz with h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
  have hfVS : ∀ w ∈ f, w ∉ A ∪ B ∪ C := by
    intro w hw
    exact hFsub (by rw [hFeq]; exact hw)
  have ha₀R₀ : a₀ ∈ R₀ := List.mem_of_mem_head? hban.1.2.1
  -- *"For by (1), `b₀ ∉ F`."*  `b₀` is a right-star, and by (1) no vertex of `f` is one.
  have hb₀ : b₀ ∉ f := fun hc => hnors b₀ hc hban.2.2.2.1
  -- *"Suppose that either `{f₂,…,f_k}` intersects `V(R₀ \ b₀)`, or there is an edge joining
  -- these two sets."*  We show no such index exists.
  have hnobad : ∀ (j : ℕ) (hj : j < f.length), 1 ≤ j →
      (f[j]'hj) ∉ R₀ ∧ ∀ x ∈ R₀, x ≠ b₀ → ¬ G.Adj (f[j]'hj) x := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨j0, hj0, hj01, hj0bad⟩ := hcon
    set P : ℕ → Prop := fun j => 1 ≤ j ∧ ∃ hj : j < f.length,
      ((f[j]'hj) ∈ R₀ ∨ ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj (f[j]'hj) x) with hP
    have hPj0 : P j0 := by
      refine ⟨hj01, hj0, ?_⟩
      by_cases hm : (f[j0]'hj0) ∈ R₀
      · exact Or.inl hm
      · obtain ⟨x, hxR, hxb, hxadj⟩ := hj0bad hm
        exact Or.inr ⟨x, hxR, hxb, hxadj⟩
    -- *"Choose `i` with `2 ≤ i ≤ k` maximum such that either `f_i ∈ V(R₀ \ b₀)` or `f_i` has a
    -- neighbour in `V(R₀ \ b₀)`."*
    obtain ⟨i, hBi, hmax⟩ : ∃ i, P i ∧ ∀ j, i < j → j ≤ f.length → ¬ P j :=
      ⟨Nat.findGreatest P f.length, Nat.findGreatest_spec (le_of_lt hj0) hPj0,
        fun j h1 h2 => Nat.findGreatest_is_greatest h1 h2⟩
    obtain ⟨hi1, hilt, hBi'⟩ := hBi
    -- *"We claim that `f_i ∉ V(R₀)`."*
    have hfiR : (f[i]'hilt) ∉ R₀ := by
      rcases Nat.lt_or_ge (i + 1) f.length with hnext | hnext
      · -- *"if `i < k` then `f_{i+1}` has no neighbour in `V(R₀ \ b₀)` from the maximality of `i`"*
        intro hmem
        refine hmax (i + 1) (by omega) (by omega) ⟨by omega, hnext, Or.inr
          ⟨f[i]'hilt, hmem, ?_, (PathBasics.path_adj_succ hfpath.1 hnext).symm⟩⟩
        intro hc
        exact hb₀ (hc ▸ List.getElem_mem hilt)
      · -- *"if `i = k` this is true, since `f_k` has neighbours in `B ∪ C`"*
        have hie : i = f.length - 1 := by omega
        have hik : (f[i]'hilt) = fk := by
          rw [hgetEq i (f.length - 1) hilt (by omega) hie]; exact hflast
        rw [hik]
        intro hmem
        by_cases hfa : fk = a₀
        · exact hban.2.2.1.2.2 y0 hy0BC (hfa ▸ hfky0)
        · by_cases hfb : fk = b₀
          · exact hb₀ (hfb ▸ (List.mem_of_mem_getLast? hfpath.2.2))
          · exact hban.2.2.2.2 fk
              ((PathBasics.mem_interior_iff_of_pathFrom hban.1).mpr ⟨hmem, hfa, hfb⟩)
              y0 (hBCsub y0 hy0BC) hfky0
    -- *"So none of `f_i, …, f_k` belong to `V(R₀)`."*
    have hno : ∀ (j : ℕ) (hj : j < f.length), i ≤ j → (f[j]'hj) ∉ R₀ := by
      intro j hj hij
      rcases eq_or_lt_of_le hij with rfl | hlt
      · exact hfiR
      · intro hmem
        exact hmax j hlt (by omega) ⟨by omega, hj, Or.inl hmem⟩
    -- the set `{f_i, …, f_k}`
    have hfS : ∀ w ∈ f.drop i, w ∈ f := fun w hw => (List.drop_sublist i f).subset hw
    have hmemS : ∀ w ∈ f.drop i, ∃ (k : ℕ) (hk : k < f.length), i ≤ k ∧ f[k]'hk = w := by
      intro w hw
      obtain ⟨j, hj, hjw⟩ := List.mem_iff_getElem.mp hw
      rw [List.length_drop] at hj
      refine ⟨i + j, by omega, by omega, ?_⟩
      rw [← hjw]; simp [List.getElem_drop]
    have hmemS' : ∀ (k : ℕ) (hk : k < f.length), i ≤ k → (f[k]'hk) ∈ f.drop i := by
      intro k hk hik
      have hlt : k - i < (f.drop i).length := by rw [List.length_drop]; omega
      have hmm := List.getElem_mem hlt
      have hik' : i + (k - i) = k := by omega
      have heq : (f.drop i)[k - i]'hlt = f[k]'hk := by
        simp only [List.getElem_drop, hik']
      rwa [heq] at hmm
    have hfiS : (f[i]'hilt) ∈ f.drop i := hmemS' i hilt le_rfl
    have hfkS : fk ∈ f.drop i := by
      have := hmemS' (f.length - 1) (by omega) (by omega)
      rwa [hflast] at this
    have hFK : {w : V | w ∈ f.drop i} ⊆ (staircaseVertices A C B R₀)ᶜ := by
      intro w hw
      obtain ⟨k, hk, hik, hkw⟩ := hmemS w hw
      rintro (hR | hVS)
      · exact hno k hk hik (hkw ▸ hR)
      · exact hfVS w (hfS w hw) hVS
    have hFconn : SPGT.ConnectedSet G {w : V | w ∈ f.drop i} :=
      InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (PathBasics.isPathList_drop hfpath.1 hilt)
    -- *"`{f_i,…,f_k}` has attachments in `V(R₀ \ b₀)` and in `B ∪ C`"*
    obtain ⟨x0, hx0R₀, hx0ne, hx0adj⟩ : ∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj (f[i]'hilt) x := by
      rcases hBi' with hc | hc
      · exact absurd hc hfiR
      · exact hc
    have hx0att : x0 ∈ attachments G {w : V | w ∈ f.drop i} (staircaseVertices A C B R₀) :=
      ⟨Or.inl hx0R₀, f[i]'hilt, hfiS, hx0adj.symm⟩
    have hy0att : y0 ∈ attachments G {w : V | w ∈ f.drop i} (staircaseVertices A C B R₀) :=
      ⟨Or.inr (hBCsub y0 hy0BC), fk, hfkS, hfky0.symm⟩
    have hloc : ¬ LocalForStaircase A C B a₀ R₀ b₀
        (attachments G {w : V | w ∈ f.drop i} (staircaseVertices A C B R₀)) := by
      rintro (h | h | h | h)
      · exact hban.2.1 x0 hx0R₀ (h hx0att)
      · exact hban.2.1 y0 (h hy0att) (hBCsub y0 hy0BC)
      · rcases h hy0att with hA | hEq
        · rcases hy0BC with hB | hC
          · exact (Set.disjoint_left.mp hAB hA) hB
          · exact (Set.disjoint_left.mp hAC hA) hC
        · exact hban.2.1 a₀ ha₀R₀ ((hEq : y0 = a₀) ▸ hBCsub y0 hy0BC)
      · rcases h hx0att with hB | hEq
        · exact hban.2.1 x0 hx0R₀ (Or.inl (Or.inr hB))
        · exact hx0ne hEq
    -- *"this contradicts 12.2"*
    rcases _root_.Workspace.Statements.S12.SPGT.thm_12_2 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀
        hK {w : V | w ∈ f.drop i} hFK hFconn hloc with
      ⟨w, hwS, hwmaj⟩ | ⟨u, v, R, hRsub, hban', -⟩ | ⟨u, v, R, hRsub, hRpath, hcase⟩
    · exact hnomaj w (by rw [hFeq]; exact hfS w hwS) hwmaj
    · exact hnors v (hfS v (hRsub v (PathBasics.isPathFrom_ends_mem hban'.1).2))
        hban'.2.2.2.1
    · have huf : u ∈ f := hfS u (hRsub u (PathBasics.isPathFrom_ends_mem hRpath).1)
      rcases hcase with ⟨hls, -, -⟩ | ⟨hrs', -, -⟩
      · have hu1 : u = f₁ := hf₁uniq u huf hls
        obtain ⟨k, hk, hik, hkw⟩ :=
          hmemS u (hRsub u (PathBasics.isPathFrom_ends_mem hRpath).1)
        have : k = 0 := hgetInj k 0 hk hpos (by rw [hkw, hu1, hf0])
        omega
      · exact hnors u huf hrs'
  -- the two conclusions
  constructor
  · -- *"`{f₂,…,f_k}` is disjoint from `V(R₀)` … and so `F ∩ V(R₀) = ∅`"*
    intro w hw
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hw
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · -- *"Since there is an edge between `{f₂,…,f_k}` and `f₁` it follows that `f₁ ∉ V(R₀)`."*
      intro hmem
      have h1 : (1 : ℕ) < f.length := by omega
      exact (hnobad 1 h1 le_rfl).2 (f[0]'hpos) hmem
        (fun hc => hb₀ (hc ▸ List.getElem_mem hpos))
        (PathBasics.path_adj_succ hfpath.1 h1).symm
    · exact (hnobad j hj hj1).1
  · -- *"there are no edges between `{f₂,…,f_k}` and `V(R₀ \ b₀)`"*
    rintro w ⟨hwf, hwne⟩ x ⟨hxR, hxb⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hwf
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    · exact absurd hf0 hwne
    · exact (hnobad j hj hj1).2 x hxR hxb

/-- The unnumbered paragraph after (2): *"Let `a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` be a step such that
`f_k` has a neighbour in `R₁ \ a₁` and `f_k` is nonadjacent to `b₂`.  (To see that such a step
exists, we argue as follows: since `f_k` has a neighbour in `B ∪ C`, there is a step
`a₁`-`R₁`-`b₁`, `a₂`-`R₂`-`b₂` such that `f_k` has a neighbour in `R₁ \ a₁`, and so we may assume
that `f_k` is adjacent to `b₂`.  Hence `f_k` has a neighbour and a nonneighbour in `B`, and the
required step exists since the strip is step-connected.)"* -/
theorem stepChoice [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk)
    (hnotB : ¬ SPGT.VertexComplete G fk B) :
    ∃ (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V),
      IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧
        (∃ x ∈ R₁, x ≠ a₁ ∧ G.Adj fk x) ∧ ¬ G.Adj fk b₂ := by
  obtain ⟨hsc, -, -⟩ := hK.1
  obtain ⟨⟨hAB, hAC, -⟩, -, -, hstepcover, hpart⟩ := hsc
  obtain ⟨-, -, -, -, -, -, -, ⟨y, hyBC, hfky⟩, -, -⟩ := hS
  by_cases hBnb : ∃ b ∈ B, G.Adj fk b
  · obtain ⟨b, hbB, hfkb⟩ := hBnb
    have hnon : ∃ b' ∈ B, ¬ G.Adj fk b' := by
      by_contra hcon
      push Not at hcon
      exact hnotB hcon
    obtain ⟨b', hb'B, hnb'⟩ := hnon
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hX, hY⟩ :=
      hpart {x : V | x ∈ B ∧ G.Adj fk x} {x : V | x ∈ B ∧ ¬ G.Adj fk x}
        (Or.inr (by
          ext z
          simp only [Set.mem_union, Set.mem_setOf_eq]
          constructor
          · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
          · intro hz
            by_cases hzz : G.Adj fk z
            · exact Or.inl ⟨hz, hzz⟩
            · exact Or.inr ⟨hz, hzz⟩))
        (Set.disjoint_left.mpr (fun _ hz hz' => hz'.2 hz.2))
        ⟨b, hbB, hfkb⟩ ⟨b', hb'B, hnb'⟩
    have ha₁A : a₁ ∈ A := hstep.1.2.1
    have ha₂A : a₂ ∈ A := hstep.2.1.2.1
    have hb₁X : b₁ ∈ {x : V | x ∈ B ∧ G.Adj fk x} := by
      rcases hX with h | h
      · exact absurd h.1 (Set.disjoint_left.mp hAB ha₁A)
      · exact h
    have hb₂Y : b₂ ∈ {x : V | x ∈ B ∧ ¬ G.Adj fk x} := by
      rcases hY with h | h
      · exact absurd h.1 (Set.disjoint_left.mp hAB ha₂A)
      · exact h
    refine ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep,
      ⟨b₁, List.mem_of_mem_getLast? hstep.1.1.2.2, ?_, hb₁X.2⟩, hb₂Y.2⟩
    rintro rfl
    exact (Set.disjoint_left.mp hAB ha₁A) hb₁X.1
  · push Not at hBnb
    have hyC : y ∈ C := by
      rcases hyBC with h | h
      · exact absurd hfky (hBnb y h)
      · exact h
    obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hy⟩ :=
      hstepcover y (Set.mem_union_right _ hyC)
    have hAC' : ∀ z ∈ A, z ∉ C := fun _ hz => Set.disjoint_left.mp hAC hz
    rcases hy with hy1 | hy2
    · refine ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, ⟨y, hy1, ?_, hfky⟩, hBnb b₂ hstep.2.1.2.2.1⟩
      rintro rfl
      exact hAC' y hstep.1.2.1 hyC
    · refine ⟨a₂, R₂, b₂, a₁, R₁, b₁, isStep_symm hstep, ⟨y, hy2, ?_, hfky⟩,
        hBnb b₁ hstep.1.2.2.1⟩
      rintro rfl
      exact hAC' y hstep.2.1.2.1 hyC

/-- **12.3 (3)**: *"`f₁a₂` is the only edge between `F` and `R₂`."*  (That `f₁a₂` **is** an edge
is immediate: `f₁` is a left-star, hence `A`-complete, and `a₂ ∈ A`.) -/
theorem claim3 [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk)
    (hnors : ∀ w ∈ f, ¬ IsRightStar G A C B w)
    (hnotB : ¬ SPGT.VertexComplete G fk B)
    (hdisj : ∀ w ∈ f, w ∉ R₀)
    (hanti : SPGT.Anticomplete G {w : V | w ∈ f ∧ w ≠ f₁} {x : V | x ∈ R₀ ∧ x ≠ b₀})
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hfk₁ : ∃ x ∈ R₁, x ≠ a₁ ∧ G.Adj fk x) (hfkb₂ : ¬ G.Adj fk b₂) :
    ∀ u ∈ f, ∀ v ∈ R₂, (G.Adj u v ↔ (u = f₁ ∧ v = a₂)) := by
  classical
  obtain ⟨⟨hFout, hFconn, -, -⟩, hmin, hFeq, hfpath, hflen, hf₁left, hf₁uniq,
    hfkatt, hattuniq, hnomajor⟩ := hS
  obtain ⟨hstrip, hban, -⟩ := hK.1
  obtain ⟨⟨hAB, hAC, hBC⟩, -, -, -, -⟩ := hstrip
  obtain ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩ := hstep
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? hfpath.2.1
  have hfkmem : fk ∈ f := List.mem_of_mem_getLast? hfpath.2.2
  have hf₁fk : f₁ ≠ fk := by
    rintro rfl
    obtain ⟨y, hy, hadj⟩ := hfkatt
    exact hf₁left.2.2 y hy hadj
  have hR₁S := claim3_rung_mem_ABC hr₁
  have hR₂S := claim3_rung_mem_ABC hr₂
  have ha₀b₀ : a₀ ≠ b₀ := by
    intro e
    have hadj := hban.2.2.1.2.1 a₁ hr₁.2.1
    rw [e] at hadj
    exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) hadj
  have ha₁R₁ : a₁ ∈ R₁ := List.mem_of_mem_head? hr₁.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ := List.mem_of_mem_getLast? hr₁.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := List.mem_of_mem_head? hr₂.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := List.mem_of_mem_getLast? hr₂.1.2.2
  have ha₀R₀ : a₀ ∈ R₀ := List.mem_of_mem_head? hban.1.2.1
  have hb₀R₀ : b₀ ∈ R₀ := List.mem_of_mem_getLast? hban.1.2.2
  have hcross₀₁ := claim3_banister_rung_edges hban hr₁
  have hcross₀₂ := claim3_banister_rung_edges hban hr₂
  have hcross₁₀ : ∀ u ∈ R₁, ∀ v ∈ R₀,
      (G.Adj u v ↔ (u = a₁ ∧ v = a₀) ∨ (u = b₁ ∧ v = b₀)) := by
    intro u hu v hv
    constructor
    · intro huv
      rcases (hcross₀₁ v hv u hu).mp huv.symm with h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr ⟨h.2, h.1⟩
    · intro h
      rcases h with h | h
      · exact h.1 ▸ h.2 ▸
          ((hcross₀₁ a₀ ha₀R₀ a₁ ha₁R₁).mpr (Or.inl ⟨rfl, rfl⟩)).symm
      · exact h.1 ▸ h.2 ▸
          ((hcross₀₁ b₀ hb₀R₀ b₁ hb₁R₁).mpr (Or.inr ⟨rfl, rfl⟩)).symm
  have hcross₂₀ : ∀ u ∈ R₂, ∀ v ∈ R₀,
      (G.Adj u v ↔ (u = a₂ ∧ v = a₀) ∨ (u = b₂ ∧ v = b₀)) := by
    intro u hu v hv
    constructor
    · intro huv
      rcases (hcross₀₂ v hv u hu).mp huv.symm with h | h
      · exact Or.inl ⟨h.2, h.1⟩
      · exact Or.inr ⟨h.2, h.1⟩
    · intro h
      rcases h with h | h
      · exact h.1 ▸ h.2 ▸
          ((hcross₀₂ a₀ ha₀R₀ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩)).symm
      · exact h.1 ▸ h.2 ▸
          ((hcross₀₂ b₀ hb₀R₀ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)).symm
  have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ := by
    exact Workspace.ProofLemmas.PrismBasics.formPrism_of_data
      ((hcross₁₂ a₁ ha₁R₁ a₂ ha₂R₂).mpr (Or.inl ⟨rfl, rfl⟩))
      (hban.2.2.1.2.1 a₁ hr₁.2.1).symm
      (hban.2.2.1.2.1 a₂ hr₂.2.1).symm
      ((hcross₁₂ b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩))
      (hban.2.2.2.1.2.1 b₁ hr₁.2.2.1).symm
      (hban.2.2.2.1.2.1 b₂ hr₂.2.2.1).symm
      (by intro e; exact (Set.disjoint_left.mp hAB (e ▸ hr₁.2.1)) hr₁.2.2.1)
      (by intro e; exact (Set.disjoint_left.mp hAB (e ▸ hr₁.2.1)) hr₂.2.2.1)
      (by intro e; exact hban.2.1 b₀ hb₀R₀ (e ▸ hR₁S a₁ ha₁R₁))
      (by intro e; exact (Set.disjoint_left.mp hAB (e ▸ hr₂.2.1)) hr₁.2.2.1)
      (by intro e; exact (Set.disjoint_left.mp hAB (e ▸ hr₂.2.1)) hr₂.2.2.1)
      (by intro e; exact hban.2.1 b₀ hb₀R₀ (e ▸ hR₂S a₂ ha₂R₂))
      (by intro e; exact hban.2.1 a₀ ha₀R₀ (e ▸ hR₁S b₁ hb₁R₁))
      (by intro e; exact hban.2.1 a₀ ha₀R₀ (e ▸ hR₂S b₂ hb₂R₂))
      (by
        intro e
        have hadj := hban.2.2.1.2.1 a₁ hr₁.2.1
        exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) (e ▸ hadj))
      hr₁.1 hr₂.1 hban.1 hcross₁₂ hcross₁₀ hcross₂₀
  have hK4' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K', happ, -⟩
    exact hK4 ⟨n, H, K', happ⟩
  obtain ⟨x₁, hx₁R₁, hx₁ne, hfkx₁⟩ := hfk₁
  have hx₁BC : x₁ ∈ B ∪ C := claim3_rung_mem_BC_of_ne_left hr₁ hx₁R₁ hx₁ne
  have hfkNoR₂ : ∀ v ∈ R₂, ¬ G.Adj fk v := by
    intro v hvR₂ hfkv
    have hvne : v ≠ b₂ := fun e => hfkb₂ (e ▸ hfkv)
    have hfknotK : fk ∉ {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀} := by
      rintro ((h | h) | h)
      · exact hFout (by rw [hFeq]; exact hfkmem) (hR₁S fk h)
      · exact hFout (by rw [hFeq]; exact hfkmem) (hR₂S fk h)
      · exact hdisj fk hfkmem h
    have hx₁att : x₁ ∈ attachments G ({fk} : Set V)
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) :=
      ⟨Or.inl (Or.inl hx₁R₁), fk, by simp, hfkx₁.symm⟩
    have hvatt : v ∈ attachments G ({fk} : Set V)
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) :=
      ⟨Or.inl (Or.inr hvR₂), fk, by simp, hfkv.symm⟩
    have hnotlocal : ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀
        (attachments G ({fk} : Set V)
          ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀})) := by
      rintro (h | h | h | h | h)
      · exact hR₁R₂ v (h hvatt) hvR₂
      · exact hR₁R₂ x₁ hx₁R₁ (h hx₁att)
      · exact hban.2.1 x₁ (h hx₁att) (hR₁S x₁ hx₁R₁)
      · have hx := h hx₁att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with e | e | e
        · exact hx₁ne e
        · exact hR₁R₂ x₁ hx₁R₁ (e ▸ ha₂R₂)
        · exact hban.2.1 a₀ ha₀R₀ (e ▸ hR₁S x₁ hx₁R₁)
      · have hv' := h hvatt
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hv'
        rcases hv' with e | e | e
        · exact hR₁R₂ b₁ hb₁R₁ (e ▸ hvR₂)
        · exact hvne e
        · exact hban.2.1 b₀ hb₀R₀ (e ▸ hR₂S v hvR₂)
    have hR₀nbr : ∃ z ∈ R₀, G.Adj fk z := by
      by_contra hn
      push Not at hn
      have hnoneR₀ : ∀ z ∈ attachments G ({fk} : Set V)
          ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}), z ∉ R₀ := by
        intro z hz hzR₀
        obtain ⟨-, w, hw, hzw⟩ := hz
        simp only [Set.mem_singleton_iff] at hw
        subst w
        exact hn z hzR₀ hzw.symm
      have hres := Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4'
        ![a₁, a₂, a₀] ![b₁, b₂, b₀] ![R₁, R₂, R₀]
        ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) ({fk} : Set V)
        hform rfl (by simpa using hfknotK) (by simp [ConnectedSet])
        (by intro hev; exact (hprism ⟨_, _, _, _, _, hev⟩).elim)
        hnotlocal hnoneR₀
      have hb₂att : b₂ ∈ attachments G ({fk} : Set V)
          ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}) := by
        rw [hres.2]
        simp
      obtain ⟨-, w, hw, hb₂w⟩ := hb₂att
      simp only [Set.mem_singleton_iff] at hw
      subst w
      exact hfkb₂ hb₂w.symm
    have hfkOutside : fk ∉ staircaseVertices A C B R₀ := by
      rintro (hR | hS)
      · exact hdisj fk hfkmem hR
      · exact hFout (by rw [hFeq]; exact hfkmem) hS
    obtain ⟨i, hi, -⟩ := Workspace.Statements.S12.SPGT.thm_12_1
      G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK fk hfkOutside
    fin_cases i
    · obtain ⟨hminor, -, -⟩ := hi
      rcases hR₀nbr with ⟨z, hzR₀, hfkz⟩
      have hzN : z ∈ G.neighborSet fk ∩ staircaseVertices A C B R₀ :=
        ⟨hfkz, Or.inl hzR₀⟩
      have hx₁N : x₁ ∈ G.neighborSet fk ∩ staircaseVertices A C B R₀ :=
        ⟨hfkx₁, Or.inr (match hx₁BC with
          | Or.inl h => Or.inl (Or.inr h)
          | Or.inr h => Or.inr h)⟩
      have hvN : v ∈ G.neighborSet fk ∩ staircaseVertices A C B R₀ :=
        ⟨hfkv, Or.inr (hR₂S v hvR₂)⟩
      rcases hminor.2 with h | h | h | h
      · exact hban.2.1 z hzR₀ (h hzN)
      · exact hban.2.1 x₁ (h hx₁N) (hR₁S x₁ hx₁R₁)
      · rcases h (hx₁N) with hxA | hxa₀
        · rcases hx₁BC with hxB | hxC
          · exact (Set.disjoint_left.mp hAB hxA) hxB
          · exact (Set.disjoint_left.mp hAC hxA) hxC
        · exact hban.2.1 a₀ ha₀R₀ (hxa₀ ▸ hR₁S x₁ hx₁R₁)
      · rcases h hvN with hvB | hvb₀
        · have hvnea₂ : v ≠ a₂ := by
            intro e
            subst v
            exact (Set.disjoint_left.mp hAB hr₂.2.1) hvB
          rcases claim3_rung_mem_BC_of_ne_left hr₂ hvR₂ hvnea₂ with hvB' | hvC
          · have evb₂ : v = b₂ := hr₂.2.2.2.2.1 v hvR₂ hvB
            exact hfkb₂ (evb₂ ▸ hfkv)
          · exact (Set.disjoint_left.mp hBC hvB) hvC
        · exact hban.2.1 b₀ hb₀R₀ (hvb₀ ▸ hR₂S v hvR₂)
    · exact (hnomajor fk (by rw [hFeq]; exact hfkmem) hi.1).elim
    · rcases hi with hleft | hright
      · obtain ⟨y, hy, hfky⟩ := hfkatt
        exact (hleft.1.2.2 y hy hfky).elim
      · exact (hnors fk hfkmem hright.1).elim
  have hNoTailA₂ : ∀ u ∈ f, u ≠ f₁ → ¬ G.Adj u a₂ := by
    intro u hu huf₁ hua₂
    obtain ⟨j, hj, hju⟩ := List.mem_iff_getElem.mp hu
    have hpos : 0 < f.length := by omega
    have hf0 : f[0]'hpos = f₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 hpos
    have hjpos : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hjpos
      · exact (huf₁ (by rw [← hju]; exact hf0)).elim
      · exact hjpos
    have hfnodup : f.Nodup := hfpath.1.2.1
    have hgetInj : ∀ (r s : ℕ) (hr : r < f.length) (hs : s < f.length),
        f[r]'hr = f[s]'hs → r = s := by
      intro r s hr hs hrs
      exact (List.Nodup.getElem_inj_iff hfnodup).mp hrs
    have hfS : ∀ w ∈ f.drop j, w ∈ f :=
      fun w hw => (List.drop_sublist j f).subset hw
    have hmemS : ∀ w ∈ f.drop j,
        ∃ (r : ℕ) (hr : r < f.length), j ≤ r ∧ f[r]'hr = w := by
      intro w hw
      obtain ⟨s, hs, hsw⟩ := List.mem_iff_getElem.mp hw
      rw [List.length_drop] at hs
      refine ⟨j + s, by omega, by omega, ?_⟩
      rw [← hsw, List.getElem_drop]
    have hmemS' : ∀ (r : ℕ) (hr : r < f.length), j ≤ r → f[r]'hr ∈ f.drop j := by
      intro r hr hjr
      have hs : r - j < (f.drop j).length := by rw [List.length_drop]; omega
      have hm := List.getElem_mem hs
      have heq : (f.drop j)[r - j]'hs = f[r]'hr := by
        simp only [List.getElem_drop]
        congr 1
        omega
      rwa [heq] at hm
    have hfjS : f[j]'hj ∈ f.drop j := hmemS' j hj le_rfl
    have hfkS : fk ∈ f.drop j := by
      have hm := hmemS' (f.length - 1) (by omega) (by omega)
      rwa [Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hfpath.2.2 hpos] at hm
    have htail_ne_f₁ : ∀ w ∈ f.drop j, w ≠ f₁ := by
      intro w hw heq
      obtain ⟨r, hr, hjr, hrw⟩ := hmemS w hw
      have hr0 : f[r]'hr = f[0]'hpos := by rw [hrw, heq, hf0]
      have : r = 0 := hgetInj r 0 hr hpos hr0
      omega
    let KP : Set V :=
      {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}
    let FT : Set V := {w : V | w ∈ f.drop j}
    have hFTK : FT ⊆ KPᶜ := by
      intro w hw
      change w ∈ f.drop j at hw
      change w ∉ ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀})
      rintro ((h | h) | h)
      · exact hFout (by rw [hFeq]; exact hfS w hw) (hR₁S w h)
      · exact hFout (by rw [hFeq]; exact hfS w hw) (hR₂S w h)
      · exact hdisj w (hfS w hw) h
    have hFTconn : ConnectedSet G FT := by
      exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (Workspace.ProofLemmas.PathBasics.isPathList_drop hfpath.1 hj)
    have hx₁att : x₁ ∈ attachments G FT KP := by
      refine ⟨?_, fk, ?_, hfkx₁.symm⟩
      · exact Or.inl (Or.inl hx₁R₁)
      · exact hfkS
    have ha₂att : a₂ ∈ attachments G FT KP := by
      refine ⟨?_, f[j]'hj, hfjS, ?_⟩
      · exact Or.inl (Or.inr ha₂R₂)
      · exact (hju ▸ hua₂).symm
    have hb₂notatt : b₂ ∉ attachments G FT KP := by
      rintro ⟨-, w, hw, hb₂w⟩
      have hwfk := hattuniq w (hfS w hw) ⟨b₂, Or.inl hr₂.2.2.1, hb₂w.symm⟩
      subst w
      exact hfkb₂ hb₂w.symm
    have hFTnotlocal : ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀]
        R₁ R₂ R₀ (attachments G FT KP) := by
      rintro (h | h | h | h | h)
      · exact hR₁R₂ a₂ (h ha₂att) ha₂R₂
      · exact hR₁R₂ x₁ hx₁R₁ (h hx₁att)
      · exact hban.2.1 x₁ (h hx₁att) (hR₁S x₁ hx₁R₁)
      · have hx := h hx₁att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with e | e | e
        · exact hx₁ne e
        · exact hR₁R₂ x₁ hx₁R₁ (e ▸ ha₂R₂)
        · exact hban.2.1 a₀ ha₀R₀ (e ▸ hR₁S x₁ hx₁R₁)
      · have ha := h ha₂att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha
        rcases ha with e | e | e
        · exact (Set.disjoint_left.mp hAB (e ▸ hr₂.2.1)) hr₁.2.2.1
        · exact (Set.disjoint_left.mp hAB (e ▸ hr₂.2.1)) hr₂.2.2.1
        · exact hban.2.1 b₀ hb₀R₀ (e ▸ hR₂S a₂ ha₂R₂)
    have hsomeR₀ : ∃ z ∈ attachments G FT KP, z ∈ R₀ := by
      by_contra hn
      push Not at hn
      have hnoneR₀ : ∀ z ∈ attachments G FT KP, z ∉ R₀ := by
        intro z hz hzR₀
        exact hn z hz hzR₀
      have hres := Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4'
        ![a₁, a₂, a₀] ![b₁, b₂, b₀] ![R₁, R₂, R₀] KP FT
        hform rfl hFTK hFTconn
        (by intro hev; exact (hprism ⟨_, _, _, _, _, hev⟩).elim)
        hFTnotlocal hnoneR₀
      apply hb₂notatt
      rw [hres.2]
      simp
    obtain ⟨z₀, hz₀att, hz₀R₀⟩ := hsomeR₀
    have hz₀eq : z₀ = b₀ := by
      by_contra hz₀ne
      obtain ⟨-, w, hw, hz₀w⟩ := hz₀att
      exact hanti w ⟨hfS w hw, htail_ne_f₁ w hw⟩ z₀ ⟨hz₀R₀, hz₀ne⟩ hz₀w.symm
    have hb₀att : b₀ ∈ attachments G FT (staircaseVertices A C B R₀) := by
      obtain ⟨hzK, w, hw, hzw⟩ := hz₀att
      refine ⟨Or.inl hb₀R₀, w, hw, ?_⟩
      exact hz₀eq ▸ hzw
    have hx₁attK : x₁ ∈ attachments G FT (staircaseVertices A C B R₀) := by
      refine ⟨Or.inr ?_, fk, hfkS, hfkx₁.symm⟩
      rcases hx₁BC with hxB | hxC
      · exact Or.inl (Or.inr hxB)
      · exact Or.inr hxC
    have ha₂attK : a₂ ∈ attachments G FT (staircaseVertices A C B R₀) := by
      refine ⟨Or.inr (Or.inl (Or.inl hr₂.2.1)), f[j]'hj, hfjS, ?_⟩
      exact (hju ▸ hua₂).symm
    have hFTstair : FT ⊆ (staircaseVertices A C B R₀)ᶜ := by
      intro w hw
      change w ∈ f.drop j at hw
      rintro (hR | hS)
      · exact hdisj w (hfS w hw) hR
      · exact hFout (by rw [hFeq]; exact hfS w hw) hS
    have hstairNotlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
        (attachments G FT (staircaseVertices A C B R₀)) := by
      rintro (h | h | h | h)
      · exact hban.2.1 b₀ hb₀R₀ (h hb₀att)
      · exact hban.2.1 x₁ (h hx₁attK) (hR₁S x₁ hx₁R₁)
      · rcases h hx₁attK with hxA | hxa₀
        · rcases hx₁BC with hxB | hxC
          · exact (Set.disjoint_left.mp hAB hxA) hxB
          · exact (Set.disjoint_left.mp hAC hxA) hxC
        · exact hban.2.1 a₀ ha₀R₀ (hxa₀ ▸ hR₁S x₁ hx₁R₁)
      · rcases h ha₂attK with haB | hab₀
        · exact (Set.disjoint_left.mp hAB hr₂.2.1) haB
        · exact hban.2.1 b₀ hb₀R₀ (hab₀ ▸ hR₂S a₂ ha₂R₂)
    rcases Workspace.Statements.S12.SPGT.thm_12_2 G hG hK4 hprism hbreaker
        A C B a₀ b₀ R₀ hK FT hFTstair hFTconn hstairNotlocal with
      ⟨w, hw, hwmaj⟩ | ⟨p, q, Q, hQsub, hQban, -⟩ |
        ⟨p, q, Q, hQsub, hQpath, hcase⟩
    · exact hnomajor w (by rw [hFeq]; exact hfS w hw) hwmaj
    · have hqT := hQsub q
          (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQban.1).2
      exact hnors q (hfS q hqT) hQban.2.2.2.1
    · have hpT := hQsub p
          (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).1
      rcases hcase with ⟨hleft, -, -⟩ | ⟨hright, -, -⟩
      · exact htail_ne_f₁ p hpT (hf₁uniq p (hfS p hpT) hleft)
      · exact hnors p (hfS p hpT) hright
  have hR₂BC : ∀ v ∈ R₂, v ≠ a₂ → v ∈ B ∪ C :=
    fun v hv hva₂ => claim3_rung_mem_BC_of_ne_left hr₂ hv hva₂
  exact Workspace.ProofLemmas.Thm123Claim3RungEdgeCharacterization
    G B C f R₂ f₁ fk a₂ (hf₁left.2.1 a₂ hr₂.2.1)
    hNoTailA₂ hR₂BC hattuniq hfkNoR₂

/-- **12.3 (4)**: *"`b₀` has neighbours in `{f₁, …, f_{k−1}}`."* -/
theorem claim4 [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk)
    (hnors : ∀ w ∈ f, ¬ IsRightStar G A C B w)
    (hnotB : ¬ SPGT.VertexComplete G fk B)
    (hdisj : ∀ w ∈ f, w ∉ R₀)
    (hanti : SPGT.Anticomplete G {w : V | w ∈ f ∧ w ≠ f₁} {x : V | x ∈ R₀ ∧ x ≠ b₀})
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hfk₁ : ∃ x ∈ R₁, x ≠ a₁ ∧ G.Adj fk x) (hfkb₂ : ¬ G.Adj fk b₂)
    (hclaim3 : ∀ u ∈ f, ∀ v ∈ R₂, (G.Adj u v ↔ (u = f₁ ∧ v = a₂))) :
    ∃ w ∈ f, w ≠ fk ∧ G.Adj b₀ w := by
  classical
  obtain ⟨⟨hFout, hFconn, -, -⟩, -, hFeq, hfpath, hflen, hf₁left, hf₁uniq,
    hfkatt, hattuniq, hnomajor⟩ := hS
  obtain ⟨hstrip, hban, -⟩ := hK.1
  obtain ⟨⟨hAB, hAC, hBC⟩, -, -, -, -⟩ := hstrip
  obtain ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩ := hstep
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? hfpath.2.1
  have hfkmem : fk ∈ f := List.mem_of_mem_getLast? hfpath.2.2
  have hf₁fk : f₁ ≠ fk := by
    rintro rfl
    obtain ⟨y, hy, hadj⟩ := hfkatt
    exact hf₁left.2.2 y hy hadj
  have hR₁S := claim3_rung_mem_ABC hr₁
  have hR₂S := claim3_rung_mem_ABC hr₂
  have ha₁R₁ : a₁ ∈ R₁ := List.mem_of_mem_head? hr₁.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ := List.mem_of_mem_getLast? hr₁.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := List.mem_of_mem_head? hr₂.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := List.mem_of_mem_getLast? hr₂.1.2.2
  have ha₀R₀ : a₀ ∈ R₀ := List.mem_of_mem_head? hban.1.2.1
  have hb₀R₀ : b₀ ∈ R₀ := List.mem_of_mem_getLast? hban.1.2.2
  have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ :=
    Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step hban
      ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩
  have ha₀b₀ : a₀ ≠ b₀ := by
    intro e
    have hadj := hban.2.2.1.2.1 a₁ hr₁.2.1
    rw [e] at hadj
    exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) hadj
  have hK4' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K', happ, -⟩
    exact hK4 ⟨n, H, K', happ⟩
  by_contra hcon
  push Not at hcon
  by_cases hb₀fk : G.Adj b₀ fk
  · -- The paper's second case: `f_k` is the unique neighbour of `b₀` in `F`.
    have hb₀only : ∀ w ∈ f, G.Adj b₀ w → w = fk := by
      intro w hw hadj
      by_contra hwfk
      exact hcon w hw hwfk hadj
    have hfkNoR₂ : ∀ v ∈ R₂, ¬ G.Adj fk v := by
      intro v hv hadj
      have h := (hclaim3 fk hfkmem v hv).mp hadj
      exact hf₁fk h.1.symm
    have hform₀₁₂ : FormPrism G ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂ :=
      (Workspace.ProofLemmas.StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism
        G A C B a₀ b₀ a₁ b₁ a₂ b₂ R₀ R₁ R₂ hK.1
        ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩ hG hprism).1
    let KP : Set V :=
      {z : V | z ∈ R₀} ∪ {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂}
    have hfkKP : fk ∉ KP := by
      change fk ∉ ({z : V | z ∈ R₀} ∪ {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂})
      rintro ((h | h) | h)
      · exact hdisj fk hfkmem h
      · exact hFout (by rw [hFeq]; exact hfkmem) (hR₁S fk h)
      · exact hFout (by rw [hFeq]; exact hfkmem) (hR₂S fk h)
    have hlocal : LocalForPrism ![a₀, a₁, a₂] ![b₀, b₁, b₂] R₀ R₁ R₂
        (attachments G ({fk} : Set V) KP) := by
      by_contra hnlocal
      have hres := Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4'
        ![a₀, a₁, a₂] ![b₀, b₁, b₂] ![R₀, R₁, R₂]
        KP ({fk} : Set V) hform₀₁₂ rfl (by simpa using hfkKP) (by simp [ConnectedSet])
        (by intro hev; exact (hprism ⟨_, _, _, _, _, hev⟩).elim)
        hnlocal (by
          intro z hz hzR₀
          obtain ⟨-, w, hw, hzw⟩ := hz
          simp only [Set.mem_singleton_iff] at hw
          subst w
          exact hfkNoR₂ z (by simpa using hzR₀) hzw.symm)
      exact Set.not_nontrivial_singleton hres.1
    obtain ⟨x₁, hx₁R₁, hx₁ne, hfkx₁⟩ := hfk₁
    have hb₀att : b₀ ∈ attachments G ({fk} : Set V) KP := by
      refine ⟨?_, fk, by simp, hb₀fk⟩
      exact Or.inl (Or.inl hb₀R₀)
    have hx₁att : x₁ ∈ attachments G ({fk} : Set V) KP := by
      refine ⟨?_, fk, by simp, hfkx₁.symm⟩
      exact Or.inl (Or.inr hx₁R₁)
    have hlocalB : attachments G ({fk} : Set V) KP ⊆
        ({![b₀, b₁, b₂] 0, ![b₀, b₁, b₂] 1, ![b₀, b₁, b₂] 2} : Set V) := by
      rcases hlocal with h | h | h | h | h
      · exact False.elim (hban.2.1 x₁ (h hx₁att) (hR₁S x₁ hx₁R₁))
      · exact False.elim (hban.2.1 b₀ hb₀R₀ (hR₁S b₀ (h hb₀att)))
      · exact False.elim (hR₁R₂ x₁ hx₁R₁ (h hx₁att))
      · have hb := h hb₀att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hb
        rcases hb with e | e | e
        · exact False.elim (ha₀b₀ e.symm)
        · exact False.elim (hban.2.1 b₀ hb₀R₀
            (by rw [e]; exact Or.inl (Or.inl hr₁.2.1)))
        · exact False.elim (hban.2.1 b₀ hb₀R₀
            (by rw [e]; exact Or.inl (Or.inl hr₂.2.1)))
      · exact h
    have hfkR₁only : ∀ y ∈ R₁, G.Adj fk y → y = b₁ := by
      intro y hy hadj
      have hyatt : y ∈ attachments G ({fk} : Set V) KP :=
        ⟨Or.inl (Or.inr hy), fk, by simp, hadj.symm⟩
      have hyB := hlocalB hyatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hyB
      rcases hyB with e | e | e
      · exact (hban.2.1 b₀ hb₀R₀ (e ▸ hR₁S y hy)).elim
      · exact e
      · exact (hR₁R₂ y hy (e ▸ hb₂R₂)).elim
    have hfk_b₁ : G.Adj fk b₁ := by
      have hx₁eq := hfkR₁only x₁ hx₁R₁ hfkx₁
      exact hx₁eq ▸ hfkx₁
    have hodd := Workspace.Statements.S11.SPGT.thm_11_3 G hG hprism A C B hK.1.1
      a₀ b₀ R₀ hban
    have hoddR₁ : Odd (pathLength R₁) := hodd.1 a₁ R₁ b₁ hr₁
    have hoddR₂ : Odd (pathLength R₂) := hodd.1 a₂ R₂ b₂ hr₂
    have hb₀notR₂ : b₀ ∉ R₂ := by
      intro hbR
      exact hban.2.1 b₀ hb₀R₀ (hR₂S b₀ hbR)
    have hb₀R₂adj : ∀ y ∈ R₂, (G.Adj b₀ y ↔ y = b₂) := by
      intro y hy
      rw [claim3_banister_rung_edges hban hr₂ b₀ hb₀R₀ y hy]
      constructor
      · rintro (⟨e, -⟩ | ⟨-, e⟩)
        · exact (ha₀b₀ e.symm).elim
        · exact e
      · intro e
        exact Or.inr ⟨rfl, e⟩
    have hq₂ : IsPathFrom G (b₀ :: R₂.reverse) b₀ a₂ := by
      have hr := Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hr₂.1
      refine Workspace.ProofLemmas.Thm121C3PathCons.isPathFrom_cons hr ?_ ?_
      · simpa only [List.mem_reverse] using hb₀notR₂
      · intro y hy
        rw [List.mem_reverse] at hy
        simpa only [SimpleGraph.adj_comm] using hb₀R₂adj y hy
    have hfq₂disj : ∀ x ∈ f, x ∉ b₀ :: R₂.reverse := by
      intro x hx hxq
      rcases List.mem_cons.mp hxq with e | hxR
      · subst x
        exact hdisj b₀ hx hb₀R₀
      · exact hFout (by rw [hFeq]; exact hx) (hR₂S x (List.mem_reverse.mp hxR))
    have hcrossfq₂ : ∀ x ∈ f, ∀ y ∈ b₀ :: R₂.reverse,
        (G.Adj x y ↔ (x = fk ∧ y = b₀) ∨ (x = f₁ ∧ y = a₂)) := by
      intro x hx y hy
      rcases List.mem_cons.mp hy with hyb | hyR
      · constructor
        · intro hadj
          have hadj' : G.Adj b₀ x := by rw [← hyb]; exact hadj.symm
          exact Or.inl ⟨hb₀only x hx hadj', hyb⟩
        · rintro (hl | hr)
          · rw [hl.1, hl.2]
            exact hb₀fk.symm
          · have : b₀ = a₂ := hyb.symm.trans hr.2
            exact False.elim (hban.2.1 b₀ hb₀R₀
              (by rw [this]; exact Or.inl (Or.inl hr₂.2.1)))
      · have hyR₂ := List.mem_reverse.mp hyR
        rw [hclaim3 x hx y hyR₂]
        constructor
        · rintro ⟨e1, e2⟩
          exact Or.inr ⟨e1, e2⟩
        · rintro (⟨-, e⟩ | h)
          · exact (hban.2.1 b₀ hb₀R₀ (e ▸ hR₂S y hyR₂)).elim
          · exact h
    have hhole₂ : IsHoleList G (f ++ (b₀ :: R₂.reverse)) := by
      refine Workspace.ProofLemmas.PathGlue.glue_hole hfpath hq₂ hfq₂disj hcrossfq₂ ?_
      simp only [List.length_append, List.length_cons, List.length_reverse]
      have := Workspace.ProofLemmas.PathBasics.path_length_pos hr₂.1.1
      omega
    have heven₂ := hG.1 _ hhole₂
    have hfodd : Odd f.length := by
      rw [Nat.even_iff] at heven₂
      rw [Nat.odd_iff] at hoddR₂ ⊢
      simp only [holeLength, List.length_append, List.length_cons, List.length_reverse,
        pathLength] at heven₂ hoddR₂
      omega
    by_cases ha₁tail : ∃ w ∈ f, w ≠ f₁ ∧ G.Adj a₁ w
    · -- The tail would violate 12.2.
      let FT : Set V := {w : V | w ∈ f ∧ w ≠ f₁}
      have htailEq : FT = {w : V | w ∈ f.tail} := by
        ext w
        simp only [FT, Set.mem_setOf_eq]
        have hpos : 0 < f.length := by omega
        have hfhead : f.head? = some f₁ := hfpath.2.1
        rcases f with _ | ⟨c, t⟩
        · exact (hfpath.1.1 rfl).elim
        have hc : c = f₁ := by simpa using hfhead
        subst c
        have hnot : f₁ ∉ t := (List.nodup_cons.mp hfpath.1.2.1).1
        simp only [List.mem_cons, List.tail_cons]
        constructor
        · rintro ⟨rfl | hw, hne⟩
          · exact (hne rfl).elim
          · exact hw
        · intro hw
          exact ⟨Or.inr hw, fun e => hnot (e ▸ hw)⟩
      have hFTstair : FT ⊆ (staircaseVertices A C B R₀)ᶜ := by
        rintro w ⟨hwf, -⟩ (hwR | hwS)
        · exact hdisj w hwf hwR
        · exact hFout (by rw [hFeq]; exact hwf) hwS
      have hFTconn : ConnectedSet G FT := by
        rw [htailEq]
        exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
          (by simpa only [List.drop_one] using
            (Workspace.ProofLemmas.PathBasics.isPathList_drop hfpath.1
              (show 1 < f.length by omega)))
      have ha₁att : a₁ ∈ attachments G FT (staircaseVertices A C B R₀) := by
        obtain ⟨w, hwf, hwne, haw⟩ := ha₁tail
        exact ⟨Or.inr (Or.inl (Or.inl hr₁.2.1)), w, ⟨hwf, hwne⟩, haw⟩
      have hb₀att' : b₀ ∈ attachments G FT (staircaseVertices A C B R₀) := by
        exact ⟨Or.inl hb₀R₀, fk, ⟨hfkmem, hf₁fk.symm⟩, hb₀fk⟩
      have hFTnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
          (attachments G FT (staircaseVertices A C B R₀)) := by
        rintro (h | h | h | h)
        · exact hban.2.1 b₀ hb₀R₀ (h hb₀att')
        · exact hban.2.1 a₁ (h ha₁att) (Or.inl (Or.inl hr₁.2.1))
        · rcases h hb₀att' with hbA | hbe
          · exact hban.2.2.2.1.1 (Or.inl (Or.inl hbA))
          · exact ha₀b₀ hbe.symm
        · rcases h ha₁att with haB | hae
          · exact (Set.disjoint_left.mp hAB hr₁.2.1) haB
          · exact hban.2.2.2.1.1 (by rw [← hae]; exact Or.inl (Or.inl hr₁.2.1))
      rcases Workspace.Statements.S12.SPGT.thm_12_2 G hG hK4 hprism hbreaker
          A C B a₀ b₀ R₀ hK FT hFTstair hFTconn hFTnonlocal with
        ⟨w, hw, hwmaj⟩ | ⟨p, q, Q, hQsub, hQban, -⟩ |
          ⟨p, q, Q, hQsub, hQpath, hcase⟩
      · exact hnomajor w (by rw [hFeq]; exact hw.1) hwmaj
      · have hqT := hQsub q (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQban.1).2
        exact hnors q hqT.1 hQban.2.2.2.1
      · have hpT := hQsub p (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).1
        rcases hcase with ⟨hleft, -, -⟩ | ⟨hright, -, -⟩
        · exact hpT.2 (hf₁uniq p hpT.1 hleft)
        · exact hnors p hpT.1 hright
    · -- Otherwise `f₁-⋯-f_k-b₁-R₁-a₁-f₁` is an odd hole.
      push Not at ha₁tail
      have hfR₁disj : ∀ x ∈ f, x ∉ R₁.reverse := by
        intro x hx hxR
        exact hFout (by rw [hFeq]; exact hx) (hR₁S x (List.mem_reverse.mp hxR))
      have hcrossfR₁ : ∀ x ∈ f, ∀ y ∈ R₁.reverse,
          (G.Adj x y ↔ (x = fk ∧ y = b₁) ∨ (x = f₁ ∧ y = a₁)) := by
        intro x hx y hy
        have hyR := List.mem_reverse.mp hy
        constructor
        · intro hxy
          by_cases hxf : x = f₁
          · subst x
            refine Or.inr ⟨rfl, ?_⟩
            rcases hR₁S y hyR with (hyA | hyB) | hyC
            · exact hr₁.2.2.2.1 y hyR hyA
            · exact (hf₁left.2.2 y (Or.inl hyB) hxy).elim
            · exact (hf₁left.2.2 y (Or.inr hyC) hxy).elim
          · have hxfk := hattuniq x hx ⟨y, claim3_rung_mem_BC_of_ne_left hr₁ hyR
                (fun e => ha₁tail x hx hxf (e ▸ hxy).symm), hxy⟩
            subst x
            exact Or.inl ⟨rfl, hfkR₁only y hyR hxy⟩
        · rintro (hl | hr)
          · rw [hl.1, hl.2]
            exact hfk_b₁
          · rw [hr.1, hr.2]
            exact hf₁left.2.1 a₁ hr₁.2.1
      have hhole₁ : IsHoleList G (f ++ R₁.reverse) := by
        refine Workspace.ProofLemmas.PathGlue.glue_hole hfpath
          (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hr₁.1)
          hfR₁disj hcrossfR₁ ?_
        simp only [List.length_append, List.length_reverse]
        have hRlen : 2 ≤ R₁.length := by
          simpa using
            (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length
              (R := ![R₁, R₂, R₀]) hform 0)
        omega
      have hev := hG.1 _ hhole₁
      rw [Nat.even_iff] at hev
      rw [Nat.odd_iff] at hfodd hoddR₁
      simp only [holeLength, List.length_append, List.length_reverse, pathLength] at hev hoddR₁
      omega
  · -- The first case of (4), where `b₀` has no neighbour in `F`.
    have hb₀none : ∀ w ∈ f, ¬ G.Adj b₀ w := by
      intro w hw hadj
      by_cases hwfk : w = fk
      · exact hb₀fk (hwfk ▸ hadj)
      · exact hcon w hw hwfk hadj
    let KP : Set V :=
      {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀}
    have hfKP : {w : V | w ∈ f} ⊆ KPᶜ := by
      intro w hw
      change w ∉ ({z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂} ∪ {z : V | z ∈ R₀})
      rintro ((h | h) | h)
      · exact hFout (by rw [hFeq]; exact hw) (hR₁S w h)
      · exact hFout (by rw [hFeq]; exact hw) (hR₂S w h)
      · exact hdisj w hw h
    obtain ⟨x₁, hx₁R₁, hx₁ne, hfkx₁⟩ := hfk₁
    have hx₁att : x₁ ∈ attachments G {w : V | w ∈ f} KP :=
      ⟨Or.inl (Or.inl hx₁R₁), fk, hfkmem, hfkx₁.symm⟩
    have ha₂att : a₂ ∈ attachments G {w : V | w ∈ f} KP := by
      refine ⟨Or.inl (Or.inr ha₂R₂), f₁, hf₁mem, ?_⟩
      exact ((hclaim3 f₁ hf₁mem a₂ ha₂R₂).mpr ⟨rfl, rfl⟩).symm
    have hnotlocal : ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀
        (attachments G {w : V | w ∈ f} KP) := by
      rintro (h | h | h | h | h)
      · exact hR₁R₂ a₂ (h ha₂att) ha₂R₂
      · exact hR₁R₂ x₁ hx₁R₁ (h hx₁att)
      · exact hban.2.1 x₁ (h hx₁att) (hR₁S x₁ hx₁R₁)
      · have hx := h hx₁att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx
        rcases hx with e | e | e
        · exact hx₁ne e
        · exact hR₁R₂ x₁ hx₁R₁ (e ▸ ha₂R₂)
        · exact hban.2.1 a₀ ha₀R₀ (e ▸ hR₁S x₁ hx₁R₁)
      · have ha := h ha₂att
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
          Set.mem_singleton_iff] at ha
        rcases ha with e | e | e
        · exact (Set.disjoint_left.mp hAB hr₂.2.1) (e ▸ hr₁.2.2.1)
        · exact (Set.disjoint_left.mp hAB hr₂.2.1) (e ▸ hr₂.2.2.1)
        · exact hban.2.1 b₀ hb₀R₀ (e ▸ Or.inl (Or.inl hr₂.2.1))
    have hsomeR₀ : ∃ z ∈ attachments G {w : V | w ∈ f} KP, z ∈ R₀ := by
      by_contra hn
      push Not at hn
      have hFlistconn : ConnectedSet G {w : V | w ∈ f} := by
        rw [← hFeq]
        exact hFconn
      have hres := Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4'
        ![a₁, a₂, a₀] ![b₁, b₂, b₀] ![R₁, R₂, R₀]
        KP {w : V | w ∈ f} hform rfl hfKP hFlistconn
        (by intro hev; exact (hprism ⟨_, _, _, _, _, hev⟩).elim)
        hnotlocal (by intro z hz hzR₀; exact hn z hz (by simpa using hzR₀))
      have hb₂att : b₂ ∈ attachments G {w : V | w ∈ f} KP := by
        rw [hres.2]
        simp
      obtain ⟨-, w, hwf, hb₂w⟩ := hb₂att
      have hc := (hclaim3 w hwf b₂ hb₂R₂).mp hb₂w.symm
      exact (Set.disjoint_left.mp hAB hr₂.2.1) (hc.2 ▸ hr₂.2.2.1)
    obtain ⟨z, hzatt, hzR₀⟩ := hsomeR₀
    obtain ⟨-, w, hwf, hzw⟩ := hzatt
    have hzb₀ : z ≠ b₀ := by
      intro e
      exact hb₀none w hwf (e ▸ hzw)
    have hwf₁ : w = f₁ := by
      by_contra hwne
      exact hanti w ⟨hwf, hwne⟩ z ⟨hzR₀, hzb₀⟩ hzw.symm
    have hf₁z : G.Adj f₁ z := hwf₁ ▸ hzw.symm
    obtain ⟨k₀, hk₀, hk₀z⟩ := List.mem_iff_getElem.mp hzR₀
    have hk₀adj : G.Adj f₁ (R₀[k₀]'hk₀) := hk₀z ▸ hf₁z
    obtain ⟨i, hi, hiadj, himax⟩ := exists_max_adj_on_list f₁ R₀ k₀ hk₀ hk₀adj
    have hilast : i < R₀.length - 1 := by
      by_contra hc
      have hie : i = R₀.length - 1 := by omega
      have hib : R₀[i]'hi = b₀ := by
        rw [getElem_eq_of_index_eq R₀ hi (show R₀.length - 1 < R₀.length by omega) hie]
        exact Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hban.1.2.2 (by omega)
      exact hb₀none f₁ hf₁mem (hib ▸ hiadj).symm
    by_cases hi₀ : i = 0
    · -- If the only `R₀`-neighbour found is its left end, 12.2 applied to all of
      -- `F` supplies a later `R₀`-attachment.  Both possible locations for that
      -- attachment contradict either the maximal choice above or the assumption on `b₀`.
      subst i
      have hzero : R₀[0]'hi = a₀ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 hi
      have hf₁a₀ : G.Adj f₁ a₀ := by
        rwa [hzero] at hiadj
      have hFstair : F ⊆ (staircaseVertices A C B R₀)ᶜ := by
        intro w hw
        change w ∉ ({z : V | z ∈ R₀} ∪ (A ∪ B ∪ C))
        rintro (hwR | hwS)
        · have hwf := hw
          rw [hFeq] at hwf
          exact hdisj w hwf hwR
        · exact hFout hw hwS
      have ha₀attK : a₀ ∈ attachments G F (staircaseVertices A C B R₀) :=
        ⟨Or.inl ha₀R₀, f₁, by rw [hFeq]; exact hf₁mem, hf₁a₀.symm⟩
      have hx₁attK : x₁ ∈ attachments G F (staircaseVertices A C B R₀) := by
        refine ⟨Or.inr (hR₁S x₁ hx₁R₁), fk, ?_, hfkx₁.symm⟩
        rw [hFeq]
        exact hfkmem
      have hFnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
          (attachments G F (staircaseVertices A C B R₀)) := by
        rintro (h | h | h | h)
        · exact hban.2.2.1.1 (h ha₀attK)
        · exact hban.2.1 x₁ (h hx₁attK) (hR₁S x₁ hx₁R₁)
        · rcases h hx₁attK with hxA | hxa₀
          · rcases claim3_rung_mem_BC_of_ne_left hr₁ hx₁R₁ hx₁ne with hxB | hxC
            · exact (Set.disjoint_left.mp hAB hxA) hxB
            · exact (Set.disjoint_left.mp hAC hxA) hxC
          · exact hban.2.2.1.1 (by rw [← hxa₀]; exact hR₁S x₁ hx₁R₁)
        · rcases h ha₀attK with haB | hab
          · exact hban.2.2.1.1 (Or.inl (Or.inr haB))
          · exact ha₀b₀ hab
      rcases Workspace.Statements.S12.SPGT.thm_12_2 G hG hK4 hprism hbreaker
          A C B a₀ b₀ R₀ hK F hFstair hFconn hFnonlocal with
        ⟨w, hwF, hwmaj⟩ | ⟨p, q, Q, hQsub, hQban, -⟩ |
          ⟨p, q, Q, hQsub, hQpath, hcase⟩
      · exact hnomajor w hwF hwmaj
      · have hqF := hQsub q
            (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQban.1).2
        have hqf := hqF
        rw [hFeq] at hqf
        exact hnors q hqf hQban.2.2.2.1
      · rcases hcase with ⟨-, ⟨x, hxR₀, hxneA, hqx⟩, -⟩ |
          ⟨hright, -, -⟩
        · have hqF := hQsub q
              (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).2
          have hqf : q ∈ f := by
            rw [hFeq] at hqF
            exact hqF
          by_cases hxb : x = b₀
          · exact hb₀none q hqf (hxb ▸ hqx.symm)
          · by_cases hq : q = f₁
            · obtain ⟨r, hr, hrx⟩ := List.mem_iff_getElem.mp hxR₀
              have hrpos : 0 < r := by
                rcases Nat.eq_zero_or_pos r with rfl | hrpos
                · exact (hxneA (by rw [← hrx]; exact hzero)).elim
                · exact hrpos
              exact himax r hr hrpos (hrx ▸ (hq ▸ hqx))
            · exact hanti q ⟨hqf, hq⟩ x ⟨hxR₀, hxb⟩ hqx
        · have hpF := hQsub p
              (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).1
          rw [hFeq] at hpF
          exact hnors p hpF hright
    · have hi1 : 1 ≤ i := by omega
      -- Choose the neighbour of `f_k` on `R₁` closest to `b₁`.
      obtain ⟨j₀, hj₀, hj₀x⟩ := List.mem_iff_getElem.mp hx₁R₁
      have hj₀1 : 1 ≤ j₀ := by
        rcases Nat.eq_zero_or_pos j₀ with rfl | h
        · have hx₁a : x₁ = a₁ := by
            rw [← hj₀x]
            exact Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hr₁.1.2.1 (by omega)
          exact (hx₁ne hx₁a).elim
        · exact h
      have hj₀adj : G.Adj fk (R₁[j₀]'hj₀) := hj₀x ▸ hfkx₁
      obtain ⟨j, hj, hjadj, hjmax⟩ := exists_max_adj_on_list fk R₁ j₀ hj₀ hj₀adj
      have hj1 : 1 ≤ j := by
        have hle : j₀ ≤ j := by
          by_contra hc
          exact hjmax j₀ hj₀ (by omega) hj₀adj
        omega
      let P₀ : List V := R₀.drop i
      let T : List V := f.drop 1
      let U : List V := R₁.drop j
      let P₁ : List V := T ++ U
      have hP₀ : IsPathFrom G P₀ (R₀[i]'hi) b₀ := isPathFrom_drop_to_last hban.1 i hi
      have hT : IsPathFrom G T (f[1]'(by omega)) fk := isPathFrom_drop_to_last hfpath 1 (by omega)
      have hU : IsPathFrom G U (R₁[j]'hj) b₁ := isPathFrom_drop_to_last hr₁.1 j hj
      have hTmem : ∀ x ∈ T, x ∈ f ∧ x ≠ f₁ := by
        intro x hx
        obtain ⟨r, hr, hr1, hrx⟩ := (mem_drop_with_index f 1).mp hx
        refine ⟨by rw [← hrx]; exact List.getElem_mem hr, ?_⟩
        intro e
        have h0 : f[0]'(by omega) = f₁ :=
          Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 (by omega)
        have : r = 0 := hfpath.1.2.1.getElem_inj_iff.mp (by rw [hrx, e, h0])
        omega
      have hUneA : ∀ y ∈ U, y ≠ a₁ := by
        intro y hy e
        obtain ⟨r, hr, hjr, hry⟩ := (mem_drop_with_index R₁ j).mp hy
        have h0 : R₁[0]'(by omega) = a₁ :=
          Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hr₁.1.2.1 (by omega)
        have : r = 0 := hr₁.1.1.2.1.getElem_inj_iff.mp (by rw [hry, e, h0])
        omega
      have hTUdisj : ∀ x ∈ T, x ∉ U := by
        intro x hx hxU
        exact hFout (by rw [hFeq]; exact (hTmem x hx).1)
          (hR₁S x (List.mem_of_mem_drop hxU))
      have hTUcross : ∀ x ∈ T, ∀ y ∈ U,
          (G.Adj x y ↔ (x = fk ∧ y = R₁[j]'hj)) := by
        intro x hx y hy
        have hxdata := hTmem x hx
        have hyR := List.mem_of_mem_drop hy
        constructor
        · intro hxy
          have hyBC := claim3_rung_mem_BC_of_ne_left hr₁ hyR (hUneA y hy)
          have hxfk := hattuniq x hxdata.1 ⟨y, hyBC, hxy⟩
          obtain ⟨r, hr, hjr, hry⟩ := (mem_drop_with_index R₁ j).mp hy
          have hrj : r = j := by
            by_contra hc
            exact hjmax r hr (by omega) (hry ▸ (hxfk ▸ hxy))
          exact ⟨hxfk, by rw [← hry]; exact getElem_eq_of_index_eq R₁ hr hj hrj⟩
        · rintro ⟨rfl, rfl⟩
          exact hjadj
      have hP₁ : IsPathFrom G P₁ (f[1]'(by omega)) b₁ := by
        exact Workspace.ProofLemmas.PathGlue.glue_path hT hU hTUdisj hTUcross
      -- The three paths link `f₁` onto the right triangle.
      have hlink : Workspace.Types.RousselRubio.SPGT.VertexCanBeLinkedOntoTriangle
          G f₁ b₀ b₁ b₂ := by
        have hP₀mem : ∀ x ∈ P₀, x ∈ R₀ := by
          intro x hx
          exact List.mem_of_mem_drop hx
        have hP₀neA : ∀ x ∈ P₀, x ≠ a₀ := by
          intro x hx e
          obtain ⟨r, hr, hir, hrx⟩ := (mem_drop_with_index R₀ i).mp hx
          have h0 : R₀[0]'(by omega) = a₀ :=
            Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hban.1.2.1 (by omega)
          have hre : r = 0 := hban.1.1.2.1.getElem_inj_iff.mp (by rw [hrx, e, h0])
          omega
        have hUmem : ∀ y ∈ U, y ∈ R₁ := by
          intro y hy
          exact List.mem_of_mem_drop hy
        refine ⟨P₀, P₁, R₂, ⟨hP₀.1, hP₁.1, hr₂.1.1⟩, ⟨?_, ?_, ?_⟩,
          ⟨Or.inr hP₀.2.2, Or.inr hP₁.2.2, Or.inr hr₂.1.2.2⟩,
          ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
        · intro x hx hxP₁
          rcases List.mem_append.mp hxP₁ with hxT | hxU
          · exact hdisj x (hTmem x hxT).1 (hP₀mem x hx)
          · exact hban.2.1 x (hP₀mem x hx) (hR₁S x (hUmem x hxU))
        · intro x hx hxR₂
          exact hban.2.1 x (hP₀mem x hx) (hR₂S x hxR₂)
        · intro x hx hxR₂
          rcases List.mem_append.mp hx with hxT | hxU
          · exact hFout (by rw [hFeq]; exact (hTmem x hxT).1) (hR₂S x hxR₂)
          · exact hR₁R₂ x (hUmem x hxU) hxR₂
        · intro x hx y hy
          constructor
          · intro hxy
            rcases List.mem_append.mp hy with hyT | hyU
            · by_cases hxb : x = b₀
              · subst x
                exact (hb₀none y (hTmem y hyT).1 hxy).elim
              · exact (hanti y (hTmem y hyT) x ⟨hP₀mem x hx, hxb⟩ hxy.symm).elim
            · rcases (claim3_banister_rung_edges hban hr₁ x (hP₀mem x hx)
                  y (hUmem y hyU)).mp hxy with hleft | hright
              · exact (hP₀neA x hx hleft.1).elim
              · exact ⟨hright.1, hright.2⟩
          · intro h
            exact h.1 ▸ h.2 ▸
              (claim3_banister_rung_edges hban hr₁ b₀ hb₀R₀ b₁ hb₁R₁).mpr
                (Or.inr ⟨rfl, rfl⟩)
        · intro x hx y hy
          constructor
          · intro hxy
            rcases (claim3_banister_rung_edges hban hr₂ x (hP₀mem x hx) y hy).mp hxy with
              hleft | hright
            · exact (hP₀neA x hx hleft.1).elim
            · exact ⟨hright.1, hright.2⟩
          · intro h
            exact h.1 ▸ h.2 ▸
              (claim3_banister_rung_edges hban hr₂ b₀ hb₀R₀ b₂ hb₂R₂).mpr
                (Or.inr ⟨rfl, rfl⟩)
        · intro x hx y hy
          constructor
          · intro hxy
            rcases List.mem_append.mp hx with hxT | hxU
            · have hc := (hclaim3 x (hTmem x hxT).1 y hy).mp hxy
              exact ((hTmem x hxT).2 hc.1).elim
            · rcases (hcross₁₂ x (hUmem x hxU) y hy).mp hxy with hleft | hright
              · exact (hUneA x hxU hleft.1).elim
              · exact ⟨hright.1, hright.2⟩
          · intro h
            exact h.1 ▸ h.2 ▸
              (hcross₁₂ b₁ hb₁R₁ b₂ hb₂R₂).mpr (Or.inr ⟨rfl, rfl⟩)
        · exact ⟨R₀[i]'hi, List.mem_of_mem_head? hP₀.2.1, hiadj⟩
        · refine ⟨f[1]'(by omega), List.mem_of_mem_head? hP₁.2.1, ?_⟩
          have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hfpath.1
            (i := 0) (by omega)
          have h0 : f[0]'(by omega) = f₁ :=
            Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 (by omega)
          rwa [h0] at hadj
        · exact ⟨a₂, ha₂R₂,
            (hclaim3 f₁ hf₁mem a₂ ha₂R₂).mpr ⟨rfl, rfl⟩⟩
      rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG f₁ b₀ b₁ b₂ hlink with
        ⟨hb₀f, -⟩ | ⟨hb₀f, -⟩ | ⟨hb₁f, hb₂f⟩
      · exact hb₀none f₁ hf₁mem hb₀f.symm
      · exact hb₀none f₁ hf₁mem hb₀f.symm
      · exact hf₁left.2.2 b₁ (Or.inl hr₁.2.2.1) hb₁f

/-- **12.3, final paragraph**: *"Choose `i` with `1 ≤ i < k` minimum such that `b₀` is adjacent
to `f_i`, and let `R₀'` be the path `f₁`-…-`f_i`-`b₀`. …  But then by (2), `a₁` can be linked
onto the triangle `{b₀, b₁, f_k}`, via `a₁`-`a₀`-`R₀`-`b₀`, `a₁`-`R₁`-`b₁`, `a₁`-`f₂`-…-`f_k`,
contrary to 2.4."*  So the situation left open after (1)–(4) is contradictory. -/
theorem endgame [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk)
    (hnors : ∀ w ∈ f, ¬ IsRightStar G A C B w)
    (hnotB : ¬ SPGT.VertexComplete G fk B)
    (hdisj : ∀ w ∈ f, w ∉ R₀)
    (hanti : SPGT.Anticomplete G {w : V | w ∈ f ∧ w ≠ f₁} {x : V | x ∈ R₀ ∧ x ≠ b₀})
    (a₁ : V) (R₁ : List V) (b₁ : V) (a₂ : V) (R₂ : List V) (b₂ : V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (hfk₁ : ∃ x ∈ R₁, x ≠ a₁ ∧ G.Adj fk x) (hfkb₂ : ¬ G.Adj fk b₂)
    (hclaim3 : ∀ u ∈ f, ∀ v ∈ R₂, (G.Adj u v ↔ (u = f₁ ∧ v = a₂)))
    (hclaim4 : ∃ w ∈ f, w ≠ fk ∧ G.Adj b₀ w) :
    False := by
  classical
  obtain ⟨⟨hFout, hFconn, -, -⟩, -, hFeq, hfpath, hflen, hf₁left, hf₁uniq,
    -, hattuniq, hnomajor⟩ := hS
  obtain ⟨hstrip, hban, -⟩ := hK.1
  obtain ⟨⟨hAB, hAC, -⟩, -, -, -, -⟩ := hstrip
  obtain ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩ := hstep
  have hf₁mem : f₁ ∈ f := List.mem_of_mem_head? hfpath.2.1
  have hfkmem : fk ∈ f := List.mem_of_mem_getLast? hfpath.2.2
  have hf₁fk : f₁ ≠ fk := by
    intro e
    obtain ⟨x, hx, hxne, hfkx⟩ := hfk₁
    exact hf₁left.2.2 x
      (claim3_rung_mem_BC_of_ne_left hr₁ hx hxne) (e ▸ hfkx)
  have ha₀b₀_endgame : a₀ ≠ b₀ := by
    intro e
    have hadj := hban.2.2.1.2.1 a₁ hr₁.2.1
    rw [e] at hadj
    exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) hadj
  have ha₀R₀ : a₀ ∈ R₀ := List.mem_of_mem_head? hban.1.2.1
  have hb₀R₀ : b₀ ∈ R₀ := List.mem_of_mem_getLast? hban.1.2.2
  have ha₁R₁ : a₁ ∈ R₁ := List.mem_of_mem_head? hr₁.1.2.1
  have hb₁R₁ : b₁ ∈ R₁ := List.mem_of_mem_getLast? hr₁.1.2.2
  have ha₂R₂ : a₂ ∈ R₂ := List.mem_of_mem_head? hr₂.1.2.1
  have hb₂R₂ : b₂ ∈ R₂ := List.mem_of_mem_getLast? hr₂.1.2.2
  have hR₁S := claim3_rung_mem_ABC hr₁
  have hR₂S := claim3_rung_mem_ABC hr₂
  obtain ⟨w₀, hw₀f, hw₀ne, hb₀w₀⟩ := hclaim4
  obtain ⟨k₀, hk₀, hk₀w⟩ := List.mem_iff_getElem.mp hw₀f
  have hlast : f[f.length - 1]'(by omega) = fk :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hfpath.2.2 (by omega)
  have hk₀last : k₀ < f.length - 1 := by
    by_contra hc
    have he : k₀ = f.length - 1 := by omega
    apply hw₀ne
    rw [← hk₀w, getElem_eq_of_index_eq f hk₀ (by omega) he, hlast]
  have hk₀adj : G.Adj b₀ (f[k₀]'hk₀) := hk₀w ▸ hb₀w₀
  obtain ⟨i, hi, hbi, himin⟩ := exists_min_adj_on_list b₀ f k₀ hk₀ hk₀adj
  have hilast : i < f.length - 1 := by
    by_contra hc
    have hklt : k₀ < i := by omega
    exact himin k₀ hk₀ hklt hk₀adj
  have hfi_ne_fk : f[i]'hi ≠ fk := by
    intro he
    have hj : i = f.length - 1 := hfpath.1.2.1.getElem_inj_iff.mp (he.trans hlast.symm)
    omega
  have hfi_ne_f₁_of_pos (hipos : 0 < i) : f[i]'hi ≠ f₁ := by
    intro he
    have hzero : f[0]'(by omega) = f₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 (by omega)
    have : i = 0 := hfpath.1.2.1.getElem_inj_iff.mp (he.trans hzero.symm)
    omega
  have htailAntiA_of_pos (hipos : 0 < i) :
      ∀ x ∈ f, x ≠ f₁ → ∀ y ∈ A, ¬ G.Adj x y := by
    intro x hxf hxf₁ y hyA hxy
    let FT : Set V := {z : V | z ∈ f ∧ z ≠ f₁}
    have hFTtail : FT = {z : V | z ∈ f.tail} := by
      ext z
      simp only [FT, Set.mem_setOf_eq]
      rcases f with _ | ⟨c, t⟩
      · exact (hfpath.1.1 rfl).elim
      have hc : c = f₁ := by simpa using hfpath.2.1
      subst c
      have hnmem : f₁ ∉ t := (List.nodup_cons.mp hfpath.1.2.1).1
      simp only [List.tail_cons, List.mem_cons]
      constructor
      · rintro ⟨rfl | hz, hne⟩
        · exact (hne rfl).elim
        · exact hz
      · intro hz
        exact ⟨Or.inr hz, fun e => hnmem (e ▸ hz)⟩
    have hFTout : FT ⊆ (staircaseVertices A C B R₀)ᶜ := by
      rintro z ⟨hzf, -⟩ (hzR | hzS)
      · exact hdisj z hzf hzR
      · exact hFout (by rw [hFeq]; exact hzf) hzS
    have hFTconn : ConnectedSet G FT := by
      rw [hFTtail]
      exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        (by simpa only [List.drop_one] using
          (Workspace.ProofLemmas.PathBasics.isPathList_drop hfpath.1 (k := 1) (by omega)))
    have hyatt : y ∈ attachments G FT (staircaseVertices A C B R₀) :=
      ⟨Or.inr (Or.inl (Or.inl hyA)), x, ⟨hxf, hxf₁⟩, hxy.symm⟩
    have hbatt : b₀ ∈ attachments G FT (staircaseVertices A C B R₀) :=
      ⟨Or.inl hb₀R₀, f[i]'hi, ⟨List.getElem_mem hi, hfi_ne_f₁_of_pos hipos⟩, hbi⟩
    have hFTnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
        (attachments G FT (staircaseVertices A C B R₀)) := by
      rintro (h | h | h | h)
      · exact hban.2.2.2.1.1 (h hbatt)
      · exact hban.2.1 y (h hyatt) (Or.inl (Or.inl hyA))
      · rcases h hbatt with hbA | hba
        · exact hban.2.2.2.1.1 (Or.inl (Or.inl hbA))
        · exact ha₀b₀_endgame hba.symm
      · rcases h hyatt with hyB | hyb
        · exact (Set.disjoint_left.mp hAB hyA) hyB
        · exact hban.2.2.2.1.1 (by rw [← hyb]; exact Or.inl (Or.inl hyA))
    rcases Workspace.Statements.S12.SPGT.thm_12_2 G hG hK4 hprism hbreaker
        A C B a₀ b₀ R₀ hK FT hFTout hFTconn hFTnonlocal with
      ⟨z, hz, hzmaj⟩ | ⟨p, q, Q, hQsub, hQban, -⟩ |
        ⟨p, q, Q, hQsub, hQpath, hcase⟩
    · exact hnomajor z (by rw [hFeq]; exact hz.1) hzmaj
    · have hq := hQsub q (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQban.1).2
      exact hnors q hq.1 hQban.2.2.2.1
    · rcases hcase with ⟨hleft, -, -⟩ | ⟨hright, -, -⟩
      · have hp := hQsub p (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).1
        exact hp.2 (hf₁uniq p hp.1 hleft)
      · have hp := hQsub p (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQpath).1
        exact hnors p hp.1 hright

  let L : List V := f.take (i + 1)
  let R₀' : List V := L ++ [b₀]
  have hLpath : IsPathFrom G L f₁ (f[i]'hi) := by
    exact isPathFrom_take_to_index hfpath i hi
  have hLmem : ∀ x ∈ L, x ∈ f := by
    intro x hx
    exact List.mem_of_mem_take hx
  have hLnefk : ∀ x ∈ L, x ≠ fk := by
    intro x hx e
    obtain ⟨j, hjmin, hjx⟩ := List.mem_take_iff_getElem.mp hx
    have hj : j < f.length := by omega
    have hjle : j ≤ i := by omega
    have hji : j = f.length - 1 := hfpath.1.2.1.getElem_inj_iff.mp (by
      rw [hjx, e, hlast])
    omega
  have hb₀notL : b₀ ∉ L := by
    intro hbL
    exact hdisj b₀ (hLmem b₀ hbL) hb₀R₀
  have hb₀onlyLastL : ∀ x ∈ L, x ≠ f[i]'hi → ¬ G.Adj b₀ x := by
    intro x hx hxlast hbx
    obtain ⟨j, hjmin, hjx⟩ := List.mem_take_iff_getElem.mp hx
    have hj : j < f.length := by omega
    have hjle : j ≤ i := by omega
    have hji : j ≠ i := by
      intro e
      exact hxlast (by rw [← hjx]; exact getElem_eq_of_index_eq f hj hi e)
    exact himin j hj (by omega) (hjx ▸ hbx)
  have hR₀'path : IsPathFrom G R₀' f₁ b₀ := by
    exact Workspace.ProofLemmas.PathAttach.isPathFrom_concat hLpath hbi hb₀notL hb₀onlyLastL
  have hprefixAntiA : ∀ x ∈ L, x ≠ f₁ → ∀ y ∈ A, ¬ G.Adj x y := by
    intro x hx hxf₁ y hyA
    by_cases hi0 : i = 0
    · obtain ⟨j, hjmin, hjx⟩ := List.mem_take_iff_getElem.mp hx
      have hj : j = 0 := by omega
      have hzero : f[0]'(by omega) = f₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 (by omega)
      exact (hxf₁ (by rw [← hjx]; exact getElem_eq_of_index_eq f (by omega) (by omega) hj |>.trans hzero)).elim
    · exact htailAntiA_of_pos (by omega) x (hLmem x hx) hxf₁ y hyA
  have hprefixAntiBC : ∀ x ∈ L, x ≠ f₁ → ∀ y ∈ B ∪ C, ¬ G.Adj x y := by
    intro x hx hxf₁ y hyBC hxy
    exact hLnefk x hx (hattuniq x (hLmem x hx) ⟨y, hyBC, hxy⟩)
  have hR₀'out : ∀ x ∈ R₀', x ∉ A ∪ B ∪ C := by
    intro x hx
    rcases List.mem_append.mp hx with hxL | hxB
    · exact hFout (by rw [hFeq]; exact hLmem x hxL)
    · have ex : x = b₀ := by simpa using hxB
      exact ex ▸ hban.2.2.2.1.1
  have hR₀'int : SPGT.Anticomplete G {x : V | x ∈ SPGT.interior R₀'} (A ∪ B ∪ C) := by
    intro x hx y hy
    have hxdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR₀'path).mp hx
    rcases List.mem_append.mp hxdata.1 with hxL | hxB
    · rcases hy with (hyA | hyB) | hyC
      · exact hprefixAntiA x hxL hxdata.2.1 y hyA
      · exact hprefixAntiBC x hxL hxdata.2.1 y (Or.inl hyB)
      · exact hprefixAntiBC x hxL hxdata.2.1 y (Or.inr hyC)
    · have ex : x = b₀ := by simpa using hxB
      exact (hxdata.2.2 ex).elim
  have hban' : IsBanister G A C B f₁ R₀' b₀ :=
    ⟨hR₀'path, hR₀'out, hf₁left, hban.2.2.2.1, hR₀'int⟩
  have hstep' : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ :=
    ⟨hr₁, hr₂, hR₁R₂, hcross₁₂⟩
  have hformBase : FormPrism G ![a₁, a₂, f₁] ![b₁, b₂, b₀] R₁ R₂ R₀' :=
    Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step hban' hstep'
  have hformMid : FormPrism G ![f₁, a₂, a₁] ![b₀, b₂, b₁] R₀' R₂ R₁ := by
    have hp := Workspace.ProofLemmas.PrismSymmetry.formPrism_perm
      (a := ![a₁, a₂, f₁]) (b := ![b₁, b₂, b₀]) (R := ![R₁, R₂, R₀'])
      hformBase (Equiv.swap (0 : Fin 3) 2)
    have haeq : (fun j => ![a₁, a₂, f₁] ((Equiv.swap (0 : Fin 3) 2) j)) =
        ![f₁, a₂, a₁] := by funext j; fin_cases j <;> rfl
    have hbeq : (fun j => ![b₁, b₂, b₀] ((Equiv.swap (0 : Fin 3) 2) j)) =
        ![b₀, b₂, b₁] := by funext j; fin_cases j <;> rfl
    have hReq : (fun j => ![R₁, R₂, R₀'] ((Equiv.swap (0 : Fin 3) 2) j)) =
        ![R₀', R₂, R₁] := by funext j; fin_cases j <;> rfl
    rw [haeq, hbeq, hReq] at hp
    exact hp
  have hform' : FormPrism G ![f₁, a₁, a₂] ![b₀, b₁, b₂] R₀' R₁ R₂ := by
    have hp := Workspace.ProofLemmas.PrismSymmetry.formPrism_perm
      (a := ![f₁, a₂, a₁]) (b := ![b₀, b₂, b₁]) (R := ![R₀', R₂, R₁])
      hformMid (Equiv.swap (1 : Fin 3) 2)
    have haeq : (fun j => ![f₁, a₂, a₁] ((Equiv.swap (1 : Fin 3) 2) j)) =
        ![f₁, a₁, a₂] := by funext j; fin_cases j <;> rfl
    have hbeq : (fun j => ![b₀, b₂, b₁] ((Equiv.swap (1 : Fin 3) 2) j)) =
        ![b₀, b₁, b₂] := by funext j; fin_cases j <;> rfl
    have hReq : (fun j => ![R₀', R₂, R₁] ((Equiv.swap (1 : Fin 3) 2) j)) =
        ![R₀', R₁, R₂] := by funext j; fin_cases j <;> rfl
    rw [haeq, hbeq, hReq] at hp
    exact hp
  let KP : Set V := {z : V | z ∈ R₀'} ∪ {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂}
  let FT : Set V := {z : V | z ∈ f.drop (i + 1)}
  have hiNext : i + 1 < f.length := by omega
  have hFTindex : ∀ x ∈ FT, ∃ (j : ℕ) (hj : j < f.length), i + 1 ≤ j ∧ f[j]'hj = x := by
    intro x hx
    exact (mem_drop_with_index f (i + 1)).mp hx
  have hFTmem : ∀ x ∈ FT, x ∈ f := by
    intro x hx
    exact List.mem_of_mem_drop hx
  have hFTneF₁ : ∀ x ∈ FT, x ≠ f₁ := by
    intro x hx e
    obtain ⟨j, hj, hij, hjx⟩ := hFTindex x hx
    have hzero : f[0]'(by omega) = f₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hfpath.2.1 (by omega)
    have : j = 0 := hfpath.1.2.1.getElem_inj_iff.mp (by rw [hjx, e, hzero])
    omega
  have hFTconn : ConnectedSet G FT :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
      (Workspace.ProofLemmas.PathBasics.isPathList_drop hfpath.1 (k := i + 1) hiNext)
  have hFTKP : FT ⊆ KPᶜ := by
    intro x hx
    change x ∉ ({z : V | z ∈ R₀'} ∪ {z : V | z ∈ R₁} ∪ {z : V | z ∈ R₂})
    rintro ((hxR₀' | hxR₁) | hxR₂)
    · rcases List.mem_append.mp hxR₀' with hxL | hxb
      · obtain ⟨j, hj, hij, hjx⟩ := hFTindex x hx
        obtain ⟨r, hrmin, hrx⟩ := List.mem_take_iff_getElem.mp hxL
        have hr : r < f.length := by omega
        have hre : j = r := hfpath.1.2.1.getElem_inj_iff.mp (hjx.trans hrx.symm)
        omega
      · have ex : x = b₀ := by simpa using hxb
        exact hdisj x (hFTmem x hx) (ex ▸ hb₀R₀)
    · exact hFout (by rw [hFeq]; exact hFTmem x hx) (hR₁S x hxR₁)
    · exact hFout (by rw [hFeq]; exact hFTmem x hx) (hR₂S x hxR₂)
  have hnoR₂ : ∀ x ∈ FT, ∀ y ∈ R₂, ¬ G.Adj x y := by
    intro x hx y hy hxy
    have hc := (hclaim3 x (hFTmem x hx) y hy).mp hxy
    exact hFTneF₁ x hx hc.1
  have hfiL : f[i]'hi ∈ L := by
    apply List.mem_take_iff_getElem.mpr
    exact ⟨i, by omega, rfl⟩
  have hfiR₀' : f[i]'hi ∈ R₀' := by
    exact List.mem_append_left _ hfiL
  have hnextFT : f[i + 1]'hiNext ∈ FT := by
    exact (mem_drop_with_index f (i + 1)).mpr ⟨i + 1, hiNext, le_rfl, rfl⟩
  have hadjNext : G.Adj (f[i]'hi) (f[i + 1]'hiNext) :=
    Workspace.ProofLemmas.PathBasics.path_adj_succ hfpath.1 hiNext
  have hfiAtt : f[i]'hi ∈ attachments G FT KP := by
    refine ⟨?_, f[i + 1]'hiNext, hnextFT, hadjNext⟩
    exact Or.inl (Or.inl hfiR₀')
  obtain ⟨x₁, hx₁R₁, hx₁ne, hfkx₁⟩ := hfk₁
  have hfkFT : fk ∈ FT := by
    apply (mem_drop_with_index f (i + 1)).mpr
    exact ⟨f.length - 1, by omega, by omega, hlast⟩
  have hx₁Att : x₁ ∈ attachments G FT KP :=
    ⟨Or.inl (Or.inr hx₁R₁), fk, hfkFT, hfkx₁.symm⟩
  have hnonlocal : ¬ LocalForPrism ![f₁, a₁, a₂] ![b₀, b₁, b₂]
      R₀' R₁ R₂ (attachments G FT KP) := by
    rintro (h | h | h | h | h)
    · exact hR₀'out x₁ (h hx₁Att) (hR₁S x₁ hx₁R₁)
    · exact hR₀'out (f[i]'hi) hfiR₀' (hR₁S (f[i]'hi) (h hfiAtt))
    · exact hR₁R₂ x₁ hx₁R₁ (h hx₁Att)
    · have hx := h hx₁Att
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with e | e | e
      · exact hf₁left.1 (e ▸ hR₁S x₁ hx₁R₁)
      · exact hx₁ne e
      · exact hR₁R₂ x₁ hx₁R₁ (e ▸ ha₂R₂)
    · have hx := h hfiAtt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with e | e | e
      · exact hdisj (f[i]'hi) (List.getElem_mem hi) (e ▸ hb₀R₀)
      · exact hFout (by rw [hFeq]; exact List.getElem_mem hi) (e ▸ hR₁S b₁ hb₁R₁)
      · exact hFout (by rw [hFeq]; exact List.getElem_mem hi) (e ▸ hR₂S b₂ hb₂R₂)
  have hnoAttR₂ : ∀ y ∈ attachments G FT KP, y ∉ R₂ := by
    rintro y ⟨-, x, hx, hyx⟩ hyR₂
    exact hnoR₂ x hx y hyR₂ hyx.symm
  have hPrismMajor : ∀ x ∈ FT,
      ¬ MajorForPrism G ![f₁, a₁, a₂] ![b₀, b₁, b₂] x := by
    exact Workspace.ProofLemmas.Thm104NoMajor.thm104_no_major G hG
      ![f₁, a₁, a₂] ![b₀, b₁, b₂] ![R₀', R₁, R₂] KP FT
      hform' rfl hFTKP
      (by intro hev; exact (hprism ⟨_, _, _, _, _, hev⟩).elim) hnoAttR₂
  obtain ⟨Q, s, t, hQpath, hQlen, hQFT, hsf₁, hsa₁, htb₀, htb₁, hQcross⟩ :=
    prismJumpPath hG hK4 ![f₁, a₁, a₂] ![b₀, b₁, b₂]
      ![R₀', R₁, R₂] KP FT hform' rfl hFTKP hFTconn hnonlocal hPrismMajor hnoR₂
  have hsf₁' : G.Adj s f₁ := by simpa using hsf₁
  have hsa₁' : G.Adj s a₁ := by simpa using hsa₁
  have htb₀' : G.Adj t b₀ := by simpa using htb₀
  have htb₁' : G.Adj t b₁ := by simpa using htb₁
  have hQcross' : ∀ x ∈ Q, ∀ z ∈ KP, G.Adj x z →
      (x = s ∧ (z = f₁ ∨ z = a₁)) ∨ (x = t ∧ (z = b₀ ∨ z = b₁)) := by
    simpa using hQcross
  have htQ : t ∈ Q := List.mem_of_mem_getLast? hQpath.2.2
  have hsQ : s ∈ Q := List.mem_of_mem_head? hQpath.2.1
  have htFT := hQFT t htQ
  have htf : t ∈ f := hFTmem t htFT
  have htfk : t = fk :=
    hattuniq t htf ⟨b₁, Or.inl hr₁.2.2.1, htb₁'⟩
  have hst : s ≠ t := by
    apply Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hQpath
    simp only [pathLength]
    omega
  have hb₀KP : b₀ ∈ KP := by
    exact Or.inl (Or.inl (List.mem_append_right L (by simp)))
  have ha₁KP : a₁ ∈ KP := Or.inl (Or.inr ha₁R₁)
  have hfkNoa₁ : ¬ G.Adj a₁ fk := by
    intro hafk
    have hc := hQcross' t htQ a₁ ha₁KP (htfk ▸ hafk.symm)
    rcases hc with hc | hc
    · exact hst hc.1.symm
    · rcases hc.2 with e | e
      · exact hban.2.2.2.1.1 (by rw [← e]; exact Or.inl (Or.inl hr₁.2.1))
      · exact (Set.disjoint_left.mp hAB hr₁.2.1) (e ▸ hr₁.2.2.1)
  have hR₁len : 2 ≤ R₁.length := by
    simpa using
      (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length
        (R := ![R₀', R₁, R₂]) hform' 1)
  let P₁ : List V := R₁.drop 1
  have hP₁path : IsPathFrom G P₁ (R₁[1]'(by omega)) b₁ :=
    isPathFrom_drop_to_last hr₁.1 1 (by omega)
  have hP₁mem : ∀ x ∈ P₁, x ∈ R₁ := by
    intro x hx
    exact List.mem_of_mem_drop hx
  have hP₁neA : ∀ x ∈ P₁, x ≠ a₁ := by
    intro x hx e
    obtain ⟨j, hj, hj1, hjx⟩ := (mem_drop_with_index R₁ 1).mp hx
    have hzero : R₁[0]'(by omega) = a₁ :=
      Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hr₁.1.2.1 (by omega)
    have : j = 0 := hr₁.1.1.2.1.getElem_inj_iff.mp (by rw [hjx, e, hzero])
    omega
  have hlink : Workspace.Types.RousselRubio.SPGT.VertexCanBeLinkedOntoTriangle
      G a₁ b₀ b₁ fk := by
    refine ⟨R₀, P₁, Q, ⟨hban.1.1, hP₁path.1, hQpath.1⟩, ⟨?_, ?_, ?_⟩,
      ⟨Or.inr hban.1.2.2, Or.inr hP₁path.2.2, Or.inr (htfk ▸ hQpath.2.2)⟩,
      ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
    · intro x hx hxP₁
      exact hban.2.1 x hx (hR₁S x (hP₁mem x hxP₁))
    · intro x hx hxQ
      exact hdisj x (hFTmem x (hQFT x hxQ)) hx
    · intro x hx hxQ
      exact hFout (by rw [hFeq]; exact hFTmem x (hQFT x hxQ))
        (hR₁S x (hP₁mem x hx))
    · intro x hx y hy
      constructor
      · intro hxy
        rcases (claim3_banister_rung_edges hban hr₁ x hx y (hP₁mem y hy)).mp hxy with
          hleft | hright
        · exact (hP₁neA y hy hleft.2).elim
        · exact ⟨hright.1, hright.2⟩
      · intro h
        exact h.1 ▸ h.2 ▸
          (claim3_banister_rung_edges hban hr₁ b₀ hb₀R₀ b₁ hb₁R₁).mpr
            (Or.inr ⟨rfl, rfl⟩)
    · intro x hx y hy
      constructor
      · intro hxy
        by_cases hxb : x = b₀
        · subst x
          rcases hQcross' y hy b₀ hb₀KP hxy.symm with hc | hc
          · rcases hc.2 with e | e
            · exact (hdisj f₁ hf₁mem (e.symm ▸ hb₀R₀)).elim
            · exact (hban.2.2.2.1.1 (by rw [e]; exact Or.inl (Or.inl hr₁.2.1))).elim
          · exact ⟨rfl, hc.1.trans htfk⟩
        · exact (hanti y ⟨hFTmem y (hQFT y hy), hFTneF₁ y (hQFT y hy)⟩
            x ⟨hx, hxb⟩ hxy.symm).elim
      · intro h
        exact h.1 ▸ h.2 ▸ (htfk ▸ htb₀'.symm)
    · intro x hx y hy
      constructor
      · intro hxy
        have hxR₁ := hP₁mem x hx
        have hxKP : x ∈ KP := Or.inl (Or.inr hxR₁)
        rcases hQcross' y hy x hxKP hxy.symm with hc | hc
        · rcases hc.2 with e | e
          · exact (hf₁left.1 (e.symm ▸ hR₁S x hxR₁)).elim
          · exact (hP₁neA x hx e).elim
        · rcases hc.2 with e | e
          · exact (hban.2.2.2.1.1 (e.symm ▸ hR₁S x hxR₁)).elim
          · exact ⟨e, hc.1.trans htfk⟩
      · intro h
        exact h.1 ▸ h.2 ▸ (htfk ▸ htb₁'.symm)
    · exact ⟨a₀, ha₀R₀, (hban.2.2.1.2.1 a₁ hr₁.2.1).symm⟩
    · refine ⟨R₁[1]'(by omega), List.mem_of_mem_head? hP₁path.2.1, ?_⟩
      have hadj := Workspace.ProofLemmas.PathBasics.path_adj_succ hr₁.1.1
        (i := 0) (by omega)
      have hzero : R₁[0]'(by omega) = a₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hr₁.1.2.1 (by omega)
      rwa [hzero] at hadj
    · exact ⟨s, hsQ, hsa₁'.symm⟩
  rcases Workspace.Statements.S02.SPGT.thm_2_4 G hG a₁ b₀ b₁ fk hlink with
    ⟨ha₁b₀, -⟩ | ⟨ha₁b₀, -⟩ | ⟨-, ha₁fk⟩
  · exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) ha₁b₀.symm
  · exact hban.2.2.2.1.2.2 a₁ (Or.inl hr₁.2.1) ha₁b₀.symm
  · exact hfkNoa₁ ha₁fk

/-- **12.3, body.**  In the situation left by the opening reduction, and assuming no vertex of
`F` is major, `F` contains a banister.  This is the whole of the printed proof from *"We may
assume there is no major vertex in `F`"* to the end. -/
theorem thm123Body [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hprism : ¬ ∃ (a b : Fin 3 → V) (R₁ R₂ R₃ : List V), IsEvenPrism G a b R₁ R₂ R₃)
    (hbreaker : ¬ ∃ A' C' B' F' Q' : Set V, IsOneBreaker G A' C' B' F' Q')
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : MaximalStaircase G A C B a₀ R₀ b₀)
    (F : Set V) (f : List V) (f₁ fk : V)
    (hS : Setup G A C B a₀ R₀ b₀ F f f₁ fk) :
    ∃ (u v : V) (R : List V), (∀ w ∈ R, w ∈ F) ∧ IsBanister G A C B u R v := by
  -- (1)
  rcases claim1 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK F f f₁ fk hS with
    hban | ⟨hnors, hnotB⟩
  · exact hban
  -- (2)
  obtain ⟨hdisj, hanti⟩ :=
    claim2 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK F f f₁ fk hS hnors hnotB
  -- the step `a₁-R₁-b₁, a₂-R₂-b₂`
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hfk₁, hfkb₂⟩ :=
    stepChoice G A C B a₀ b₀ R₀ hK F f f₁ fk hS hnotB
  -- (3)
  have hclaim3 :=
    claim3 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK F f f₁ fk hS hnors hnotB hdisj hanti
      a₁ R₁ b₁ a₂ R₂ b₂ hstep hfk₁ hfkb₂
  -- (4)
  have hclaim4 :=
    claim4 G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK F f f₁ fk hS hnors hnotB hdisj hanti
      a₁ R₁ b₁ a₂ R₂ b₂ hstep hfk₁ hfkb₂ hclaim3
  -- the final paragraph is a contradiction
  exact absurd
    (endgame G hG hK4 hprism hbreaker A C B a₀ b₀ R₀ hK F f f₁ fk hS hnors hnotB hdisj hanti
      a₁ R₁ b₁ a₂ R₂ b₂ hstep hfk₁ hfkb₂ hclaim3 hclaim4)
    not_false

end Workspace.ProofLemmas.Thm123Body
