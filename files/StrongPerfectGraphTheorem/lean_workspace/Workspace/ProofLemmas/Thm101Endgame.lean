import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm101Assembly
-- extra imports needed by the proof only
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.Thm101K4Appearance
import Workspace.ProofLemmas.Thm101ClaimOne
import Workspace.Statements.S02.Thm_2_4

/-!
# 10.1, the last printed paragraph: `X₁ ⊆ V(R₂)` and `X₂ ⊆ V(R₁)`

Proof of `Workspace.ProofLemmas.Thm101Endgame.endgame`, following `paper/proofs/10_1.md`
sentence by sentence.  It is claim (1)'s Case A with the single vertex `f₁` replaced by the
whole path `f₁-⋯-fₙ`, so the `cᵢ`/`dᵢ`/`Cᵢ`/`Dᵢ` machinery, the `link_direct` packaging and the
slice lemmas are all imported from `Workspace.ProofLemmas.Thm101ClaimOne`; the helpers above
the theorem are the three appeals to 2.4 in their path-connector form.

One simplification over claim (1): the paper's *"but `f₁` has at most one neighbour in `A`
(because `n ≥ 2`)"* is automatic here — every `V(K)`-neighbour of `f₁` lies on `R₁`, and
`A ∩ V(R₁) = {a₁}` — so the second linking needs no `A`/`B` exchange.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101Endgame

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT
open Workspace.ProofLemmas.Thm101ClaimOne

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (10.1, closing paragraph): *"If `c₁, d₁` are nonadjacent, then `f₁` can be linked
onto `A` via `f₁-c₁-C₁-a₁`, `f₁-⋯-fₙ-c₂-C₂-a₂`, `f₁-d₁-D₁-b₁-b₃-R₃-a₃`; but `f₁` has at most
one neighbour in `A` (because `n ≥ 2`), contrary to 2.4."*

`k0`, `k0'` index `c₁`, `d₁` on `R 0`; `k1` indexes `c₂` on `R 1`.  `hgap` is *"`c₁, d₁` are
nonadjacent"* (with `c₁ ≠ d₁`), `hb1` the already-established `c₂ ≠ b₂`.  No `A`/`B` exchange is
needed here: `f₁`'s neighbours in `V(K)` all lie on `R 0`, and `A ∩ V(R 0) = {a₁}` — that is
exactly the paper's parenthesis *"because `n ≥ 2`"*. -/
theorem link_nonadjacent_path {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {f : List V} {f₁ fn : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hf : IsPathFrom G f f₁ fn) (hn : 2 ≤ f.length)
    (hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i)
    (hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0)
    (hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1)
    (hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y)
    {k0 k0' k1 : ℕ} (hk0 : k0 < (R 0).length) (hk0' : k0' < (R 0).length)
    (hk1 : k1 < (R 1).length)
    (hc1 : G.Adj f₁ ((R 0)[k0]'hk0)) (hd1 : G.Adj f₁ ((R 0)[k0']'hk0'))
    (hc2 : G.Adj fn ((R 1)[k1]'hk1))
    (hk1min : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj fn ((R 1)[t]'ht) → k1 ≤ t)
    (hgap : k0 + 1 < k0')
    (hb1 : (R 1)[k1]'hk1 ≠ b 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hndf : f.Nodup := hf.1.2.1
  have hflen : 0 < f.length := by omega
  have h1f : 1 < f.length := by omega
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  have hf0 : f[0]'hflen = f₁ := PathBasics.getElem_zero_of_head? hf.2.1 hflen
  have ha0nd : a 0 ∉ (R 0).drop k0' := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k0' + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have hb0nt : b 0 ∉ (R 0).take (k0 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have hb1nt : b 1 ∉ (R 1).take (k1 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hte, hlast1])
    exact hb1 ((hnd1.getElem_inj_iff.mpr (by omega : k1 = t)).trans hte)
  -- the tail `f₂-⋯-fₙ`
  have htail : IsPathFrom G (f.drop 1) (f[1]'h1f) fn := drop_pathFrom hf h1f
  have hmemtail : ∀ x ∈ f.drop 1, x ∈ f ∧ x ≠ f₁ := by
    intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
    refine ⟨List.getElem_mem _, ?_⟩
    intro hc
    rw [← hf0] at hc
    have := hndf.getElem_inj_iff.mp hc
    omega
  have hnoTail : ∀ x ∈ f.drop 1, ∀ (i : Fin 3) (y : V), y ∈ R i → i ≠ 1 → ¬ G.Adj x y := by
    intro x hx i y hy hi hadj
    obtain ⟨hxf, hxne1⟩ := hmemtail x hx
    by_cases hxn : x = fn
    · exact hi (hNn i y hy (hxn ▸ hadj))
    · exact hNint x hxf hxne1 hxn i y hy hadj
  -- `P₂ = f₁-⋯-fₙ-c₂-C₂-a₂` with its first vertex removed
  have hdisjTail : ∀ x ∈ f.drop 1, x ∉ ((R 1).take (k1 + 1)).reverse := by
    intro x hx hy
    rw [List.mem_reverse] at hy
    exact hfK x (hmemtail x hx).1 1 (List.mem_of_mem_take hy)
  have hcrossTail : ∀ x ∈ f.drop 1, ∀ y ∈ ((R 1).take (k1 + 1)).reverse,
      (G.Adj x y ↔ (x = fn ∧ y = (R 1)[k1]'hk1)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    obtain ⟨hxf, hxne1⟩ := hmemtail x hx
    constructor
    · intro hadj
      by_cases hxn : x = fn
      · subst hxn
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hy
        exact ⟨rfl, hnd1.getElem_inj_iff.mpr (by have := hk1min t ht hadj; omega)⟩
      · exact absurd hadj (hNint x hxf hxne1 hxn 1 y (List.mem_of_mem_take hy))
    · rintro ⟨rfl, rfl⟩
      exact hc2
  have hP2 : IsPathFrom G (f.drop 1 ++ ((R 1).take (k1 + 1)).reverse) (f[1]'h1f) (a 1) :=
    PathGlue.glue_path htail
      (PathBasics.isPathFrom_reverse (take_pathFrom (hp 1) hk1)) hdisjTail hcrossTail
  have hmemP2 : ∀ x : V, x ∈ f.drop 1 ++ ((R 1).take (k1 + 1)).reverse ↔
      (x ∈ f.drop 1 ∨ x ∈ (R 1).take (k1 + 1)) := by
    intro x; rw [List.mem_append, List.mem_reverse]
  -- `P₃ = d₁-D₁-b₁-b₃-R₃-a₃`
  have hdisjD2 : ∀ x ∈ (R 0).drop k0', x ∉ (R 2).reverse := by
    intro x hx hx2
    rw [List.mem_reverse] at hx2
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) hx2
  have hcrossD : ∀ x ∈ (R 0).drop k0', ∀ y ∈ (R 2).reverse,
      (G.Adj x y ↔ (x = b 0 ∧ y = b 2)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    rw [hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y hy]
    exact ⟨fun h => h.elim (fun h1 => absurd (h1.1 ▸ hx) ha0nd) id, fun h => Or.inr h⟩
  have hP3 : IsPathFrom G ((R 0).drop k0' ++ (R 2).reverse) ((R 0)[k0']'hk0') (a 2) :=
    PathGlue.glue_path (drop_pathFrom (hp 0) hk0')
      (PathBasics.isPathFrom_reverse (hp 2)) hdisjD2 hcrossD
  have hmemP3 : ∀ y : V, y ∈ (R 0).drop k0' ++ (R 2).reverse ↔
      (y ∈ (R 0).drop k0' ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  have hadj01 : G.Adj f₁ (f[1]'h1f) := by
    have h := (PathBasics.path_adj_iff hf.1 hflen h1f).mpr (Or.inl rfl)
    rwa [hf0] at h
  have hlink := link_direct (v := f₁)
    (take_pathFrom (hp 0) hk0).1 hP2.1 hP3.1
    (fun x hx hx2 => by
      rcases (hmemP2 x).mp hx2 with h | h
      · exact hfK x (hmemtail x h).1 0 (List.mem_of_mem_take hx)
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
          (List.mem_of_mem_take hx) (List.mem_of_mem_take h))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp h
        have heq : t = k0' + s := hnd0.getElem_inj_iff.mp (by rw [hte, hse])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) h)
    (fun x hx hx3 => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact hfK x (hmemtail x h1).1 0 (List.mem_of_mem_drop h)
        · exact hfK x (hmemtail x h1).1 2 h
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
            (List.mem_of_mem_take h1) (List.mem_of_mem_drop h)
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_take h1) h)
    (Or.inl (take_pathFrom (hp 0) hk0).2.1) (Or.inr hP2.2.2) (Or.inr hP3.2.2)
    (hAtri 0 1 (by decide)) (hAtri 0 2 (by decide)) (hAtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hmemP2 y).mp hy with h | h
      · exact absurd hadj.symm (hnoTail y h 0 x (List.mem_of_mem_take hx) (by decide))
      · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_take hx) y
          (List.mem_of_mem_take h)).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 ht hs).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y h).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · exfalso
        rcases (hmemP3 y).mp hy with h | h
        · exact hnoTail x h1 0 y (List.mem_of_mem_drop h) (by decide) hadj
        · exact hnoTail x h1 2 y h (by decide) hadj
      · rcases (hmemP3 y).mp hy with h | h
        · exfalso
          rcases (hedge 1 0 (by decide) x (List.mem_of_mem_take h1) y
            (List.mem_of_mem_drop h)).mp hadj with hh | hh
          · exact ha0nd (hh.2 ▸ h)
          · exact hb1nt (hh.1 ▸ h1)
        · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_take h1) y h).mp hadj with hh | hh
          · exact hh
          · exact absurd (hh.1 ▸ h1) hb1nt)
    ⟨(R 0)[k0]'hk0, PathBasics.getLast_mem (take_pathFrom (hp 0) hk0).2.2, hc1⟩
    ⟨f[1]'h1f, (hmemP2 _).mpr (Or.inl (PathBasics.head_mem htail.2.1)), hadj01⟩
    ⟨(R 0)[k0']'hk0', (hmemP3 _).mpr
      (Or.inl (PathBasics.head_mem (drop_pathFrom (hp 0) hk0').2.1)), hd1⟩
  have hnotA : ∀ i : Fin 3, i ≠ 0 → ¬ G.Adj f₁ (a i) := fun i hi hadj =>
    hi (hN1 i (a i) (PathBasics.head_mem (hp i).2.1) hadj)
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG f₁ (a 0) (a 1) (a 2) hlink with
      h | h | h
  exacts [hnotA 1 (by decide) h.2, hnotA 2 (by decide) h.2, hnotA 1 (by decide) h.1]

/-- PAPER (10.1, closing paragraph): *"If `c₁ = d₁`, then from the symmetry we may assume that
`c₁ ≠ a₁`, and `c₂ ≠ b₂`; but then `c₁` can be linked onto `A`, via `c₁-C₁-a₁`,
`c₁-f₁-⋯-fₙ-c₂-C₂-a₂`, `c₁-D₁-b₁-b₃-R₃-a₃`, contrary to 2.4."*

`honly0` is `c₁ = d₁`: `(R 0)[j0+1]` is the *only* attachment of `f₁` on `R 0`; writing the
index as `j0 + 1` is the paper's `c₁ ≠ a₁`, and `hb1` is its `c₂ ≠ b₂`. -/
theorem link_equal_path {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {f : List V} {f₁ fn : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hf : IsPathFrom G f f₁ fn) (hn : 2 ≤ f.length)
    (hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i)
    (hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0)
    (hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1)
    (hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y)
    {j0 k1 : ℕ} (hk0 : j0 + 1 < (R 0).length) (hk1 : k1 < (R 1).length)
    (hc1 : G.Adj f₁ ((R 0)[j0 + 1]'hk0)) (hc2 : G.Adj fn ((R 1)[k1]'hk1))
    (honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj f₁ ((R 0)[t]'ht) → t = j0 + 1)
    (hk1min : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj fn ((R 1)[t]'ht) → k1 ≤ t)
    (hb1 : (R 1)[k1]'hk1 ≠ b 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hj0 : j0 < (R 0).length := by omega
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  have hb0nt : b 0 ∉ (R 0).take (j0 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have ha0nd : a 0 ∉ (R 0).drop (j0 + 2) := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : j0 + 2 + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have hb1nt : b 1 ∉ (R 1).take (k1 + 1) := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hmem
    have heq : t = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hte, hlast1])
    exact hb1 ((hnd1.getElem_inj_iff.mpr (by omega : k1 = t)).trans hte)
  -- no vertex of `f` has a neighbour on `C₁` or on `D₁`
  have hfC1 : ∀ x ∈ f, ∀ y ∈ (R 0).take (j0 + 1), ¬ G.Adj x y := by
    intro x hx y hy hadj
    obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hy
    by_cases hx1 : x = f₁
    · subst hx1
      have := honly0 t ht hadj
      omega
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 0 _ (List.getElem_mem ht) hadj) (by decide)
    · exact hNint x hx hx1 hxn 0 _ (List.getElem_mem ht) hadj
  have hfD1 : ∀ x ∈ f, ∀ y ∈ (R 0).drop (j0 + 2), ¬ G.Adj x y := by
    intro x hx y hy hadj
    obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hy
    by_cases hx1 : x = f₁
    · subst hx1
      have := honly0 (j0 + 2 + s) hs hadj
      omega
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 0 _ (List.getElem_mem hs) hadj) (by decide)
    · exact hNint x hx hx1 hxn 0 _ (List.getElem_mem hs) hadj
  have hfR2 : ∀ x ∈ f, ∀ y ∈ R 2, ¬ G.Adj x y := by
    intro x hx y hy hadj
    by_cases hx1 : x = f₁
    · subst hx1
      exact absurd (hN1 2 y hy hadj) (by decide)
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 2 y hy hadj) (by decide)
    · exact hNint x hx hx1 hxn 2 y hy hadj
  -- `P₂ = f₁-⋯-fₙ-c₂-C₂-a₂`
  have hdisjF : ∀ x ∈ f, x ∉ ((R 1).take (k1 + 1)).reverse := by
    intro x hx hy
    rw [List.mem_reverse] at hy
    exact hfK x hx 1 (List.mem_of_mem_take hy)
  have hcrossF : ∀ x ∈ f, ∀ y ∈ ((R 1).take (k1 + 1)).reverse,
      (G.Adj x y ↔ (x = fn ∧ y = (R 1)[k1]'hk1)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    constructor
    · intro hadj
      by_cases hxn : x = fn
      · subst hxn
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hy
        exact ⟨rfl, hnd1.getElem_inj_iff.mpr (by have := hk1min t ht hadj; omega)⟩
      by_cases hx1 : x = f₁
      · subst hx1
        exact absurd (hN1 1 y (List.mem_of_mem_take hy) hadj) (by decide)
      · exact absurd hadj (hNint x hx hx1 hxn 1 y (List.mem_of_mem_take hy))
    · rintro ⟨rfl, rfl⟩
      exact hc2
  have hP2 : IsPathFrom G (f ++ ((R 1).take (k1 + 1)).reverse) f₁ (a 1) :=
    PathGlue.glue_path hf
      (PathBasics.isPathFrom_reverse (take_pathFrom (hp 1) hk1)) hdisjF hcrossF
  have hmemP2 : ∀ x : V, x ∈ f ++ ((R 1).take (k1 + 1)).reverse ↔
      (x ∈ f ∨ x ∈ (R 1).take (k1 + 1)) := by
    intro x; rw [List.mem_append, List.mem_reverse]
  -- `P₃ = D₁-b₁-b₃-R₃-a₃`
  have hdisjD2 : ∀ x ∈ (R 0).drop (j0 + 2), x ∉ (R 2).reverse := by
    intro x hx hx2
    rw [List.mem_reverse] at hx2
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) hx2
  have hcrossD : ∀ x ∈ (R 0).drop (j0 + 2), ∀ y ∈ (R 2).reverse,
      (G.Adj x y ↔ (x = b 0 ∧ y = b 2)) := by
    intro x hx y hy
    rw [List.mem_reverse] at hy
    rw [hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y hy]
    exact ⟨fun h => h.elim (fun h1 => absurd (h1.1 ▸ hx) ha0nd) id, fun h => Or.inr h⟩
  have hmemP3 : ∀ y : V, y ∈ (R 0).drop (j0 + 2) ++ (R 2).reverse ↔
      (y ∈ (R 0).drop (j0 + 2) ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  obtain ⟨hP3l, hP3e, hP3n⟩ :
      IsPathList G ((R 0).drop (j0 + 2) ++ (R 2).reverse) ∧
      ((R 0).drop (j0 + 2) ++ (R 2).reverse).getLast? = some (a 2) ∧
      (∃ x ∈ (R 0).drop (j0 + 2) ++ (R 2).reverse, G.Adj ((R 0)[j0 + 1]'hk0) x) := by
    by_cases hlt : j0 + 2 < (R 0).length
    · have hg := PathGlue.glue_path (drop_pathFrom (hp 0) hlt)
        (PathBasics.isPathFrom_reverse (hp 2)) hdisjD2 hcrossD
      refine ⟨hg.1, hg.2.2, ⟨(R 0)[j0 + 2]'hlt, ?_, ?_⟩⟩
      · rw [hmemP3]
        exact Or.inl (mem_drop_iff.mpr ⟨0, by omega, by congr 1⟩)
      · exact PathBasics.path_adj_succ (hp 0).1 hlt
    · have hnil : (R 0).drop (j0 + 2) = [] := List.drop_eq_nil_of_le (by omega)
      have hb0 : (R 0)[j0 + 1]'hk0 = b 0 :=
        (hnd0.getElem_inj_iff.mpr (by omega : j0 + 1 = (R 0).length - 1)).trans hlast0
      rw [hnil, List.nil_append]
      refine ⟨(PathBasics.isPathFrom_reverse (hp 2)).1,
        (PathBasics.isPathFrom_reverse (hp 2)).2.2, ⟨b 2, ?_, ?_⟩⟩
      · rw [List.mem_reverse]
        exact PathBasics.getLast_mem (hp 2).2.2
      · rw [hb0]
        exact hBtri 0 2 (by decide)
  have hlink := link_direct (v := (R 0)[j0 + 1]'hk0)
    (take_pathFrom (hp 0) hj0).1 hP2.1 hP3l
    (fun x hx hx2 => by
      rcases (hmemP2 x).mp hx2 with h | h
      · exact hfK x h 0 (List.mem_of_mem_take hx)
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
          (List.mem_of_mem_take hx) (List.mem_of_mem_take h))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨t, ht, htk, hte⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp h
        have heq : t = j0 + 2 + s := hnd0.getElem_inj_iff.mp (by rw [hte, hse])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) h)
    (fun x hx hx3 => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact hfK x h1 0 (List.mem_of_mem_drop h)
        · exact hfK x h1 2 h
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
            (List.mem_of_mem_take h1) (List.mem_of_mem_drop h)
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_take h1) h)
    (Or.inl (take_pathFrom (hp 0) hj0).2.1) (Or.inr hP2.2.2) (Or.inr hP3e)
    (hAtri 0 1 (by decide)) (hAtri 0 2 (by decide)) (hAtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hmemP2 y).mp hy with h | h
      · exact absurd hadj.symm (hfC1 y h x hx)
      · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_take hx) y
          (List.mem_of_mem_take h)).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff.mp hx
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 ht hs).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y h).mp hadj with hh | hh
        · exact hh
        · exact absurd (hh.1 ▸ hx) hb0nt)
    (fun x hx y hy hadj => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · exfalso
        rcases (hmemP3 y).mp hy with h | h
        · exact hfD1 x h1 y h hadj
        · exact hfR2 x h1 y h hadj
      · rcases (hmemP3 y).mp hy with h | h
        · exfalso
          rcases (hedge 1 0 (by decide) x (List.mem_of_mem_take h1) y
            (List.mem_of_mem_drop h)).mp hadj with hh | hh
          · exact ha0nd (hh.2 ▸ h)
          · exact hb1nt (hh.1 ▸ h1)
        · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_take h1) y h).mp hadj with hh | hh
          · exact hh
          · exact absurd (hh.1 ▸ h1) hb1nt)
    ⟨(R 0)[j0]'hj0, PathBasics.getLast_mem (take_pathFrom (hp 0) hj0).2.2,
      (PathBasics.path_adj_succ (hp 0).1 hk0).symm⟩
    ⟨f₁, (hmemP2 _).mpr (Or.inl (PathBasics.head_mem hf.2.1)), hc1.symm⟩
    hP3n
  have hnotA : ∀ i : Fin 3, i ≠ 0 → ¬ G.Adj ((R 0)[j0 + 1]'hk0) (a i) := by
    intro i hi hadj
    have hai : a i ∈ R i := PathBasics.head_mem (hp i).2.1
    rcases (hedge 0 i (Ne.symm hi) _ (List.getElem_mem hk0) (a i) hai).mp hadj with hh | hh
    · have h0 : (R 0)[j0 + 1]'hk0 = (R 0)[0]'(by omega) := by rw [hh.1, hfirst0]
      have := hnd0.getElem_inj_iff.mp h0
      omega
    · exact hABne i i hh.2
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG ((R 0)[j0 + 1]'hk0)
      (a 0) (a 1) (a 2) hlink with h | h | h
  exacts [hnotA 1 (by decide) h.2, hnotA 2 (by decide) h.2, hnotA 1 (by decide) h.1]

/-- The mirror image of `link_equal_path` under the closing paragraph's *"from the symmetry we
may assume"*: the same linking with the two triangles interchanged, so the three paths are
`c₁-D₁-b₁`, `c₁-f₁-⋯-fₙ-d₂-D₂-b₂` and `c₁-C₁-a₁-a₃-R₃-b₃`, and the triangle is `B`. -/
theorem link_equal_path_mirror {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {f : List V} {f₁ fn : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hf : IsPathFrom G f f₁ fn) (hn : 2 ≤ f.length)
    (hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i)
    (hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0)
    (hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1)
    (hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y)
    {m0 k1' : ℕ} (hm0lt : m0 < (R 0).length) (hm0 : m0 + 1 < (R 0).length)
    (hk1' : k1' < (R 1).length)
    (hc1 : G.Adj f₁ ((R 0)[m0]'hm0lt)) (hd2 : G.Adj fn ((R 1)[k1']'hk1'))
    (honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj f₁ ((R 0)[t]'ht) → t = m0)
    (hk1max : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj fn ((R 1)[t]'ht) → t ≤ k1')
    (ha1 : (R 1)[k1']'hk1' ≠ a 1) : False := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hk1pos : 1 ≤ k1' := by
    by_contra hcon
    exact ha1 ((hnd1.getElem_inj_iff.mpr (by omega : k1' = 0)).trans hfirst1)
  have ha0nd : a 0 ∉ (R 0).drop (m0 + 1) := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : m0 + 1 + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have ha1nd : a 1 ∉ (R 1).drop k1' := by
    intro hmem
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hmem
    have heq : k1' + s = 0 := hnd1.getElem_inj_iff.mp (by rw [hse, hfirst1])
    omega
  have hb0nt : b 0 ∉ (R 0).take m0 := by
    intro hmem
    obtain ⟨t, ht, htk, hte⟩ := mem_take_iff'.mp hmem
    have heq : t = (R 0).length - 1 := hnd0.getElem_inj_iff.mp (by rw [hte, hlast0])
    omega
  have hfT0 : ∀ x ∈ f, ∀ y ∈ (R 0).take m0, ¬ G.Adj x y := by
    intro x hx y hy hadj
    obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff'.mp hy
    by_cases hx1 : x = f₁
    · subst hx1
      have := honly0 t ht hadj
      omega
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 0 _ (List.getElem_mem ht) hadj) (by decide)
    · exact hNint x hx hx1 hxn 0 _ (List.getElem_mem ht) hadj
  have hfD0 : ∀ x ∈ f, ∀ y ∈ (R 0).drop (m0 + 1), ¬ G.Adj x y := by
    intro x hx y hy hadj
    obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hy
    by_cases hx1 : x = f₁
    · subst hx1
      have := honly0 (m0 + 1 + s) hs hadj
      omega
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 0 _ (List.getElem_mem hs) hadj) (by decide)
    · exact hNint x hx hx1 hxn 0 _ (List.getElem_mem hs) hadj
  have hfR2 : ∀ x ∈ f, ∀ y ∈ R 2, ¬ G.Adj x y := by
    intro x hx y hy hadj
    by_cases hx1 : x = f₁
    · subst hx1
      exact absurd (hN1 2 y hy hadj) (by decide)
    by_cases hxn : x = fn
    · subst hxn
      exact absurd (hNn 2 y hy hadj) (by decide)
    · exact hNint x hx hx1 hxn 2 y hy hadj
  -- `P₂ = f₁-⋯-fₙ-d₂-D₂-b₂`
  have hdisjF : ∀ x ∈ f, x ∉ (R 1).drop k1' := fun x hx hy =>
    hfK x hx 1 (List.mem_of_mem_drop hy)
  have hcrossF : ∀ x ∈ f, ∀ y ∈ (R 1).drop k1',
      (G.Adj x y ↔ (x = fn ∧ y = (R 1)[k1']'hk1')) := by
    intro x hx y hy
    constructor
    · intro hadj
      by_cases hxn : x = fn
      · subst hxn
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hy
        exact ⟨rfl, hnd1.getElem_inj_iff.mpr (by have := hk1max (k1' + s) hs hadj; omega)⟩
      by_cases hx1 : x = f₁
      · subst hx1
        exact absurd (hN1 1 y (List.mem_of_mem_drop hy) hadj) (by decide)
      · exact absurd hadj (hNint x hx hx1 hxn 1 y (List.mem_of_mem_drop hy))
    · rintro ⟨rfl, rfl⟩
      exact hd2
  have hP2 : IsPathFrom G (f ++ (R 1).drop k1') f₁ (b 1) :=
    PathGlue.glue_path hf (drop_pathFrom (hp 1) hk1') hdisjF hcrossF
  have hmemP2 : ∀ x : V, x ∈ f ++ (R 1).drop k1' ↔ (x ∈ f ∨ x ∈ (R 1).drop k1') := by
    intro x; rw [List.mem_append]
  -- `P₃ = C₁-a₁-a₃-R₃-b₃`
  have hmemP3 : ∀ y : V, y ∈ ((R 0).take m0).reverse ++ R 2 ↔
      (y ∈ (R 0).take m0 ∨ y ∈ R 2) := by
    intro y; rw [List.mem_append, List.mem_reverse]
  obtain ⟨hP3l, hP3e, hP3n⟩ :
      IsPathList G (((R 0).take m0).reverse ++ R 2) ∧
      (((R 0).take m0).reverse ++ R 2).getLast? = some (b 2) ∧
      (∃ x ∈ ((R 0).take m0).reverse ++ R 2, G.Adj ((R 0)[m0]'hm0lt) x) := by
    by_cases hpos : 1 ≤ m0
    · obtain ⟨i0, rfl⟩ : ∃ i0, m0 = i0 + 1 := ⟨m0 - 1, by omega⟩
      have hi0lt : i0 < (R 0).length := by omega
      have hrev : IsPathFrom G (((R 0).take (i0 + 1)).reverse) ((R 0)[i0]'hi0lt) (a 0) :=
        PathBasics.isPathFrom_reverse (take_pathFrom (hp 0) hi0lt)
      have hdisjT2 : ∀ x ∈ ((R 0).take (i0 + 1)).reverse, x ∉ R 2 := by
        intro x hx hx2
        rw [List.mem_reverse] at hx
        exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_take hx) hx2
      have hcrossT2 : ∀ x ∈ ((R 0).take (i0 + 1)).reverse, ∀ y ∈ R 2,
          (G.Adj x y ↔ (x = a 0 ∧ y = a 2)) := by
        intro x hx y hy
        rw [List.mem_reverse] at hx
        rw [hedge 0 2 (by decide) x (List.mem_of_mem_take hx) y hy]
        exact ⟨fun h => h.elim id (fun h1 => absurd (h1.1 ▸ hx) hb0nt), fun h => Or.inl h⟩
      have hg := PathGlue.glue_path hrev (hp 2) hdisjT2 hcrossT2
      refine ⟨hg.1, hg.2.2, ⟨(R 0)[i0]'hi0lt, ?_, ?_⟩⟩
      · rw [hmemP3]
        exact Or.inl (mem_take_iff'.mpr ⟨i0, hi0lt, by omega, rfl⟩)
      · exact (PathBasics.path_adj_succ (hp 0).1 hm0lt).symm
    · have hnil : (R 0).take m0 = [] := by rw [show m0 = 0 by omega]; simp
      have ha0 : (R 0)[m0]'hm0lt = a 0 :=
        (hnd0.getElem_inj_iff.mpr (by omega : m0 = 0)).trans hfirst0
      rw [hnil]
      simp only [List.reverse_nil, List.nil_append]
      exact ⟨(hp 2).1, (hp 2).2.2,
        ⟨a 2, PathBasics.head_mem (hp 2).2.1, by rw [ha0]; exact hAtri 0 2 (by decide)⟩⟩
  have hlink := link_direct (v := (R 0)[m0]'hm0lt)
    (drop_pathFrom (hp 0) hm0).1 hP2.1 hP3l
    (fun x hx hx2 => by
      rcases (hmemP2 x).mp hx2 with h | h
      · exact hfK x h 0 (List.mem_of_mem_drop hx)
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
          (List.mem_of_mem_drop hx) (List.mem_of_mem_drop h))
    (fun x hx hx3 => by
      rcases (hmemP3 x).mp hx3 with h | h
      · obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, hte⟩ := mem_take_iff'.mp h
        have heq : m0 + 1 + s = t := hnd0.getElem_inj_iff.mp (by rw [hse, hte])
        omega
      · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) (List.mem_of_mem_drop hx) h)
    (fun x hx hx3 => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact hfK x h1 0 (List.mem_of_mem_take h)
        · exact hfK x h1 2 h
      · rcases (hmemP3 x).mp hx3 with h | h
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 0)
            (List.mem_of_mem_drop h1) (List.mem_of_mem_take h)
        · exact paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_drop h1) h)
    (Or.inr (drop_pathFrom (hp 0) hm0).2.2) (Or.inr hP2.2.2) (Or.inr hP3e)
    (hBtri 0 1 (by decide)) (hBtri 0 2 (by decide)) (hBtri 1 2 (by decide))
    (fun x hx y hy hadj => by
      rcases (hmemP2 y).mp hy with h | h
      · exact absurd hadj.symm (hfD0 y h x hx)
      · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_drop hx) y
          (List.mem_of_mem_drop h)).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha0nd
        · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP3 y).mp hy with h | h
      · exfalso
        obtain ⟨s, hs, rfl⟩ := mem_drop_iff.mp hx
        obtain ⟨t, ht, htk, rfl⟩ := mem_take_iff'.mp h
        have hh := (PathBasics.path_adj_iff (hp 0).1 hs ht).mp hadj
        omega
      · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_drop hx) y h).mp hadj with hh | hh
        · exact absurd (hh.1 ▸ hx) ha0nd
        · exact hh)
    (fun x hx y hy hadj => by
      rcases (hmemP2 x).mp hx with h1 | h1
      · exfalso
        rcases (hmemP3 y).mp hy with h | h
        · exact hfT0 x h1 y h hadj
        · exact hfR2 x h1 y h hadj
      · rcases (hmemP3 y).mp hy with h | h
        · exfalso
          rcases (hedge 1 0 (by decide) x (List.mem_of_mem_drop h1) y
            (List.mem_of_mem_take h)).mp hadj with hh | hh
          · exact ha1nd (hh.1 ▸ h1)
          · exact hb0nt (hh.2 ▸ h)
        · rcases (hedge 1 2 (by decide) x (List.mem_of_mem_drop h1) y h).mp hadj with hh | hh
          · exact absurd (hh.1 ▸ h1) ha1nd
          · exact hh)
    ⟨(R 0)[m0 + 1]'hm0, PathBasics.head_mem (drop_pathFrom (hp 0) hm0).2.1,
      PathBasics.path_adj_succ (hp 0).1 hm0⟩
    ⟨f₁, (hmemP2 _).mpr (Or.inl (PathBasics.head_mem hf.2.1)), hc1.symm⟩
    hP3n
  have hnotB : ∀ i : Fin 3, i ≠ 0 → ¬ G.Adj ((R 0)[m0]'hm0lt) (b i) := by
    intro i hi hadj
    have hbi : b i ∈ R i := PathBasics.getLast_mem (hp i).2.2
    rcases (hedge 0 i (Ne.symm hi) _ (List.getElem_mem hm0lt) (b i) hbi).mp hadj with hh | hh
    · exact hABne i i hh.2.symm
    · have h0 : (R 0)[m0]'hm0lt = (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) := by
        rw [hh.1, hlast0]
      have := hnd0.getElem_inj_iff.mp h0
      omega
  rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG ((R 0)[m0]'hm0lt)
      (b 0) (b 1) (b 2) hlink with h | h | h
  exacts [hnotB 1 (by decide) h.2, hnotB 2 (by decide) h.2, hnotB 1 (by decide) h.1]

/-- PAPER (10.1, closing paragraph): *"So `c₁ ≠ d₁` and similarly `c₂ ≠ d₂`."*  `hnotA`/`hnotB`
are the two halves of the non-locality of `X` that the argument consumes. -/
theorem two_attachments_path {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {f : List V} {f₁ fn : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hf : IsPathFrom G f f₁ fn) (hn : 2 ≤ f.length)
    (hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i)
    (hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0)
    (hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1)
    (hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y)
    (hnotA : ¬ ∀ x : V, ((x ∈ R 0 ∧ G.Adj f₁ x) ∨ (x ∈ R 1 ∧ G.Adj fn x)) →
      (x = a 0 ∨ x = a 1 ∨ x = a 2))
    (hnotB : ¬ ∀ x : V, ((x ∈ R 0 ∧ G.Adj f₁ x) ∨ (x ∈ R 1 ∧ G.Adj fn x)) →
      (x = b 0 ∨ x = b 1 ∨ x = b 2))
    (hmeet0 : ∃ x ∈ R 0, G.Adj f₁ x) (hmeet1 : ∃ x ∈ R 1, G.Adj fn x) :
    ∃ x ∈ R 0, ∃ y ∈ R 0, x ≠ y ∧ G.Adj f₁ x ∧ G.Adj f₁ y := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hlast0 : (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) = b 0 :=
    PathBasics.getElem_last_of_getLast? (hp 0).2.2 (by have := hlen2 0; omega)
  have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
    PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  obtain ⟨k0, hk0, -, hc1, -, -, -, hk0min⟩ := first_attach (hp 0) hmeet0
  obtain ⟨k0', hk0', -, hd1, -, -, -, hk0max⟩ := last_attach (hp 0) hmeet0
  obtain ⟨k1, hk1, -, hc2, -, -, -, hk1min⟩ := first_attach (hp 1) hmeet1
  obtain ⟨k1', hk1', -, hd2, -, -, -, hk1max⟩ := last_attach (hp 1) hmeet1
  have hk1le : k1 ≤ k1' := hk1min k1' hk1' hd2
  rcases Nat.lt_or_ge k0 k0' with hlt | hge
  · exact ⟨(R 0)[k0]'hk0, List.getElem_mem _, (R 0)[k0']'hk0', List.getElem_mem _,
      fun hc => absurd (hnd0.getElem_inj_iff.mp hc) (by omega), hc1, hd1⟩
  exfalso
  have hk0le : k0 ≤ k0' := hk0min k0' hk0' hd1
  have honly0 : ∀ (t : ℕ) (ht : t < (R 0).length), G.Adj f₁ ((R 0)[t]'ht) → t = k0 := by
    intro t ht hadj
    have h1 := hk0min t ht hadj
    have h2 := hk0max t ht hadj
    omega
  by_cases hbr1 : 1 ≤ k0 ∧ (R 1)[k1]'hk1 ≠ b 1
  · obtain ⟨j0, hj0⟩ : ∃ j0, k0 = j0 + 1 := ⟨k0 - 1, by omega⟩
    subst hj0
    exact link_equal_path hG hprism hf hn hfK hN1 hNn hNint hk0 hk1 hc1 hc2 honly0 hk1min
      hbr1.2
  by_cases hbr2 : k0 + 1 < (R 0).length ∧ (R 1)[k1']'hk1' ≠ a 1
  · exact link_equal_path_mirror hG hprism hf hn hfK hN1 hNn hNint hk0 hbr2.1 hk1' hc1 hd2
      honly0 hk1max hbr2.2
  rcases Nat.eq_zero_or_pos k0 with hk00 | hk0pos
  · -- `c₁ = a₁` and `d₂ = a₂`, so `X ⊆ A`
    apply hnotA
    have hd1a : (R 1)[k1']'hk1' = a 1 := by
      by_contra hcon
      exact hbr2 ⟨by have := hlen2 0; omega, hcon⟩
    have hk1'0 : k1' = 0 := hnd1.getElem_inj_iff.mp (by rw [hd1a, hfirst1])
    rintro x (⟨hx0, hadj⟩ | ⟨hx1, hadj⟩)
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx0
      have h0 : (R 0)[t]'ht = (R 0)[0]'(by have := hlen2 0; omega) :=
        hnd0.getElem_inj_iff.mpr (by have := honly0 t ht hadj; omega)
      rw [h0, hfirst0]
      simp
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx1
      have h0 : (R 1)[t]'ht = (R 1)[0]'(by have := hlen2 1; omega) :=
        hnd1.getElem_inj_iff.mpr (by have := hk1max t ht hadj; omega)
      rw [h0, hfirst1]
      simp
  · -- `c₂ = b₂` and `c₁ = b₁`, so `X ⊆ B`
    apply hnotB
    have hc1b : (R 1)[k1]'hk1 = b 1 := by
      by_contra hcon
      exact hbr1 ⟨hk0pos, hcon⟩
    have hk1eq : k1 = (R 1).length - 1 := hnd1.getElem_inj_iff.mp (by rw [hc1b, hlast1])
    have hk0end : k0 + 1 = (R 0).length := by
      by_contra hcon
      refine hbr2 ⟨by omega, ?_⟩
      intro hd1a
      have hk1'0 : k1' = 0 := hnd1.getElem_inj_iff.mp (by rw [hd1a, hfirst1])
      have := hlen2 1
      omega
    rintro x (⟨hx0, hadj⟩ | ⟨hx1, hadj⟩)
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx0
      have h0 : (R 0)[t]'ht = (R 0)[(R 0).length - 1]'(by have := hlen2 0; omega) :=
        hnd0.getElem_inj_iff.mpr (by have := honly0 t ht hadj; omega)
      rw [h0, hlast0]
      simp
    · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hx1
      have h0 : (R 1)[t]'ht = (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) :=
        hnd1.getElem_inj_iff.mpr (by have := hk1min t ht hadj; omega)
      rw [h0, hlast1]
      simp

/-- PAPER (10.1, closing paragraph): *"So `c₁, d₁` are adjacent, and similarly so are
`c₂, d₂`."* -/
theorem ends_adjacent_path {G : SimpleGraph V} (hG : Berge G)
    {a b : Fin 3 → V} {R : Fin 3 → List V} {f : List V} {f₁ fn : V}
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hf : IsPathFrom G f f₁ fn) (hn : 2 ≤ f.length)
    (hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i)
    (hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0)
    (hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1)
    (hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y)
    {k0 k0' k1 k1' : ℕ} (hk0 : k0 < (R 0).length) (hk0' : k0' < (R 0).length)
    (hk1 : k1 < (R 1).length) (hk1' : k1' < (R 1).length)
    (hc1 : G.Adj f₁ ((R 0)[k0]'hk0)) (hd1 : G.Adj f₁ ((R 0)[k0']'hk0'))
    (hc2 : G.Adj fn ((R 1)[k1]'hk1))
    (hk1min : ∀ (t : ℕ) (ht : t < (R 1).length), G.Adj fn ((R 1)[t]'ht) → k1 ≤ t)
    (hk1lt : k1 < k1') : k0' ≤ k0 + 1 := by
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hlast1 : (R 1)[(R 1).length - 1]'(by have := hlen2 1; omega) = b 1 :=
    PathBasics.getElem_last_of_getLast? (hp 1).2.2 (by have := hlen2 1; omega)
  by_contra hcon
  have hb1 : (R 1)[k1]'hk1 ≠ b 1 := by
    intro h
    have := hnd1.getElem_inj_iff.mp (h.trans hlast1.symm)
    omega
  exact link_nonadjacent_path hG hprism hf hn hfK hN1 hNn hNint hk0 hk0' hk1 hc1 hd1 hc2
    hk1min (by omega) hb1

/-! ### The closing paragraph itself -/

/-- **10.1, the last printed paragraph**: the case `X₁ ⊆ V(R₂)` and `X₂ ⊆ V(R₁)`. -/
theorem endgame (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ)
    (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f}) (hn : 2 ≤ f.length)
    (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ {v : V | v ∈ R 1})
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R 0}) :
    Thm101Assembly.Concl G a b R K f f₁ fn := by
  classical
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hf₁ne : f₁ ≠ fn :=
    PathBasics.isPathFrom_ends_ne hf (by change 1 ≤ f.length - 1; omega)
  have hf₁F : f₁ ∈ F := by rw [hfF]; exact PathBasics.head_mem hf.2.1
  have hfnF : fn ∈ F := by rw [hfF]; exact PathBasics.getLast_mem hf.2.2
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hKR : ∀ x : V, x ∈ K → ∃ i : Fin 3, x ∈ R i := by
    intro x hx
    rw [hK] at hx
    simp only [Set.mem_union, Set.mem_setOf_eq] at hx
    rcases hx with (h | h) | h
    exacts [⟨0, h⟩, ⟨1, h⟩, ⟨2, h⟩]
  have hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i := by
    intro x hx i hxi
    exact (hFK (by rw [hfF]; exact hx)) (hRK i x hxi)
  have hN1 : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj f₁ x → i = 0 := by
    intro i x hxi hadj
    have h0 : x ∈ R 0 := hX2 ⟨hRK i x hxi, f₁, ⟨hf₁F, by simp [hf₁ne]⟩, hadj.symm⟩
    by_contra hne
    exact paths_disjoint hprism (fun hc => hne hc.symm) h0 hxi
  have hNn : ∀ (i : Fin 3) (x : V), x ∈ R i → G.Adj fn x → i = 1 := by
    intro i x hxi hadj
    have h1 : x ∈ R 1 := hX1 ⟨hRK i x hxi, fn, ⟨hfnF, by simp [hf₁ne.symm]⟩, hadj.symm⟩
    by_contra hne
    exact paths_disjoint hprism (fun hc => hne hc.symm) h1 hxi
  have hNint : ∀ x ∈ f, x ≠ f₁ → x ≠ fn → ∀ (i : Fin 3) (y : V), y ∈ R i → ¬ G.Adj x y := by
    intro x hx hx1 hxn i y hyi hadj
    have hxF : x ∈ F := by rw [hfF]; exact hx
    have h1 : y ∈ R 1 := hX1 ⟨hRK i y hyi, x, ⟨hxF, by simp [hx1]⟩, hadj.symm⟩
    have h0 : y ∈ R 0 := hX2 ⟨hRK i y hyi, x, ⟨hxF, by simp [hxn]⟩, hadj.symm⟩
    exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1) h0 h1
  have hXsub : ∀ x : V, x ∈ attachments G F K →
      ((x ∈ R 0 ∧ G.Adj f₁ x) ∨ (x ∈ R 1 ∧ G.Adj fn x)) := by
    rintro x ⟨hxK, w, hwF, hadj⟩
    have hwf : w ∈ f := by rw [hfF] at hwF; exact hwF
    obtain ⟨i, hxi⟩ := hKR x hxK
    by_cases hw1 : w = f₁
    · subst hw1
      have hi : i = 0 := hN1 i x hxi hadj.symm
      subst hi
      exact Or.inl ⟨hxi, hadj.symm⟩
    by_cases hwn : w = fn
    · subst hwn
      have hi : i = 1 := hNn i x hxi hadj.symm
      subst hi
      exact Or.inr ⟨hxi, hadj.symm⟩
    · exact absurd hadj.symm (hNint w hwf hw1 hwn i x hxi)
  have hnotA : ¬ ∀ x : V, ((x ∈ R 0 ∧ G.Adj f₁ x) ∨ (x ∈ R 1 ∧ G.Adj fn x)) →
      (x = a 0 ∨ x = a 1 ∨ x = a 2) := by
    intro hall
    exact hFloc (Or.inr (Or.inr (Or.inr (Or.inl (fun x hx => by
      have h := hall x (hXsub x hx); simpa using h)))))
  have hnotB : ¬ ∀ x : V, ((x ∈ R 0 ∧ G.Adj f₁ x) ∨ (x ∈ R 1 ∧ G.Adj fn x)) →
      (x = b 0 ∨ x = b 1 ∨ x = b 2) := by
    intro hall
    exact hFloc (Or.inr (Or.inr (Or.inr (Or.inr (fun x hx => by
      have h := hall x (hXsub x hx); simpa using h)))))
  have hmeet0 : ∃ x ∈ R 0, G.Adj f₁ x := by
    by_contra hcon
    refine hFloc (Or.inr (Or.inl (fun x hx => ?_)))
    rcases hXsub x hx with ⟨h0, hadj⟩ | ⟨h1, -⟩
    · exact absurd ⟨x, h0, hadj⟩ hcon
    · exact h1
  have hmeet1 : ∃ x ∈ R 1, G.Adj fn x := by
    by_contra hcon
    refine hFloc (Or.inl (fun x hx => ?_))
    rcases hXsub x hx with ⟨h0, -⟩ | ⟨h1, hadj⟩
    · exact h0
    · exact absurd ⟨x, h1, hadj⟩ hcon
  -- the mirrored labelling: swap the two path indices and traverse `f` backwards
  have hs0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := by decide
  have hs1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := by decide
  have hs2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
  have hprism' := PrismSymmetry.formPrism_perm hprism (Equiv.swap (0 : Fin 3) 1)
  have hfr : IsPathFrom G f.reverse fn f₁ := PathBasics.isPathFrom_reverse hf
  have hnr : 2 ≤ f.reverse.length := by simpa using hn
  have hfKr : ∀ x ∈ f.reverse, ∀ i : Fin 3, x ∉ R ((Equiv.swap (0 : Fin 3) 1) i) :=
    fun x hx i => hfK x (List.mem_reverse.mp hx) _
  have hN1r : ∀ (i : Fin 3) (x : V), x ∈ R ((Equiv.swap (0 : Fin 3) 1) i) →
      G.Adj fn x → i = 0 := by
    intro i x hxi hadj
    exact (Equiv.swap (0 : Fin 3) 1).injective ((hNn _ x hxi hadj).trans hs0.symm)
  have hNnr : ∀ (i : Fin 3) (x : V), x ∈ R ((Equiv.swap (0 : Fin 3) 1) i) →
      G.Adj f₁ x → i = 1 := by
    intro i x hxi hadj
    exact (Equiv.swap (0 : Fin 3) 1).injective ((hN1 _ x hxi hadj).trans hs1.symm)
  have hNintr : ∀ x ∈ f.reverse, x ≠ fn → x ≠ f₁ → ∀ (i : Fin 3) (y : V),
      y ∈ R ((Equiv.swap (0 : Fin 3) 1) i) → ¬ G.Adj x y :=
    fun x hx h1 h2 i y hy => hNint x (List.mem_reverse.mp hx) h2 h1 _ y hy
  have hnotA' : ¬ ∀ x : V, ((x ∈ R ((Equiv.swap (0 : Fin 3) 1) 0) ∧ G.Adj fn x) ∨
      (x ∈ R ((Equiv.swap (0 : Fin 3) 1) 1) ∧ G.Adj f₁ x)) →
      (x = a ((Equiv.swap (0 : Fin 3) 1) 0) ∨ x = a ((Equiv.swap (0 : Fin 3) 1) 1) ∨
        x = a ((Equiv.swap (0 : Fin 3) 1) 2)) := by
    rw [hs0, hs1, hs2]
    intro hall
    exact hnotA fun x hx => by have h := hall x hx.symm; tauto
  have hnotB' : ¬ ∀ x : V, ((x ∈ R ((Equiv.swap (0 : Fin 3) 1) 0) ∧ G.Adj fn x) ∨
      (x ∈ R ((Equiv.swap (0 : Fin 3) 1) 1) ∧ G.Adj f₁ x)) →
      (x = b ((Equiv.swap (0 : Fin 3) 1) 0) ∨ x = b ((Equiv.swap (0 : Fin 3) 1) 1) ∨
        x = b ((Equiv.swap (0 : Fin 3) 1) 2)) := by
    rw [hs0, hs1, hs2]
    intro hall
    exact hnotB fun x hx => by have h := hall x hx.symm; tauto
  -- the paper's `c₁, d₁, c₂, d₂`
  obtain ⟨k0, hk0, -, hc1, -, -, -, hk0min⟩ := first_attach (hp 0) hmeet0
  obtain ⟨k0', hk0', -, hd1, -, -, -, hk0max⟩ := last_attach (hp 0) hmeet0
  obtain ⟨k1, hk1, -, hc2, -, -, -, hk1min⟩ := first_attach (hp 1) hmeet1
  obtain ⟨k1', hk1', -, hd2, -, -, -, hk1max⟩ := last_attach (hp 1) hmeet1
  -- "So `c₁ ≠ d₁` and similarly `c₂ ≠ d₂`"
  have hk0lt : k0 < k0' := by
    obtain ⟨x, hx, y, hy, hxy, hax, hay⟩ :=
      two_attachments_path hG hprism hf hn hfK hN1 hNn hNint hnotA hnotB hmeet0 hmeet1
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    have h1 := hk0min s hs hax
    have h2 := hk0max s hs hax
    have h3 := hk0min t ht hay
    have h4 := hk0max t ht hay
    rcases Nat.lt_or_ge k0 k0' with h | h
    · exact h
    · exact absurd (hnd0.getElem_inj_iff.mpr (by omega : s = t)) hxy
  have hk1lt : k1 < k1' := by
    obtain ⟨x, hx, y, hy, hxy, hax, hay⟩ :=
      two_attachments_path (R := fun i => R ((Equiv.swap (0 : Fin 3) 1) i))
        hG hprism' hfr hnr hfKr hN1r hNnr hNintr hnotA' hnotB'
        (by simp only [hs0]; exact hmeet1) (by simp only [hs1]; exact hmeet0)
    rw [hs0] at hx hy
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hy
    have h1 := hk1min s hs hax
    have h2 := hk1max s hs hax
    have h3 := hk1min t ht hay
    have h4 := hk1max t ht hay
    rcases Nat.lt_or_ge k1 k1' with h | h
    · exact h
    · exact absurd (hnd1.getElem_inj_iff.mpr (by omega : s = t)) hxy
  -- "So `c₁, d₁` are adjacent, and similarly so are `c₂, d₂`"
  have hk0succ : k0' = k0 + 1 := by
    have h := ends_adjacent_path hG hprism hf hn hfK hN1 hNn hNint hk0 hk0' hk1 hk1'
      hc1 hd1 hc2 hk1min hk1lt
    omega
  have hk1succ : k1' = k1 + 1 := by
    have h := ends_adjacent_path (R := fun i => R ((Equiv.swap (0 : Fin 3) 1) i))
      hG hprism' hfr hnr hfKr hN1r hNnr hNintr hk1 hk1' hk0 hk0' hc2 hd2 hc1 hk0min hk0lt
    omega
  subst hk0succ
  subst hk1succ
  -- "but then statement 1 of the theorem holds"
  have hno : ∀ x ∈ f, ∀ k ∈ K, G.Adj x k →
      (x = f₁ ∧ (k = (R 0)[k0]'hk0 ∨ k = (R 0)[k0 + 1]'hk0')) ∨
      (x = fn ∧ (k = (R 1)[k1]'hk1 ∨ k = (R 1)[k1 + 1]'hk1')) := by
    intro x hx kk hkkK hadj
    by_cases hx1 : x = f₁
    · subst hx1
      obtain ⟨i, hki⟩ := hKR kk hkkK
      have hi : i = 0 := hN1 i kk hki hadj
      subst hi
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hki
      have h1 := hk0min t ht hadj
      have h2 := hk0max t ht hadj
      rcases (by omega : t = k0 ∨ t = k0 + 1) with h | h
      · exact Or.inl ⟨rfl, Or.inl (hnd0.getElem_inj_iff.mpr h)⟩
      · exact Or.inl ⟨rfl, Or.inr (hnd0.getElem_inj_iff.mpr h)⟩
    by_cases hxn : x = fn
    · subst hxn
      obtain ⟨i, hki⟩ := hKR kk hkkK
      have hi : i = 1 := hNn i kk hki hadj
      subst hi
      obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hki
      have h1 := hk1min t ht hadj
      have h2 := hk1max t ht hadj
      rcases (by omega : t = k1 ∨ t = k1 + 1) with h | h
      · exact Or.inr ⟨rfl, Or.inl (hnd1.getElem_inj_iff.mpr h)⟩
      · exact Or.inr ⟨rfl, Or.inr (hnd1.getElem_inj_iff.mpr h)⟩
    · obtain ⟨i, hki⟩ := hKR kk hkkK
      exact absurd hadj (hNint x hx hx1 hxn i kk hki)
  refine ⟨a, b, R, Equiv.refl (Fin 3), rfl, Or.inl ⟨rfl, rfl⟩,
    Or.inl ⟨(R 0)[k0]'hk0, (R 0)[k0 + 1]'hk0', List.getElem_mem _, List.getElem_mem _,
      PathBasics.path_adj_succ (hp 0).1 hk0', hc1, hd1,
      (R 1)[k1]'hk1, (R 1)[k1 + 1]'hk1', List.getElem_mem _, List.getElem_mem _,
      PathBasics.path_adj_succ (hp 1).1 hk1', hc2, hd2, hno, ?_⟩⟩
  exact _root_.Workspace.ProofLemmas.Thm101K4Appearance.appears_K4_of_case_one G hG a b R K
    f f₁ fn ((R 0)[k0]'hk0) ((R 0)[k0 + 1]'hk0') ((R 1)[k1]'hk1) ((R 1)[k1 + 1]'hk1')
    hprism hK hf (fun x hx hc => hfK x hx 0 (by
      obtain ⟨i, hi⟩ := hKR x hc
      exact absurd (hfK x hx i hi) (by simp)))
    (List.getElem_mem _) (List.getElem_mem _) (PathBasics.path_adj_succ (hp 0).1 hk0')
    hc1 hd1
    (List.getElem_mem _) (List.getElem_mem _) (PathBasics.path_adj_succ (hp 1).1 hk1')
    hc2 hd2 hno

end Workspace.ProofLemmas.Thm101Endgame
