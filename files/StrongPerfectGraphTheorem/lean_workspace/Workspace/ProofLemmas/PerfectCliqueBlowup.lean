import Mathlib
import Workspace.Types.Core
import Workspace.Types.Replication
import Workspace.Statements.S01.Thm_E7_lovasz_replication

/-!
# Blowing one vertex up into a clique preserves perfection

§5.2 of the proof of 1.5:

> *"Now a theorem of Lovász [16] shows that replicating a vertex of a perfect graph
> makes another perfect graph; so if we replace `z` by a set `Z` of `t − s` vertices
> all complete to `B₁` and to each other, and with no other neighbours in
> `Aᵢ ∪ B`, then the graph we make is perfect."*

The result is stated as an **interface**: adjacency equations through one named
injection `ζ`, rather than an isomorphism of induced subgraphs.  That is deliberate.
The isomorphism form would force the re-association
`(K.induce S).induce T ≃g K.induce (Subtype.val '' T)`, which exists neither in
Mathlib nor in this project; with the vertex-level interface, §5.3–§5.5 never form an
`induce` of an `induce` and never mention the vertex type of `K⁺` again.

The intended construction is `Nat.le_induction` from `n = 1` (base: `K⁺ := K`, `ζ` the
inclusion, `Z := {v}`), the step replicating (`Workspace.Types.Replication.replicateVertex`)
the image of the **original** `v` at every stage — never the newest copy — which is
what keeps `Z` a clique all of whose members have the same outside-neighbourhood.
Clause `hperfect` is `thm_E7_lovasz_replication` applied at each step.

The hypothesis `1 ≤ n` is essential: for `n = 0` the clause `Z.ncard = n` fails to be
usable and §5.4's `|c(Z)| = t − s` collapses.

Instance plumbing: let instance synthesis supply `Fintype`/`DecidableEq` on the
iterated `⊕ Unit` types; do not force `Classical.decEq`, or the instance in the goal
will not match the one in the `thm_E7_lovasz_replication` application.
-/

set_option autoImplicit false

universe u

namespace Workspace.ProofLemmas.PerfectCliqueBlowup

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Replication.SPGT

/-- Replacing the vertex `v` of `K` by a clique `Z` of `n ≥ 1` vertices, all with the
same neighbourhood as `v` had, produces a graph `K⁺` which is perfect whenever `K` is.

The five conclusions are, in order: `ζ` is injective; the range of `ζ` and `Z` are
disjoint and cover `V(K⁺)`; `Z` has exactly `n` vertices and is a clique; `ζ` is an
isomorphism onto its image; every vertex of `Z` has the neighbourhood `v` had; and
`K⁺` inherits perfection from `K`. -/
theorem exists_blowup {W : Type u} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (v : W) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (W' : Type u) (_ : Fintype W') (_ : DecidableEq W') (K' : SimpleGraph W')
      (Z : Set W') (ζ : {u : W // u ≠ v} → W'),
      Function.Injective ζ ∧
      Disjoint (Set.range ζ) Z ∧
      Set.range ζ ∪ Z = Set.univ ∧
      Z.ncard = n ∧
      K'.IsClique Z ∧
      (∀ a b : {u : W // u ≠ v}, K'.Adj (ζ a) (ζ b) ↔ K.Adj (a : W) (b : W)) ∧
      (∀ w ∈ Z, ∀ a : {u : W // u ≠ v}, K'.Adj w (ζ a) ↔ K.Adj v (a : W)) ∧
      (IsPerfect K → IsPerfect K') := by
  induction n, hn using Nat.le_induction with
  | base =>
      -- `n = 1`: nothing to replicate — take `K⁺ := K`, `ζ` the inclusion, `Z := {v}`
      refine ⟨W, inferInstance, inferInstance, K, {v}, Subtype.val, Subtype.val_injective,
        ?_, ?_, Set.ncard_singleton v, SimpleGraph.isClique_singleton (G := K) v,
        fun a b => Iff.rfl, ?_, id⟩
      · rw [Set.disjoint_left]
        rintro x ⟨a, rfl⟩ hx
        exact a.2 hx
      · ext x
        simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff, Set.mem_univ, iff_true]
        rcases eq_or_ne x v with rfl | h
        · exact Or.inr rfl
        · exact Or.inl ⟨⟨x, h⟩, rfl⟩
      · intro w hw a
        rw [show w = v from hw]
  | succ n hn ih =>
      obtain ⟨W', hFin, hDec, K', Z, ζ, hinj, hdisj, hcover, hncard, hclique,
        hζadj, hZadj, hperf⟩ := ih
      letI : Fintype W' := hFin
      letI : DecidableEq W' := hDec
      -- replicate a member of `Z` (never a `ζ`-vertex), so `Z` stays a clique whose
      -- members all have the neighbourhood `v` had
      obtain ⟨z₀, hz₀⟩ : Z.Nonempty := (Set.ncard_pos (Set.toFinite Z)).mp (by omega)
      have hζnotZ : ∀ a : {u : W // u ≠ v}, ζ a ∉ Z :=
        fun a => Set.disjoint_left.mp hdisj ⟨a, rfl⟩
      refine ⟨W' ⊕ Unit, inferInstance, inferInstance, replicateVertex K' z₀,
        Sum.inl '' Z ∪ {Sum.inr ()}, fun a => Sum.inl (ζ a),
        fun a b h => hinj (Sum.inl_injective h), ?_, ?_, ?_, ?_,
        fun a b => hζadj a b, ?_, fun hp => ?_⟩
      · -- the `ζ`-image is still disjoint from the enlarged `Z`
        rw [Set.disjoint_left]
        rintro x ⟨a, rfl⟩ hx
        rcases hx with ⟨z, hzZ, hz⟩ | hx
        · exact hζnotZ a ((Sum.inl_injective hz) ▸ hzZ)
        · exact Sum.inl_ne_inr hx
      · -- and together they still cover
        ext x
        simp only [Set.mem_union, Set.mem_range, Set.mem_image, Set.mem_singleton_iff,
          Set.mem_univ, iff_true]
        rcases x with y | uu
        · rcases (hcover ▸ Set.mem_univ y : y ∈ Set.range ζ ∪ Z) with ⟨a, rfl⟩ | hy
          · exact Or.inl ⟨a, rfl⟩
          · exact Or.inr (Or.inl ⟨y, hy, rfl⟩)
        · exact Or.inr (Or.inr (by cases uu; rfl))
      · -- one more vertex
        rw [Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _),
          Set.ncard_image_of_injective Z Sum.inl_injective, hncard, Set.ncard_singleton]
        rw [Set.disjoint_left]
        rintro x ⟨z, -, rfl⟩ hx
        exact Sum.inl_ne_inr hx
      · -- still a clique: the new vertex is adjacent to `z₀` and to all of `Z \ {z₀}`
        rintro x hx y hy hxy
        rcases hx with ⟨a, haZ, rfl⟩ | hx <;> rcases hy with ⟨b, hbZ, rfl⟩ | hy
        · exact hclique haZ hbZ (fun h => hxy (by rw [h]))
        · rw [Set.mem_singleton_iff] at hy
          subst hy
          rcases eq_or_ne a z₀ with rfl | hne
          · exact Or.inl rfl
          · exact Or.inr (hclique haZ hz₀ hne)
        · rw [Set.mem_singleton_iff] at hx
          subst hx
          rcases eq_or_ne b z₀ with rfl | hne
          · exact Or.inl rfl
          · exact Or.inr (hclique hbZ hz₀ hne)
        · rw [Set.mem_singleton_iff] at hx hy
          exact absurd (hx.trans hy.symm) hxy
      · -- and every member of the enlarged `Z` still has the neighbourhood `v` had
        rintro w (⟨z, hzZ, rfl⟩ | hw) a
        · exact hZadj z hzZ a
        · rw [Set.mem_singleton_iff] at hw
          subst hw
          constructor
          · rintro (h | h)
            · exact absurd (h ▸ hz₀) (hζnotZ a)
            · exact (hZadj z₀ hz₀ a).mp h.symm
          · exact fun h => Or.inr ((hZadj z₀ hz₀ a).mpr h).symm
      · -- one application of Lovász's replication theorem (E7) per step
        exact Workspace.MainTheorem.SPGT.thm_E7_lovasz_replication K' z₀ (hperf hp)

end Workspace.ProofLemmas.PerfectCliqueBlowup
