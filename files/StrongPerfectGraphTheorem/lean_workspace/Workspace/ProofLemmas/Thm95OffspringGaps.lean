import Workspace.ProofLemmas.Thm95OffspringDefs
import Workspace.ProofLemmas.Thm95OffspringSplit
import Workspace.ProofLemmas.Thm95OffspringGapComplete
import Workspace.ProofLemmas.Thm95OffspringGapTwist
import Workspace.ProofLemmas.Thm95OffspringParallel

/-!
# The four sentences of 9.5(1) about the offspring that are still open

PAPER (9.5(1), printed p. 52), the paragraph beginning *"For the moment fix `j` with
`1 ≤ j ≤ n`"*.  The construction of the enlarged striation rests on five assertions of the
paper.  Two of them (that an offspring is an antistrip, and that the offspring of `Tⱼ` cover
`V(Tⱼ)`) are proved in `Thm95OffspringFacts`; the four here are the ones whose proofs are odd
hole arguments, together with the paper's second bullet about twists.

Throughout, `U` is `{z | Gx.Adj r z}` and `V` is `{z | Gx.Adj s z}` (`r = f₁`, `s = f_k`), and
the hypotheses `hnoS`, `hcover`, `hZ`, `hXY`, `hint` are the five consequences of 9.3.3 listed
in the docstring of `Thm95Offspring.offspring_striation`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringGaps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set the paper calls `U` (`W = true`) or `V` (`W = false`): the neighbours of `f₁`,
respectively of `f_k`. -/
def side (Gx : SimpleGraph V) (r s : V) : Bool → Set V
  | true => {z : V | Gx.Adj r z}
  | false => {z : V | Gx.Adj s z}

/-- **Labelled gap (9.5(1), p. 52).**

PAPER: *"Every `Tⱼ`-antirung has one end in `U` and the other in `V`."*

`x` is the end in `Xⱼ` and `y` the end in `Yⱼ`; the conclusion is that one of them is adjacent
to `f₁` and the other to `f_k`.  (Both are adjacent to exactly one of `f₁, f_k` by `hcover` and
`hXY`; what is asserted here is that they are adjacent to *different* ones.) -/
theorem antirung_ends_split {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    {R : List V} {r s : V}
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R)) (hRset : {v : V | v ∈ R} = F)
    (hrs : r ≠ s)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (hcover : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ∨ Gx.Adj s z))
    (hZ : ∀ (k : Fin n) (z : V), z ∈ (T k).2.1 → (Gx.Adj r z ∧ Gx.Adj s z))
    (hXY : ∀ (k : Fin n) (z : V), z ∈ (T k).1 ∪ (T k).2.2 → ¬ (Gx.Adj r z ∧ Gx.Adj s z))
    (hint : ∀ k : Fin n,
      Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k)))
    (j : Fin n) {Q : List V} (hQ : IsSRung Gxᶜ (T j) Q) {x y : V}
    (hQxy : IsPathFrom Gxᶜ Q x y) :
    (Gx.Adj r x ∧ Gx.Adj s y) ∨ (Gx.Adj s x ∧ Gx.Adj r y) := by
  obtain ⟨a, b, hpab, haX, hbY⟩ := Thm95OffspringSplit.rung_ends (T j) Q hQ
  obtain ⟨rfl, rfl⟩ := Thm95GapBasics.end_eq_of_same_path hQxy hpab
  have hXsub : ∀ Tx : Set V × Set V × Set V, Tx.1 ⊆ stripVertices Tx := by
    rintro ⟨X, Z, Y⟩ z hz; exact Or.inl (Or.inl hz)
  have hYsub : ∀ Tx : Set V × Set V × Set V, Tx.2.2 ⊆ stripVertices Tx := by
    rintro ⟨X, Z, Y⟩ z hz; exact Or.inl (Or.inr hz)
  have hrF : r ∈ F := hRset ▸ (PathBasics.head_mem hR.2.1)
  have hsF : s ∈ F := hRset ▸ (PathBasics.getLast_mem hR.2.2)
  have hnx := hXY j x (Or.inl haX)
  have hny := hXY j y (Or.inr hbY)
  rcases hcover j x (hXsub (T j) haX) with hx | hx <;>
    rcases hcover j y (hYsub (T j) hbY) with hy | hy
  · exact absurd (Thm95OffspringSplit.ends_not_same_side hG hL hFsub hnoS j hQ hQxy hrF hsF
      hx hy (fun h => hnx ⟨hx, h⟩) (fun h => hny ⟨hy, h⟩) (fun z hz => (hZ j z hz).2)) id
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (Thm95OffspringSplit.ends_not_same_side hG hL hFsub hnoS j hQ hQxy hsF hrF
      hx hy (fun h => hnx ⟨h, hx⟩) (fun h => hny ⟨h, hy⟩) (fun z hz => (hZ j z hz).1)) id

/-- **Labelled gap (9.5(1), p. 52).**

PAPER: *"Suppose there is such a nonedge; and choose `Tⱼ`-antirungs `xⱼ-Qⱼ-yⱼ`, `x'ⱼ-Q'ⱼ-y'ⱼ`
where `xⱼ ∈ U` is nonadjacent to `x'ⱼ ∈ V`, say.  Now `xⱼ, x'ⱼ` have a common neighbour
`d₁ ∈ A₁ ∪ B₁`, and then `d₁-xⱼ-f₁-⋯-f_k-x'ⱼ-d₁` is an odd hole.  This proves that `Mⱼ` is
complete to `Nⱼ`."* -/
theorem offVerts_complete {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    {R : List V} {r s : V}
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R)) (hRset : {v : V | v ∈ R} = F)
    (hrs : r ≠ s)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (hcover : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ∨ Gx.Adj s z))
    (hZ : ∀ (k : Fin n) (z : V), z ∈ (T k).2.1 → (Gx.Adj r z ∧ Gx.Adj s z))
    (hXY : ∀ (k : Fin n) (z : V), z ∈ (T k).1 ∪ (T k).2.2 → ¬ (Gx.Adj r z ∧ Gx.Adj s z))
    (hint : ∀ k : Fin n,
      Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k)))
    (j : Fin n) :
    Complete Gx (offVerts Gx (T j) (side Gx r s true))
      (offVerts Gx (T j) (side Gx r s false)) := by
  classical
  obtain ⟨hm2, hn2⟩ : 2 ≤ m ∧ 2 ≤ n := ⟨hL.2.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2.2.1⟩
  let i₀ : Fin m := ⟨0, by omega⟩
  have hFR : ∀ w ∈ R, w ∈ F := fun w hw => hRset ▸ hw
  have hout : ∀ z ∈ stripVertices (T j), z ∉ R := fun z hz hzR =>
    hFsub (hFR z hzR) (StriationCompl.stripVertices_T_subset S T j hz)
  have hintanti : ∀ z ∈ stripVertices (T j), ∀ w ∈ SPGT.interior R, ¬ Gx.Adj z w :=
    fun z hz w hw hadj => hint j w hw z hz hadj.symm
  have hcomm : ∀ p q : V, ((p ∈ (T j).1 ∧ q ∈ (T j).1) ∨ (p ∈ (T j).2.2 ∧ q ∈ (T j).2.2)) →
      ∃ d : V, Gx.Adj d p ∧ Gx.Adj d q ∧ d ∉ R ∧ ∀ w ∈ R, ¬ Gx.Adj d w := by
    intro p q hpos
    obtain ⟨d, hd, h1, h2⟩ := Thm95OffspringGapComplete.exists_common_neighbour (hL.1 i₀)
      (hL.2.2.2.2.2.2.2.2.2.2.2.1 i₀ j) hpos
    exact ⟨d, h1, h2,
      fun hdR => hFsub (hFR d hdR) (StriationCompl.stripVertices_S_subset S T i₀ hd),
      fun w hw hadj => hnoS i₀ w (hFR w hw) d hd hadj.symm⟩
  exact Thm95OffspringGapComplete.offVerts_complete_aux hG (hL.2.1 j) hR hodd
    (fun Q x y hQ hp => antirung_ends_split hG hL hFsub hR hodd hRset hrs hnoS hcover hZ hXY
      hint j hQ hp)
    (hXY j) hout hintanti hcomm

/-- **Labelled gap (9.5(1), p. 52).**

PAPER: *"Since there is no `Tⱼ`-antirung with both ends in `Mⱼ` or both ends in `Nⱼ`, it
follows that `Mⱼ ∩ Nⱼ = ∅`."*

This is no longer a gap: it follows from the next sentence of the paper, *"`Mⱼ` is complete to
`Nⱼ`"*, because no vertex is adjacent to itself. -/
theorem offVerts_disjoint {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    {R : List V} {r s : V}
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R)) (hRset : {v : V | v ∈ R} = F)
    (hrs : r ≠ s)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (hcover : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ∨ Gx.Adj s z))
    (hZ : ∀ (k : Fin n) (z : V), z ∈ (T k).2.1 → (Gx.Adj r z ∧ Gx.Adj s z))
    (hXY : ∀ (k : Fin n) (z : V), z ∈ (T k).1 ∪ (T k).2.2 → ¬ (Gx.Adj r z ∧ Gx.Adj s z))
    (hint : ∀ k : Fin n,
      Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k)))
    (j : Fin n) :
    Disjoint (offVerts Gx (T j) (side Gx r s true)) (offVerts Gx (T j) (side Gx r s false)) := by
  refine Set.disjoint_left.mpr (fun v hv hv' => ?_)
  exact absurd (offVerts_complete hG hL hFsub hR hodd hRset hrs hnoS hcover hZ hXY hint j
    v hv v hv') Gx.irrefl

/-- **Labelled gap (9.5(1), p. 52), the second bullet.**

PAPER: *"for all `i` with `1 ≤ i ≤ m`, there exists `j` with `1 ≤ j ≤ n` such that `S₀, Sᵢ`
disagree on one of the offspring of `Tⱼ`, and there exists `j` such that `S₀, Sᵢ` agree on one
of the offspring of `Tⱼ`.  For if the first were false, say, then each of the `Tⱼ`'s has only
one offspring, and we could add `f₁` to `Aᵢ`, `{f₂,…,f_{k-1}}` to `Cᵢ`, and `f_k` to `Bᵢ`,
contradicting the maximality of the striation; while if the second were false we could do the
same with `f₁, f_k` exchanged."*

Since no maximality hypothesis is available here, the escape clause is stated as the second
disjunct: it says exactly that `f₁` and `f_k` have the same neighbours on every antistrip as
some end `a ∈ Aᵢ`, respectively `b ∈ Bᵢ`, of the strip `Sᵢ` (the two orders correspond to the
paper's *"with `f₁, f_k` exchanged"*), which is what makes the addition of `f₁, f_k` to `Sᵢ` a
striation on `V(L) ∪ F`. -/
theorem twist_or_merge {Gx : SimpleGraph V} {m n : ℕ}
    {S : Fin m → Set V × Set V × Set V} {T : Fin n → Set V × Set V × Set V} {F : Set V}
    (hG : Berge Gx) (hL : IsStriation Gx S T)
    (hFsub : F ⊆ (striationVertices S T)ᶜ)
    {R : List V} {r s : V}
    (hR : IsPathFrom Gx R r s) (hodd : Odd (pathLength R)) (hRset : {v : V | v ∈ R} = F)
    (hrs : r ≠ s)
    (hnoS : ∀ k : Fin m, Anticomplete Gx F (stripVertices (S k)))
    (hcover : ∀ (k : Fin n) (z : V), z ∈ stripVertices (T k) → (Gx.Adj r z ∨ Gx.Adj s z))
    (hZ : ∀ (k : Fin n) (z : V), z ∈ (T k).2.1 → (Gx.Adj r z ∧ Gx.Adj s z))
    (hXY : ∀ (k : Fin n) (z : V), z ∈ (T k).1 ∪ (T k).2.2 → ¬ (Gx.Adj r z ∧ Gx.Adj s z))
    (hint : ∀ k : Fin n,
      Anticomplete Gx {v : V | v ∈ SPGT.interior R} (stripVertices (T k))) :
    (∀ i : Fin m, ∃ p q : Fin n × Bool, p ≠ q ∧
        (offVerts Gx (T p.1) (side Gx r s p.2)).Nonempty ∧
        (offVerts Gx (T q.1) (side Gx r s q.2)).Nonempty ∧
        IsTwist Gx (newStrip R r s) (S i)
          (offspring Gx (T p.1) (side Gx r s p.2))
          (offspring Gx (T q.1) (side Gx r s q.2))) ∨
      (∃ (i : Fin m) (a b : V),
        ((a ∈ (S i).1 ∧ b ∈ (S i).2.2) ∨ (a ∈ (S i).2.2 ∧ b ∈ (S i).1)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (Gx.Adj r w ↔ Gx.Adj a w)) ∧
        (∀ (j : Fin n) (w : V), w ∈ stripVertices (T j) → (Gx.Adj s w ↔ Gx.Adj b w))) := by
  classical
  have hXsub : ∀ Tx : Set V × Set V × Set V, Tx.1 ⊆ stripVertices Tx := by
    rintro ⟨X, Z, Y⟩ z hz; exact Or.inl (Or.inl hz)
  have hsplit : ∀ (j : Fin n) (Q : List V) (x y : V), IsSRung Gxᶜ (T j) Q →
      IsPathFrom Gxᶜ Q x y → (Gx.Adj r x ∧ Gx.Adj s y) ∨ (Gx.Adj s x ∧ Gx.Adj r y) :=
    fun j Q x y hQ hp => antirung_ends_split hG hL hFsub hR hodd hRset hrs hnoS hcover hZ hXY
      hint j hQ hp
  refine Thm95OffspringGapTwist.twist_or_merge_aux hL (side Gx r s)
    (fun j => Thm95OffspringParallel.parallel_newStrip (hL.2.1 j) (hsplit j) (hZ j) (hXY j)
      (hint j))
    (fun j => Thm95OffspringParallel.coParallel_newStrip (hL.2.1 j) (hsplit j) (hZ j) (hXY j)
      (hint j))
    (fun j => Thm95OffspringFacts.offVerts_cover (hL.2.1 j)
      (fun z hz => hcover j z (hXsub (T j) hz)))

end Workspace.ProofLemmas.Thm95OffspringGaps
