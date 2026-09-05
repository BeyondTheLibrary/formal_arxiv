import Workspace.ProofLemmas.Thm95GapBasics
import Workspace.ProofLemmas.Thm95StripExtension
import Workspace.ProofLemmas.Thm95OffspringGeneric

/-!
# The offspring of an antistrip, and the new strip of 9.5(1)

PAPER (9.5(1), printed p. 52): *"let `Mⱼ` be the union of the vertex sets of all `Tⱼ`-antirungs
`xⱼ-Qⱼ-yⱼ` such that `xⱼ ∈ U`, and `Nⱼ` the union of all those with `xⱼ ∈ V`. … Now if `Mⱼ` is
nonempty, then `(Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ)` is an antistrip, and similarly if `Nⱼ` is nonempty
it also induces an antistrip.  We call these the offspring of `Tⱼ`. … Also, there is a new strip
`S₀ = ({f₁}, {f₂,…,f_{k-1}}, {f_k})`."*

`offVerts G T W` is the paper's `Mⱼ` (for `W = U`) and `Nⱼ` (for `W = V`): the union of the
vertex sets of the `T`-antirungs whose end in `X` lies in `W`.  `offspring G T W` is the triple
the paper forms from it, and `newStrip` is `S₀`.

This file contains only the bookkeeping that does not use the graph being Berge: how a vertex of
an offspring sits on its antistrip, that an antirung of an offspring is an antirung of the
parent, that being parallel is inherited by a sub-antistrip, and that `S₀` is a strip.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringDefs

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT

variable {V : Type*} {G : SimpleGraph V}

/-- **PAPER (9.5(1), p. 52):** *"let `Mⱼ` be the union of the vertex sets of all `Tⱼ`-antirungs
`xⱼ-Qⱼ-yⱼ` such that `xⱼ ∈ U`"*.  Here `W` is the paper's `U` (or `V`), and the end `xⱼ` is the
end of the antirung lying in `T.1`, i.e. its first vertex. -/
def offVerts (G : SimpleGraph V) (T : Set V × Set V × Set V) (W : Set V) : Set V :=
  {v : V | ∃ Q : List V, IsSRung Gᶜ T Q ∧ v ∈ Q ∧ ∃ x, Q.head? = some x ∧ x ∈ W}

/-- **PAPER (9.5(1), p. 52):** *"`(Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ)`"*, the offspring of `T`
belonging to `W`. -/
def offspring (G : SimpleGraph V) (T : Set V × Set V × Set V) (W : Set V) :
    Set V × Set V × Set V :=
  (offVerts G T W ∩ T.1, offVerts G T W ∩ T.2.1, offVerts G T W ∩ T.2.2)

/-- **PAPER (9.5(1), p. 52):** *"there is a new strip `S₀ = ({f₁}, {f₂,…,f_{k-1}}, {f_k})`"*. -/
def newStrip (R : List V) (r s : V) : Set V × Set V × Set V :=
  ({r}, {v : V | v ∈ SPGT.interior R}, {s})

/-! ### Where a vertex of an antirung can sit -/

/-- A vertex of a `T`-antirung lies in `V(T)`. -/
theorem mem_stripVertices_of_mem_srung {T : Set V × Set V × Set V} {Q : List V}
    (hQ : IsSRung Gᶜ T Q) {v : V} (hv : v ∈ Q) : v ∈ stripVertices T :=
  KnotFromTwist.mem_stripVertices_of_isSRung hQ hv

/-- `offVerts` is a subset of the vertex set of the antistrip. -/
theorem offVerts_subset (T : Set V × Set V × Set V) (W : Set V) :
    offVerts G T W ⊆ stripVertices T := by
  rintro v ⟨Q, hQ, hv, -⟩
  exact mem_stripVertices_of_mem_srung hQ hv

/-- The vertex set of an offspring is exactly `Mⱼ` (resp. `Nⱼ`). -/
theorem stripVertices_offspring (T : Set V × Set V × Set V) (W : Set V) :
    stripVertices (offspring G T W) = offVerts G T W := by
  obtain ⟨X, Z, Y⟩ := T
  refine Set.ext (fun v => ⟨?_, ?_⟩)
  · rintro ((⟨h, -⟩ | ⟨h, -⟩) | ⟨h, -⟩) <;> exact h
  · intro hv
    rcases offVerts_subset (G := G) (X, Z, Y) W hv with (h | h) | h
    · exact Or.inl (Or.inl ⟨hv, h⟩)
    · exact Or.inl (Or.inr ⟨hv, h⟩)
    · exact Or.inr ⟨hv, h⟩

/-- On an antirung, a vertex of `X` is the first vertex. -/
theorem head_of_mem_X {T : Set V × Set V × Set V} (hT : IsAntistrip G T) {Q : List V}
    (hQ : IsSRung Gᶜ T Q) {v : V} (hv : v ∈ Q) (hvX : v ∈ T.1) : Q.head? = some v := by
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨x, y, hpath, hxX, hyY, -, -, hint⟩ := hQ
  by_cases hvx : v = x
  · exact hvx ▸ hpath.2.1
  by_cases hvy : v = y
  · exact absurd (hvy ▸ hyY) (Set.disjoint_left.mp hT.1 hvX)
  · exact absurd (hint v ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hvx, hvy⟩))
      (Set.disjoint_left.mp hT.2.1 hvX)

/-- On an antirung, a vertex of `Y` is the last vertex. -/
theorem last_of_mem_Y {T : Set V × Set V × Set V} (hT : IsAntistrip G T) {Q : List V}
    (hQ : IsSRung Gᶜ T Q) {v : V} (hv : v ∈ Q) (hvY : v ∈ T.2.2) : Q.getLast? = some v := by
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨x, y, hpath, hxX, hyY, -, -, hint⟩ := hQ
  by_cases hvy : v = y
  · exact hvy ▸ hpath.2.2
  by_cases hvx : v = x
  · exact absurd hvY (Set.disjoint_left.mp hT.1 (hvx ▸ hxX))
  · exact absurd (hint v ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hvx, hvy⟩))
      (Set.disjoint_left.mp hT.2.2.1 hvY)

/-- A vertex of an offspring lying in `X` lies in `W`: it is the first vertex of the antirung
that put it there. -/
theorem mem_W_of_mem_offVerts_X {T : Set V × Set V × Set V} (hT : IsAntistrip G T) {W : Set V}
    {v : V} (hv : v ∈ offVerts G T W) (hvX : v ∈ T.1) : v ∈ W := by
  obtain ⟨Q, hQ, hvQ, x, hx, hxW⟩ := hv
  have h : some v = some x := (head_of_mem_X hT hQ hvQ hvX).symm.trans hx
  exact (Option.some.inj h) ▸ hxW

/-! ### Antirungs of an offspring -/

/-- Every vertex of an antirung of an offspring of `T` lies in the offspring's vertex set. -/
theorem mem_offVerts_of_mem_srung_offspring {T : Set V × Set V × Set V} {W : Set V}
    {Q : List V} (hQ : IsSRung Gᶜ (offspring G T W) Q) {v : V} (hv : v ∈ Q) :
    v ∈ offVerts G T W := by
  obtain ⟨a, b, hpath, ha, hb, -, -, hint⟩ := hQ
  by_cases hva : v = a
  · exact hva ▸ ha.1
  by_cases hvb : v = b
  · exact hvb ▸ hb.1
  · exact (hint v ((PathBasics.mem_interior_iff_of_pathFrom hpath).mpr ⟨hv, hva, hvb⟩)).1

/-- An antirung of an offspring of `T` is an antirung of `T`. -/
theorem srung_offspring {T : Set V × Set V × Set V} {W : Set V} {Q : List V}
    (hQ : IsSRung Gᶜ (offspring G T W) Q) : IsSRung Gᶜ T Q := by
  have hmem := fun {v : V} (hv : v ∈ Q) => mem_offVerts_of_mem_srung_offspring hQ hv
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨a, b, hpath, ha, hb, htail, hlast, hint⟩ := hQ
  refine ⟨a, b, hpath, ha.2, hb.2, ?_, ?_, fun v hv => (hint v hv).2⟩
  · exact fun v hv hvX => htail v hv ⟨hmem (List.mem_of_mem_tail hv), hvX⟩
  · exact fun v hv hvY => hlast v hv ⟨hmem (List.mem_of_mem_dropLast hv), hvY⟩


/-! ### Parallelism is inherited by a sub-antistrip -/

/-- Being parallel is inherited by a triple whose three sets are contained in the three sets of
the antistrip.  Each offspring is such a triple, so it keeps the relation of its parent to every
strip of the striation. -/
theorem parallel_mono {S T T' : Set V × Set V × Set V}
    (hpar : ParallelStripAntistrip G S T)
    (h1 : T'.1 ⊆ T.1) (h2 : T'.2.1 ⊆ T.2.1) (h3 : T'.2.2 ⊆ T.2.2) :
    ParallelStripAntistrip G S T' := by
  obtain ⟨A, C, B⟩ := S
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨X', Z', Y'⟩ := T'
  exact ⟨⟨fun a ha w hw => hpar.1.1 a ha w (hw.imp (fun h => h1 h) (fun h => h2 h)),
      fun b hb w hw => hpar.1.2 b hb w (hw.imp (fun h => h3 h) (fun h => h2 h))⟩,
    fun x hx w hw => hpar.2.1 x (h1 hx) w hw,
    fun y hy w hw => hpar.2.2 y (h3 hy) w hw⟩

/-- The co-parallel version of `parallel_mono`. -/
theorem coParallel_mono {S T T' : Set V × Set V × Set V}
    (hpar : CoParallel G S T)
    (h1 : T'.1 ⊆ T.1) (h2 : T'.2.1 ⊆ T.2.1) (h3 : T'.2.2 ⊆ T.2.2) :
    CoParallel G S T' := by
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨X', Z', Y'⟩ := T'
  exact parallel_mono hpar h3 h2 h1

/-- Each offspring of `T` sits inside `T` componentwise. -/
theorem offspring_le (T : Set V × Set V × Set V) (W : Set V) :
    (offspring G T W).1 ⊆ T.1 ∧ (offspring G T W).2.1 ⊆ T.2.1 ∧
      (offspring G T W).2.2 ⊆ T.2.2 :=
  ⟨fun _ h => h.2, fun _ h => h.2, fun _ h => h.2⟩

/-- Parallelism and co-parallelism pass from `T` to each of its offspring. -/
theorem parallel_offspring {S T : Set V × Set V × Set V} (W : Set V)
    (h : ParallelStripAntistrip G S T ∨ CoParallel G S T) :
    ParallelStripAntistrip G S (offspring G T W) ∨ CoParallel G S (offspring G T W) := by
  obtain ⟨h1, h2, h3⟩ := offspring_le (G := G) T W
  exact h.imp (fun h => parallel_mono h h1 h2 h3) (fun h => coParallel_mono h h1 h2 h3)

/-! ### The new strip -/

/-- `R` is a rung of the new strip `S₀`. -/
theorem newStrip_srung {R : List V} {r s : V} (hR : IsPathFrom G R r s) :
    IsSRung G (newStrip R r s) R :=
  ⟨r, s, hR, rfl, rfl,
    fun v hv hvr => Thm95StripExtension.tail_ne_head hR hv hvr,
    fun v hv hvs => Thm95StripExtension.dropLast_ne_last hR hv hvs,
    fun _ hv => hv⟩

/-- **PAPER (9.5(1), p. 52):** *"there is a new strip `S₀ = ({f₁}, {f₂,…,f_{k-1}}, {f_k})`"*.
It is a strip: its only end sets are the two ends of the path, and `R` itself is a rung
through every one of its vertices. -/
theorem newStrip_isStrip {R : List V} {r s : V} (hR : IsPathFrom G R r s) (hrs : r ≠ s) :
    IsStrip G (newStrip R r s) := by
  have hint : ∀ {x : V}, x ∈ SPGT.interior R ↔ x ∈ R ∧ x ≠ r ∧ x ≠ s :=
    fun {x} => PathBasics.mem_interior_iff_of_pathFrom hR
  refine ⟨?_, ?_, ?_, ⟨r, rfl⟩, ⟨s, rfl⟩, ?_⟩
  · exact Set.disjoint_singleton.mpr hrs
  · exact Set.disjoint_left.mpr (by rintro v rfl hv; exact (hint.mp hv).2.1 rfl)
  · exact Set.disjoint_left.mpr (by rintro v rfl hv; exact (hint.mp hv).2.2 rfl)
  · intro v hv
    refine ⟨R, newStrip_srung hR, ?_⟩
    rcases hv with (hv | hv) | hv
    · exact hv ▸ PathBasics.head_mem hR.2.1
    · exact hv ▸ PathBasics.getLast_mem hR.2.2
    · exact PathBasics.interior_subset hv

/-- The vertex set of the new strip is the vertex set of `R`. -/
theorem stripVertices_newStrip {R : List V} {r s : V} (hR : IsPathFrom G R r s) :
    stripVertices (newStrip R r s) = {v : V | v ∈ R} := by
  have hint : ∀ {x : V}, x ∈ SPGT.interior R ↔ x ∈ R ∧ x ≠ r ∧ x ≠ s :=
    fun {x} => PathBasics.mem_interior_iff_of_pathFrom hR
  refine Set.ext (fun v => ⟨?_, ?_⟩)
  · rintro ((hv | hv) | hv)
    · exact hv ▸ PathBasics.head_mem hR.2.1
    · exact hv ▸ PathBasics.getLast_mem hR.2.2
    · exact PathBasics.interior_subset hv
  · intro hv
    by_cases hvr : v = r
    · exact Or.inl (Or.inl hvr)
    by_cases hvs : v = s
    · exact Or.inl (Or.inr hvs)
    · exact Or.inr (hint.mpr ⟨hv, hvr, hvs⟩)

end Workspace.ProofLemmas.Thm95OffspringDefs
