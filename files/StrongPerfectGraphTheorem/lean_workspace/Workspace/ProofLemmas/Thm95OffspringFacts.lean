import Workspace.ProofLemmas.Thm95OffspringDefs

/-!
# The two sentences of 9.5(1) about the offspring that need no odd hole

PAPER (9.5(1), printed p. 52): *"Now if `Mⱼ` is nonempty, then `(Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ)` is
an antistrip, and similarly if `Nⱼ` is nonempty it also induces an antistrip."*  Together with
the covering statement (every vertex of `Tⱼ` lies on some `Tⱼ`-antirung, and that antirung's end
in `Xⱼ` is adjacent to exactly one of `f₁, f_k`, so lies in `U` or in `V`), these are the two
assertions of the paragraph that are pure bookkeeping about rungs.

The file also carries the version of `Thm95StripExtension.odd_rungs` that takes its two
antistrips one by one instead of as a `Fin n`-family, which is what the new strip `S₀` needs:
its rungs are odd because each of them closes to a hole through two of the offspring.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm95OffspringFacts

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.ProofLemmas.Thm95OffspringDefs

variable {V : Type*} {G : SimpleGraph V}

/-- An antirung of `T` whose end in `X` lies in `W` is an antirung of the offspring of `T`
belonging to `W`. -/
theorem srung_to_offspring {T : Set V × Set V × Set V} {W : Set V} {Q : List V}
    (hQ : IsSRung Gᶜ T Q) {x : V} (hx : Q.head? = some x) (hxW : x ∈ W) :
    IsSRung Gᶜ (offspring G T W) Q := by
  have hmem : ∀ v ∈ Q, v ∈ offVerts G T W := fun v hv => ⟨Q, hQ, hv, x, hx, hxW⟩
  obtain ⟨X, Z, Y⟩ := T
  obtain ⟨a, b, hpath, ha, hb, htail, hlast, hint⟩ := hQ
  refine ⟨a, b, hpath, ⟨hmem a (PathBasics.head_mem hpath.2.1), ha⟩,
    ⟨hmem b (PathBasics.getLast_mem hpath.2.2), hb⟩, ?_, ?_,
    fun v hv => ⟨hmem v (PathBasics.interior_subset hv), hint v hv⟩⟩
  · exact fun v hv hvX => htail v hv hvX.2
  · exact fun v hv hvY => hlast v hv hvY.2

/-- **PAPER (9.5(1), p. 52):** *"Now if `Mⱼ` is nonempty, then `(Mⱼ ∩ Xⱼ, Mⱼ ∩ Zⱼ, Mⱼ ∩ Yⱼ)` is
an antistrip, and similarly if `Nⱼ` is nonempty it also induces an antistrip."* -/
theorem offspring_isAntistrip {T : Set V × Set V × Set V} (hT : IsAntistrip G T) (W : Set V)
    (hne : (offVerts G T W).Nonempty) : IsAntistrip G (offspring G T W) := by
  obtain ⟨v₀, Q₀, hQ₀, hv₀, x₀, hx₀, hx₀W⟩ := hne
  have hQ₀' := srung_to_offspring hQ₀ hx₀ hx₀W
  obtain ⟨X, Z, Y⟩ := T
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Set.disjoint_of_subset (fun _ h => h.2) (fun _ h => h.2) hT.1
  · exact Set.disjoint_of_subset (fun _ h => h.2) (fun _ h => h.2) hT.2.1
  · exact Set.disjoint_of_subset (fun _ h => h.2) (fun _ h => h.2) hT.2.2.1
  · obtain ⟨a, b, hpath, ha, -, -, -, -⟩ := hQ₀'
    exact ⟨a, ha⟩
  · obtain ⟨a, b, hpath, -, hb, -, -, -⟩ := hQ₀'
    exact ⟨b, hb⟩
  · intro u hu
    have huM : u ∈ offVerts G (X, Z, Y) W := by
      rcases hu with (hu | hu) | hu <;> exact hu.1
    obtain ⟨Q, hQ, huQ, x, hx, hxW⟩ := huM
    exact ⟨Q, srung_to_offspring hQ hx hxW, huQ⟩

/-- **PAPER (9.5(1), p. 52):** the two offspring of `Tⱼ` cover `V(Tⱼ)`.  Every vertex of the
antistrip lies on some antirung, and that antirung's end in `Xⱼ` is adjacent to `f₁` or to
`f_k`. -/
theorem offVerts_cover {T : Set V × Set V × Set V} (hT : IsAntistrip G T) {W₁ W₂ : Set V}
    (hcov : ∀ z ∈ T.1, z ∈ W₁ ∨ z ∈ W₂) :
    offVerts G T W₁ ∪ offVerts G T W₂ = stripVertices T := by
  refine Set.ext (fun v => ⟨?_, ?_⟩)
  · rintro (hv | hv) <;> exact offVerts_subset T _ hv
  · intro hv
    obtain ⟨X, Z, Y⟩ := T
    obtain ⟨Q, hQ, hvQ⟩ := hT.2.2.2.2.2 v hv
    obtain ⟨a, b, hpath, ha, -, -, -, -⟩ := id hQ
    rcases hcov a ha with h | h
    · exact Or.inl ⟨Q, hQ, hvQ, a, hpath.2.1, h⟩
    · exact Or.inr ⟨Q, hQ, hvQ, a, hpath.2.1, h⟩

/-- **PAPER (9.1):** *"Certainly `P₁` is odd since `x₁-a₁-P₁-b₁-y₂-x₁` is a hole."*  The
version of `Thm95StripExtension.odd_rungs` that takes the two antistrips explicitly. -/
theorem odd_rungs_two (hG : Berge G) {U T₁ T₂ : Set V × Set V × Set V}
    (hU : IsStrip G U) (hT₁ : IsAntistrip G T₁) (hT₂ : IsAntistrip G T₂)
    (hd₁ : Disjoint (stripVertices U) (stripVertices T₁))
    (hd₂ : Disjoint (stripVertices U) (stripVertices T₂))
    (hcomp : Complete G (stripVertices T₁) (stripVertices T₂))
    (hp₁ : ParallelStripAntistrip G U T₁ ∨ CoParallel G U T₁)
    (hp₂ : ParallelStripAntistrip G U T₂ ∨ CoParallel G U T₂)
    {p : List V} (hp : IsSRung G U p) : Odd (pathLength p) := by
  obtain ⟨a, b, x, -, hpath, ha, hb, hx, -, hxa, -⟩ :=
    Thm95StripExtension.private_neighbours hT₁ hp₁ hp
  obtain ⟨a', b', -, y, hpath', -, -, -, hy, -, hyb⟩ :=
    Thm95StripExtension.private_neighbours hT₂ hp₂ hp
  have hb' : b' = b := Option.some.inj (hpath'.2.2.symm.trans hpath.2.2)
  subst b'
  have hab : a ≠ b := by
    obtain ⟨A, C, B⟩ := U
    exact fun heq => Set.disjoint_left.mp hU.1 ha (heq ▸ hb)
  have hlen : 1 ≤ pathLength p := by
    have h0 := PathBasics.length_eq_pathLength_add_one hpath.1
    have hhead := PathBasics.getElem_zero_of_head? hpath.2.1 (by omega)
    have hlast := PathBasics.getElem_last_of_getLast? hpath.2.2 (by omega)
    by_contra h
    have heq : p.length - 1 = 0 := by unfold pathLength at h; omega
    have hlast' : p[0] = b := by simpa only [heq] using hlast
    exact hab (hhead.symm.trans hlast')
  exact Thm91.odd_of_two_attachments hG hpath hlen
    (fun hx' => Set.disjoint_left.mp hd₁
      (KnotFromTwist.mem_stripVertices_of_isSRung hp hx') hx)
    (fun hy' => Set.disjoint_left.mp hd₂
      (KnotFromTwist.mem_stripVertices_of_isSRung hp hy') hy)
    (hcomp x hx y hy) hxa hyb

end Workspace.ProofLemmas.Thm95OffspringFacts
