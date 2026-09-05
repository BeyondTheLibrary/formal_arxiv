import Workspace.ProofLemmas.Thm232ClosingInactive
import Workspace.ProofLemmas.Thm232ClosingGeometry

/-! Orient the two complete triples using the side with no attachment. -/

set_option autoImplicit false

namespace Workspace.ProofLemmas.Thm232ClosingOrientation

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Wheels Workspace.Types.Wheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.KiteTailBasics

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER (23.2, printed p. 141): “This proves that `x₀ = c₃`, and therefore
`x₁ ≠ c₁`. By exchanging `x₀,x₁`, we deduce that `x₁` has a neighbour in `F`.”
The four complete edges identify the inactive end once its other neighbour has
been proved complete. -/
theorem orientation (G : SimpleGraph V) (hG : InF8 G)
    (C : List V) (Y : Set V) (hw : IsWheel G C Y)
    (x₀ z x₁ c₁ c₂ c₃ : V) (k d : ℕ)
    (hd2 : 2 ≤ d) (hdn : d + 2 ≤ C.length)
    (hpre1 : [x₀, z, x₁] <+: C.rotate k)
    (hpre2 : [c₁, c₂, c₃] <+: C.rotate (k + d))
    (h0Y : VertexComplete G x₀ Y) (hzY : VertexComplete G z Y)
    (h1Y : VertexComplete G x₁ Y)
    (hnb : IsRimNeighbours G C z x₀ x₁)
    (hexh : ∀ a b : V, a ∈ C → b ∈ C → EdgeComplete G Y a b →
      ({a,b} : Set V) = {x₀,z} ∨ ({a,b} : Set V) = {z,x₁} ∨
      ({a,b} : Set V) = {c₁,c₂} ∨ ({a,b} : Set V) = {c₂,c₃})
    (T R : List V) (y w : V) (hTeq : T = z :: y :: R)
    (hT : IsPathFrom G T z w) (hwC : w ∈ C) (hwz : w ≠ z)
    (havoid : ∀ a ∈ T, a ≠ x₀ ∧ a ≠ x₁)
    (hint : ∀ a ∈ SPGT.interior T, a ∉ Y ∧ ¬ VertexComplete G a Y)
    (h3 : VertexAnticomplete G y ({a : V | a ∈ C} \ ({z,x₀,x₁} : Set V)))
    (hF : VertexAnticomplete G x₀ {a : V | a ∈ SPGT.interior T} ∨
      VertexAnticomplete G x₁ {a : V | a ∈ SPGT.interior T}) :
    (VertexAnticomplete G x₀ {a : V | a ∈ SPGT.interior T} ∧ x₀ = c₃ ∧
        ∃ a ∈ SPGT.interior T, G.Adj x₁ a) ∨
      (VertexAnticomplete G x₁ {a : V | a ∈ SPGT.interior T} ∧ x₁ = c₁ ∧
        ∃ a ∈ SPGT.interior T, G.Adj x₀ a) := by
  have hzC := (hole_triple hw.1.1 ⟨k,hpre1⟩).2.1
  obtain ⟨h01, h02, h12, h13⟩ :=
    Thm232ClosingGeometry.outer_ne hw.1.1 hw.1.2 hd2 hdn hpre1 hpre2
  have h0z : x₀ ≠ z := hnb.2.2.2.1.ne'
  have h1z : x₁ ≠ z := hnb.2.2.2.2.1.ne'
  have h01ne := hnb.1
  have hleft : VertexAnticomplete G x₀ {a : V | a ∈ SPGT.interior T} → x₀ = c₃ := by
    intro hanti
    obtain ⟨r⟩ := Thm232ClosingRegion.region hw hzC hnb hTeq hT hwC hwz havoid hint h3 hanti
    have hsY := Thm232ClosingInactive.next_complete hG hw hzC hnb h0Y hzY h1Y r
    have hedge := hexh x₀ r.s hnb.2.1 r.sC ⟨r.pnb.2.2.2.2.1, h0Y, hsY⟩
    have hsz : r.s ≠ z := r.pnb.1.symm
    simp only [Set.pair_eq_pair_iff] at hedge
    rcases hedge with (⟨_, he⟩ | ⟨he, _⟩) | (⟨he, _⟩ | ⟨he, _⟩) |
        (⟨he, _⟩ | ⟨he, _⟩) | (⟨he, _⟩ | ⟨he, _⟩)
    · exact (hsz he).elim
    · exact (h0z he).elim
    · exact (h0z he).elim
    · exact (h01ne he).elim
    · exact (h01 he).elim
    · exact (h02 he).elim
    · exact (h02 he).elim
    · exact he
  have hright : VertexAnticomplete G x₁ {a : V | a ∈ SPGT.interior T} → x₁ = c₁ := by
    intro hanti
    have h3' : VertexAnticomplete G y ({a : V | a ∈ C} \ ({z,x₁,x₀} : Set V)) := by
      have heq : ({z,x₁,x₀} : Set V) = {z,x₀,x₁} := by
        ext a
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        tauto
      rwa [heq]
    have hnb' := isRimNeighbours_symm hnb
    obtain ⟨r⟩ := Thm232ClosingRegion.region hw hzC hnb' hTeq hT hwC hwz
      (fun a ha => (havoid a ha).symm) hint h3' hanti
    have hsY := Thm232ClosingInactive.next_complete hG hw hzC hnb' h1Y hzY h0Y r
    have hedge := hexh x₁ r.s hnb.2.2.1 r.sC ⟨r.pnb.2.2.2.2.1, h1Y, hsY⟩
    have hsz : r.s ≠ z := r.pnb.1.symm
    simp only [Set.pair_eq_pair_iff] at hedge
    rcases hedge with (⟨he, _⟩ | ⟨he, _⟩) | (⟨he, _⟩ | ⟨_, he⟩) |
        (⟨he, _⟩ | ⟨he, _⟩) | (⟨he, _⟩ | ⟨he, _⟩)
    · exact (h01ne he.symm).elim
    · exact (h1z he).elim
    · exact (h1z he).elim
    · exact (hsz he).elim
    · exact he
    · exact (h12 he).elim
    · exact (h12 he).elim
    · exact (h13 he).elim
  have hno := Thm232ClosingGeometry.not_both_overlap hw.1.1 hw.1.2 hd2 hdn hpre1 hpre2
  rcases hF with hF | hF
  · refine Or.inl ⟨hF, hleft hF, ?_⟩
    by_contra hnone
    have hanti : VertexAnticomplete G x₁ {a : V | a ∈ SPGT.interior T} :=
      fun a ha hadj => hnone ⟨a, ha, hadj⟩
    exact hno ⟨hleft hF, hright hanti⟩
  · refine Or.inr ⟨hF, hright hF, ?_⟩
    by_contra hnone
    have hanti : VertexAnticomplete G x₀ {a : V | a ∈ SPGT.interior T} :=
      fun a ha hadj => hnone ⟨a, ha, hadj⟩
    exact hno ⟨hleft hanti, hright hF⟩

end Workspace.ProofLemmas.Thm232ClosingOrientation
