import Workspace.Types.Tracks

set_option autoImplicit false

namespace Workspace.ProofLemmas.TwoVertexSplitNetwork

open Workspace.Types.Tracks.SPGT

abbrev Node (U : Type*) := U × Bool
abbrev Arc (U : Type*) := U ⊕ (U × U)

def tail {U : Type*} : Arc U → Node U
  | .inl x => (x, false)
  | .inr xy => (xy.1, true)

def head {U : Type*} : Arc U → Node U
  | .inl x => (x, true)
  | .inr xy => (xy.2, false)

noncomputable def capacity {U : Type*} (G : SimpleGraph U) (u v : U) : Arc U → Nat := by
  classical
  exact fun
    | .inl x => if x = u ∨ x = v then 2 else 1
    | .inr xy => if G.Adj xy.1 xy.2 then 2 else 0

def separator {U : Type*} (X : Set (Node U)) : Set U :=
  {x : U | (x, false) ∈ X ∧ (x, true) ∉ X}

noncomputable def cutCapacity {U : Type*} [Fintype U]
    (G : SimpleGraph U) (u v : U) (X : Set (Node U)) : Nat := by
  classical
  exact ∑ a : Arc U,
    if tail a ∈ X ∧ head a ∉ X then capacity G u v a else 0

theorem two_le_cutCapacity
    {U : Type*} [Fintype U] (G : SimpleGraph U) (u v : U)
    (huv : u ≠ v) (hG : IsKConnected G 2)
    (X : Set (Node U)) (huX : (u, true) ∈ X) (hvX : (v, false) ∉ X) :
    2 ≤ cutCapacity G u v X := by
  classical
  by_contra hcut
  have hcutlt : cutCapacity G u v X < 2 := by omega
  let term : Arc U → Nat := fun a =>
    if tail a ∈ X ∧ head a ∉ X then capacity G u v a else 0
  have hterm_lt (a : Arc U) : term a < 2 := by
    have hle : term a ≤ ∑ b : Arc U, term b := by
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
    have hsum : (∑ b : Arc U, term b) =
        cutCapacity G u v X := rfl
    omega
  let S : Set U := separator X
  have huS : u ∉ S := by
    intro hu
    exact hu.2 huX
  have hvS : v ∉ S := by
    intro hv
    exact hvX hv.1
  have hS : S.ncard < 2 := by
    by_contra hn
    have htwo : 1 < S.ncard := by omega
    obtain ⟨x, hx, y, hy, hxy⟩ := (Set.one_lt_ncard (s := S)).mp htwo
    have hxu : x ≠ u := by
      intro h
      subst x
      exact huS hx
    have hxv : x ≠ v := by
      intro h
      subst x
      exact hvS hx
    have hyu : y ≠ u := by
      intro h
      subst y
      exact huS hy
    have hyv : y ≠ v := by
      intro h
      subst y
      exact hvS hy
    have hx' : (x, false) ∈ X ∧ (x, true) ∉ X := by
      simpa [S, separator] using hx
    have hy' : (y, false) ∈ X ∧ (y, true) ∉ X := by
      simpa [S, separator] using hy
    have htx : term (Sum.inl x) = 1 := by
      simp [term, tail, head, capacity, hx', hxu, hxv]
    have hty : term (Sum.inl y) = 1 := by
      simp [term, tail, head, capacity, hy', hyu, hyv]
    have hpair : term (Sum.inl x) + term (Sum.inl y) ≤
        ∑ a : Arc U, term a := by
      rw [← Finset.sum_pair (show Sum.inl x ≠ (Sum.inl y : Arc U) by simpa)]
      exact Finset.sum_le_sum_of_subset (by simp)
    have hsum : (∑ a : Arc U, term a) =
        cutCapacity G u v X := rfl
    omega
  have hedge_cross {x y : U} (hxy : G.Adj x y) (hx : (x, true) ∈ X) :
      (y, false) ∈ X := by
    by_contra hy
    have ht : term (Sum.inr (x, y)) = 2 := by
      simp [term, tail, head, capacity, hx, hy, hxy]
    have := hterm_lt (Sum.inr (x, y))
    omega
  have hconn := hG.2 S hS
  let uS : ↑(Sᶜ) := ⟨u, huS⟩
  let vS : ↑(Sᶜ) := ⟨v, hvS⟩
  obtain ⟨p, hp⟩ := hconn.exists_isPath uS vS
  have huvS : uS ≠ vS := by
    intro h
    exact huv (congrArg Subtype.val h)
  have propagate : ∀ {a b : ↑(Sᶜ)} (q : (G.induce Sᶜ).Walk a b),
      (a.1, true) ∈ X →
      (b.1, true) ∈ X ∧ (q.length = 0 ∨ (b.1, false) ∈ X) := by
    intro a b q
    induction q with
    | nil =>
        intro ha
        exact ⟨ha, Or.inl rfl⟩
    | @cons a b c hab q ih =>
        intro ha
        have habG : G.Adj a.1 b.1 := hab
        have hbIn : (b.1, false) ∈ X := hedge_cross habG ha
        have hbOut : (b.1, true) ∈ X := by
          by_contra hbOut
          exact b.property ⟨hbIn, hbOut⟩
        obtain ⟨hcOut, hq⟩ := ih hbOut
        refine ⟨hcOut, Or.inr ?_⟩
        rcases hq with hzero | hcIn
        · have hbc : b = c := SimpleGraph.Walk.eq_of_length_eq_zero hzero
          subst c
          exact hbIn
        · exact hcIn
  obtain ⟨-, hpNil⟩ := propagate p huX
  have hpne : p.length ≠ 0 := by
    intro h
    exact huvS (SimpleGraph.Walk.eq_of_length_eq_zero h)
  exact hvX (hpNil.resolve_left hpne)

end Workspace.ProofLemmas.TwoVertexSplitNetwork
