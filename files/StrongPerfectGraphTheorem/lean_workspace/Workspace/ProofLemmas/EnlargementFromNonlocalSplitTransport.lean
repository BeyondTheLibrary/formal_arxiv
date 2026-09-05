import Workspace.ProofLemmas.EnlargementFromNonlocalSplitCore

/-!
# Moving a subdivision witness onto `Fin n`, and branches through two marked vertices

Two general facts used to finish the track splitting of 7.5 and 8.5.

The first is bookkeeping: `Promotion` asks for the refined skeleton on a type `Fin m`, while
the refined skeleton is built on a sum type, so its witness has to be carried across the
isomorphism.

The second is the reason the two marked vertices stay on no common branch.  In the refined
skeleton every vertex other than the two marks is a branch-vertex, so a branch containing both
marks has no room between them, and they are adjacent.
-/

set_option autoImplicit false

namespace Workspace.ProofLemmas.EnlargementFromNonlocalSplitTransport

open Workspace.Types.Tracks Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.NoCrossTrackBranch
open Workspace.ProofLemmas.EnlargementFromNonlocalSplitCore

variable {W : Type*}

/-- Transport a subdivision witness along an isomorphism of the graph being subdivided. -/
theorem subData_of_iso {X : Type*} {n : ℕ} {B : SimpleGraph X} {B' : SimpleGraph (Fin n)}
    (ψ : B ≃g B') {H : SimpleGraph W} {ι : X → W} {T : X → X → List W}
    (h : FullWitness B H ι T) :
    SubData B' H (fun u => ι (ψ.symm u)) (fun u v => T (ψ.symm u) (ψ.symm v)) := by
  have hadj : ∀ u v : Fin n, B'.Adj u v → B.Adj (ψ.symm u) (ψ.symm v) := by
    intro u v huv
    exact ψ.symm.map_rel_iff.mpr huv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.inj.comp (EquivLike.injective ψ.symm)
  · intro u v huv; exact h.track _ _ (hadj u v huv)
  · intro u v huv; exact h.len _ _ (hadj u v huv)
  · intro u v huv; exact h.rev _ _ (hadj u v huv)
  · intro u v u' v' huv hu'v' hne w hw
    refine h.disj _ _ _ _ (hadj u v huv) (hadj u' v' hu'v') ?_ w hw
    intro hq
    refine hne ?_
    rcases Sym2.eq_iff.mp hq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [show u = u' from (EquivLike.injective ψ.symm) h1,
        show v = v' from (EquivLike.injective ψ.symm) h2]
    · rw [show u = v' from (EquivLike.injective ψ.symm) h1,
        show v = u' from (EquivLike.injective ψ.symm) h2]
      exact Sym2.eq_swap
  · intro u v huv w hw
    rintro ⟨u', hu'⟩
    exact h.new _ _ (hadj u v huv) w hw ⟨ψ.symm u', hu'⟩
  · intro w
    rcases h.cover w with ⟨x, hx⟩ | ⟨x, y, hxy, hw⟩
    · exact Or.inl ⟨ψ x, by simpa using hx⟩
    · exact Or.inr ⟨ψ x, ψ y, ψ.map_rel_iff.mpr hxy, by simpa using hw⟩
  · ext e
    rw [h.edges]
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨x, y, hxy, hw⟩
      exact ⟨ψ x, ψ y, ψ.map_rel_iff.mpr hxy, by simpa using hw⟩
    · rintro ⟨u, v, huv, hw⟩
      exact ⟨ψ.symm u, ψ.symm v, hadj u v huv, hw⟩

/-- If every vertex apart from `a` and `b` is a branch-vertex, then a branch through both of
them makes them adjacent: no vertex is available to sit between them. -/
theorem adj_of_common_branch {X : Type*} {B : SimpleGraph X} {a b : X} (hab : a ≠ b)
    (hcov : ∀ v : X, v ∈ branchVertices B ∨ v = a ∨ v = b)
    {q : List X} (hq : IsBranch B q) (ha : a ∈ q) (hb : b ∈ q) : B.Adj a b := by
  obtain ⟨p, hp, hpa⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨r, hr, hrb⟩ := List.mem_iff_getElem.mp hb
  have hne : p ≠ r := by
    intro h; subst h; exact hab (hpa.symm.trans hrb)
  -- no index lies strictly between the two
  have hmid : ∀ c : ℕ, ∀ hc : c < q.length, min p r < c → c < max p r → False := by
    intro c hc h1 h2
    have hc1 : 1 ≤ c := by
      have : min p r < c := h1
      omega
    have hc2 : c + 1 < q.length := by
      have : c < max p r := h2
      have : max p r < q.length := by
        rcases max_cases p r with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      omega
    have hint : q[c] ∈ trackInterior q := by
      have := Workspace.ProofLemmas.SubdivisionCounting.mem_trackInterior_getElem q (c - 1)
        (by omega)
      rwa [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show c - 1 + 1 = c by omega) (by omega) hc] at this
    rcases hcov q[c] with hbr | hqc
    · exact hq.2.1 _ hint hbr
    · have hnd := hq.1.2.1
      rcases hqc with hqc | hqc
      · have : c = p := (List.Nodup.getElem_inj_iff hnd).mp (hqc.trans hpa.symm)
        omega
      · have : c = r := (List.Nodup.getElem_inj_iff hnd).mp (hqc.trans hrb.symm)
        omega
  have hstep : max p r = min p r + 1 := by
    by_contra hcon
    have hlt : min p r < max p r := by
      rcases max_cases p r with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        rcases min_cases p r with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> omega
    have : min p r + 1 < q.length := by
      have : max p r < q.length := by
        rcases max_cases p r with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
      omega
    exact hmid (min p r + 1) this (by omega) (by omega)
  have hlenmax : max p r < q.length := by
    rcases max_cases p r with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hadj : B.Adj (q[min p r]'(by omega)) (q[min p r + 1]'(by omega)) :=
    hq.1.2.2 (min p r) (by omega)
  rcases min_cases p r with ⟨hmin, -⟩ | ⟨hmin, -⟩
  · have hmax : max p r = r := by omega
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q hmin (by omega) hp,
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show min p r + 1 = r by omega) (by omega) hr, hpa, hrb] at hadj
    exact hadj
  · have hmax : max p r = p := by omega
    rw [Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q hmin (by omega) hr,
      Workspace.ProofLemmas.SubdivisionCounting.getElem_eq_of_index_eq q
        (show min p r + 1 = p by omega) (by omega) hp, hpa, hrb] at hadj
    exact hadj.symm

end Workspace.ProofLemmas.EnlargementFromNonlocalSplitTransport
