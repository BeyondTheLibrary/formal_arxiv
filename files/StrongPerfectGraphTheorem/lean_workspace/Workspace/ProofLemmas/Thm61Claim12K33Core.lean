import Workspace.ProofLemmas.Thm61Claim12SixVertices

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Workspace.ProofLemmas.Thm61Claim12K33Core

open Workspace.Types.Tracks.SPGT
open Workspace.ProofLemmas.Thm61EvenEndgameHelpers
open Workspace.ProofLemmas.SubdivisionCounting

/-- The graph identification in "but then `J = K₃,₃`" in claim (12). Four degree-three
vertices on a four-cycle force the sixth-to-fifth edge by 3-connectivity. -/
theorem identify
    {m : ℕ} {J : SimpleGraph (Fin m)} (hJ : IsKConnected J 3)
    {a b c d p q : Fin m} (hnd : [a, b, c, d, p, q].Nodup)
    (hab : J.Adj a b) (hbc : J.Adj b c) (hcd : J.Adj c d) (hda : J.Adj d a)
    (hap : J.Adj a p) (hcp : J.Adj c p) (hbq : J.Adj b q) (hdq : J.Adj d q)
    (hdega : (J.neighborSet a).ncard = 3) (hdegb : (J.neighborSet b).ncard = 3)
    (hdegc : (J.neighborSet c).ncard = 3) (hdegd : (J.neighborSet d).ncard = 3) :
    Nonempty (J ≃g completeBipartiteGraph (Fin 3) (Fin 3)) ∧ J.Adj p q ∧
      (∀ x, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = p ∨ x = q) ∧
      ¬ J.Adj a c ∧ ¬ J.Adj a q ∧ ¬ J.Adj c q ∧
      ¬ J.Adj b d ∧ ¬ J.Adj b p ∧ ¬ J.Adj d p := by
  classical
  have hn := hnd
  simp only [List.nodup_cons, List.mem_cons, List.mem_nil_iff, not_or,
    not_false_eq_true, List.nodup_nil, and_true] at hn
  have hall := six_vertices_of_alternating_degree_three_cycle hJ hab hbc hcd hda hap hcp hbq hdq
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    hdega hdegb hdegc hdegd
  have hNa := fun x (hx : J.Adj a x) =>
    neighbor_of_degree_three hdega (by omega) (by omega) (by omega) hab hda.symm hap hx
  have hNc := fun x (hx : J.Adj c x) =>
    neighbor_of_degree_three hdegc (by omega) (by omega) (by omega) hbc.symm hcd hcp hx
  have hNb := fun x (hx : J.Adj b x) =>
    neighbor_of_degree_three hdegb (by omega) (by omega) (by omega) hab.symm hbc hbq hx
  have hNd := fun x (hx : J.Adj d x) =>
    neighbor_of_degree_three hdegd (by omega) (by omega) (by omega) hda hcd.symm hdq hx
  have hnac : ¬ J.Adj a c := by intro h; have := hNa c h; omega
  have hnaq : ¬ J.Adj a q := by intro h; have := hNa q h; omega
  have hncq : ¬ J.Adj c q := by intro h; have := hNc q h; omega
  have hnbd : ¬ J.Adj b d := by intro h; have := hNb d h; omega
  have hnbp : ¬ J.Adj b p := by intro h; have := hNb p h; omega
  have hndp : ¬ J.Adj d p := by intro h; have := hNd p h; omega
  have hpq : J.Adj p q := by
    by_contra hh
    have hs : J.neighborSet p ⊆ ({a, c} : Set (Fin m)) := by
      intro x hx
      rcases hall x with rfl | rfl | rfl | rfl | rfl | rfl
      · simp
      · exact False.elim (hnbp hx.symm)
      · simp
      · exact False.elim (hndp hx.symm)
      · exact False.elim (J.irrefl hx)
      · exact False.elim (hh hx)
    have hle := Set.ncard_le_ncard hs (Set.toFinite _)
    rw [Set.ncard_pair (show a ≠ c by omega)] at hle
    have := three_le_degree_of_three_connected J hJ p
    omega
  refine ⟨?_, hpq, hall, hnac, hnaq, hncq, hnbd, hnbp, hndp⟩
  apply iso_completeBipartite_three_three ![a, c, q] ![b, d, p]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> omega
  · intro i j hij
    fin_cases i <;> fin_cases j <;> dsimp at hij ⊢ <;> omega
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;> omega
  · intro x
    rcases hall x with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inr ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inr ⟨1, rfl⟩
    · exact Or.inr ⟨2, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;>
      first | assumption | exact hda.symm | exact hbc.symm | exact hbq.symm | exact hdq.symm | exact hpq.symm
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;>
      first | exact J.irrefl | exact hnac | exact hnaq | exact hncq | exact fun h => hnac h.symm | exact fun h => hnaq h.symm | exact fun h => hncq h.symm
  · intro i j
    fin_cases i <;> fin_cases j <;> dsimp <;>
      first | exact J.irrefl | exact hnbd | exact hnbp | exact hndp | exact fun h => hnbd h.symm | exact fun h => hnbp h.symm | exact fun h => hndp h.symm

end Workspace.ProofLemmas.Thm61Claim12K33Core
