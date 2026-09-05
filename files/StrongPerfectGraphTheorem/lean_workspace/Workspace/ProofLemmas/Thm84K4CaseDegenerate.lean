import Workspace.ProofLemmas.Thm84K4CaseOldRung
import Workspace.ProofLemmas.Thm83MixedRungs

/-! # Closing the short-branch case by a four-cycle of zero rungs -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.Thm84K4CaseDegenerate

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems.SPGT Workspace.Types.Appearances.SPGT
open Thm84K4CaseRungs

variable {V U W : Type*} [Fintype V] [DecidableEq V] [Fintype U] [Fintype W]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {R R' : U → U → List V} {r r' : U → U → V} {H : SimpleGraph W}

/-- PAPER (8.4, printed p. 42): "But then `L(H)` is degenerate."
The four zero rungs become the four edges of the required cycle of branch vertices. -/
theorem degenerate_of_zero_four_cycle (hJ : IsKConnected J 3)
    (hSN : IsJStripSystem G J S N) (hForms : FormsLineGraph G J S N R H)
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    {a b c d : U} (hnd : [a, b, c, d].Nodup)
    (hcover : ∀ u, u = a ∨ u = b ∨ u = c ∨ u = d)
    (hab : J.Adj a b) (hbc : J.Adj b c) (hcd : J.Adj c d) (hda : J.Adj d a)
    (hzab : pathLength (R a b) = 0) (hzbc : pathLength (R b c) = 0)
    (hzcd : pathLength (R c d) = 0) (hzda : pathLength (R d a) = 0) :
    DegenerateAppearance J H := by
  obtain ⟨ι, B, hinj, hrange, hbranch, hdict, -⟩ :=
    Thm83MixedRungs.dict G J hJ S N hSN H R hForms
  refine Or.inl ⟨hK4, ι a, ι b, ι c, ι d, ?_,
    Thm83MixedRungs.zero_rung_to_adj hbranch hdict hab hzab,
    Thm83MixedRungs.zero_rung_to_adj hbranch hdict hbc hzbc,
    Thm83MixedRungs.zero_rung_to_adj hbranch hdict hcd hzcd,
    Thm83MixedRungs.zero_rung_to_adj hbranch hdict hda hzda, ?_⟩
  · simpa only [List.map_cons, List.map_nil] using hnd.map hinj
  · intro w hw
    rw [← hrange] at hw
    obtain ⟨u, rfl⟩ := hw
    rcases hcover u with he | he | he | he <;> rw [he] <;> simp

/-- After the attachment equality is read on the rungs, saturation supplies a zero
rung from each of `a,b` to one of `c,d`. The hole and linkage argument makes `ab`
zero as well. Bipartiteness, expressed by triangle parity, forces the two choices
to be opposite, completing the four-cycle. -/
theorem degenerate_of_short_attachment
    (hG : Berge G) (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    (hForms : FormsLineGraph G J S N R H)
    (hR' : ∀ u v, J.Adj u v → IsUVRung G J S N u v (R' u v))
    (hsym : ∀ u v, J.Adj u v → R v u = (R u v).reverse)
    (hsym' : ∀ u v, J.Adj u v → R' v u = (R' u v).reverse)
    (h : Ends G J S N R r) (h' : Ends G J S N R' r')
    (hK4 : Nonempty (J ≃g (⊤ : SimpleGraph (Fin 4))))
    {a b c d : U} (hab : J.Adj a b) (hac : J.Adj a c) (had : J.Adj a d)
    (hbc : J.Adj b c) (hbd : J.Adj b d) (hcd : J.Adj c d)
    (hcover : ∀ u, u = a ∨ u = b ∨ u = c ∨ u = d)
    (hdiff : ∀ u v, J.Adj u v → s(u, v) ≠ s(a, b) → R u v = R' u v)
    {y : V} (hy : y ∉ stripSystemVertices J S)
    (hsat : ∀ u v w, J.Adj u v → J.Adj u w →
      ¬ G.Adj y (r u v) → ¬ G.Adj y (r u w) → v = w)
    (hnone : ∀ x ∈ R' a b, ¬ G.Adj y x)
    (hclean : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d →
      ∀ x ∈ R' u v, G.Adj y x ↔ x = r' v u)
    (hcdzero : pathLength (R' c d) = 0) : DegenerateAppearance J H := by
  classical
  have hcross_adj : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d → J.Adj u v := by
    intro u hu v hv
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> subst u <;> subst v <;> assumption
  have hcross_diff : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d → R u v = R' u v := by
    intro u hu v hv
    apply hdiff u v (hcross_adj u hu v hv)
    rcases hu with hu | hu <;> rcases hv with hv | hv <;> subst u <;> subst v <;>
      simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
        hbc.ne, hbc.ne', hbd.ne, hbd.ne']
  have hhead : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d → r u v = r' u v := by
    intro u hu v hv
    exact head_eq_of_eq h h' (hcross_adj u hu v hv) (hcross_diff u hu v hv)
  have zero_of_head : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d →
      G.Adj y (r u v) → pathLength (R' u v) = 0 := by
    intro u hu v hv hyuv
    rw [hhead u hu v hv] at hyuv
    exact (h'.zero_iff (hcross_adj u hu v hv)).mpr
      ((hclean u hu v hv _ (h'.head_mem (hcross_adj u hu v hv))).mp hyuv)
  have exists_zero : ∀ u, u = a ∨ u = b →
      pathLength (R' u c) = 0 ∨ pathLength (R' u d) = 0 := by
    intro u hu
    by_cases hc : G.Adj y (r u c)
    · exact Or.inl (zero_of_head u hu c (Or.inl rfl) hc)
    by_cases hd : G.Adj y (r u d)
    · exact Or.inr (zero_of_head u hu d (Or.inr rfl) hd)
    exact (hcd.ne (hsat u c d (hcross_adj u hu c (Or.inl rfl))
      (hcross_adj u hu d (Or.inr rfl)) hc hd)).elim
  have low_b : ¬ (G.Adj y (r b c) ∧ G.Adj y (r b d)) := by
    rintro ⟨hyc, hyd⟩
    have hzc := zero_of_head b (Or.inr rfl) c (Or.inl rfl) hyc
    have hzd := zero_of_head b (Or.inr rfl) d (Or.inr rfl) hyd
    have hp := triangle_parity hG hJ hSN hR' hbc hcd hbd.symm
    rw [hzc, hcdzero, hsym' b d hbd] at hp
    simpa [pathLength, show (R' b d).length - 1 = 0 from hzd] using hp
  have hyt : G.Adj y (r b a) := by
    by_contra ht
    by_cases hc : G.Adj y (r b c)
    · have hd : ¬ G.Adj y (r b d) := fun hd => low_b ⟨hc, hd⟩
      exact had.ne (hsat b a d hab.symm hbd ht hd)
    · exact hac.ne (hsat b a c hab.symm hbc ht hc)
  have hzab : pathLength (R a b) = 0 := by
    rcases exists_zero b (Or.inr rfl) with hzbc | hzbd
    · exact Thm84K4CaseOldRung.old_rung_zero hG hJ hSN hR' hsym' h h'
        hab hac had hbc hbd hcd hy hyt hnone hclean hzbc hcdzero
    · have hzdc : pathLength (R' d c) = 0 := by rw [hsym' c d hcd]; simpa [pathLength] using hcdzero
      exact Thm84K4CaseOldRung.old_rung_zero hG hJ hSN hR' hsym' h h'
        hab had hac hbd hbc hcd.symm hy hyt hnone
        (fun u hu v hv => hclean u hu v hv.symm) hzbd hzdc
  have hzcd : pathLength (R c d) = 0 := by
    rw [hdiff c d hcd (by simp [Sym2.eq_iff, hac.ne', hbc.ne'])]
    exact hcdzero
  have zero_old : ∀ u, u = a ∨ u = b →
      pathLength (R u c) = 0 ∨ pathLength (R u d) = 0 := by
    intro u hu
    rw [hcross_diff u hu c (Or.inl rfl), hcross_diff u hu d (Or.inr rfl)]
    exact exists_zero u hu
  have hnd : [a, b, c, d].Nodup := by simp [hab.ne, hac.ne, had.ne, hbc.ne, hbd.ne, hcd.ne]
  have hzrev : ∀ u v, J.Adj u v → pathLength (R u v) = 0 → pathLength (R v u) = 0 := by
    intro u v huv hz
    rw [hsym u v huv]
    simpa [pathLength] using hz
  have no_same : ∀ v, J.Adj a v → J.Adj b v →
      pathLength (R a v) = 0 → pathLength (R b v) = 0 → False := by
    intro v hav hbv hzav hzbv
    have hp := triangle_parity hG hJ hSN hForms.1 hab hbv hav.symm
    rw [hzab, hzbv, hzrev a v hav hzav] at hp
    simpa using hp
  rcases zero_old a (Or.inl rfl) with hzac | hzad <;>
    rcases zero_old b (Or.inr rfl) with hzbc | hzbd
  · exact (no_same c hac hbc hzac hzbc).elim
  · apply degenerate_of_zero_four_cycle hJ hSN hForms hK4
      (a := a) (b := b) (c := d) (d := c)
    · simp [hab.ne, hac.ne, had.ne, hbc.ne, hbd.ne, hcd.ne']
    · intro u; rcases hcover u with h | h | h | h <;> tauto
    · exact hab
    · exact hbd
    · exact hcd.symm
    · exact hac.symm
    · exact hzab
    · exact hzbd
    · exact hzrev c d hcd hzcd
    · exact hzrev a c hac hzac
  · exact degenerate_of_zero_four_cycle hJ hSN hForms hK4 hnd hcover hab hbc hcd had.symm
      hzab hzbc hzcd (hzrev a d had hzad)
  · exact (no_same d had hbd hzad hzbd).elim

end Workspace.ProofLemmas.Thm84K4CaseDegenerate
