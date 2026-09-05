import Workspace.ProofLemmas.Thm84K4CaseRungs

/-! # The changed rung has length zero in the short case of 8.4 -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false

namespace Workspace.ProofLemmas.Thm84K4CaseOldRung

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.StripSystems.SPGT
open Thm84K4CaseRungs

variable {V U : Type*} [Fintype V] [DecidableEq V] [Fintype U]
  {G : SimpleGraph V} {J : SimpleGraph U} {S : U → U → Set V} {N : U → Set V}
  {R R' : U → U → List V} {r r' : U → U → V}

/-- PAPER (8.4, printed p. 42): "If `r_{2,1}` has no neighbour in `R'_{1,2}`,
then ... is an odd hole, a contradiction. ... but then `y` can be linked onto the
triangle `T'_1` ... contrary to 2.4. ... So `r_{2,1} = r_{1,2}`."

Here `bc` is the zero rung at `b`, and `cd` is the short alternative-5 branch.
Taking the other rung `ad` as the second path handles both choices in the printed proof. -/
theorem old_rung_zero
    (hG : Berge G) (hJ : IsKConnected J 3) (hSN : IsJStripSystem G J S N)
    (hR' : ∀ u v, J.Adj u v → IsUVRung G J S N u v (R' u v))
    (hsym' : ∀ u v, J.Adj u v → R' v u = (R' u v).reverse)
    (h : Ends G J S N R r) (h' : Ends G J S N R' r')
    {a b c d : U} (hab : J.Adj a b) (hac : J.Adj a c) (had : J.Adj a d)
    (hbc : J.Adj b c) (hbd : J.Adj b d) (hcd : J.Adj c d)
    {y : V} (hy : y ∉ stripSystemVertices J S)
    (hyt : G.Adj y (r b a))
    (hnone : ∀ x ∈ R' a b, ¬ G.Adj y x)
    (hclean : ∀ u, u = a ∨ u = b → ∀ v, v = c ∨ v = d →
      ∀ x ∈ R' u v, G.Adj y x ↔ x = r' v u)
    (hbczero : pathLength (R' b c) = 0) (hcdzero : pathLength (R' c d) = 0) :
    pathLength (R a b) = 0 := by
  by_contra hpos
  have hendsne : r a b ≠ r b a := fun he => hpos ((h.zero_iff hab).mpr he)
  have htNa : r b a ∉ N a := fun ht =>
    hendsne ((h.first a b hab _ (h.last_mem hab)).mp ht).symm
  have htS : r b a ∈ S a b := h.sub a b hab _ (h.last_mem hab)
  have htNb := h.head_N hab.symm
  have hbdo : Odd (pathLength (R' b d)) := by
    have hp := triangle_parity hG hJ hSN hR' hbc hcd hbd.symm
    rw [hbczero, hcdzero, hsym' b d hbd] at hp
    simpa [pathLength] using hp
  have hbdne : r' b d ≠ r' d b := by
    intro he
    have hz := (h'.zero_iff hbd).mpr he
    rw [hz] at hbdo
    exact (by simpa using hbdo : False)
  have hzNd : r' b d ∉ N d := fun hz =>
    hbdne ((h'.last b d hbd _ (h'.head_mem hbd)).mp hz)
  have hyz : ¬ G.Adj y (r' b d) := fun hz =>
    hbdne ((hclean b (Or.inr rfl) d (Or.inr rfl) _ (h'.head_mem hbd)).mp hz)
  have hbadA : ¬ (G.Adj y (r' a d) ∧ G.Adj y (r' a c)) := by
    rintro ⟨hyd, hyc⟩
    have hzad := (h'.zero_iff had).mpr
      ((hclean a (Or.inl rfl) d (Or.inr rfl) _ (h'.head_mem had)).mp hyd)
    have hzac := (h'.zero_iff hac).mpr
      ((hclean a (Or.inl rfl) c (Or.inl rfl) _ (h'.head_mem hac)).mp hyc)
    have hp := triangle_parity hG hJ hSN hR' hac hcd had.symm
    rw [hzac, hcdzero, hsym' a d had] at hp
    simpa [pathLength, show (R' a d).length - 1 = 0 from hzad] using hp
  have hsab_ad : s(a, b) ≠ s(a, d) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsab_ac : s(a, b) ≠ s(a, c) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsba_ad : s(b, a) ≠ s(a, d) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsba_ac : s(b, a) ≠ s(a, c) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsad_ac : s(a, d) ≠ s(a, c) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsbd_ba : s(b, d) ≠ s(b, a) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have hsbd_ad : s(b, d) ≠ s(a, d) := by simp [Sym2.eq_iff, hab.ne, hab.ne', hac.ne, hac.ne', had.ne, had.ne',
    hbc.ne, hbc.ne', hbd.ne, hbd.ne', hcd.ne, hcd.ne']
  have htout : ∀ v, v = c ∨ v = d → r b a ∉ R' a v := by
    intro v hv hx
    rcases hv with hv | hv
    · subst v
      exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN hab hac hsab_ac)
        htS (h'.sub a c hac _ hx)
    · subst v
      exact Set.disjoint_left.mp (StripSystemBasics.strip_disjoint hSN hab had hsab_ad)
        htS (h'.sub a d had _ hx)
  have htanti : ∀ v, v = c ∨ v = d → ∀ x ∈ R' a v, ¬ G.Adj (r b a) x := by
    intro v hv x hx htx
    rcases hv with hv | hv
    · subst v
      exact htNa (StripSystemBasics.mem_N_of_adj hSN hab hac hbc.ne htS
        (h'.sub a c hac _ hx) htx).1
    · subst v
      exact htNa (StripSystemBasics.mem_N_of_adj hSN hab had hbd.ne htS
        (h'.sub a d had _ hx) htx).1
  have hPno : ∀ x ∈ R' b a, ¬ G.Adj y x := by
    intro x hx
    exact hnone x (by simpa [hsym' a b hab] using hx)
  have hPQ : ∀ x ∈ R' b a, ∀ w ∈ R' a d,
      G.Adj x w ↔ x = r' a b ∧ w = r' a d := by
    intro x hx w hw
    exact h'.cross hSN hab had hbd.ne x (by simpa [hsym' a b hab] using hx) w hw
  have hPC : ∀ x ∈ R' b a, ∀ w ∈ R' a c,
      G.Adj x w ↔ x = r' a b ∧ w = r' a c := by
    intro x hx w hw
    exact h'.cross hSN hab hac hbc.ne x (by simpa [hsym' a b hab] using hx) w hw
  have htP := Thm84K4CaseGeometry.no_neighbor_of_triangle_link hG
    (h'.path b a hab.symm).1 (h'.path a d had).1 (h'.path a c hac).1
    (h'.path b a hab.symm).2.2 (h'.path a d had).2.1 (h'.path a c hac).2.1
    (h'.disjoint hSN hab.symm had hsba_ad) (h'.disjoint hSN hab.symm hac hsba_ac)
    (h'.disjoint hSN had hac hsad_ac) hPQ hPC (h'.cross hSN had hac hcd.ne')
    (htout d (Or.inr rfl)) (htout c (Or.inl rfl))
    (htanti d (Or.inr rfl)) (htanti c (Or.inl rfl)) hyt
    ⟨r' d a, h'.last_mem had,
      (hclean a (Or.inl rfl) d (Or.inr rfl) _ (h'.last_mem had)).mpr rfl⟩
    ⟨r' c a, h'.last_mem hac,
      (hclean a (Or.inl rfl) c (Or.inl rfl) _ (h'.last_mem hac)).mpr rfl⟩
    (hnone _ (h'.head_mem hab)) hbadA
  have hzP : ∀ x ∈ R' b a, G.Adj (r' b d) x ↔ x = r' b a := by
    intro x hx
    simpa using h'.cross hSN hbd hab.symm had.ne' (r' b d) (h'.head_mem hbd) x hx
  have hzQ : ∀ x ∈ R' a d, ¬ G.Adj (r' b d) x := by
    intro x hx hzx
    apply hzNd
    exact (StripSystemBasics.mem_N_of_adj hSN hbd.symm had.symm hab.ne'
      (by rw [StripSystemBasics.strip_symm hSN hbd.symm]; exact h'.head_strip hbd)
      (by rw [StripSystemBasics.strip_symm hSN had.symm]; exact h'.sub a d had x hx) hzx).1
  have hyout : ∀ u v, J.Adj u v → y ∉ R' u v := by
    intro u v huv hyR
    exact hy (StripSystemBasics.strip_subset_vertices huv (h'.sub u v huv y hyR))
  have htz : G.Adj (r b a) (r' b d) :=
    StripSystemBasics.Nuv_complete hSN hab.symm hbd had.ne _
      ⟨htNb, h.head_strip hab.symm⟩ _ ⟨h'.head_N hbd, h'.head_strip hbd⟩
  have hpar : Even (pathLength (R' b a) + pathLength (R' a d)) := by
    have hp := triangle_parity hG hJ hSN hR' hab.symm had hbd.symm
    rw [hsym' b d hbd] at hp
    simp only [pathLength, List.length_reverse, Nat.odd_iff] at hp hbdo
    simp only [pathLength, Nat.even_iff]
    omega
  exact Thm84K4CaseGeometry.short_case_hole_absurd hG
    (h'.path b a hab.symm) (h'.path a d had)
    (h'.disjoint hSN hab.symm had hsba_ad) hPQ hPno
    (hclean a (Or.inl rfl) d (Or.inr rfl)) htP (htanti d (Or.inr rfl)) hzP hzQ
    ⟨hyout b a hab.symm, hyout a d had⟩
    ⟨fun ht => hPno _ ht hyt, htout d (Or.inr rfl)⟩
    ⟨fun hz => h'.disjoint hSN hbd hab.symm hsbd_ba _ (h'.head_mem hbd) hz,
      fun hz => h'.disjoint hSN hbd had hsbd_ad _ (h'.head_mem hbd) hz⟩
    hyt htz hyz hpar

end Workspace.ProofLemmas.Thm84K4CaseOldRung
