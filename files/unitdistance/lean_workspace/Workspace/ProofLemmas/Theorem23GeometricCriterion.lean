import Mathlib
import Workspace.Types.PlanarCounting
import Workspace.Types.DiscriminantsClassNumber
import Workspace.Types.AdmissibleDatum
import Workspace.Types.MinkowskiWindow
import Workspace.Types.CMAdjoinI
import Workspace.ProofLemmas.Prop22NormOneElements
import Workspace.ProofLemmas.Lemma24Averaging
import Workspace.ProofLemmas.Lemma25ProjectionInjective
import Workspace.ProofLemmas.Lemma25PlanarCount
import Workspace.ProofLemmas.Lemma26SizeBound
import Workspace.ProofLemmas.SublemmaLatticeDiscrete
import Workspace.ProofLemmas.Thm23EmbeddingSelectionExists
import Workspace.ProofLemmas.Thm23RadiusChoice
import Workspace.ProofLemmas.Thm23FinalBound

set_option maxHeartbeats 800000

open scoped NumberField
open Workspace.Types.PlanarCounting
open Workspace.Types.DiscriminantsClassNumber
open Workspace.Types.AdmissibleDatum
open Workspace.Types.MinkowskiWindow
open Workspace.Types.CMAdjoinI
open Filter

theorem Theorem23GeometricCriterion
    (t : ℕ) (ht : 0 < t) (q : Fin t → ℕ)
    (data : ℕ → AdmissibleDatum)
    (hshare_t : ∀ j, (data j).t = t)
    (hshare_q : ∀ j, HEq (data j).q q)
    (hdeg : Filter.Tendsto (fun j => deg (data j)) Filter.atTop Filter.atTop)
    (H : ℝ) (hH : 0 < H)
    (hclass : ∀ j, (classNumber (data j).K : ℝ) ≤ H ^ (deg (data j)))
    (hgamma : 0 < (t : ℝ) * Real.log 2 - Real.log H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 1 ≤ n ∧
      (nuMax n : ℝ) ≥ (n : ℝ) ^ ((1 : ℝ) + δ) := by
  classical
  set γ : ℝ := (t : ℝ) * Real.log 2 - Real.log H with hγdef
  have hγ : 0 < γ := hgamma
  -- `∏ q_b ≥ 1` and `D₀ ≥ 1` (`j`-independent).
  have hprod_pos : 1 ≤ ∏ b : Fin t, q b := by
    have key : (∏ b : Fin (data 0).t, (data 0).q b) = ∏ b : Fin t, q b := by
      have ht0 := hshare_t 0
      subst ht0
      rw [eq_of_heq (hshare_q 0)]
    rw [← key]
    exact Finset.one_le_prod' (fun b _ => ((data 0).hq_prime b).one_lt.le)
  set D0 : ℕ := (∏ b : Fin t, q b) ^ 2 with hD0def
  have hD0_pos : 1 ≤ D0 := by rw [hD0def]; exact Nat.one_le_pow _ _ hprod_pos
  -- Every `data j` has `Dq (data j) = D₀`.
  have hDq : ∀ j, Dq (data j) = D0 := by
    intro j
    have key : (∏ b : Fin (data j).t, (data j).q b) = ∏ b : Fin t, q b := by
      have htj := hshare_t j
      subst htj
      rw [eq_of_heq (hshare_q j)]
    simp only [Dq, Qprod, hD0def, key]
  -- radius `R`.
  obtain ⟨R, hRhalf, hR1, hρ⟩ := Thm23RadiusChoice γ hγ
  have hRpos : (0 : ℝ) < R := by linarith
  -- constant `B`.
  set B : ℝ := 2 * Real.log (4 * R * (D0 : ℝ)) with hBdef
  have h4RD0 : (1 : ℝ) < 4 * R * (D0 : ℝ) := by
    have hD0R : (1 : ℝ) ≤ (D0 : ℝ) := by exact_mod_cast hD0_pos
    nlinarith
  have hB : 0 < B := by rw [hBdef]; have := Real.log_pos h4RD0; linarith
  -- Per-`j` construction.
  have hperj : ∀ j : ℕ, ∃ P : Finset (EuclideanSpace ℝ (Fin 2)),
      ((1 / 2) * Real.exp (γ * (deg (data j) : ℝ) / 2) * (P.card : ℝ) ≤ (nu P : ℝ)) ∧
      ((P.card : ℝ) ≤ Real.exp (B * (deg (data j) : ℝ))) ∧
      (Real.exp (γ * (deg (data j) : ℝ) / 2) ≤ (P.card : ℝ)) := by
    intro j
    set d := data j with hddef
    set f := deg d with hfdef
    have hcm : IsAdjoinI d.L d.K := d.h_adjoin
    -- `NeZero f`.
    haveI hNZ : NeZero f := ⟨(Module.finrank_pos (R := ℚ) (M := d.L)).ne'⟩
    have hDD1 : 1 ≤ Dq d := by rw [hDq j]; exact hD0_pos
    have hDDne : (Dq d : d.K) ≠ 0 := by
      have : Dq d ≠ 0 := by omega
      exact_mod_cast this
    -- embedding selection.
    obtain ⟨sel⟩ := Thm23EmbeddingSelectionExists d
    -- norm-one set from Prop 2.2.
    obtain ⟨U0, hU0_int, -, hU0_unit, hU0_card⟩ := Prop22NormOneElements d H hH (hclass j)
    set U' : Finset (Fin f → ℂ) := U0.image (minkowskiMap sel) with hU'def
    -- `Φ` is injective.
    have hΦinj : Function.Injective (minkowskiMap sel) := by
      intro x y hxy
      have hne : Nonempty (Fin f) := ⟨⟨0, (Module.finrank_pos (R := ℚ) (M := d.L))⟩⟩
      obtain ⟨r0⟩ := hne
      have := congr_fun hxy r0
      simp only [minkowskiMap, Pi.ringHom_apply] at this
      exact (sel.sigma r0).injective this
    -- `U' ⊆ Λ`.
    have hU_lat : ∀ z ∈ U', z ∈ lattice sel (Dq d) := by
      intro z hz
      rw [hU'def, Finset.mem_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      obtain ⟨ω, hω⟩ : ∃ ω : 𝓞 d.K, algebraMap (𝓞 d.K) d.K ω = (Dq d : d.K) * u :=
        ⟨NumberField.RingOfIntegers.restrict (fun _ : Unit => (Dq d : d.K) * u)
          (fun _ => hU0_int u hu) (), rfl⟩
      rw [lattice, AddMonoidHom.mem_range]
      refine ⟨ω, ?_⟩
      show latticeHom sel (Dq d) ω = minkowskiMap sel u
      simp only [latticeHom, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
        AddMonoidHom.coe_coe, AddMonoidHom.mulRight_apply]
      congr 1
      rw [hω, mul_right_comm, mul_inv_cancel₀ hDDne, one_mul]
    -- unit-modulus coordinates.
    have hU_coord : ∀ z ∈ U', ∀ r, ‖z r‖ = 1 := by
      intro z hz r
      rw [hU'def, Finset.mem_image] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      show ‖minkowskiMap sel u r‖ = 1
      simp only [minkowskiMap, Pi.ringHom_apply]
      exact hU0_unit u hu (sel.sigma r)
    -- nonzero.
    have hU_ne : ∀ z ∈ U', z ≠ 0 := by
      intro z hz hz0
      obtain ⟨r0⟩ : Nonempty (Fin f) := ⟨⟨0, (Module.finrank_pos (R := ℚ) (M := d.L))⟩⟩
      have := hU_coord z hz r0
      rw [hz0] at this
      simp at this
    -- cardinality.
    have hU'card : (U'.card : ℝ) ≥ Real.exp (γ * (f : ℝ)) := by
      rw [hU'def, Finset.card_image_of_injective _ hΦinj]
      refine le_trans ?_ hU0_card
      rw [hγdef, hfdef]
      apply le_of_eq
      rw [hshare_t j]
    -- Averaging (Lemma 2.4).
    obtain ⟨a, ha_ne, hE⟩ := Lemma24Averaging hcm sel (Dq d) hDD1 R hRhalf γ hγ U'
      hU_lat hU_ne hU_coord hU'card hρ
    -- `X_a` is finite.
    have hXfin : (Xset sel (Dq d) R a).Finite :=
      (SublemmaLatticeDiscrete hcm sel (Dq d) hDD1 R).1 a
    set X : Finset (Fin f → ℂ) := hXfin.toFinset with hXdef
    have hXeq : (X : Set (Fin f → ℂ)) = Xset sel (Dq d) R a := hXfin.coe_toFinset
    have hNc : Ncount sel (Dq d) R a = X.card := by
      rw [Ncount, Set.ncard_eq_toFinset_card _ hXfin]
    -- projection injective ⇒ `|π(X)| = |X|`.
    have hprojcard : (X.image (fun z => z 0)).card = X.card := by
      apply Finset.card_image_of_injOn
      intro x hx y hy hxy
      have hxX : x ∈ Xset sel (Dq d) R a := by rw [← hXeq]; exact hx
      have hyX : y ∈ Xset sel (Dq d) R a := by rw [← hXeq]; exact hy
      exact Lemma25ProjectionInjective sel (Dq d) a hxX.1 hyX.1 hxy
    -- planar count (Lemma 2.5).
    have hplanar := Lemma25PlanarCount sel (Dq d) R a γ U' X hXeq hU_coord hE
    set P : Finset (EuclideanSpace ℝ (Fin 2)) := embedFinset (X.image (fun z => z 0)) with hPdef
    have hPcard : P.card = X.card := by
      rw [hPdef, embedFinset, Finset.card_image_of_injective _ toPlane.injective, hprojcard]
    -- size bound (Lemma 2.6).
    have hsize26 : (Ncount sel (Dq d) R a : ℝ) ≤ (4 * R * (Dq d : ℝ)) ^ (2 * f) :=
      Lemma26SizeBound hcm sel (Dq d) hDD1 R hRhalf a
    refine ⟨P, ?_, ?_, ?_⟩
    · -- `nu P ≥ ½ e^{γf/2} |P|`.
      rw [hPdef] at *
      rw [hPcard]
      calc (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * (X.card : ℝ)
          = (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * ((X.image (fun z => z 0)).card : ℝ) := by
            rw [hprojcard]
        _ ≤ (nu (embedFinset (X.image (fun z => z 0))) : ℝ) := hplanar
    · -- `|P| ≤ e^{B f}`.
      rw [hPcard, ← hNc]
      calc (Ncount sel (Dq d) R a : ℝ) ≤ (4 * R * (Dq d : ℝ)) ^ (2 * f) := hsize26
        _ = Real.exp (B * (f : ℝ)) := by
            rw [hDq j, hBdef, ← Real.rpow_natCast (4 * R * (D0:ℝ)) (2 * f),
              Real.rpow_def_of_pos (by linarith)]
            congr 1
            push_cast
            ring
    · -- `e^{γf/2} ≤ |P|`.
      rw [hPcard, ← hNc]
      -- `E_a ≤ Ncount²`, combined with `hE`, and `Ncount ≥ 1`.
      have hNpos : 1 ≤ Ncount sel (Dq d) R a := by
        rw [hNc]
        rw [Finset.one_le_card, ← Finset.coe_nonempty, hXeq]
        exact ha_ne
      have hE2 : (Ecount sel (Dq d) R U' a : ℝ) ≤ (Ncount sel (Dq d) R a : ℝ) ^ 2 := by
        have hEfin : {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel (Dq d) R a ∧ p.2 ∈ Xset sel (Dq d) R a ∧ p.2 - p.1 ∈ U'}.Finite :=
          (SublemmaLatticeDiscrete hcm sel (Dq d) hDD1 R).2 U' a
        have hsub : {p : (Fin f → ℂ) × (Fin f → ℂ) |
            p.1 ∈ Xset sel (Dq d) R a ∧ p.2 ∈ Xset sel (Dq d) R a ∧ p.2 - p.1 ∈ U'}
            ⊆ Xset sel (Dq d) R a ×ˢ Xset sel (Dq d) R a :=
          fun p hp => ⟨hp.1, hp.2.1⟩
        have : Ecount sel (Dq d) R U' a ≤ (Ncount sel (Dq d) R a) ^ 2 := by
          rw [Ecount, Ncount, sq, ← Set.ncard_prod]
          exact Set.ncard_le_ncard hsub (hXfin.prod hXfin)
        calc (Ecount sel (Dq d) R U' a : ℝ) ≤ ((Ncount sel (Dq d) R a) ^ 2 : ℕ) := by exact_mod_cast this
          _ = (Ncount sel (Dq d) R a : ℝ) ^ 2 := by push_cast; ring
      -- from hE : Ecount ≥ exp(γf/2) Ncount, and hE2 : Ecount ≤ Ncount²
      have hNcR : (1 : ℝ) ≤ (Ncount sel (Dq d) R a : ℝ) := by exact_mod_cast hNpos
      have hkey : Real.exp (γ * (f : ℝ) / 2) * (Ncount sel (Dq d) R a : ℝ)
          ≤ (Ncount sel (Dq d) R a : ℝ) ^ 2 := le_trans hE hE2
      nlinarith [hkey, hNcR, sq_nonneg ((Ncount sel (Dq d) R a : ℝ))]
  -- Extract the sequences and apply the final bound.
  choose Pseq hPnu hPsize hPlb using hperj
  exact Thm23FinalBound γ B hγ hB (fun j => deg (data j)) (fun j => (Pseq j).card) Pseq
    hdeg (fun j => rfl) hPnu hPsize hPlb
