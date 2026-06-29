import Mathlib
import Workspace.Types.L1AndTVDistance

open MeasureTheory

theorem PinskerScheffeIdentity :
    ∀ (f g : ℝ → ℝ),
      Measurable f → Measurable g →
      (∀ x, 0 ≤ f x) → (∀ x, 0 ≤ g x) →
      Integrable f volume → Integrable g volume →
      (∫ x, f x ∂volume) = 1 → (∫ x, g x ∂volume) = 1 →
      Workspace.Types.L1AndTVDistance.L1Norm (fun x => f x - g x) =
        2 * ((∫ x in {x : ℝ | f x > g x}, f x ∂volume) -
             (∫ x in {x : ℝ | f x > g x}, g x ∂volume)) := by
  intro f g hf hg hfnn hgnn hfi hgi hfint hgint
  -- Let A := {x | f x > g x}
  set A : Set ℝ := {x : ℝ | f x > g x} with hAdef
  -- A is measurable
  have hAmeas : MeasurableSet A := by
    have : MeasurableSet {x : ℝ | g x < f x} :=
      measurableSet_lt hg hf
    simpa [A, hAdef] using this
  -- The function f - g is integrable
  have hfgi : Integrable (fun x => f x - g x) volume := hfi.sub hgi
  -- Unfold L1Norm
  unfold Workspace.Types.L1AndTVDistance.L1Norm
  -- Split the integral over A and Aᶜ
  have habs_int : Integrable (fun x => |f x - g x|) volume := hfgi.abs
  have hsplit :
      ∫ x, |f x - g x| ∂volume =
        (∫ x in A, |f x - g x| ∂volume) + (∫ x in Aᶜ, |f x - g x| ∂volume) := by
    rw [← integral_add_compl hAmeas habs_int]
  rw [hsplit]
  -- On A, |f x - g x| = f x - g x
  have hA_eq : ∫ x in A, |f x - g x| ∂volume = ∫ x in A, f x - g x ∂volume := by
    apply setIntegral_congr_fun hAmeas
    intro x hx
    have hgf : g x < f x := hx
    have hpos : 0 < f x - g x := by linarith
    show |f x - g x| = f x - g x
    exact abs_of_pos hpos
  -- On Aᶜ, |f x - g x| = g x - f x
  have hAc_eq : ∫ x in Aᶜ, |f x - g x| ∂volume = ∫ x in Aᶜ, g x - f x ∂volume := by
    apply setIntegral_congr_fun hAmeas.compl
    intro x hx
    -- hx : x ∈ Aᶜ means ¬ (g x < f x), i.e. f x ≤ g x
    have hxnotin : x ∉ A := hx
    have hle : f x ≤ g x := not_lt.mp hxnotin
    have hnonpos : f x - g x ≤ 0 := by linarith
    show |f x - g x| = g x - f x
    rw [abs_of_nonpos hnonpos]
    ring
  rw [hA_eq, hAc_eq]
  -- Now split each set integral into pieces
  have hfiA : IntegrableOn f A volume := hfi.integrableOn
  have hgiA : IntegrableOn g A volume := hgi.integrableOn
  have hfiAc : IntegrableOn f Aᶜ volume := hfi.integrableOn
  have hgiAc : IntegrableOn g Aᶜ volume := hgi.integrableOn
  have hint_A_sub : ∫ x in A, f x - g x ∂volume =
      (∫ x in A, f x ∂volume) - (∫ x in A, g x ∂volume) := by
    exact integral_sub hfiA hgiA
  have hint_Ac_sub : ∫ x in Aᶜ, g x - f x ∂volume =
      (∫ x in Aᶜ, g x ∂volume) - (∫ x in Aᶜ, f x ∂volume) := by
    exact integral_sub hgiAc hfiAc
  rw [hint_A_sub, hint_Ac_sub]
  -- Use ∫_{Aᶜ} h = ∫ h - ∫_A h
  have hf_compl : ∫ x in Aᶜ, f x ∂volume = 1 - ∫ x in A, f x ∂volume := by
    rw [setIntegral_compl hAmeas hfi, hfint]
  have hg_compl : ∫ x in Aᶜ, g x ∂volume = 1 - ∫ x in A, g x ∂volume := by
    rw [setIntegral_compl hAmeas hgi, hgint]
  rw [hf_compl, hg_compl]
  ring
