import Mathlib
import Workspace.Types.AdmissibleDatum
import Workspace.Types.CMAdjoinI

open scoped NumberField
open Workspace.Types.AdmissibleDatum
open Workspace.Types.CMAdjoinI

set_option maxHeartbeats 800000

/-- **Tower step for conjugate-pair indexing.** A prime `𝔓` of `𝓞 K` lying over the rational
prime `q_b` lies over a prime `𝔮 := 𝔓 ∩ 𝓞 L` of `𝓞 L`, which itself lies over `q_b`. -/
theorem PrimeOverQbLiesOverPrimeOverQ (d : AdmissibleDatum) (b : Fin d.t)
    (𝔓 : Ideal (𝓞 d.K)) (h𝔓 : 𝔓 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.K)) :
    ∃ 𝔮 : Ideal (𝓞 d.L), 𝔮 ∈ Ideal.primesOver (Ideal.span {(d.q b : ℤ)}) (𝓞 d.L) ∧
      𝔓 ∈ Ideal.primesOver 𝔮 (𝓞 d.K) := by
  obtain ⟨h𝔓p, h𝔓o⟩ := h𝔓
  haveI := h𝔓p
  haveI := h𝔓o
  set 𝔮 : Ideal (𝓞 d.L) := 𝔓.under (𝓞 d.L) with h𝔮def
  haveI h𝔮p : 𝔮.IsPrime := inferInstance
  haveI h𝔓o' : 𝔓.LiesOver 𝔮 := ⟨rfl⟩
  refine ⟨𝔮, ⟨h𝔮p, ⟨?_⟩⟩, ⟨h𝔓p, h𝔓o'⟩⟩
  show Ideal.span {(d.q b : ℤ)} = 𝔮.under ℤ
  rw [h𝔮def, Ideal.under_under]
  exact h𝔓o.over
