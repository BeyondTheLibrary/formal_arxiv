-- Cited from: E. S. Golod and I. R. Shafarevich, On the class field tower, Izv. Akad. Nauk SSSR Ser. Mat. 28(2):261-272, 1964 (English transl. AMS Transl. (2) 48 (1965), 91-102); H. Koch, Galois Theory of p-Extensions, Springer, 2002, Chapter 11.
-- Paper label: Proposition 3.4 (Golod-Shafarevich inequality) / Proposition A.9
-- NL statement: If a finite nontrivial finitely generated pro-p group G has generator rank d(G) and relation rank r(G), then r(G) > d(G)^2 / 4 (division-free: d(G)^2 < 4 r(G)).
--
-- The generating-function argument — the "clever" half of Golod–Shafarevich — is proved from
-- Mathlib in `Workspace.ProofLemmas.GolodShafarevichCore.gs_core`, as is the fact that a nontrivial
-- pro-p group has generator rank ≥ 1 and that d(G) is finite for a topologically finitely generated
-- G.  The only admitted input is `Workspace.PriorWork.GolodShafarevichFiltration` (the Hilbert
-- function of the augmentation filtration of 𝔽_p[G]).
import Mathlib
import Workspace.Types.ProPGroup
import Workspace.Types.ProPPresentationRank
import Workspace.ProofLemmas.GolodShafarevichCore
import Workspace.PriorWork.GolodShafarevichFiltration

open Workspace.Types.ProPGroup
open Workspace.Types.ProPPresentationRank

/-- **Proposition 3.4 (Golod–Shafarevich).** A finite nontrivial (finitely generated) pro-`p`
group has `r(G) > d(G)^2 / 4` (division-free: `d(G)^2 < 4·r(G)`). -/
theorem GolodShafarevichInequality (p : ℕ) [Fact p.Prime] (G : Type*) [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (hpro : IsProP p G) (hfg : TopFinitelyGenerated G) (hfin : Finite G) (hnt : Nontrivial G) :
    (dRank G) ^ 2 < 4 * relRank p G := by
  obtain ⟨_, _, hT2, _, _⟩ := hpro
  haveI := hT2
  -- `dRank G` is finite
  obtain ⟨S₀, hS₀⟩ := hfg
  have hdle : dRank G ≤ (S₀.card : ℕ∞) := sInf_le ⟨S₀, hS₀, rfl⟩
  have hdne : dRank G ≠ ⊤ := by
    intro h
    rw [h] at hdle
    exact (ENat.coe_ne_top S₀.card) (top_le_iff.mp hdle)
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp hdne
  have hd1 : 1 ≤ d := by
    have := Workspace.ProofLemmas.GolodShafarevichCore.one_le_dRank G hnt
    rw [← hd] at this
    exact_mod_cast this
  by_cases hr : relRank p G = ⊤
  · rw [hr, ← hd]
    have h4 : (4 : ℕ∞) * ⊤ = ⊤ := by
      simp
    rw [h4]
    refine lt_of_le_of_ne le_top ?_
    have : ((d : ℕ∞)) ^ 2 = ((d ^ 2 : ℕ) : ℕ∞) := by push_cast; ring
    rw [this]
    exact ENat.coe_ne_top _
  · obtain ⟨r, hrr⟩ := ENat.ne_top_iff_exists.mp hr
    obtain ⟨c, hc0, hc1, hrec, N, hN⟩ :=
      GolodShafarevichFiltration p G ⟨‹_›, ‹_›, ‹_›, ‹_›, ‹_›⟩ ⟨S₀, hS₀⟩ hfin hnt d r hd hrr
    have hcore := Workspace.ProofLemmas.GolodShafarevichCore.gs_core d r hd1 c hc0 hc1 hrec N hN
    rw [← hd, ← hrr]
    exact_mod_cast hcore
