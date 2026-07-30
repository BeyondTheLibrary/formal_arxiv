import Mathlib
import Workspace.Types.MinkowskiWindow
import Workspace.Types.PlanarCounting
import Workspace.ProofLemmas.Lemma25ProjectionInjective

open scoped NumberField
open Workspace.Types.MinkowskiWindow
open Workspace.Types.PlanarCounting

/-- Counting identity: the number of *ordered* pairs of distinct points at distance `1`
drawn from a finite set `Q` in the plane is exactly twice the number of *unordered* such
pairs (which is `nu Q`). Each unordered unit segment `{a,b}` has precisely two orientations
`(a,b)` and `(b,a)`. -/
lemma card_ordered_unit (Q : Finset (EuclideanSpace ℝ (Fin 2))) :
    ((Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1)).card
      = 2 * nu Q := by
  classical
  set W := Q.sym2.filter (fun s => ¬ s.IsDiag ∧ distSym2 s = 1) with hW
  set T := (Q ×ˢ Q).filter (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1) with hT
  -- The `Sym2.mk` map sends `T` into `W`.
  have H : Set.MapsTo (fun pq : (EuclideanSpace ℝ (Fin 2)) × (EuclideanSpace ℝ (Fin 2)) =>
      s(pq.1, pq.2)) ↑T ↑W := by
    intro pq hpq
    rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨h1, h2⟩, hne, hd⟩ := hpq
    rw [Finset.mem_coe, hW, Finset.mem_filter]
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.mk_mem_sym2_iff]; exact ⟨h1, h2⟩
    · rw [Sym2.mk_isDiag_iff]; exact hne
    · rw [distSym2_mk]; exact hd
  -- Each fibre has exactly two elements.
  have hfib : ∀ w ∈ W, ({a ∈ T | s(a.1, a.2) = w}).card = 2 := by
    intro w
    induction w using Sym2.ind with
    | _ a b =>
      intro hw
      rw [hW, Finset.mem_filter] at hw
      obtain ⟨hmem, hdiag, hdist⟩ := hw
      rw [Finset.mk_mem_sym2_iff] at hmem
      rw [Sym2.mk_isDiag_iff] at hdiag
      rw [distSym2_mk] at hdist
      have hne : a ≠ b := hdiag
      have hset : {p ∈ T | s(p.1, p.2) = s(a, b)} = ({(a, b), (b, a)} : Finset _) := by
        ext p
        rw [Finset.mem_filter, hT, Finset.mem_filter, Finset.mem_product,
            Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff]
        constructor
        · rintro ⟨⟨⟨_, _⟩, _, _⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
          · left; rfl
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨⟨⟨hmem.1, hmem.2⟩, hne, hdist⟩, Or.inl ⟨rfl, rfl⟩⟩
          · exact ⟨⟨⟨hmem.2, hmem.1⟩, fun h => hne h.symm, by rw [dist_comm]; exact hdist⟩,
              Or.inr ⟨rfl, rfl⟩⟩
      rw [hset, Finset.card_pair]
      intro h
      exact hne (congrArg Prod.fst h)
  rw [Finset.card_eq_sum_card_fiberwise H, Finset.sum_congr rfl hfib, Finset.sum_const,
      smul_eq_mul]
  have hnu : W.card = nu Q := by rw [hW, nu]; congr!
  rw [hnu, Nat.mul_comm]

section MinkowskiLemmas

variable {L K : Type*} [Field L] [NumberField L] [NumberField.IsTotallyReal L]
  [Field K] [NumberField K] [Algebra L K] {f : ℕ}

theorem Lemma25PlanarCount [NeZero f] (sel : EmbeddingSelection L K f) (DD : ℕ) (R : ℝ)
    (a : Fin f → ℂ) (γ : ℝ)
    (U : Finset (Fin f → ℂ))
    (X : Finset (Fin f → ℂ)) (hX : (X : Set (Fin f → ℂ)) = Xset sel DD R a)
    (hU_coord : ∀ u ∈ U, ∀ r, ‖u r‖ = 1)
    (hE : (Ecount sel DD R U a : ℝ) ≥ Real.exp (γ * (f : ℝ) / 2) * (Ncount sel DD R a : ℝ)) :
    (nu (embedFinset (X.image (fun z => z 0))) : ℝ)
      ≥ (1 / 2) * Real.exp (γ * (f : ℝ) / 2) * ((X.image (fun z => z 0)).card : ℝ) := by
  classical
  set P := X.image (fun z => z 0) with hP
  -- Step 1: the projection is injective on `X`, hence `|P| = |X|`.
  have hXsub : (↑X : Set (Fin f → ℂ)) ⊆ {z | z - a ∈ lattice sel DD} := by
    rw [hX]; intro z hz; exact hz.1
  have hinjX : Set.InjOn (fun z : Fin f → ℂ => z 0) ↑X :=
    (Lemma25ProjectionInjective sel DD a).mono hXsub
  have hPcard : P.card = X.card := by
    rw [hP]; exact Finset.card_image_of_injOn hinjX
  -- `Ncount = |X|`.
  have hNcard : Ncount sel DD R a = X.card := by
    rw [Ncount, ← hX, Set.ncard_coe_finset]
  -- `Ecount = |SF|` where `SF` is the finset of counted pairs.
  set SF := (X ×ˢ X).filter (fun p => p.2 - p.1 ∈ U) with hSF
  have hEcard : Ecount sel DD R U a = SF.card := by
    rw [Ecount]
    have hScoe : {p : (Fin f → ℂ) × (Fin f → ℂ) |
        p.1 ∈ Xset sel DD R a ∧ p.2 ∈ Xset sel DD R a ∧ p.2 - p.1 ∈ U} = (↑SF : Set _) := by
      ext p
      simp only [hSF, Finset.coe_filter, Finset.mem_product, Set.mem_setOf_eq, ← hX,
        Finset.mem_coe]
      tauto
    rw [hScoe, Set.ncard_coe_finset]
  -- The projection map into the plane injects `SF` into the ordered unit pairs `T`.
  set T := ((embedFinset P) ×ˢ (embedFinset P)).filter
      (fun pq => pq.1 ≠ pq.2 ∧ dist pq.1 pq.2 = 1) with hT
  have hmaps : Set.MapsTo (fun p : (Fin f → ℂ) × (Fin f → ℂ) =>
      (toPlane (p.1 0), toPlane (p.2 0))) ↑SF ↑T := by
    intro p hp
    rw [Finset.mem_coe, hSF, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨⟨hp1X, hp2X⟩, hpU⟩ := hp
    have hnorm : ‖p.2 0 - p.1 0‖ = 1 := by
      have := hU_coord (p.2 - p.1) hpU 0
      rwa [Pi.sub_apply] at this
    have hP1 : p.1 0 ∈ P := by rw [hP]; exact Finset.mem_image_of_mem _ hp1X
    have hP2 : p.2 0 ∈ P := by rw [hP]; exact Finset.mem_image_of_mem _ hp2X
    have hd : dist (toPlane (p.1 0)) (toPlane (p.2 0)) = 1 := by
      rw [toPlane.isometry.dist_eq, dist_eq_norm, norm_sub_rev, hnorm]
    rw [Finset.mem_coe]
    dsimp only
    rw [hT, Finset.mem_filter, Finset.mem_product]
    refine ⟨⟨Finset.mem_image_of_mem _ hP1, Finset.mem_image_of_mem _ hP2⟩, ?_, hd⟩
    dsimp only
    intro h
    rw [h, dist_self] at hd
    norm_num at hd
  have hinj : Set.InjOn (fun p : (Fin f → ℂ) × (Fin f → ℂ) =>
      (toPlane (p.1 0), toPlane (p.2 0))) ↑SF := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, hSF, Finset.mem_filter, Finset.mem_product] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨he1, he2⟩ := hpq
    have e1 : p.1 0 = q.1 0 := toPlane.injective he1
    have e2 : p.2 0 = q.2 0 := toPlane.injective he2
    have f1 : p.1 = q.1 := hinjX hp.1.1 hq.1.1 e1
    have f2 : p.2 = q.2 := hinjX hp.1.2 hq.1.2 e2
    exact Prod.ext f1 f2
  have hle : SF.card ≤ T.card := Finset.card_le_card_of_injOn _ hmaps hinj
  have hTnu : T.card = 2 * nu (embedFinset P) := by rw [hT]; exact card_ordered_unit (embedFinset P)
  have hEle : Ecount sel DD R U a ≤ 2 * nu (embedFinset P) := by
    rw [hEcard, ← hTnu]; exact hle
  -- Real arithmetic.
  have hEle' : (Ecount sel DD R U a : ℝ) ≤ 2 * (nu (embedFinset P) : ℝ) := by
    exact_mod_cast hEle
  have hcastN : (Ncount sel DD R a : ℝ) = (P.card : ℝ) := by rw [hNcard, ← hPcard]
  have hE2 : Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ) ≤ (Ecount sel DD R U a : ℝ) := by
    rw [← hcastN]; exact hE
  have hcombine : Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)
      ≤ 2 * (nu (embedFinset P) : ℝ) := le_trans hE2 hEle'
  rw [ge_iff_le, show (1 / 2 : ℝ) * Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)
      = (1 / 2) * (Real.exp (γ * (f : ℝ) / 2) * (P.card : ℝ)) by ring]
  linarith [hcombine]

end MinkowskiLemmas
