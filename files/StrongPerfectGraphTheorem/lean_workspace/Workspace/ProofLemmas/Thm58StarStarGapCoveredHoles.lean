import Workspace.ProofLemmas.Thm58StarStarGapCoveredTrack

/-!
# The two completions of `T`, and the contradiction

PAPER: *"But `T` can be completed to a hole via `r₁-R_{v₁v₂}-r₂-a₂-a₃` and via
`r₁-p₁-⋯-pₙ-a₂-a₃`, and these two completions have different parity, a contradiction."*

The first completion is the cycle `T ++ R.tail ++ [a₂]`, the second one `T ++ P ++ [a₂]`.  They
have `|T| + |R|` and `|T| + |P| + 1` vertices, and both `|R|` and `|P|` are even, so the two
holes have different parity.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm58StarStarGapCoveredHoles

open Workspace.Types.Core.SPGT Workspace.Types.Tracks.SPGT
open Workspace.Types.Appearances.SPGT
open Thm58StarBranchBasics Thm58StarStarBasics Thm58StarStarHoles
open ThreeTracksLineGraphPrism TrackToRungPath Thm58StarStarGapCoveredSetup
open Thm58StarStarTracks Thm58StarStarGapCoveredTrack

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {m n : ℕ} {J : SimpleGraph (Fin m)}
  {H : SimpleGraph (Fin n)} {K : Set V} {φ : H.lineGraph ≃g G.induce K}
  {N : Fin n → Set V} {F : Set V} {P : List V} {p₁ p₂ : V} {c₁ c₂ w : Fin n}
  {q : List (Fin n)} {R : List V} {r₁ r₂ : V}

variable (hc : Cov G m J n H K φ N F P p₁ p₂ c₁ c₂ w q R r₁ r₂)

include hc

/-- Membership in the rung, read through the edge dictionary. -/
theorem mem_R_iff' (y : V) : y ∈ R ↔ y ∈ edgeImage φ (trackEdges q) := by
  constructor
  · intro hy
    have h : y ∈ {x : V | x ∈ R} := hy
    rw [hc.rungSet] at h
    exact h
  · intro hy
    have h : y ∈ {x : V | x ∈ R} := by rw [hc.rungSet]; exact hy
    exact h

/-- PAPER: *"`a₂`"* is adjacent, among the vertices of the rung, only to `r₂`. -/
theorem a₂_adj_rung {y : V} (hy : y ∈ R) (hne : y ≠ r₂) : ¬ G.Adj hc.a₂ y := by
  intro hadj
  have hxR : hc.a₂ ∉ edgeImage φ (trackEdges q) := fun hcon =>
    a₂_not_mem_R hc ((mem_R_iff' hc _).mpr hcon)
  rcases adj_rung_imp (star_eq hc.ctx) hc.branch hc.from' (a₂_mem_K hc) hxR
      ((mem_R_iff' hc y).mp hy) hadj with ⟨hx, -⟩ | ⟨-, hy'⟩
  · exact a₂_not_mem_star₁ hc hx
  · have : y ∈ N c₂ ∩ {x : V | x ∈ R} := ⟨hy', hy⟩
    rw [hc.int₂] at this
    exact hne this

/-- PAPER: *"`a₂`"* is adjacent, among the vertices of the outside path, only to `pₙ`. -/
theorem a₂_adj_path {y : V} (hy : y ∈ P) (hne : y ≠ p₂) : ¬ G.Adj hc.a₂ y := by
  intro hadj
  by_cases hy₁ : y = p₁
  · subst hy₁
    exact a₂_not_mem_star₁ hc (first_adj_mem hc.ctx (a₂_mem_K hc) hadj.symm)
  · exact a₂_not_mem_star₁ hc
      (mid_adj_mem hc.ctx hy hy₁ hne (a₂_mem_K hc) hadj.symm).1

/-- PAPER, the closing sentence of the proof of 5.8 (4): the two completions of `T`. -/
theorem holes_of_T (hp₁r₁ : G.Adj p₁ r₁) :
    ∃ C D : List V, IsHoleList G C ∧ IsHoleList G D ∧ C.length % 2 ≠ D.length % 2 := by
  classical
  obtain ⟨T, a₃, hT, hT2, hTK, ha₃w, hTN₂, ha₁T, hTR, hTw⟩ := exists_T hc
  have ha₃r₁ : a₃ ≠ r₁ :=
    PathBasics.isPathFrom_ends_ne hT (by simp only [pathLength]; omega)
  have ha₃T : a₃ ∈ T := (PathBasics.isPathFrom_ends_mem hT).1
  have hr₁T : r₁ ∈ T := (PathBasics.isPathFrom_ends_mem hT).2
  -- `a₂` and the path `T`
  have ha₂T : hc.a₂ ∉ T := fun hmem => hTN₂ _ hmem (a₂_mem_star₂ hc)
  have ha₂a₃ : G.Adj hc.a₂ a₃ := by
    refine star_adj (star_eq hc.ctx) w (a₂_mem_starw hc) ha₃w ?_
    intro hcon
    exact hTN₂ _ ha₃T (hcon ▸ a₂_mem_star₂ hc)
  have ha₂T' : ∀ x ∈ T, G.Adj hc.a₂ x → x = a₃ := by
    intro x hx hadj
    obtain ⟨e, he, rfl⟩ := exists_edge (φ := φ) (hTK x hx)
    have hL : H.lineGraph.Adj ⟨s(c₂, w), hc.adjw₂⟩ ⟨e, he⟩ := φ.map_rel_iff.mp hadj
    obtain ⟨-, v, hv1, hv2⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp hL
    have hvw : v = w := by
      rcases Sym2.mem_iff.mp hv1 with h | h
      · exact absurd ((Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) he).mpr (h ▸ hv2))
          (hTN₂ _ hx)
      · exact h
    exact hTw _ hx ((Thm58StarStarGapTracks.mem_star_iff (star_eq hc.ctx) he).mpr (hvw ▸ hv2))
  have hr₂T : r₂ ∉ T := fun hmem => (r_ne hc) (hTR _ hmem (r₂_mem_R hc)).symm
  have ha₃R : a₃ ∉ R := fun hmem => ha₃r₁ (hTR _ ha₃T hmem)
  -- the rung, split at its first vertex
  have hRlen : 2 ≤ R.length := two_le_R_length hc
  obtain ⟨x0, t0, h0⟩ := List.exists_cons_of_ne_nil hc.rung.1.1
  have hx0 : x0 = r₁ := by
    have h := hc.rung.2.1
    rw [h0] at h
    simpa using h
  rw [hx0] at h0
  have ht0 : t0 ≠ [] := by
    intro hcon
    rw [h0, hcon] at hRlen
    simp at hRlen
  obtain ⟨x1, t1, h1⟩ := List.exists_cons_of_ne_nil ht0
  rw [h1] at h0
  subst h0
  have hnd := hc.rung.1.2.1
  have hr₁tail : r₁ ∉ (x1 :: t1) := by
    simp only [List.nodup_cons] at hnd
    exact hnd.1
  have hRt : IsPathFrom G (x1 :: t1) x1 r₂ := by
    refine ⟨?_, rfl, ?_⟩
    · have := PathBasics.isPathList_drop hc.rung.1 (k := 1) (by simp)
      simpa using this
    · have := hc.rung.2.2
      rwa [List.getLast?_cons_cons] at this
  have hadjx1 : G.Adj r₁ x1 := by
    have := PathBasics.path_adj_succ hc.rung.1 (i := 0) (by simp)
    simpa using this
  have hkey : ∀ y ∈ (x1 :: t1), G.Adj r₁ y → y = x1 := by
    intro y hy hadj
    have hmem : y ∈ (r₁ :: x1 :: t1) := List.mem_cons_of_mem _ hy
    obtain ⟨j, hj, hjy⟩ := List.mem_iff_getElem.mp hmem
    have h0' : (r₁ :: x1 :: t1)[0]'(by simp) = r₁ := rfl
    have hadj' : G.Adj ((r₁ :: x1 :: t1)[0]'(by simp)) ((r₁ :: x1 :: t1)[j]'hj) := by
      rw [h0', hjy]; exact hadj
    have := (PathBasics.path_adj_iff hc.rung.1 (by simp) hj).mp hadj'
    have hj1 : j = 1 := by omega
    subst hj1
    exact hjy.symm
  -- `T` and the tail of the rung
  have hdisjTR : ∀ x ∈ T, x ∉ (x1 :: t1) := by
    intro x hx hmem
    have hxR : x ∈ (r₁ :: x1 :: t1) := List.mem_cons_of_mem _ hmem
    rw [hTR x hx hxR] at hmem
    exact hr₁tail hmem
  have hcrossTR : ∀ x ∈ T, ∀ y ∈ (x1 :: t1), (G.Adj x y ↔ (x = r₁ ∧ y = x1)) := by
    intro x hx y hy
    constructor
    · intro hadj
      have hyR : y ∈ (r₁ :: x1 :: t1) := List.mem_cons_of_mem _ hy
      by_cases hxr : x = r₁
      · subst hxr
        exact ⟨rfl, hkey y hy hadj⟩
      · exfalso
        have hxR : x ∉ edgeImage φ (trackEdges q) := fun hcon =>
          hxr (hTR x hx ((mem_R_iff' hc _).mpr hcon))
        rcases adj_rung_imp (star_eq hc.ctx) hc.branch hc.from' (hTK x hx) hxR
            ((mem_R_iff' hc y).mp hyR) hadj with ⟨-, hy'⟩ | ⟨hx', -⟩
        · have : y ∈ N c₁ ∩ {z : V | z ∈ (r₁ :: x1 :: t1)} := ⟨hy', hyR⟩
          rw [hc.int₁] at this
          rw [this] at hy
          exact hr₁tail hy
        · exact hTN₂ x hx hx'
    · rintro ⟨rfl, rfl⟩
      exact hadjx1
  have hTRpath : IsPathFrom G (T ++ (x1 :: t1)) a₃ r₂ :=
    PathGlue.glue_path hT hRt hdisjTR hcrossTR
  -- `T` and the outside path
  have hFK : F ⊆ Kᶜ := hc.ctx.ready.2.2.2.2.1
  have hdisjTP : ∀ x ∈ T, x ∉ P := by
    intro x hx hmem
    have hxF : x ∈ F := by rw [← vertices hc.ctx]; exact hmem
    exact hFK hxF (hTK x hx)
  have hcrossTP : ∀ x ∈ T, ∀ y ∈ P, (G.Adj x y ↔ (x = r₁ ∧ y = p₁)) := by
    intro x hx y hy
    constructor
    · intro hadj
      by_cases hy₂ : y = p₂
      · exact absurd (last_adj_mem hc.ctx (hTK x hx) (hy₂ ▸ hadj.symm)) (hTN₂ x hx)
      by_cases hy₁ : y = p₁
      · refine ⟨?_, hy₁⟩
        subst hy₁
        by_contra hxr
        have hx₁ : x ∈ N c₁ \ {r₁} :=
          ⟨first_adj_mem hc.ctx (hTK x hx) hadj.symm, by simpa using hxr⟩
        have hxa : x = hc.a₁ := hc.sing₁ x hx₁ hadj.symm
        rw [hxa] at hx
        exact ha₁T hx
      · exact absurd (mid_adj_mem hc.ctx hy hy₁ hy₂ (hTK x hx) hadj.symm).2 (hTN₂ x hx)
    · rintro ⟨rfl, rfl⟩
      exact hp₁r₁.symm
  have hTPpath : IsPathFrom G (T ++ P) a₃ p₂ :=
    PathGlue.glue_path hT (path hc.ctx) hdisjTP hcrossTP
  -- the two holes
  have hsingle : IsPathFrom G [hc.a₂] hc.a₂ hc.a₂ :=
    ⟨PathBasics.isPathList_singleton G hc.a₂, rfl, rfl⟩
  have hlenP : 2 ≤ P.length := two_le_length hc.ctx
  have hhole₁ : IsHoleList G ((T ++ (x1 :: t1)) ++ [hc.a₂]) := by
    refine PathGlue.glue_hole hTRpath hsingle ?_ ?_ ?_
    · intro x hx
      rw [List.mem_singleton]
      intro hcon
      subst hcon
      rcases List.mem_append.mp hx with hx | hx
      · exact ha₂T hx
      · exact a₂_not_mem_R hc (List.mem_cons_of_mem _ hx)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rcases List.mem_append.mp hx with hx | hx
      · constructor
        · intro hadj
          exact Or.inr ⟨ha₂T' x hx hadj.symm, rfl⟩
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact absurd hx hr₂T
          · exact ha₂a₃.symm
      · have hyR : x ∈ (r₁ :: x1 :: t1) := List.mem_cons_of_mem _ hx
        constructor
        · intro hadj
          refine Or.inl ⟨?_, rfl⟩
          by_contra hne
          exact a₂_adj_rung hc hyR hne hadj.symm
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · refine star_adj (star_eq hc.ctx) c₂ (r₂_mem_star₂ hc) (a₂_mem_star₂ hc) ?_
            intro hcon
            exact a₂_not_mem_R hc (hcon ▸ r₂_mem_R hc)
          · exact absurd hyR ha₃R
    · simp only [List.length_append, List.length_cons, List.length_singleton]
      omega
  have hhole₂ : IsHoleList G ((T ++ P) ++ [hc.a₂]) := by
    refine PathGlue.glue_hole hTPpath hsingle ?_ ?_ ?_
    · intro x hx
      rw [List.mem_singleton]
      intro hcon
      subst hcon
      rcases List.mem_append.mp hx with hx | hx
      · exact ha₂T hx
      · have hxF : hc.a₂ ∈ F := by
          have hv := vertices hc.ctx
          rw [Set.ext_iff] at hv
          exact (hv hc.a₂).mp hx
        exact hFK hxF (a₂_mem_K hc)
    · intro x hx y hy
      rw [List.mem_singleton] at hy
      subst hy
      rcases List.mem_append.mp hx with hx | hx
      · constructor
        · intro hadj
          exact Or.inr ⟨ha₂T' x hx hadj.symm, rfl⟩
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact absurd (hdisjTP _ hx) (by
              simpa using PathBasics.getLast_mem (path hc.ctx).2.2)
          · exact ha₂a₃.symm
      · constructor
        · intro hadj
          refine Or.inl ⟨?_, rfl⟩
          by_contra hne
          exact a₂_adj_path hc hx hne hadj.symm
        · rintro (⟨rfl, -⟩ | ⟨rfl, -⟩)
          · exact adj_p₂_a₂ hc
          · exact absurd hx (hdisjTP _ ha₃T)
    · simp only [List.length_append, List.length_singleton]
      omega
  refine ⟨_, _, hhole₁, hhole₂, ?_⟩
  have hRl : (r₁ :: x1 :: t1).length = t1.length + 2 := by simp
  have heR : Even (r₁ :: x1 :: t1).length := even_R_length hc
  have heP : Even P.length := even_P_length hc
  rcases heR with ⟨k, hk⟩
  rcases heP with ⟨l, hl⟩
  simp only [List.length_append, List.length_cons, List.length_singleton]
  rw [hRl] at hk
  omega

end Workspace.ProofLemmas.Thm58StarStarGapCoveredHoles
