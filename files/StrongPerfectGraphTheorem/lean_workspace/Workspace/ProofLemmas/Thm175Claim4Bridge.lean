import Workspace.ProofLemmas.Thm175Claim4Exceptional

/-! The two clean paths through `z,x₁` in the first paragraph of 17.5 (4). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim4Bridge

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm175Optimal
open Workspace.ProofLemmas.Thm175Claim4Setup

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {z : V} {c : Counterexample G z}

theorem path_via_x (s : Setup c) {R : List V} {u v : V}
    (hR : IsPathFrom G R u v) (hsub : ∀ w ∈ R, w ∈ c.core.p)
    (hxu : G.Adj s.x₁ u) (hxonly : ∀ w ∈ R, w ≠ u → ¬ G.Adj s.x₁ w) :
    IsPathFrom G (z :: s.x₁ :: R) z v := by
  have hxR : s.x₁ ∉ R := fun hx => x₁_notMem_p s (hsub _ hx)
  have hzx : G.Adj z s.x₁ := c.hzXY s.x₁ (Or.inl (x₁_mem s))
  apply PathAttach.isPathFrom_cons (PathAttach.isPathFrom_cons hR hxu hxR hxonly) hzx
  · intro hz
    rcases List.mem_cons.mp hz with he | hz
    · exact hzx.ne he
    · exact c.core.hzP (hsub z hz)
  · intro w hw hne
    rcases List.mem_cons.mp hw with he | hw
    · exact (hne he).elim
    · exact c.core.hzanti w (hsub w hw)

theorem interior_cases (s : Setup c) {R : List V} {v w : V}
    (hQ : IsPathFrom G (z :: s.x₁ :: R) z v)
    (hw : w ∈ SPGT.interior (z :: s.x₁ :: R)) :
    w = s.x₁ ∨ (w ∈ R ∧ w ≠ v) := by
  have hh := (PathBasics.mem_interior_iff_of_pathFrom hQ).mp hw
  rcases List.mem_cons.mp hh.1 with he | hw
  · exact (hh.2.1 he).elim
  · rcases List.mem_cons.mp hw with he | hw
    · exact Or.inl he
    · exact Or.inr ⟨hw, hh.2.2⟩

theorem clean_via_x (s : Setup c) {R : List V} {v : V}
    (hQ : IsPathFrom G (z :: s.x₁ :: R) z v)
    (honly : ∀ w ∈ R, VertexComplete G w (wSet s) → w = v) :
    ∀ w ∈ SPGT.interior (z :: s.x₁ :: R), ¬ VertexComplete G w (wSet s) := by
  intro w hw hc
  rcases interior_cases s hQ hw with he | ⟨hwR, hne⟩
  · exact Thm175Claim4Exceptional.x₁_not_complete s (he ▸ hc)
  · exact hne (honly w hwR hc)

theorem out_via_x (s : Setup c) {R : List V} (hsub : ∀ w ∈ R, w ∈ c.core.p) :
    ∀ w ∈ z :: s.x₁ :: R, w ∉ wSet s := by
  intro w hw
  rcases List.mem_cons.mp hw with he | hw
  · intro hc
    have hz : z ∈ wSet s := (congrArg (fun v => v ∈ wSet s) he).mp hc
    exact G.irrefl (z_complete_wSet s z hz)
  · rcases List.mem_cons.mp hw with he | hw
    · exact fun hc => x₁_notMem_wSet s (he ▸ hc)
    · exact p_out_wSet s w (hsub w hw)

/-- PAPER: "... so `k=j+1` ... every `W`-complete vertex in `P\p₁` is
adjacent to `p_k` ... `i=1`, and so `j=2,k=3`, and the `W`-complete vertices
in `P` are `p₁,p₂` and possibly `p₄`." -/
theorem restricted_complete_vertices (hG : InF7 G) (s : Setup c)
    (hfirst : ∀ v ∈ c.core.p, (VertexComplete G v c.X ↔ v = c.core.p₁))
    (a d : ℕ) (had : a < d) (hd : d < c.core.p.length)
    (hxa : G.Adj s.x₁ (c.core.p[a]'(lt_trans had hd)))
    (hxd : G.Adj s.x₁ (c.core.p[d]'hd))
    (hno : ∀ k (hk : k < c.core.p.length), a < k → k < d → ¬ G.Adj s.x₁ (c.core.p[k]'hk))
    (heven : Even (d - a)) (i : ℕ) (hi : i + 1 < c.core.p.length)
    (hai : a ≤ i) (hijd : i + 1 < d)
    (hiW : VertexComplete G (c.core.p[i]'(by omega)) (wSet s))
    (hjW : VertexComplete G (c.core.p[i + 1]'hi) (wSet s))
    (hlocal : ∀ k (hk : k < c.core.p.length), a ≤ k → k ≤ d →
      VertexComplete G (c.core.p[k]'hk) (wSet s) → k = i ∨ k = i + 1) :
    ∃ h1 : 1 < c.core.p.length,
      VertexComplete G (c.core.p[1]'h1) (wSet s) ∧
      ∀ k (hk : k < c.core.p.length),
        VertexComplete G (c.core.p[k]'hk) (wSet s) → k = 0 ∨ k = 1 ∨ k = 3 := by
  let P := c.core.p
  have hplen : P.length = c.core.p.length := rfl
  let T := (P.drop a).take (i - a + 1)
  let R := ((P.drop (i + 1)).take (d - (i + 1) + 1)).reverse
  have hT : IsPathFrom G T (P[a]'(by omega)) (P[i]'(by omega)) := by
    refine ⟨PathBasics.isPathList_take
      (PathBasics.isPathList_drop c.core.hp.1 (by omega)) (by omega),
      PathBasics.head?_slice P hai (by omega), PathBasics.getLast?_slice P hai (by omega)⟩
  have hTsub : ∀ w ∈ T, w ∈ c.core.p := fun w hw =>
    List.drop_subset _ _ (List.take_subset _ _ hw)
  have hTlen : T.length = i - a + 1 := PathBasics.length_slice P hai (by omega)
  have hTonly : ∀ w ∈ T, VertexComplete G w (wSet s) → w = P[i]'(by omega) := by
    intro w hw hc
    obtain ⟨k, hk, hak, hki, hkw⟩ := (PathBasics.mem_slice_iff P hai (by omega)).mp hw
    have hh := hlocal k hk hak (by omega) (hkw ▸ hc)
    have he : k = i := by omega
    subst k
    exact hkw.symm
  have hxTonly : ∀ w ∈ T, w ≠ P[a]'(by omega) → ¬ G.Adj s.x₁ w := by
    intro w hw hne ha
    obtain ⟨k, hk, hak, hki, hkw⟩ := (PathBasics.mem_slice_iff P hai (by omega)).mp hw
    have hka : k ≠ a := by intro he; subst k; exact hne hkw.symm
    exact hno k hk (by omega) (by omega) (hkw ▸ ha)
  have hQT := path_via_x s hT hTsub hxa hxTonly
  have hQTlen : pathLength (z :: s.x₁ :: T) = i - a + 2 := by simp [pathLength, hTlen]
  have hantiT : ∀ w ∈ SPGT.interior (z :: s.x₁ :: T), ¬ G.Adj (P[i + 1]'hi) w := by
    intro w hw ha
    rcases interior_cases s hQT hw with he | ⟨hwT, hwne⟩
    · exact hno (i + 1) hi (by omega) hijd (by simpa only [he] using ha.symm)
    · obtain ⟨k, hk, hak, hki, hkw⟩ := (PathBasics.mem_slice_iff P hai (by omega)).mp hwT
      have hkin : k ≠ i := by intro he; subst k; exact hwne hkw.symm
      have hadj : G.Adj (P[i + 1]'hi) (P[k]'hk) := hkw ▸ ha
      have := (PathBasics.path_adj_iff c.core.hp.1 hi hk).mp hadj
      omega
  have hTeven := Thm175Claim4CleanPaths.even hG.1.1.1.1 (wSet_anticonnected s) hQT
    (by rw [hQTlen]; omega) (out_via_x s hTsub) (z_complete_wSet s) hiW
    (clean_via_x s hQT hTonly) (P[i + 1]'hi) hjW hantiT
  have hR : IsPathFrom G R (P[d]'hd) (P[i + 1]'hi) :=
    PathBasics.isPathFrom_reverse (PathBasics.isPathFrom_slice c.core.hp.1 hijd hd)
  have hRsub : ∀ w ∈ R, w ∈ c.core.p := fun w hw =>
    List.drop_subset _ _ (List.take_subset _ _ (List.mem_reverse.mp hw))
  have hRlen : R.length = d - (i + 1) + 1 := by
    rw [List.length_reverse]
    exact PathBasics.length_slice P (by omega) hd
  have hRonly : ∀ w ∈ R, VertexComplete G w (wSet s) → w = P[i + 1]'hi := by
    intro w hw hc
    obtain ⟨k, hk, hik, hkd, hkw⟩ :=
      (PathBasics.mem_slice_iff P (by omega) hd).mp (List.mem_reverse.mp hw)
    have hh := hlocal k hk (by omega) hkd (hkw ▸ hc)
    have he : k = i + 1 := by omega
    subst k
    exact hkw.symm
  have hxRonly : ∀ w ∈ R, w ≠ P[d]'hd → ¬ G.Adj s.x₁ w := by
    intro w hw hne ha
    obtain ⟨k, hk, hik, hkd, hkw⟩ :=
      (PathBasics.mem_slice_iff P (by omega) hd).mp (List.mem_reverse.mp hw)
    have hkn : k ≠ d := by intro he; subst k; exact hne hkw.symm
    exact hno k hk (by omega) (by omega) (hkw ▸ ha)
  have hQR := path_via_x s hR hRsub hxd hxRonly
  have hQRlen : pathLength (z :: s.x₁ :: R) = d - (i + 1) + 2 := by
    simp [pathLength, hRlen]
  have hRodd : Odd (pathLength (z :: s.x₁ :: R)) := by
    rw [Nat.odd_iff, hQRlen]
    rw [Nat.even_iff, hQTlen] at hTeven
    rw [Nat.even_iff] at heven
    omega
  have hthree := Thm175Claim4CleanPaths.length_three hG.1.1 (wSet_anticonnected s) hQR
    (by rw [hQRlen]; omega) (out_via_x s hRsub) (z_complete_wSet s) hjW
    (clean_via_x s hQR hRonly) hRodd
  have hdi : d = i + 2 := by rw [hQRlen] at hthree; omega
  have hcover : ∀ w, VertexComplete G w (wSet s) →
      G.Adj w s.x₁ ∨ G.Adj w (P[d]'hd) := by
    intro w hw
    obtain ⟨v, hv, hwv⟩ := _root_.Workspace.Statements.S02.SPGT.thm_2_2 G hG.1.1.1.1
      (wSet s) (wSet_anticonnected s) (z :: s.x₁ :: R) z (P[i + 1]'hi) hQR
      (out_via_x s hRsub) hRodd (z_complete_wSet s) hjW
      (Thm175Claim4CleanPaths.noedge hQR (by rw [hQRlen]; omega)
        (clean_via_x s hQR hRonly)) w hw
    rcases interior_cases s hQR hv with he | ⟨hvR, hvne⟩
    · exact Or.inl (he ▸ hwv)
    · obtain ⟨k, hk, hik, hkd, hkv⟩ :=
        (PathBasics.mem_slice_iff P (by omega) hd).mp (List.mem_reverse.mp hvR)
      have hkin : k ≠ i + 1 := by intro he; subst k; exact hvne hkv.symm
      have hkd' : k = d := by omega
      subst k
      exact Or.inr (hkv ▸ hwv)
  have hp0 := PathBasics.getElem_zero_of_head? c.core.hp.2.1
    (show 0 < c.core.p.length by omega)
  have hzero : ∀ k (hk : k < P.length), VertexComplete G (P[k]'hk) (wSet s) →
      G.Adj (P[k]'hk) s.x₁ → k = 0 := by
    intro k hk hc ha
    have he := (hfirst _ (List.getElem_mem hk)).mp (complete_X_of_complete_wSet s hc ha.symm)
    exact c.core.hp.1.2.1.getElem_inj_iff.mp (he.trans hp0.symm)
  have hi0 : i = 0 := by
    rcases hcover (P[i]'(by omega)) hiW with ha | ha
    · exact hzero i (by omega) hiW ha
    · have := (PathBasics.path_adj_iff c.core.hp.1 (show i < P.length by omega) hd).mp ha
      omega
  have hd2 : d = 2 := by omega
  refine ⟨by omega, ?_, ?_⟩
  · simpa only [hi0] using hjW
  · intro k hk hc
    rcases hcover (P[k]'hk) hc with ha | ha
    · exact Or.inl (hzero k hk hc ha)
    · have := (PathBasics.path_adj_iff c.core.hp.1 hk hd).mp ha
      omega

end Workspace.ProofLemmas.Thm175Claim4Bridge
