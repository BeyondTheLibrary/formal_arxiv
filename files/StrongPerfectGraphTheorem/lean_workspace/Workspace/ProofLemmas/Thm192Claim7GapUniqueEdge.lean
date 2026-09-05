import Workspace.ProofLemmas.Thm192Claim6Basics
import Workspace.Statements.S02.Thm_2_3

/-! The unique complete edge of the shortened hole in claim (7). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Workspace.ProofLemmas.Thm192Claim7GapUniqueEdge

open Workspace.Types.Core Workspace.Types.Core.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem no_edge_any {G : SimpleGraph V} {Y : Set V} {P : List V} (hP : IsPathList G P)
    (hno : ∀ i (hi : i + 1 < P.length), ¬ EdgeComplete G Y (P[i]'(by omega)) (P[i+1]'hi)) :
    ∀ u ∈ P, ∀ v ∈ P, ¬ EdgeComplete G Y u v := by
  intro u hu v hv hE
  obtain ⟨i, hi, hiu⟩ := List.getElem_of_mem hu
  obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
  have hadj : G.Adj (P[i]'hi) (P[j]'hj) := by rw [hiu, hjv]; exact hE.1
  rcases (PathBasics.path_adj_iff hP hi hj).mp hadj with hij | hji
  · subst j
    exact hno i hj (by rwa [hiu, hjv])
  · subst i
    exact hno j hi (by rw [hiu, hjv]; exact ⟨hE.1.symm, hE.2.2, hE.2.1⟩)

/-- PAPER (2.3, used in (7)): if a hole has just one `Y`-complete edge, the ends
of that edge are its only `Y`-complete vertices. -/
theorem only_complete_of_unique_edge {G : SimpleGraph V} (hG : Berge G)
    {Y : Set V} (hY : AnticonnectedSet G Y) {C : List V} (hC : IsHoleList G C)
    (hCY : ∀ w ∈ C, w ∉ Y) {a b : V} (ha : a ∈ C) (hb : b ∈ C)
    (hab : EdgeComplete G Y a b)
    (honly : ∀ u ∈ C, ∀ v ∈ C, EdgeComplete G Y u v → s(u,v) = s(a,b)) :
    ∀ w ∈ C, VertexComplete G w Y → w = a ∨ w = b := by
  have hset : {e : Sym2 V | ∃ u ∈ C, ∃ v ∈ C, e = s(u,v) ∧ EdgeComplete G Y u v} = {s(a,b)} := by
    ext e
    constructor
    · rintro ⟨u, hu, v, hv, he, hE⟩
      exact he.trans (honly u hu v hv hE)
    · intro he
      exact ⟨a, ha, b, hb, he, hab⟩
  rcases (Workspace.Statements.S02.SPGT.thm_2_3 G hG Y hY C (Or.inr hC) hCY).2 hC
      with heven | ⟨u, v, huv, hne, hadj⟩
  · rw [hset, Set.ncard_singleton] at heven
    exact (by simpa using heven : False).elim
  · have ha' : a = u ∨ a = v := by
      have : a ∈ {w : V | w ∈ C ∧ VertexComplete G w Y} := ⟨ha, hab.2.1⟩
      rwa [huv] at this
    have hb' : b = u ∨ b = v := by
      have : b ∈ {w : V | w ∈ C ∧ VertexComplete G w Y} := ⟨hb, hab.2.2⟩
      rwa [huv] at this
    intro w hw hwc
    have hw' : w = u ∨ w = v := by
      have : w ∈ {w : V | w ∈ C ∧ VertexComplete G w Y} := ⟨hw, hwc⟩
      rwa [huv] at this
    have habne := hab.1.ne
    rcases ha' with ha' | ha' <;> rcases hb' with hb' | hb' <;>
      rcases hw' with hw' | hw' <;> aesop

/-- PAPER (claim (7)): "Consequently `zx₁` is the unique `Y`-complete edge of
the hole `z-x₂-pᵢ-⋯-pₙ-x₁-z`." -/
theorem cut_only_complete {G : SimpleGraph V} (hG : Berge G)
    {Y : Set V} (hY : AnticonnectedSet G Y) {P : List V} {a b z u : V}
    (hP : IsPathFrom G P a b) {i : ℕ} (hi : 0 < i) (hin : i + 1 < P.length)
    (hC : IsHoleList G (z :: u :: P.drop i))
    (hCY : ∀ w ∈ z :: u :: P.drop i, w ∉ Y)
    (hzY : VertexComplete G z Y) (hbY : VertexComplete G b Y)
    (huY : ¬ VertexComplete G u Y) (hzb : G.Adj z b)
    (hzI : ∀ w ∈ SPGT.interior P, ¬ G.Adj z w)
    (hno : ∀ k (hk : k + 1 < P.length), ¬ EdgeComplete G Y (P[k]'(by omega)) (P[k+1]'hk)) :
    ∀ w ∈ z :: u :: P.drop i, VertexComplete G w Y → w = z ∨ w = b := by
  have hmem : ∀ w ∈ P.drop i, w ∈ P ∧ (w = b ∨ w ∈ SPGT.interior P) := by
    intro w hw
    obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem hw
    have hik : i + k < P.length := by simp only [List.length_drop] at hk; omega
    have he : (P[i+k]'hik) = w := by simpa only [List.getElem_drop] using hkw
    refine ⟨List.mem_of_mem_drop hw, ?_⟩
    by_cases hlast : i + k = P.length - 1
    · left
      rw [← he]
      exact (hP.1.2.1.getElem_inj_iff.mpr hlast).trans
        (PathBasics.getElem_last_of_getLast? hP.2.2 (by omega))
    · right
      rw [← he]
      exact PathBasics.getElem_mem_interior hP.1 hik (by omega) (by omega)
  have hbC : b ∈ z :: u :: P.drop i := by
    simp only [List.mem_cons]
    right; right
    rw [List.mem_iff_getElem]
    refine ⟨P.length - 1 - i, by simp; omega, ?_⟩
    rw [List.getElem_drop]
    have he : i + (P.length - 1 - i) = P.length - 1 := by omega
    simpa only [he] using PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hznbr : ∀ w ∈ z :: u :: P.drop i, VertexComplete G w Y → G.Adj z w → w = b := by
    intro w hw hwY hzw
    rcases List.mem_cons.mp hw with hwz | hw
    · exact (hzw.ne hwz.symm).elim
    rcases List.mem_cons.mp hw with hwu | hw
    · exact (huY (hwu ▸ hwY)).elim
    rcases (hmem w hw).2 with hwb | hwI
    · exact hwb
    · exact (hzI w hwI hzw).elim
  apply only_complete_of_unique_edge hG hY hC hCY (by simp) hbC ⟨hzb, hzY, hbY⟩
  intro r hr s hs hE
  by_cases hrz : r = z
  · have hsb := hznbr s hs hE.2.2 (hrz ▸ hE.1)
    rw [hrz, hsb]
  by_cases hsz : s = z
  · have hrb := hznbr r hr hE.2.1 (hsz ▸ hE.1.symm)
    rw [hrb, hsz, Sym2.eq_swap]
  have hrP : r ∈ P := by
    rcases List.mem_cons.mp hr with hr | hr
    · exact (hrz hr).elim
    rcases List.mem_cons.mp hr with hr | hr
    · exact (huY (hr ▸ hE.2.1)).elim
    · exact (hmem r hr).1
  have hsP : s ∈ P := by
    rcases List.mem_cons.mp hs with hs | hs
    · exact (hsz hs).elim
    rcases List.mem_cons.mp hs with hs | hs
    · exact (huY (hs ▸ hE.2.2)).elim
    · exact (hmem s hs).1
  exact (no_edge_any hP.1 hno r hrP s hsP hE).elim

end Workspace.ProofLemmas.Thm192Claim7GapUniqueEdge
