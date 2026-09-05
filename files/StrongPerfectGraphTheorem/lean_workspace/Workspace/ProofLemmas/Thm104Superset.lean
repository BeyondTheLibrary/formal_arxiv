import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.Statements.S10.Thm_10_1

/-!
# 10.4, third step: `a₁, b₁, a₂, b₂` are all attachments

PAPER (proof of 10.4, printed p. 61): *"By 10.1, there is a path in `F` satisfying one of
10.1.1-4; and since it has no attachments in `R₃`, it must satisfy 10.1.1 or 10.1.3, and in
either case `a₁, b₁, a₂, b₂` are all attachments of `F`."*

10.1 delivers its conclusion for a relabelling `(a', b', R') = (a∘σ, b∘σ, R∘σ)` of the prism
(possibly with the two triangles interchanged).  Alternative 10.1.2 makes all three of
`a'₁, a'₂, a'₃` attachments and 10.1.4 makes a vertex of `R'₃` one, so in both of them the
index `i` with `σ(i) = 3` produces an attachment inside `V(R₃)` — excluded.  In 10.1.1 and
10.1.3 the attachments produced lie in `V(R'₁) ∪ V(R'₂)`, which forces `σ(3) = 3`, i.e.
`{σ(1), σ(2)} = {1, 2}`; and in each of the two the four vertices `a'₁, b'₁, a'₂, b'₂` are
attachments — in 10.1.1 because the two adjacent attachments on `R'ᵢ` cannot be internal
(second step) and hence are its two ends.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm104Superset

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's third sentence in the proof of 10.4: `a₁, b₁, a₂, b₂` are all attachments
of `F` in `K`. -/
theorem thm104_superset (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hR₃ : ∀ v ∈ attachments G F K, v ∉ R 2)
    (hsub : ∀ x ∈ attachments G F K, x = a 0 ∨ x = b 0 ∨ x = a 1 ∨ x = b 1) :
    ({a 0, b 0, a 1, b 1} : Set V) ⊆ attachments G F K := by
  obtain ⟨htA, htB, hab, hP0, hP1, hP2, h01, h02, h12⟩ := id hprism
  have fin3 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  -- the six triangle vertices lie on their paths, and every vertex of a path lies in `K`
  have hamem : ∀ i : Fin 3, a i ∈ R i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    rcases hi with rfl | rfl | rfl
    · exact List.mem_of_mem_head? hP0.2.1
    · exact List.mem_of_mem_head? hP1.2.1
    · exact List.mem_of_mem_head? hP2.2.1
  have hbmem : ∀ i : Fin 3, b i ∈ R i := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    rcases hi with rfl | rfl | rfl
    · exact List.mem_of_mem_getLast? hP0.2.2
    · exact List.mem_of_mem_getLast? hP1.2.2
    · exact List.mem_of_mem_getLast? hP2.2.2
  have hmemK : ∀ (i : Fin 3) (x : V), x ∈ R i → x ∈ K := by
    intro i x hx
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by fin_cases i <;> decide
    rw [hK]
    rcases hi with rfl | rfl | rfl
    · exact Or.inl (Or.inl hx)
    · exact Or.inl (Or.inr hx)
    · exact Or.inr hx
  -- the four cross-non-memberships between `R₁` and `R₂`
  have ha1R0 : a 1 ∉ R 0 := by
    intro hmem
    rcases (h02 (a 1) hmem (a 2) (hamem 2)).mp (htA 1 2 (by decide)) with ⟨h, -⟩ | ⟨h, -⟩
    · exact (htA 1 0 (by decide)).ne h
    · exact hab 1 0 h
  have hb1R0 : b 1 ∉ R 0 := by
    intro hmem
    rcases (h02 (b 1) hmem (b 2) (hbmem 2)).mp (htB 1 2 (by decide)) with ⟨h, -⟩ | ⟨h, -⟩
    · exact hab 0 1 h.symm
    · exact (htB 1 0 (by decide)).ne h
  have ha0R1 : a 0 ∉ R 1 := by
    intro hmem
    rcases (h12 (a 0) hmem (a 2) (hamem 2)).mp (htA 0 2 (by decide)) with ⟨h, -⟩ | ⟨h, -⟩
    · exact (htA 0 1 (by decide)).ne h
    · exact hab 0 1 h
  have hb0R1 : b 0 ∉ R 1 := by
    intro hmem
    rcases (h12 (b 0) hmem (b 2) (hbmem 2)).mp (htB 0 2 (by decide)) with ⟨h, -⟩ | ⟨h, -⟩
    · exact hab 1 0 h.symm
    · exact (htB 0 1 (by decide)).ne h
  -- an attachment on `R₁` (resp. `R₂`) is one of its two ends
  have pin : ∀ j : Fin 3, j ≠ 2 → ∀ x ∈ attachments G F K, x ∈ R j → x = a j ∨ x = b j := by
    intro j hj x hx hxj
    have hj' : j = 0 ∨ j = 1 := by fin_cases j <;> simp_all <;> decide
    rcases hsub x hx with rfl | rfl | rfl | rfl <;> rcases hj' with rfl | rfl
    · exact Or.inl rfl
    · exact absurd hxj ha0R1
    · exact Or.inr rfl
    · exact absurd hxj hb0R1
    · exact absurd hxj ha1R0
    · exact Or.inl rfl
    · exact absurd hxj hb1R0
    · exact Or.inr rfl
  -- 10.1
  obtain ⟨f, f₁, fn, hf, hfF, hflen, a', b', R', σ, hR'eq, hab'eq, hcase⟩ :=
    Workspace.Statements.S10.SPGT.thm_10_1 G hG a b R K F hprism hK hFK hFconn hFloc hmaj
  have hf₁ : f₁ ∈ f := List.mem_of_mem_head? hf.2.1
  have hfn : fn ∈ f := List.mem_of_mem_getLast? hf.2.2
  have hR'mem : ∀ i : Fin 3, R' i = R (σ i) := by intro i; rw [hR'eq]
  have ha'b' : ∀ i : Fin 3,
      (a' i = a (σ i) ∧ b' i = b (σ i)) ∨ (a' i = b (σ i) ∧ b' i = a (σ i)) := by
    intro i
    rcases hab'eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [h1], by rw [h2]⟩
    · exact Or.inr ⟨by rw [h1], by rw [h2]⟩
  have ha'mem : ∀ i : Fin 3, a' i ∈ R (σ i) := by
    intro i
    rcases ha'b' i with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact hamem (σ i)
    · exact hbmem (σ i)
  have hb'mem : ∀ i : Fin 3, b' i ∈ R (σ i) := by
    intro i
    rcases ha'b' i with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h]
    · exact hbmem (σ i)
    · exact hamem (σ i)
  -- being adjacent to a vertex of the path `f` makes a vertex of `K` an attachment
  have attach : ∀ (x z : V) (i : Fin 3), x ∈ R i → z ∈ f → G.Adj z x →
      x ∈ attachments G F K := by
    intro x z i hxi hz hadj
    exact ⟨hmemK i x hxi, z, hfF z hz, hadj.symm⟩
  have noR2 : ∀ (x z : V), x ∈ R 2 → z ∈ f → G.Adj z x → False := by
    intro x z hx2 hz hadj
    exact hR₃ x (attach x z 2 hx2 hz hadj) hx2
  -- `σ` fixes the index `3` as soon as the first two indices avoid it
  have hσ2 : σ 0 ≠ 2 → σ 1 ≠ 2 → σ 2 = 2 := by
    intro h0 h1
    have hex : σ (σ.symm 2) = 2 := by simp
    have hi : σ.symm 2 = 0 ∨ σ.symm 2 = 1 ∨ σ.symm 2 = 2 := fin3 _
    rcases hi with h | h | h
    · rw [h] at hex; exact absurd hex h0
    · rw [h] at hex; exact absurd hex h1
    · rw [h] at hex; exact hex
  -- from a pair of attachments on the relabelled prism back to the original labels
  have pairback : ∀ i : Fin 3, a' i ∈ attachments G F K → b' i ∈ attachments G F K →
      a (σ i) ∈ attachments G F K ∧ b (σ i) ∈ attachments G F K := by
    intro i h1 h2
    rcases ha'b' i with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact ⟨e1 ▸ h1, e2 ▸ h2⟩
    · exact ⟨e2 ▸ h2, e1 ▸ h1⟩
  -- the two surviving alternatives both give the four attachments
  have main : ∀ j : Fin 3, j ≠ 2 → a j ∈ attachments G F K ∧ b j ∈ attachments G F K := by
    have key : (σ 2 = 2) ∧ ∀ i : Fin 3, i ≠ 2 →
        a (σ i) ∈ attachments G F K ∧ b (σ i) ∈ attachments G F K := by
      rcases hcase with h1 | h2 | h3 | h4
      · -- 10.1.1
        obtain ⟨u, u', hu, hu', huu', hf1u, hf1u', w, w', hw, hw', hww', hfnw, hfnw', -, -⟩ := h1
        rw [hR'mem 0] at hu hu'
        rw [hR'mem 1] at hw hw'
        have hs0 : σ 0 ≠ 2 := by
          intro h; exact noR2 u f₁ (h ▸ hu) hf₁ hf1u
        have hs1 : σ 1 ≠ 2 := by
          intro h; exact noR2 w fn (h ▸ hw) hfn hfnw
        have hends : ∀ (j : Fin 3) (p q : V), j ≠ 2 → p ∈ R j → q ∈ R j → G.Adj p q →
            p ∈ attachments G F K → q ∈ attachments G F K →
            a j ∈ attachments G F K ∧ b j ∈ attachments G F K := by
          intro j p q hj hp hq hpq hpa hqa
          rcases pin j hj p hpa hp with rfl | rfl <;> rcases pin j hj q hqa hq with rfl | rfl
          · exact absurd rfl hpq.ne
          · exact ⟨hpa, hqa⟩
          · exact ⟨hqa, hpa⟩
          · exact absurd rfl hpq.ne
        refine ⟨hσ2 hs0 hs1, ?_⟩
        intro i hi
        have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all <;> decide
        rcases hi' with rfl | rfl
        · exact hends (σ 0) u u' hs0 hu hu' huu'
            (attach u f₁ (σ 0) hu hf₁ hf1u) (attach u' f₁ (σ 0) hu' hf₁ hf1u')
        · exact hends (σ 1) w w' hs1 hw hw' hww'
            (attach w fn (σ 1) hw hfn hfnw) (attach w' fn (σ 1) hw' hfn hfnw')
      · -- 10.1.2 is impossible
        obtain ⟨-, hA, -, -⟩ := h2
        exfalso
        have hex : σ (σ.symm 2) = 2 := by simp
        have hm := ha'mem (σ.symm 2)
        rw [hex] at hm
        exact noR2 (a' (σ.symm 2)) f₁ hm hf₁ (hA (σ.symm 2))
      · -- 10.1.3
        obtain ⟨-, h1a0, h1a1, hnb0, hnb1, -⟩ := h3
        have hs0 : σ 0 ≠ 2 := by
          intro h; exact noR2 (a' 0) f₁ (h ▸ ha'mem 0) hf₁ h1a0
        have hs1 : σ 1 ≠ 2 := by
          intro h; exact noR2 (a' 1) f₁ (h ▸ ha'mem 1) hf₁ h1a1
        refine ⟨hσ2 hs0 hs1, ?_⟩
        intro i hi
        have hi' : i = 0 ∨ i = 1 := by fin_cases i <;> simp_all <;> decide
        rcases hi' with rfl | rfl
        · exact pairback 0 (attach (a' 0) f₁ (σ 0) (ha'mem 0) hf₁ h1a0)
            (attach (b' 0) fn (σ 0) (hb'mem 0) hfn hnb0)
        · exact pairback 1 (attach (a' 1) f₁ (σ 1) (ha'mem 1) hf₁ h1a1)
            (attach (b' 1) fn (σ 1) (hb'mem 1) hfn hnb1)
      · -- 10.1.4 is impossible
        obtain ⟨h1a0, h1a1, ⟨y, hy, -, hfny⟩, -⟩ := h4
        exfalso
        have hex : σ (σ.symm 2) = 2 := by simp
        have hi : σ.symm 2 = 0 ∨ σ.symm 2 = 1 ∨ σ.symm 2 = 2 := fin3 _
        rcases hi with h | h | h
        · have h0 : σ 0 = 2 := by rw [← h]; exact hex
          have hm := ha'mem 0
          rw [h0] at hm
          exact noR2 (a' 0) f₁ hm hf₁ h1a0
        · have h0 : σ 1 = 2 := by rw [← h]; exact hex
          have hm := ha'mem 1
          rw [h0] at hm
          exact noR2 (a' 1) f₁ hm hf₁ h1a1
        · rw [h] at hex
          rw [hR'mem 2, hex] at hy
          exact noR2 y fn hy hfn hfny
    intro j hj
    obtain ⟨hs2, hkey⟩ := key
    have hji : σ.symm j ≠ 2 := by
      intro h
      have : σ (σ.symm j) = σ 2 := by rw [h]
      rw [Equiv.apply_symm_apply, hs2] at this
      exact hj this
    have := hkey (σ.symm j) hji
    rwa [Equiv.apply_symm_apply] at this
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact (main 0 (by decide)).1
  · exact (main 0 (by decide)).2
  · exact (main 1 (by decide)).1
  · exact (main 1 (by decide)).2

end Workspace.ProofLemmas.Thm104Superset
