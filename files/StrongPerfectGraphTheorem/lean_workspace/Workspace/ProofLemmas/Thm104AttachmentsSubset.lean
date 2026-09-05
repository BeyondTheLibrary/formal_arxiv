import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PrismBasics
import Workspace.Statements.S10.Thm_10_3

/-!
# 10.4, second step: no internal vertex of `R₁` or `R₂` is an attachment

PAPER (proof of 10.4, printed p. 61): *"By 10.3 no internal vertex of `R₁` or `R₂` is an
attachment of `F`."*

For `R₁` this is 10.3 applied verbatim: an internal attachment `x₁` of `R₁` together with any
attachment `x₂ ∉ R₁` (one exists because the attachment set is not local) yields a path whose
first vertex is adjacent to `a₃` (or to `b₃`), so `a₃` (or `b₃`) is an attachment lying in
`V(R₃)` — contrary to hypothesis.  For `R₂` it is the same argument after interchanging the
indices `1` and `2`, which is the relabelled prism `R₂, R₁, R₃`.

Combining with *"none are in `V(R₃)`"* this pins the attachment set inside `{a₁, b₁, a₂, b₂}`,
which is the inclusion `⊆` of 10.4's conclusion.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm104AttachmentsSubset

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The paper's second sentence in the proof of 10.4, together with the inclusion it gives:
no attachment of `F` is an internal vertex of `R₁` or of `R₂`, and hence (since none lies in
`V(R₃)`) every attachment is one of `a₁, b₁, a₂, b₂`. -/
theorem thm104_attachments_subset (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (hmaj : ∀ v ∈ F, ¬ MajorForPrism G a b v)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hR₃ : ∀ v ∈ attachments G F K, v ∉ R 2) :
    (∀ x ∈ attachments G F K, x ∉ SPGT.interior (R 0)) ∧
      (∀ x ∈ attachments G F K, x ∉ SPGT.interior (R 1)) ∧
      (∀ x ∈ attachments G F K, x = a 0 ∨ x = b 0 ∨ x = a 1 ∨ x = b 1) := by
  obtain ⟨htA, htB, hab, hP0, hP1, hP2, h01, h02, h12⟩ := id hprism
  have ha2mem : a 2 ∈ R 2 := List.mem_of_mem_head? hP2.2.1
  have hb2mem : b 2 ∈ R 2 := List.mem_of_mem_getLast? hP2.2.2
  have ha2K : a 2 ∈ K := by rw [hK]; exact Or.inr ha2mem
  have hb2K : b 2 ∈ K := by rw [hK]; exact Or.inr hb2mem
  -- the attachment set is not contained in `V(R₁)`, nor in `V(R₂)`
  rw [LocalForPrism] at hFloc
  push_neg at hFloc
  obtain ⟨hn0, hn1, -, -, -⟩ := hFloc
  obtain ⟨y0, hy0, hy0R⟩ := Set.not_subset.mp hn0
  obtain ⟨y1, hy1, hy1R⟩ := Set.not_subset.mp hn1
  -- the contradiction both applications of 10.3 end in
  have final : ∀ (f : List V) (f₁ fn : V), IsPathFrom G f f₁ fn → (∀ v ∈ f, v ∈ F) →
      (G.Adj f₁ (a 2) ∨ G.Adj f₁ (b 2)) → False := by
    intro f f₁ fn hf hfF hadj
    have hf₁F : f₁ ∈ F := hfF f₁ (List.mem_of_mem_head? hf.2.1)
    rcases hadj with h | h
    · exact hR₃ (a 2) ⟨ha2K, f₁, hf₁F, h.symm⟩ ha2mem
    · exact hR₃ (b 2) ⟨hb2K, f₁, hf₁F, h.symm⟩ hb2mem
  -- (i) no attachment is an internal vertex of `R₁`
  have step0 : ∀ x ∈ attachments G F K, x ∉ SPGT.interior (R 0) := by
    intro x hx hxint
    obtain ⟨f, f₁, fn, hf, hfF, hcase⟩ :=
      Workspace.Statements.S10.SPGT.thm_10_3 G hG hK4 a b R K F hprism hK hFK hFconn hmaj
        x y0 hx hxint hy0 hy0R
    rcases hcase with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩
    · exact final f f₁ fn hf hfF (Or.inl h)
    · exact final f f₁ fn hf hfF (Or.inr h)
  -- (ii) the same for `R₂`, via the relabelled prism `R₂, R₁, R₃`
  have hprism' : FormPrism G ![a 1, a 0, a 2] ![b 1, b 0, b 2] (R 1) (R 0) (R 2) := by
    refine PrismBasics.formPrism_of_data (htA 1 0 (by decide)) (htA 1 2 (by decide))
      (htA 0 2 (by decide)) (htB 1 0 (by decide)) (htB 1 2 (by decide)) (htB 0 2 (by decide))
      (hab 1 1) (hab 1 0) (hab 1 2) (hab 0 1) (hab 0 0) (hab 0 2)
      (hab 2 1) (hab 2 0) (hab 2 2) hP1 hP0 hP2 ?_ h12 h02
    intro u hu v hv
    rw [SimpleGraph.adj_comm, h01 v hv u hu]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr ⟨h2, h1⟩
  have hR' : ∀ i : Fin 3, (![R 1, R 0, R 2] : Fin 3 → List V) i = ![R 1, R 0, R 2] i := fun _ => rfl
  have hK' : K = {v : V | v ∈ (![R 1, R 0, R 2] : Fin 3 → List V) 0} ∪
      {v : V | v ∈ (![R 1, R 0, R 2] : Fin 3 → List V) 1} ∪
      {v : V | v ∈ (![R 1, R 0, R 2] : Fin 3 → List V) 2} := by
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hK, Set.union_comm {v : V | v ∈ R 0} {v : V | v ∈ R 1}]
  have hmaj' : ∀ v ∈ F, ¬ MajorForPrism G ![a 1, a 0, a 2] ![b 1, b 0, b 2] v := by
    intro v hv hcon
    refine hmaj v hv ?_
    obtain ⟨hA, hB⟩ := hcon
    refine ⟨?_, ?_⟩
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.insert_comm] using hA
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.insert_comm] using hB
  have step1 : ∀ x ∈ attachments G F K, x ∉ SPGT.interior (R 1) := by
    intro x hx hxint
    obtain ⟨f, f₁, fn, hf, hfF, hcase⟩ :=
      Workspace.Statements.S10.SPGT.thm_10_3 G hG hK4 ![a 1, a 0, a 2] ![b 1, b 0, b 2]
        ![R 1, R 0, R 2] K F (by simpa using hprism') hK' hFK hFconn hmaj'
        x y1 hx (by simpa using hxint) hy1 (by simpa using hy1R)
    rcases hcase with ⟨-, h, -, -⟩ | ⟨-, h, -, -⟩
    · exact final f f₁ fn hf hfF (Or.inl (by simpa using h))
    · exact final f f₁ fn hf hfF (Or.inr (by simpa using h))
  refine ⟨step0, step1, ?_⟩
  intro x hx
  have hxK : x ∈ K := hx.1
  rw [hK] at hxK
  rcases hxK with (hx0 | hx1) | hx2
  · have := step0 x hx
    rw [PathBasics.mem_interior_iff_of_pathFrom hP0] at this
    push_neg at this
    rcases eq_or_ne x (a 0) with rfl | hne0
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (this hx0 hne0))
  · have := step1 x hx
    rw [PathBasics.mem_interior_iff_of_pathFrom hP1] at this
    push_neg at this
    rcases eq_or_ne x (a 1) with rfl | hne1
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (this hx1 hne1)))
  · exact absurd hx2 (hR₃ x hx)

end Workspace.ProofLemmas.Thm104AttachmentsSubset
