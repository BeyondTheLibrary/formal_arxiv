import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Knots
import Workspace.Types.Decompositions
import Workspace.Types.SkewTools
import Workspace.Types.Overshadowed
import Workspace.ProofLemmas.ConnectedSetUnionAttach
import Workspace.ProofLemmas.ComponentsOfSetBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.StriationCompl
import Workspace.ProofLemmas.Thm96StriationTools
import Workspace.Statements.S04.Thm_4_2
import Workspace.Statements.S09.Thm_9_5

/-!
# Claim (1) steps for theorem 9.6

These lemmas follow the three moves in the printed claim.  The vertices complete to the chosen
anticomponent resolve the striation.  A component left after deleting those vertices and `N`
cannot leave its first strip.  The resulting two sides form the loose skew partition used in 4.2.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Workspace.ProofLemmas.Thm96Claim1Steps

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Knots Workspace.Types.Knots.SPGT
open Workspace.Types.Decompositions Workspace.Types.Decompositions.SPGT
open Workspace.Types.SkewTools Workspace.Types.SkewTools.SPGT
open Workspace.Types.Overshadowed Workspace.Types.Overshadowed.SPGT
open Workspace.ProofLemmas.Thm96StriationTools

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The set called `X` in claim (1): all vertices complete to the anticomponent `N₁`. -/
def completeSet (G : SimpleGraph V) (N₁ : Set V) : Set V :=
  {v : V | VertexComplete G v N₁}

private theorem component_add_adjacent {G : SimpleGraph V} {X F : Set V}
    (hF : IsComponent G X F) {x y : V} (hx : x ∈ F) (hy : y ∈ X)
    (hxy : G.Adj x y) : y ∈ F := by
  have hcon : ConnectedSet G (F ∪ {y}) :=
    ConnectedSetUnionAttach.connectedSet_union_singleton hF.2.1 ⟨x, hx, hxy.symm⟩
  have heq := hF.2.2 (F ∪ {y}) Set.subset_union_left
    (Set.union_subset hF.1 (Set.singleton_subset_iff.mpr hy)) hcon
  have hy' : y ∈ F ∪ {y} := Or.inr rfl
  rwa [heq] at hy'

/-- PAPER (9.6, claim (1)): 9.5 in the complement says that the vertices complete to `N₁`
resolve the original striation. -/
theorem completeSet_resolves
    (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (hL : IsStriation G S T)
    (hGc : Berge Gᶜ)
    (hnoenlc : ¬ ∃ (k : ℕ) (J' : SimpleGraph (Fin k)),
      IsJEnlargement (⊤ : SimpleGraph (Fin 4)) J' ∧ (Appears Gᶜ J' ∨ Appears Gᶜᶜ J'))
    (hnooverc : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜ.induce K'),
      IsAppearance Gᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧ IsOvershadowedAppearance Gᶜ H K' φ)
    (hnoovercc : ¬ ∃ (k : ℕ) (H : SimpleGraph (Fin k)) (K' : Set V)
      (φ : H.lineGraph ≃g Gᶜᶜ.induce K'),
      IsAppearance Gᶜᶜ (⊤ : SimpleGraph (Fin 4)) H K' ∧
        IsOvershadowedAppearance Gᶜᶜ H K' φ)
    (hmaxc : MaximalStriation Gᶜ T S)
    (N N₁ : Set V) (hN₁ : IsComponent Gᶜ N N₁)
    (hN₁sub : N₁ ⊆ (striationVertices S T)ᶜ)
    (hNlocal : ∀ f ∈ N₁,
      LocalForStriation Gᶜ T S (Gᶜ.neighborSet f ∩ striationVertices T S)) :
    ResolvesStriation G S T (completeSet G N₁) := by
  let X := completeSet G N₁
  let L := striationVertices S T
  have hswap : striationVertices T S = L := StriationCompl.striationVertices_swap S T
  have hatt : attachments Gᶜ N₁ (striationVertices T S) = L \ X := by
    ext v
    constructor
    · rintro ⟨hvL, f, hf, hvf⟩
      have hvL' : v ∈ L := by rw [← hswap]; exact hvL
      refine ⟨hvL', ?_⟩
      intro hvX
      exact ((SimpleGraph.compl_adj G v f).mp hvf).2 (hvX f hf)
    · rintro ⟨hvL, hvX⟩
      have hncomp : ¬ VertexComplete G v N₁ := hvX
      simp only [VertexComplete] at hncomp
      push_neg at hncomp
      obtain ⟨f, hf, hvf⟩ := hncomp
      have hvfne : v ≠ f := by
        intro h
        subst f
        exact (hN₁sub hf) hvL
      refine ⟨?_, f, hf, (SimpleGraph.compl_adj G v f).mpr ⟨hvfne, hvf⟩⟩
      rw [hswap]
      exact hvL
  have hlocal : LocalForStriation Gᶜ T S (L \ X) := by
    rw [← hatt]
    exact _root_.Workspace.Statements.S09.SPGT.thm_9_5 Gᶜ hGc hnoenlc
      hnooverc hnoovercc n m T S hmaxc N₁
      (by rw [hswap]; exact hN₁sub) hN₁.2.1 hNlocal
  let X₀ : Set V := L ∩ X
  have hX₀sub : X₀ ⊆ L := Set.inter_subset_left
  have hdiff : L \ X₀ = L \ X := by
    ext v
    constructor
    · rintro ⟨hvL, hv⟩
      exact ⟨hvL, fun hvX => hv ⟨hvL, hvX⟩⟩
    · rintro ⟨hvL, hvX⟩
      exact ⟨hvL, fun hv => hvX hv.2⟩
  have hres₀ : ResolvesStriation G S T X₀ :=
    (StriationCompl.resolves_iff_local_compl hL hX₀sub).mpr (by
      rw [hdiff]
      exact hlocal)
  refine ⟨?_, ?_, ?_⟩
  · intro j j' hj hj'
    apply hres₀.1 j j'
    · intro hsub
      exact hj (fun v hv => hsub hv |>.2)
    · intro hsub
      exact hj' (fun v hv => hsub hv |>.2)
  · intro i p hp
    obtain ⟨v, hvp, hv⟩ := hres₀.2.1 i p hp
    exact ⟨v, hvp, hv.2⟩
  · intro u hu w hw huw
    rcases hres₀.2.2 u hu w hw huw with huX | hwX
    · exact Or.inl huX.2
    · exact Or.inr hwX.2

/-- PAPER (9.6, claim (1)): the component `U` left after deleting `X ∪ N` cannot meet a
second part of the striation, and no other strip can attach to it. -/
theorem component_confined_to_strip
    (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (M N X : Set V) (hL : IsStriation G S T)
    (hpart : M ∪ N = (striationVertices S T)ᶜ)
    (hres : ResolvesStriation G S T X)
    (hattLocal : ∀ F : Set V, IsComponent G M F →
      LocalForStriation G S T (attachments G F (striationVertices S T)))
    (i : Fin m) (u : V) (huS : u ∈ stripVertices (S i))
    (huW : u ∈ (X ∪ N)ᶜ)
    (U : Set V) (hU : IsComponent G ((X ∪ N)ᶜ) U) (huU : u ∈ U) :
    (U ∩ striationVertices S T ⊆ stripVertices (S i)) ∧
      ∀ k : Fin m, k ≠ i → Anticomplete G (stripVertices (S k)) U := by
  let W : Set V := (X ∪ N)ᶜ
  let Good : V → Prop := fun v =>
    v ∈ stripVertices (S i) ∨
      ∃ F : Set V, IsComponent G M F ∧ v ∈ F ∧
        ∃ a ∈ attachments G F (striationVertices S T),
          a ∈ stripVertices (S i) ∧ a ∉ X
  have memM_of_offL : ∀ {v : V}, v ∈ W → v ∉ striationVertices S T → v ∈ M := by
    intro v hvW hvL
    have hvMN : v ∈ M ∪ N := by rw [hpart]; exact hvL
    rcases hvMN with hvM | hvN
    · exact hvM
    · exact absurd hvN (fun h => hvW (Or.inr h))
  have step : ∀ {x y : V}, x ∈ W → y ∈ W → G.Adj x y → Good x → Good y := by
    intro x y hxW hyW hxy hxGood
    have hxnotX : x ∉ X := fun h => hxW (Or.inl h)
    have hynotX : y ∉ X := fun h => hyW (Or.inl h)
    rcases hxGood with hxS | ⟨F, hF, hxF, a, haatt, haS, hanX⟩
    · by_cases hyL : y ∈ striationVertices S T
      · rcases hyL with hySs | hyTs
        · obtain ⟨k, hySk⟩ := Set.mem_iUnion.mp hySs
          by_cases hki : k = i
          · exact Or.inl (hki ▸ hySk)
          · exfalso
            rcases lt_trichotomy k i with hki' | hki' | hik'
            · exact hL.2.2.2.2.2.2.2.2.2.1 k i hki' y hySk x hxS hxy.symm
            · exact hki hki'
            · exact hL.2.2.2.2.2.2.2.2.2.1 i k hik' x hxS y hySk hxy
        · exfalso
          rcases hres.2.2 x (Set.mem_iUnion.mpr ⟨i, hxS⟩) y hyTs hxy with h | h
          · exact hxnotX h
          · exact hynotX h
      · have hyM := memM_of_offL hyW hyL
        obtain ⟨F, hF, hyF⟩ := ComponentsOfSetBasics.exists_isComponent_mem G M hyM
        exact Or.inr ⟨F, hF, hyF, x,
          ⟨Or.inl (Set.mem_iUnion.mpr ⟨i, hxS⟩), y, hyF, hxy⟩, hxS, hxnotX⟩
    · by_cases hyL : y ∈ striationVertices S T
      · have hyatt : y ∈ attachments G F (striationVertices S T) :=
          ⟨hyL, x, hxF, hxy.symm⟩
        rcases hyL with hySs | hyTs
        · obtain ⟨k, hySk⟩ := Set.mem_iUnion.mp hySs
          have hki := (hattLocal F hF).1 i k
            ⟨a, haatt, haS⟩ ⟨y, hyatt, hySk⟩
          exact Or.inl (hki ▸ hySk)
        · exfalso
          have hay := (hattLocal F hF).2.2 a
            ⟨haatt, Set.mem_iUnion.mpr ⟨i, haS⟩⟩ y ⟨hyatt, hyTs⟩
          rcases hres.2.2 a (Set.mem_iUnion.mpr ⟨i, haS⟩) y hyTs hay with h | h
          · exact hanX h
          · exact hynotX h
      · have hyM := memM_of_offL hyW hyL
        have hyF := component_add_adjacent hF hxF hyM hxy
        exact Or.inr ⟨F, hF, hyF, a, haatt, haS, hanX⟩
  have preserve : ∀ {x y : ↥U}, (G.induce U).Reachable x y → Good x.1 → Good y.1 := by
    intro x y hr hx
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact hx
    | @cons x y z hadj w ih =>
        apply ih
        exact step (hU.1 x.2) (hU.1 y.2) hadj hx
  have hUGood : ∀ v ∈ U, Good v := by
    intro v hvU
    exact preserve (hU.2.1 ⟨u, huU⟩ ⟨v, hvU⟩) (Or.inl huS)
  constructor
  · rintro v ⟨hvU, hvL⟩
    rcases hUGood v hvU with hvS | ⟨F, hF, hvF, a, haatt, haS, hanX⟩
    · exact hvS
    · exact False.elim ((hpart ▸ (Set.mem_union_left N (hF.1 hvF))) hvL)
  · intro k hki y hySk v hvU hyv
    rcases hUGood v hvU with hvS | ⟨F, hF, hvF, a, haatt, haS, hanX⟩
    · rcases lt_trichotomy k i with h | h | h
      · exact hL.2.2.2.2.2.2.2.2.2.1 k i h y hySk v hvS hyv
      · exact hki h
      · exact hL.2.2.2.2.2.2.2.2.2.1 i k h v hvS y hySk hyv.symm
    · have hyatt : y ∈ attachments G F (striationVertices S T) :=
        ⟨Or.inl (Set.mem_iUnion.mpr ⟨k, hySk⟩), v, hvF, hyv⟩
      have hik := (hattLocal F hF).1 i k
        ⟨a, haatt, haS⟩ ⟨y, hyatt, hySk⟩
      exact hki hik.symm

private theorem connected_crossing_edge {G : SimpleGraph V} {P A : Set V}
    (hP : ConnectedSet G P) {u v : V} (huP : u ∈ P) (huA : u ∈ A)
    (hvP : v ∈ P) (hvA : v ∉ A) :
    ∃ x ∈ P, x ∈ A ∧ ∃ y ∈ P, y ∉ A ∧ G.Adj x y := by
  by_contra hno
  push_neg at hno
  have preserve : ∀ {x y : ↥P}, (G.induce P).Reachable x y → x.1 ∈ A → y.1 ∈ A := by
    intro x y hr hxA
    obtain ⟨w⟩ := hr
    induction w with
    | nil => exact hxA
    | @cons x y z hadj w ih =>
        apply ih
        by_contra hyA
        exact hno x.1 x.2 hxA y.1 y.2 hyA hadj
  exact hvA (preserve (hP ⟨u, huP⟩ ⟨v, hvP⟩) huA)

/-- PAPER (9.6, end of claim (1)): once `U` is confined to one strip, the paper's
`(U ∪ V', N₁ ∪ X')` is a loose skew partition. -/
theorem loose_partition_from_confined
    (G : SimpleGraph V) {m n : ℕ}
    (S : Fin m → Set V × Set V × Set V) (T : Fin n → Set V × Set V × Set V)
    (N N₁ : Set V) (hL : IsStriation G S T)
    (hNsub : N ⊆ (striationVertices S T)ᶜ)
    (hN₁ : IsComponent Gᶜ N N₁) (f : V) (hfN₁ : f ∈ N₁)
    (hres : ResolvesStriation G S T (completeSet G N₁))
    (i : Fin m) (u : V) (huS : u ∈ stripVertices (S i))
    (huNotX : u ∉ completeSet G N₁)
    (U : Set V)
    (hU : IsComponent G ((completeSet G N₁ ∪ N)ᶜ) U) (huU : u ∈ U)
    (hconf : U ∩ striationVertices S T ⊆ stripVertices (S i))
    (hanti : ∀ k : Fin m, k ≠ i → Anticomplete G (stripVertices (S k)) U) :
    AdmitsLooseSkewPartition G := by
  let X := completeSet G N₁
  let X' : Set V := {x : V | x ∈ X ∧ ∃ y ∈ U, G.Adj x y}
  let V' : Set V := (U ∪ N₁ ∪ X')ᶜ
  let A : Set V := U ∪ V'
  let B : Set V := N₁ ∪ X'
  have hN₁ne : N₁.Nonempty := ⟨f, hfN₁⟩
  have hN₁N : N₁ ⊆ N := hN₁.1
  have hUsubW : U ⊆ (X ∪ N)ᶜ := hU.1
  have hUN : Disjoint U N₁ := Set.disjoint_left.mpr (by
    intro x hxU hxN₁
    exact hUsubW hxU (Or.inr (hN₁N hxN₁)))
  have hUX : Disjoint U X' := Set.disjoint_left.mpr (by
    intro x hxU hxX'
    exact hUsubW hxU (Or.inl hxX'.1))
  have hN₁X : Disjoint N₁ X' := Set.disjoint_left.mpr (by
    intro x hxN₁ hxX'
    exact (hxX'.1 x hxN₁).ne rfl)
  have hNcover : N ⊆ N₁ ∪ X := by
    intro x hxN
    by_cases hxN₁ : x ∈ N₁
    · exact Or.inl hxN₁
    · apply Or.inr
      obtain ⟨D, hD, hxD⟩ := ComponentsOfSetBasics.exists_isComponent_mem Gᶜ N hxN
      have hDN : D ≠ N₁ := fun h => hxN₁ (h ▸ hxD)
      intro y hyN₁
      by_contra hxy
      have hxyne : x ≠ y := by
        intro h
        subst y
        exact Set.disjoint_left.mp
          (ComponentsOfSetBasics.disjoint_of_isComponent Gᶜ hD hN₁ hDN) hxD hyN₁
      exact ComponentsOfSetBasics.anticomplete_of_isComponent Gᶜ hD hN₁ hDN
        x hxD y hyN₁ ⟨hxyne, hxy⟩
  have hX'ne : X'.Nonempty := by
    obtain ⟨P, hP, huP⟩ := exists_rung_through (hL.1 i) huS
    obtain ⟨x, hxP, hxX⟩ := hres.2.1 i P hP
    have hPdata := rung_connected_subset hP
    have hxNotU : x ∉ U := by
      intro hxU
      exact hUsubW hxU (Or.inl hxX)
    obtain ⟨a, haP, haU, b, hbP, hbNotU, hab⟩ :=
      connected_crossing_edge hPdata.1 huP huU hxP hxNotU
    have hbL : b ∈ striationVertices S T := hPdata.2 hbP |> fun hbS =>
      Or.inl (Set.mem_iUnion.mpr ⟨i, hbS⟩)
    have hbNotN : b ∉ N := fun hbN => (hNsub hbN) hbL
    have hbX : b ∈ X := by
      by_contra hbX
      have hbW : b ∈ (X ∪ N)ᶜ := fun h => h.elim hbX hbNotN
      exact hbNotU (component_add_adjacent hU haU hbW hab)
    exact ⟨b, hbX, a, haU, hab.symm⟩
  have hV'ne : V'.Nonempty := by
    have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    obtain ⟨k, hki⟩ : ∃ k : Fin m, k ≠ i := by
      by_cases hi : i = ⟨0, h0⟩
      · exact ⟨⟨1, h1⟩, by rw [hi]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, h0⟩, Ne.symm hi⟩
    obtain ⟨P, hP⟩ := exists_rung (hL.1 k)
    obtain ⟨q, hqP, hqX⟩ := hres.2.1 k P hP
    have hqSk : q ∈ stripVertices (S k) := (rung_connected_subset hP).2 hqP
    have hqL : q ∈ striationVertices S T :=
      Or.inl (Set.mem_iUnion.mpr ⟨k, hqSk⟩)
    have hqNotU : q ∉ U := by
      intro hqU
      have hqSi := hconf ⟨hqU, hqL⟩
      exact Set.disjoint_left.mp (hL.2.2.1 k i hki) hqSk hqSi
    have hqNotN₁ : q ∉ N₁ := fun hqN => (hNsub (hN₁N hqN)) hqL
    have hqNotX' : q ∉ X' := by
      rintro ⟨-, y, hyU, hqy⟩
      exact hanti k hki q hqSk y hyU hqy
    exact ⟨q, fun h => h.elim (fun h => h.elim hqNotU hqNotN₁) hqNotX'⟩
  have hAUB : A ∪ B = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hxU : x ∈ U
    · exact Or.inl (Or.inl hxU)
    by_cases hxN : x ∈ N₁
    · exact Or.inr (Or.inl hxN)
    by_cases hxX : x ∈ X'
    · exact Or.inr (Or.inr hxX)
    · exact Or.inl (Or.inr (fun h => h.elim (fun h => h.elim hxU hxN) hxX))
  have hABdisj : Disjoint A B := Set.disjoint_left.mpr (by
    intro x hxA hxB
    rcases hxA with hxU | hxV
    · rcases hxB with hxN | hxX
      · exact Set.disjoint_left.mp hUN hxU hxN
      · exact Set.disjoint_left.mp hUX hxU hxX
    · rcases hxB with hxN | hxX
      · exact hxV (Or.inl (Or.inr hxN))
      · exact hxV (Or.inr hxX))
  have hUantiV : Anticomplete G U V' := by
    intro x hxU y hyV hxy
    by_cases hyW : y ∈ (X ∪ N)ᶜ
    · exact hyV (Or.inl (Or.inl (component_add_adjacent hU hxU hyW hxy)))
    · have hyXN : y ∈ X ∪ N := by
        by_contra h
        exact hyW h
      rcases hyXN with hyX | hyN
      · exact hyV (Or.inr ⟨hyX, x, hxU, hxy.symm⟩)
      · rcases hNcover hyN with hyN₁ | hyX
        · exact hyV (Or.inl (Or.inr hyN₁))
        · exact hyV (Or.inr ⟨hyX, x, hxU, hxy.symm⟩)
  have hAncon : ¬ ConnectedSet G A :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      rfl ⟨u, huU⟩ hV'ne (by
        refine Set.disjoint_left.mpr ?_
        intro x hxU hxV
        exact hxV (Or.inl (Or.inl hxU))) hUantiV
  have hN₁completeX : Complete G N₁ X' := by
    intro x hxN y hyX
    exact (hyX.1 x hxN).symm
  have hantiC : Anticomplete Gᶜ N₁ X' := by
    intro x hxN y hyX hxy
    exact ((SimpleGraph.compl_adj G x y).mp hxy).2 (hN₁completeX x hxN y hyX)
  have hBnacon : ¬ AnticonnectedSet G B :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.not_connectedSet_of_split
      rfl hN₁ne hX'ne hN₁X hantiC
  have hskew : IsSkewPartition G A B := ⟨hAUB, hABdisj, hAncon, hBnacon⟩
  have hN₁compB : IsAnticomponent G B N₁ :=
    _root_.Workspace.Statements.S04.SPGT.Helpers42.isComponent_of_split
      (_root_.Workspace.Statements.S04.SPGT.Helpers42.isComponent_self hN₁.2.1)
      hN₁ne rfl hantiC
  -- The witness chosen above for `V'` was obtained from a resolving rung and is in `X`.
  -- Recover such a witness directly, retaining its completeness proof.
  have hlooseWitness : ∃ q ∈ V', q ∈ X := by
    have hm : 2 ≤ m := hL.2.2.2.2.2.2.2.1
    have h0 : 0 < m := by omega
    have h1 : 1 < m := by omega
    obtain ⟨k, hki⟩ : ∃ k : Fin m, k ≠ i := by
      by_cases hi : i = ⟨0, h0⟩
      · exact ⟨⟨1, h1⟩, by rw [hi]; simp [Fin.ext_iff]⟩
      · exact ⟨⟨0, h0⟩, Ne.symm hi⟩
    obtain ⟨P, hP⟩ := exists_rung (hL.1 k)
    obtain ⟨q, hqP, hqX⟩ := hres.2.1 k P hP
    have hqSk : q ∈ stripVertices (S k) := (rung_connected_subset hP).2 hqP
    have hqL : q ∈ striationVertices S T :=
      Or.inl (Set.mem_iUnion.mpr ⟨k, hqSk⟩)
    have hqNotU : q ∉ U := by
      intro hqU
      exact Set.disjoint_left.mp (hL.2.2.1 k i hki) hqSk (hconf ⟨hqU, hqL⟩)
    have hqNotN₁ : q ∉ N₁ := fun hqN => (hNsub (hN₁N hqN)) hqL
    have hqNotX' : q ∉ X' := by
      rintro ⟨-, y, hyU, hqy⟩
      exact hanti k hki q hqSk y hyU hqy
    exact ⟨q, fun h => h.elim (fun h => h.elim hqNotU hqNotN₁) hqNotX', hqX⟩
  obtain ⟨q₀, hq₀V, hq₀X⟩ := hlooseWitness
  exact ⟨A, B, hskew, Or.inr ⟨q₀, Or.inr hq₀V, N₁, hN₁compB, hq₀X⟩⟩

end Workspace.ProofLemmas.Thm96Claim1Steps
