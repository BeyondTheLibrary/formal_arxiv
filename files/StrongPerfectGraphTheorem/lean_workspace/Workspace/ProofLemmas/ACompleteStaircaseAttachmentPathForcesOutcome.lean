import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.Types.Staircases
import Workspace.ProofLemmas.StaircaseStepBanisterOddPrism
import Workspace.ProofLemmas.MinimalNonlocalStaircaseAttachmentPath
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismFromBanisterAndStep
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.Thm121C3PathCons
import Workspace.ProofLemmas.Thm132AdjoinBanister
import Workspace.Statements.S10.Thm_10_4

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Workspace.ProofLemmas.ACompleteStaircaseAttachmentPathForcesOutcome

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.Types.Staircases.SPGT

variable {V : Type*}

private theorem step_symm {G : SimpleGraph V} {A C B : Set V}
    {a₁ b₁ a₂ b₂ : V} {R₁ R₂ : List V}
    (h : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂) :
    IsStep G A C B a₂ R₂ b₂ a₁ R₁ b₁ := by
  refine ⟨h.2.1, h.1, fun z hz₂ hz₁ => h.2.2.1 z hz₁ hz₂, ?_⟩
  intro u hu v hv
  rw [G.adj_comm, h.2.2.2 v hv u hu]
  constructor <;> rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · exact Or.inl ⟨h₂, h₁⟩
  · exact Or.inr ⟨h₂, h₁⟩
  · exact Or.inl ⟨h₂, h₁⟩
  · exact Or.inr ⟨h₂, h₁⟩

private theorem rung_mem_strip {G : SimpleGraph V} {A C B : Set V}
    {a b : V} {R : List V} (hR : IsRungOfStrip G A C B a R b) :
    ∀ z ∈ R, z ∈ A ∪ B ∪ C := by
  intro z hz
  by_cases hza : z = a
  · exact Or.inl (Or.inl (hza ▸ hR.2.1))
  by_cases hzb : z = b
  · exact Or.inl (Or.inr (hzb ▸ hR.2.2.1))
  · exact Or.inr (hR.2.2.2.2.2 z
      ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hR.1).2
        ⟨hz, hza, hzb⟩))

private theorem getElem_eq_of_index_eq {W : Type*} (p : List W) {i j : ℕ}
    (hi : i < p.length) (hj : j < p.length) (hij : i = j) : p[i]'hi = p[j]'hj := by
  subst j
  rfl

private theorem isPathFrom_take_to_index {G : SimpleGraph V} {p : List V} {u v : V}
    (hp : IsPathFrom G p u v) (i : ℕ) (hi : i < p.length) :
    IsPathFrom G (p.take (i + 1)) u (p[i]'hi) := by
  refine ⟨Workspace.ProofLemmas.PathBasics.isPathList_take hp.1 (by omega), ?_, ?_⟩
  · simpa [List.head?_take] using hp.2.1
  · have h := Workspace.ProofLemmas.PathBasics.getLast?_slice p
        (i := 0) (j := i) (by omega) hi
    simpa using h

/-- The first vertex of `p` having a neighbour in `X`. -/
private theorem exists_min_adj_to_set [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (p : List V) (X : Set V)
    (hex : ∃ x ∈ p, ∃ y ∈ X, G.Adj x y) :
    ∃ (i : ℕ) (hi : i < p.length) (y : V), y ∈ X ∧ G.Adj (p[i]'hi) y ∧
      ∀ (j : ℕ) (hj : j < p.length), j < i → ∀ z ∈ X, ¬ G.Adj (p[j]'hj) z := by
  classical
  obtain ⟨x, hxp, y, hyX, hxy⟩ := hex
  obtain ⟨i₀, hi₀, hi₀x⟩ := List.getElem_of_mem hxp
  have hindex : ∃ i : ℕ, ∃ hi : i < p.length, ∃ y ∈ X, G.Adj (p[i]'hi) y :=
    ⟨i₀, hi₀, y, hyX, hi₀x ▸ hxy⟩
  obtain ⟨hi, y, hyX, hadj⟩ := Nat.find_spec hindex
  refine ⟨Nat.find hindex, hi, y, hyX, hadj, ?_⟩
  intro j hj hji z hzX hjz
  exact Nat.find_min hindex hji ⟨hj, z, hzX, hjz⟩

private theorem left_obstruction_nonlocal [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (D : Set V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hleft : ∃ x ∈ D, ∃ u ∈ A ∪ C, G.Adj x u)
    (hrung : ∃ x ∈ D, ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r) :
    ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G D (staircaseVertices A C B R₀)) := by
  obtain ⟨x, hxD, u, hu, hxu⟩ := hleft
  obtain ⟨y, hyD, r, hrR, hrne, hyr⟩ := hrung
  have hban := hK.2.1
  have huS : u ∈ A ∪ B ∪ C := hu.elim (fun h => Or.inl (Or.inl h)) Or.inr
  have huatt : u ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inr huS, x, hxD, hxu.symm⟩
  have hratt : r ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inl hrR, y, hyD, hyr.symm⟩
  rintro (hloc | hloc | hloc | hloc)
  · exact hban.2.1 r hrR (hloc hratt)
  · exact hban.2.1 u (hloc huatt) huS
  · rcases hloc hratt with hrA | hra
    · exact hban.2.1 r hrR (Or.inl (Or.inl hrA))
    · exact hrne (Set.mem_singleton_iff.mp hra)
  · rcases hloc huatt with huB | hub
    · rcases hu with huA | huC
      · exact Set.disjoint_left.mp hK.1.1.1 huA huB
      · exact Set.disjoint_left.mp hK.1.1.2.2 huB huC
    · exact hban.2.1 b₀
        (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)
        (Set.mem_singleton_iff.mp hub ▸ huS)

private theorem right_obstruction_nonlocal [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (D : Set V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hright : ∃ x ∈ D, ∃ u ∈ B ∪ C, G.Adj x u)
    (hrung : ∃ x ∈ D, ∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj x r) :
    ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G D (staircaseVertices A C B R₀)) := by
  obtain ⟨x, hxD, u, hu, hxu⟩ := hright
  obtain ⟨y, hyD, r, hrR, hrne, hyr⟩ := hrung
  have hban := hK.2.1
  have huS : u ∈ A ∪ B ∪ C := hu.elim (fun h => Or.inl (Or.inr h)) Or.inr
  have huatt : u ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inr huS, x, hxD, hxu.symm⟩
  have hratt : r ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inl hrR, y, hyD, hyr.symm⟩
  rintro (hloc | hloc | hloc | hloc)
  · exact hban.2.1 r hrR (hloc hratt)
  · exact hban.2.1 u (hloc huatt) huS
  · rcases hloc huatt with huA | hua
    · rcases hu with huB | huC
      · exact Set.disjoint_left.mp hK.1.1.1 huA huB
      · exact Set.disjoint_left.mp hK.1.1.2.1 huA huC
    · exact hban.2.1 a₀ (Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1)
        (Set.mem_singleton_iff.mp hua ▸ huS)
  · rcases hloc hratt with hrB | hrb
    · exact hban.2.1 r hrR (Or.inl (Or.inr hrB))
    · exact hrne (Set.mem_singleton_iff.mp hrb)

/-- The application of 10.4 to the first stretch of the attachment path. -/
private theorem prefix_prism_ends [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (p : List V) (f₁ pk : V) (hp : IsPathFrom G p f₁ pk)
    (hpOut : ∀ x ∈ p, x ∉ staircaseVertices A C B R₀)
    (i : ℕ) (hi : i < p.length)
    (hmin : ∀ (j : ℕ) (hj : j < p.length), j < i →
      ∀ z ∈ B ∪ C, ¬ G.Adj (p[j]'hj) z)
    (hnoR₀ : ∀ x ∈ p.take (i + 1), ∀ r ∈ R₀, ¬ G.Adj x r)
    (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V)
    (hstep : IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂)
    (y : V) (hyR₁ : y ∈ R₁) (hya₁ : y ≠ a₁)
    (hiy : G.Adj (p[i]'hi) y)
    (hAComplete : VertexComplete G f₁ A) :
    0 < i ∧ G.Adj (p[i]'hi) b₁ ∧ G.Adj (p[i]'hi) b₂ := by
  classical
  let L : List V := p.take (i + 1)
  let D : Set V := {x : V | x ∈ L}
  let KP : Set V := {x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂} ∪ {x : V | x ∈ R₀}
  have hLp : IsPathFrom G L f₁ (p[i]'hi) := by
    simpa [L] using isPathFrom_take_to_index hp i hi
  have hf₁L : f₁ ∈ L := Workspace.ProofLemmas.PathBasics.head_mem hLp.2.1
  have hpiL : p[i]'hi ∈ L := Workspace.ProofLemmas.PathBasics.getLast_mem hLp.2.2
  have hDconn : ConnectedSet G D :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hLp.1
  have hform : FormPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ :=
    Workspace.ProofLemmas.PrismFromBanisterAndStep.formPrism_of_banister_and_step hK.2.1 hstep
  have hR₁S : ∀ x ∈ R₁, x ∈ A ∪ B ∪ C := rung_mem_strip hstep.1
  have hR₂S : ∀ x ∈ R₂, x ∈ A ∪ B ∪ C := rung_mem_strip hstep.2.1
  have hDK : D ⊆ KPᶜ := by
    intro x hx
    change x ∉ ({x : V | x ∈ R₁} ∪ {x : V | x ∈ R₂} ∪ {x : V | x ∈ R₀})
    rintro ((hxR₁ | hxR₂) | hxR₀)
    · exact hpOut x (List.take_subset _ _ hx) (Or.inr (hR₁S x hxR₁))
    · exact hpOut x (List.take_subset _ _ hx) (Or.inr (hR₂S x hxR₂))
    · exact hpOut x (List.take_subset _ _ hx) (Or.inl hxR₀)
  have ha₁R₁ := Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1
  have hb₁R₁ := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
  have ha₂R₂ := Workspace.ProofLemmas.PathBasics.head_mem hstep.2.1.1.2.1
  have hb₂R₂ := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2
  have ha₀R₀ := Workspace.ProofLemmas.PathBasics.head_mem hK.2.1.1.2.1
  have hb₀R₀ := Workspace.ProofLemmas.PathBasics.getLast_mem hK.2.1.1.2.2
  have att {z x : V} (hz : z ∈ KP) (hx : x ∈ D) (hzx : G.Adj z x) :
      z ∈ attachments G D KP := ⟨hz, x, hx, hzx⟩
  have ha₁att : a₁ ∈ attachments G D KP :=
    att (Or.inl (Or.inl ha₁R₁)) hf₁L (hAComplete a₁ hstep.1.2.1).symm
  have ha₂att : a₂ ∈ attachments G D KP :=
    att (Or.inl (Or.inr ha₂R₂)) hf₁L (hAComplete a₂ hstep.2.1.2.1).symm
  have hyatt : y ∈ attachments G D KP := att (Or.inl (Or.inl hyR₁)) hpiL hiy.symm
  have hnonlocal : ¬ LocalForPrism ![a₁, a₂, a₀] ![b₁, b₂, b₀]
      R₁ R₂ R₀ (attachments G D KP) := by
    rintro (hloc | hloc | hloc | hloc | hloc)
    · exact hstep.2.2.1 a₂ (hloc ha₂att) ha₂R₂
    · exact hstep.2.2.1 a₁ ha₁R₁ (hloc ha₁att)
    · exact hK.2.1.2.1 a₁ (hloc ha₁att) (Or.inl (Or.inl hstep.1.2.1))
    · have hytri := hloc hyatt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hytri
      rcases hytri with hya₁' | hya₂ | hya₀
      · exact hya₁ hya₁'
      · exact hstep.2.2.1 y hyR₁ (hya₂ ▸ ha₂R₂)
      · exact hK.2.1.2.1 a₀ ha₀R₀ (hya₀ ▸ hR₁S y hyR₁)
    · have ha₁tri := hloc ha₁att
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, Set.mem_insert_iff,
        Set.mem_singleton_iff] at ha₁tri
      rcases ha₁tri with ha₁b₁ | ha₁b₂ | ha₁b₀
      · exact Set.disjoint_left.mp hK.1.1.1 hstep.1.2.1 (ha₁b₁ ▸ hstep.1.2.2.1)
      · exact Set.disjoint_left.mp hK.1.1.1 hstep.1.2.1 (ha₁b₂ ▸ hstep.2.1.2.2.1)
      · exact hK.2.1.2.1 b₀ hb₀R₀ (ha₁b₀.symm ▸ Or.inl (Or.inl hstep.1.2.1))
  have hnoThird : ∀ z ∈ attachments G D KP, z ∉ R₀ := by
    intro z hz hzR₀
    obtain ⟨-, x, hxD, hzx⟩ := hz
    exact hnoR₀ x hxD z hzR₀ hzx.symm
  have hK4' : ¬ ∃ (n : ℕ) (H : SimpleGraph (Fin n)) (K' : Set V),
      IsAppearance G (⊤ : SimpleGraph (Fin 4)) H K' ∧
        NondegenerateAppearance (⊤ : SimpleGraph (Fin 4)) H := by
    rintro ⟨n, H, K', happ, -⟩
    exact hK4 ⟨n, H, K', happ⟩
  have hmaj : IsEvenPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] R₁ R₂ R₀ →
      ∀ z ∈ D, ¬ MajorForPrism G ![a₁, a₂, a₀] ![b₁, b₂, b₀] z := by
    intro hev
    exact (hNoEvenPrism ⟨![a₁, a₂, a₀], ![b₁, b₂, b₀], R₁, R₂, R₀, hev⟩).elim
  have h104 := Workspace.Statements.S10.SPGT.thm_10_4 G hG hK4'
    ![a₁, a₂, a₀] ![b₁, b₂, b₀] ![R₁, R₂, R₀] KP D hform
    (by simp [KP]) hDK hDconn hmaj hnonlocal hnoThird
  have endpoint (b : V) (hbB : b ∈ B) (hbatt : b ∈ attachments G D KP) :
      G.Adj (p[i]'hi) b := by
    obtain ⟨-, x, hxD, hbx⟩ := hbatt
    obtain ⟨j, hjtake, hjx⟩ := List.mem_take_iff_getElem.mp hxD
    have hj : j < p.length := by omega
    have hji : j ≤ i := by omega
    have hjeq : j = i := by
      by_contra hne
      exact hmin j hj (by omega) b (Or.inl hbB) (hjx ▸ hbx.symm)
    have heq : p[j]'hj = p[i]'hi := getElem_eq_of_index_eq p hj hi hjeq
    rw [← heq, hjx]
    exact hbx.symm
  have hb₁att : b₁ ∈ attachments G D KP := by rw [h104.2]; simp
  have hb₂att : b₂ ∈ attachments G D KP := by rw [h104.2]; simp
  have hipos : 0 < i := by
    by_contra hnot
    have hi0 : i = 0 := by omega
    subst i
    obtain ⟨x, hxD, z, hzD, hxz⟩ := h104.1
    obtain ⟨j, hj, hjx⟩ := List.mem_take_iff_getElem.mp hxD
    obtain ⟨k, hk, hkz⟩ := List.mem_take_iff_getElem.mp hzD
    have hjk : j = k := by omega
    exact hxz (hjx.symm.trans (getElem_eq_of_index_eq p (by omega) (by omega) hjk) |>.trans hkz)
  exact ⟨hipos, endpoint b₁ hstep.1.2.2.1 hb₁att,
    endpoint b₂ hstep.2.1.2.2.1 hb₂att⟩

/-- The two odd-hole comparisons which make the last vertex `B`-complete. -/
private theorem last_vertex_BComplete [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃)
    (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (f : List V) (f₁ fk : V) (hf : IsPathFrom G f f₁ fk) (hlen : 2 ≤ f.length)
    (hfOut : ∀ x ∈ f, x ∉ staircaseVertices A C B R₀)
    (hAComplete : VertexComplete G f₁ A)
    (hbeforeBC : ∀ x ∈ f, x ≠ fk → ∀ y ∈ B ∪ C, ¬ G.Adj x y)
    (htailAC : ∀ x ∈ f, x ≠ f₁ → ∀ y ∈ A ∪ C, ¬ G.Adj x y)
    (hfkB : ∃ b ∈ B, G.Adj fk b)
    (hfkb₀ : G.Adj fk b₀)
    (hb₀only : ∀ x ∈ f, G.Adj x b₀ → x = fk) :
    VertexComplete G fk B := by
  classical
  have hS := hK.1
  have hban := hK.2.1
  have hf₁mem := Workspace.ProofLemmas.PathBasics.head_mem hf.2.1
  have hfkmem := Workspace.ProofLemmas.PathBasics.getLast_mem hf.2.2
  have hf₁fk : f₁ ≠ fk := by
    apply Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hf
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
    omega
  intro b hbB
  by_contra hfknotb
  let X : Set V := {z : V | z ∈ B ∧ G.Adj fk z}
  let Y : Set V := {z : V | z ∈ B ∧ ¬ G.Adj fk z}
  have hXY : X ∪ Y = B := by
    ext z
    simp only [X, Y, Set.mem_union, Set.mem_setOf_eq]
    tauto
  have hdXY : Disjoint X Y := Set.disjoint_left.2 (by
    intro z hzX hzY
    exact hzY.2 hzX.2)
  have hXne : X.Nonempty := by
    obtain ⟨z, hzB, hfkz⟩ := hfkB
    exact ⟨z, hzB, hfkz⟩
  have hYne : Y.Nonempty := ⟨b, hbB, hfknotb⟩
  obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep, hendX, hendY⟩ :=
    hS.2.2.2.2 X Y (Or.inr hXY) hdXY hXne hYne
  have hb₁X : b₁ ∈ X := by
    rcases hendX with ha₁X | hb₁X
    · exact (Set.disjoint_left.mp hS.1.1 hstep.1.2.1 ha₁X.1).elim
    · exact hb₁X
  have hb₂Y : b₂ ∈ Y := by
    rcases hendY with ha₂Y | hb₂Y
    · exact (Set.disjoint_left.mp hS.1.1 hstep.2.1.2.1 ha₂Y.1).elim
    · exact hb₂Y
  have hpr := Workspace.ProofLemmas.StaircaseStepBanisterOddPrism.staircaseStepBanisterOddPrism
    G A C B a₀ b₀ a₁ b₁ a₂ b₂ R₀ R₁ R₂ hK hstep hG hNoEvenPrism
  have hR₁S := rung_mem_strip hstep.1
  have hR₂S := rung_mem_strip hstep.2.1
  have ha₁R₁ := Workspace.ProofLemmas.PathBasics.head_mem hstep.1.1.2.1
  have hb₁R₁ := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.1.1.2.2
  have ha₂R₂ := Workspace.ProofLemmas.PathBasics.head_mem hstep.2.1.1.2.1
  have hb₂R₂ := Workspace.ProofLemmas.PathBasics.getLast_mem hstep.2.1.1.2.2
  have hdisj₁ : ∀ x ∈ f, x ∉ R₁ := by
    intro x hxf hxR
    exact hfOut x hxf (Or.inr (hR₁S x hxR))
  have hcross₁ : ∀ x ∈ f, ∀ y ∈ R₁.reverse,
      (G.Adj x y ↔ (x = fk ∧ y = b₁) ∨ (x = f₁ ∧ y = a₁)) := by
    intro x hxf y hyrev
    have hy := List.mem_reverse.mp hyrev
    constructor
    · intro hxy
      rcases hR₁S y hy with (hyA | hyB) | hyC
      · have hya : y = a₁ := hstep.1.2.2.2.1 y hy hyA
        have hxf₁ : x = f₁ := by
          by_contra hxne
          exact htailAC x hxf hxne y (Or.inl hyA) hxy
        exact Or.inr ⟨hxf₁, hya⟩
      · have hyb : y = b₁ := hstep.1.2.2.2.2.1 y hy hyB
        have hxfk : x = fk := by
          by_contra hxne
          exact hbeforeBC x hxf hxne y (Or.inl hyB) hxy
        exact Or.inl ⟨hxfk, hyb⟩
      · by_cases hxfk : x = fk
        · exact (htailAC x hxf (hxfk ▸ hf₁fk.symm) y (Or.inr hyC) hxy).elim
        · exact (hbeforeBC x hxf hxfk y (Or.inr hyC) hxy).elim
    · rintro (hc | hc)
      · exact hc.1 ▸ hc.2 ▸ hb₁X.2
      · exact hc.1 ▸ hc.2 ▸ hAComplete a₁ hstep.1.2.1
  have hhole₁ : IsHoleList G (f ++ R₁.reverse) :=
    Workspace.ProofLemmas.PathGlue.glue_hole hf
      (Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hstep.1.1)
      (fun x hx hxR => hdisj₁ x hx (List.mem_reverse.mp hxR)) hcross₁ (by
        rw [List.length_reverse]
        have hRlen : 2 ≤ R₁.length := by
          simpa only [Matrix.cons_val_one, Matrix.head_cons] using
            (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length
              (a := ![a₀, a₁, a₂]) (b := ![b₀, b₁, b₂])
              (R := ![R₀, R₁, R₂]) hpr.1 1)
        simpa using (show 4 ≤ f.length + R₁.length by omega))
  have hevenHole₁ := hG.1 _ hhole₁
  simp only [holeLength, List.length_append, List.length_reverse] at hevenHole₁
  have hR₁len : R₁.length = pathLength R₁ + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hstep.1.1.1
  have hR₁even : Even R₁.length := by
    rw [hR₁len]
    exact hpr.2.2.1.add_odd odd_one
  have hfeven : Even f.length := (Nat.even_add.mp hevenHole₁).mpr hR₁even

  have hR₂rev : IsPathFrom G R₂.reverse b₂ a₂ :=
    Workspace.ProofLemmas.PathBasics.isPathFrom_reverse hstep.2.1.1
  have hb₀notR₂ : b₀ ∉ R₂ := by
    intro hbR
    exact hban.2.1 b₀ (Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2)
      (hR₂S b₀ hbR)
  have hb₀R₂ : ∀ y ∈ R₂.reverse, (G.Adj b₀ y ↔ y = b₂) := by
    intro y hyrev
    have hy := List.mem_reverse.mp hyrev
    constructor
    · intro hby
      rcases hR₂S y hy with (hyA | hyB) | hyC
      · exact (hban.2.2.2.1.2.2 y (Or.inl hyA) hby).elim
      · exact hstep.2.1.2.2.2.2.1 y hy hyB
      · exact (hban.2.2.2.1.2.2 y (Or.inr hyC) hby).elim
    · intro hyb₂
      rw [hyb₂]
      exact hban.2.2.2.1.2.1 b₂ hstep.2.1.2.2.1
  have hQ : IsPathFrom G (b₀ :: R₂.reverse) b₀ a₂ :=
    Workspace.ProofLemmas.Thm121C3PathCons.isPathFrom_cons hR₂rev
      (by simpa using hb₀notR₂) hb₀R₂
  have hdisj₂ : ∀ x ∈ f, x ∉ b₀ :: R₂.reverse := by
    intro x hxf hxQ
    rcases List.mem_cons.mp hxQ with hxb₀ | hxR₂
    · exact hfOut x hxf (Or.inl (hxb₀ ▸
        Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2))
    · exact hfOut x hxf (Or.inr (hR₂S x (List.mem_reverse.mp hxR₂)))
  have hcross₂ : ∀ x ∈ f, ∀ y ∈ b₀ :: R₂.reverse,
      (G.Adj x y ↔ (x = fk ∧ y = b₀) ∨ (x = f₁ ∧ y = a₂)) := by
    intro x hxf y hyQ
    constructor
    · intro hxy
      rcases List.mem_cons.mp hyQ with hyb₀ | hyrev
      · exact Or.inl ⟨hb₀only x hxf (hyb₀ ▸ hxy), hyb₀⟩
      · have hy := List.mem_reverse.mp hyrev
        rcases hR₂S y hy with (hyA | hyB) | hyC
        · have hya : y = a₂ := hstep.2.1.2.2.2.1 y hy hyA
          have hxf₁ : x = f₁ := by
            by_contra hxne
            exact htailAC x hxf hxne y (Or.inl hyA) hxy
          exact Or.inr ⟨hxf₁, hya⟩
        · have hyb : y = b₂ := hstep.2.1.2.2.2.2.1 y hy hyB
          by_cases hxfk : x = fk
          · exact (hb₂Y.2 (hxfk ▸ hyb ▸ hxy)).elim
          · exact (hbeforeBC x hxf hxfk y (Or.inl hyB) hxy).elim
        · by_cases hxfk : x = fk
          · exact (htailAC x hxf (hxfk ▸ hf₁fk.symm) y (Or.inr hyC) hxy).elim
          · exact (hbeforeBC x hxf hxfk y (Or.inr hyC) hxy).elim
    · rintro (hc | hc)
      · exact hc.1 ▸ hc.2 ▸ hfkb₀
      · exact hc.1 ▸ hc.2 ▸ hAComplete a₂ hstep.2.1.2.1
  have hhole₂ : IsHoleList G (f ++ (b₀ :: R₂.reverse)) :=
    Workspace.ProofLemmas.PathGlue.glue_hole hf hQ hdisj₂ hcross₂ (by
      have hRlen : 2 ≤ R₂.length := by
        simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          (Workspace.ProofLemmas.HyperprismFromPrism.formPrism_two_le_length
            (a := ![a₀, a₁, a₂]) (b := ![b₀, b₁, b₂])
            (R := ![R₀, R₁, R₂]) hpr.1 2)
      simp only [List.length_cons, List.length_reverse]
      omega)
  have hevenHole₂ := hG.1 _ hhole₂
  simp only [holeLength, List.length_append, List.length_cons,
    List.length_reverse] at hevenHole₂
  have hR₂len : R₂.length = pathLength R₂ + 1 :=
    Workspace.ProofLemmas.PathBasics.length_eq_pathLength_add_one hstep.2.1.1.1
  have hR₂even : Even R₂.length := by
    rw [hR₂len]
    exact hpr.2.2.2.add_odd odd_one
  have hQodd : Odd (1 + R₂.length) := odd_one.add_even hR₂even
  have hQeven : Even (1 + R₂.length) := by
    simpa [Nat.add_comm] using (Nat.even_add.mp hevenHole₂).mp hfeven
  exact (Nat.not_even_iff_odd.mpr hQodd hQeven).elim

/-- An A-complete first vertex of a minimal nonlocal staircase-attachment path
forces one of the three outcomes of theorem 12.2. -/
theorem aCompleteStaircaseAttachmentPathForcesOutcome
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (F_orig F : Set V) (f : List V) (f₁ fk : V)
    (hBerge : Berge G)
    (hK4 : ¬ Appears G (⊤ : SimpleGraph (Fin 4)))
    (hNoEvenPrism :
      ¬ ∃ (alpha beta : Fin 3 → V) (P₁ P₂ P₃ : List V),
        IsEvenPrism G alpha beta P₁ P₂ P₃)
    (hMaximal : MaximalStaircase G A C B a₀ R₀ b₀)
    (hFsub : F ⊆ F_orig)
    (hFoutside : F ⊆ (staircaseVertices A C B R₀)ᶜ)
    (hFconn : ConnectedSet G F)
    (hFnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G F (staircaseVertices A C B R₀)))
    (hFminimal : ∀ D : Set V, D ⊂ F → ConnectedSet G D →
      LocalForStaircase A C B a₀ R₀ b₀
        (attachments G D (staircaseVertices A C B R₀)))
    (hFvertices : F = {v : V | v ∈ f})
    (hPath : IsPathFrom G f f₁ fk)
    (hLength : 2 ≤ f.length)
    (hLeftAttach : ∃ u ∈ A ∪ C, G.Adj f₁ u)
    (hLeftUnique : ∀ x ∈ F, (∃ u ∈ A ∪ C, G.Adj x u) → x = f₁)
    (hRungAttach : ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj fk r)
    (hRungUnique : ∀ x ∈ F, (∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r) → x = fk)
    (hAComplete : VertexComplete G f₁ A) :
    (∃ w ∈ F_orig, MajorForStaircase G A C B a₀ R₀ b₀ w) ∨
    (∃ (u v : V) (R : List V),
      (∀ w ∈ R, w ∈ F_orig) ∧
      IsBanister G A C B u R v ∧
      Anticomplete G {w : V | w ∈ R} {w : V | w ∈ R₀}) ∨
    (∃ (u v : V) (R : List V),
      (∀ w ∈ R, w ∈ F_orig) ∧
      IsPathFrom G R u v ∧
      ((IsLeftStar G A C B u ∧
          (∃ x ∈ R₀, x ≠ a₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)) ∨
        (IsRightStar G A C B u ∧
          (∃ x ∈ R₀, x ≠ b₀ ∧ G.Adj v x) ∧
          Anticomplete G {w : V | w ∈ R ∧ w ≠ u} (A ∪ B ∪ C)))) := by
  classical
  have hK : IsStaircase G A C B a₀ R₀ b₀ := hMaximal.1
  have hS : StepConnected G A C B := hK.1
  have hban : IsBanister G A C B a₀ R₀ b₀ := hK.2.1
  have hf₁mem : f₁ ∈ f := Workspace.ProofLemmas.PathBasics.head_mem hPath.2.1
  have hfkmem : fk ∈ f := Workspace.ProofLemmas.PathBasics.getLast_mem hPath.2.2
  have hf₁F : f₁ ∈ F := by rw [hFvertices]; exact hf₁mem
  have hfkF : fk ∈ F := by rw [hFvertices]; exact hfkmem
  have hf₁fk : f₁ ≠ fk := by
    apply Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hPath
    rw [Workspace.ProofLemmas.PathBasics.pathLength_eq]
    omega
  have ha₀b₀ : a₀ ≠ b₀ := by
    apply Workspace.ProofLemmas.PathBasics.isPathFrom_ends_ne hban.1
    exact le_trans (by decide : 1 ≤ 3) hK.2.2
  have hfOut : ∀ x ∈ f, x ∉ staircaseVertices A C B R₀ := by
    intro x hx
    exact hFoutside (by rw [hFvertices]; exact hx)
  have hfStripOut : ∀ x ∈ f, x ∉ A ∪ B ∪ C := by
    intro x hx hxs
    exact hfOut x hx (Or.inr hxs)
  by_cases hBC : ∃ x ∈ F, ∃ y ∈ B ∪ C, G.Adj x y
  · have hBCf : ∃ x ∈ f, ∃ y ∈ B ∪ C, G.Adj x y := by
      obtain ⟨x, hxF, y, hy, hxy⟩ := hBC
      exact ⟨x, by simpa [hFvertices] using hxF, y, hy, hxy⟩
    obtain ⟨i, hi, yi, hyiBC, hfiyi, hmin⟩ := exists_min_adj_to_set G f (B ∪ C) hBCf
    let L : List V := f.take (i + 1)
    have hLpath : IsPathFrom G L f₁ (f[i]'hi) := by
      simpa [L] using isPathFrom_take_to_index hPath i hi
    have hLmem : ∀ x ∈ L, x ∈ f := fun x hx => List.take_subset _ _ hx
    by_cases hnoR₀ : ∀ x ∈ L, ∀ r ∈ R₀, ¬ G.Adj x r
    · have hyiS : yi ∈ A ∪ B ∪ C := hyiBC.elim
          (fun h => Or.inl (Or.inr h)) Or.inr
      obtain ⟨a₁, R₁, b₁, a₂, R₂, b₂, hstep₀, hyirungs⟩ :=
        hS.2.2.2.1 yi hyiS
      have first_step : ∃ (a₁ b₁ a₂ b₂ : V) (R₁ R₂ : List V),
          IsStep G A C B a₁ R₁ b₁ a₂ R₂ b₂ ∧ yi ∈ R₁ := by
        rcases hyirungs with hyiR₁ | hyiR₂
        · exact ⟨a₁, b₁, a₂, b₂, R₁, R₂, hstep₀, hyiR₁⟩
        · exact ⟨a₂, b₂, a₁, b₁, R₂, R₁, step_symm hstep₀, hyiR₂⟩
      obtain ⟨a₁, b₁, a₂, b₂, R₁, R₂, hstep, hyiR₁⟩ := first_step
      have hyinea₁ : yi ≠ a₁ := by
        intro hyia
        rcases hyiBC with hyiB | hyiC
        · exact Set.disjoint_left.mp hS.1.1 hstep.1.2.1 (hyia ▸ hyiB)
        · exact Set.disjoint_left.mp hS.1.2.1 hstep.1.2.1 (hyia ▸ hyiC)
      obtain ⟨hipos, hfib₁, hfib₂⟩ := prefix_prism_ends G hBerge hK4 hNoEvenPrism
        A C B a₀ b₀ R₀ hK f f₁ fk hPath hfOut i hi hmin (by simpa [L] using hnoR₀)
        a₁ b₁ a₂ b₂ R₁ R₂ hstep yi hyiR₁ hyinea₁ hfiyi hAComplete
      have hfiB : VertexComplete G (f[i]'hi) B := by
        intro b hbB
        by_contra hfib
        let X : Set V := {z : V | z ∈ B ∧ G.Adj (f[i]'hi) z}
        let Y : Set V := {z : V | z ∈ B ∧ ¬ G.Adj (f[i]'hi) z}
        have hXY : X ∪ Y = B := by
          ext z
          simp only [X, Y, Set.mem_union, Set.mem_setOf_eq]
          tauto
        have hdXY : Disjoint X Y := Set.disjoint_left.2 (by
          intro z hzX hzY
          exact hzY.2 hzX.2)
        have hXne : X.Nonempty := ⟨b₁, hstep.1.2.2.1, hfib₁⟩
        have hYne : Y.Nonempty := ⟨b, hbB, hfib⟩
        obtain ⟨c₁, Q₁, d₁, c₂, Q₂, d₂, hst, hendX, hendY⟩ :=
          hS.2.2.2.2 X Y (Or.inr hXY) hdXY hXne hYne
        have hd₁X : d₁ ∈ X := by
          rcases hendX with hc₁X | hd₁X
          · exact (Set.disjoint_left.mp hS.1.1 hst.1.2.1 hc₁X.1).elim
          · exact hd₁X
        have hd₂Y : d₂ ∈ Y := by
          rcases hendY with hc₂Y | hd₂Y
          · exact (Set.disjoint_left.mp hS.1.1 hst.2.1.2.1 hc₂Y.1).elim
          · exact hd₂Y
        have hd₁R₁ := Workspace.ProofLemmas.PathBasics.getLast_mem hst.1.1.2.2
        have hc₁d₁ : c₁ ≠ d₁ := by
          intro hcd
          exact Set.disjoint_left.mp hS.1.1 hst.1.2.1 (hcd ▸ hst.1.2.2.1)
        have hends := prefix_prism_ends G hBerge hK4 hNoEvenPrism
          A C B a₀ b₀ R₀ hK f f₁ fk hPath hfOut i hi hmin (by simpa [L] using hnoR₀)
          c₁ d₁ c₂ d₂ Q₁ Q₂ hst d₁ hd₁R₁ hc₁d₁.symm hd₁X.2 hAComplete
        exact hd₂Y.2 hends.2.2
      have hzero : f[0]'(by omega) = f₁ :=
        Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hPath.2.1 (by omega)
      have hfinef₁ : f[i]'hi ≠ f₁ := by
        rw [← hzero]
        exact Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hPath.1 hi (by omega) (by omega)
      have hfiF : f[i]'hi ∈ F := by rw [hFvertices]; exact List.getElem_mem hi
      have hf₁antiBC : VertexAnticomplete G f₁ (B ∪ C) := by
        intro z hzBC hf₁z
        exact hmin 0 (by omega) hipos z hzBC (hzero ▸ hf₁z)
      have hfiantiAC : VertexAnticomplete G (f[i]'hi) (A ∪ C) := by
        intro z hzAC hfiz
        exact hfinef₁ (hLeftUnique (f[i]'hi) hfiF ⟨z, hzAC, hfiz⟩)
      have hLint : Anticomplete G {x : V | x ∈ interior L} (A ∪ B ∪ C) := by
        intro x hx y hy hxy
        have hxdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hLpath).1 hx
        have hxF : x ∈ F := by rw [hFvertices]; exact hLmem x hxdata.1
        rcases hy with (hyA | hyB) | hyC
        · exact hxdata.2.1 (hLeftUnique x hxF ⟨y, Or.inl hyA, hxy⟩)
        · obtain ⟨j, hjtake, hjx⟩ := List.mem_take_iff_getElem.mp hxdata.1
          have hj : j < f.length := by omega
          have hji : j < i := by
            by_contra hn
            have hjeq : j = i := by omega
            exact hxdata.2.2 (hjx.symm.trans (getElem_eq_of_index_eq f hj hi hjeq))
          exact hmin j hj hji y (Or.inl hyB) (hjx ▸ hxy)
        · exact hxdata.2.1 (hLeftUnique x hxF ⟨y, Or.inr hyC, hxy⟩)
      have hbanL : IsBanister G A C B f₁ L (f[i]'hi) := by
        refine ⟨hLpath, ?_, ?_, ?_, hLint⟩
        · exact fun x hx => hfStripOut x (hLmem x hx)
        · exact ⟨hfStripOut f₁ hf₁mem, hAComplete, hf₁antiBC⟩
        · exact ⟨hfStripOut (f[i]'hi) (List.getElem_mem hi), hfiB, hfiantiAC⟩
      refine Or.inr (Or.inl ⟨f₁, f[i]'hi, L, ?_, hbanL, ?_⟩)
      · intro x hx
        exact hFsub (by rw [hFvertices]; exact hLmem x hx)
      · intro x hx r hr hxr
        exact hnoR₀ x hx r hr hxr
    · push Not at hnoR₀
      obtain ⟨x₀, hx₀L, r₀, hr₀R, hx₀r⟩ := hnoR₀
      have hilast : i = f.length - 1 := by
        by_contra hine
        have hilt : i < f.length - 1 := by omega
        let D : Set V := {x : V | x ∈ L}
        have hDsub : D ⊆ F := by
          intro x hx
          rw [hFvertices]
          exact hLmem x hx
        have hlast : f[f.length - 1]'(by omega) = fk :=
          Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPath.2.2 (by omega)
        have hfknotD : fk ∉ D := by
          intro hfkD
          obtain ⟨j, hjtake, hjfk⟩ := List.mem_take_iff_getElem.mp hfkD
          have hj : j < f.length := by omega
          have heq : j = f.length - 1 := hPath.1.2.1.getElem_inj_iff.mp (hjfk.trans hlast.symm)
          omega
        have hDproper : D ⊂ F := ⟨hDsub, fun hFD => hfknotD (hFD hfkF)⟩
        have hDconn : ConnectedSet G D :=
          Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hLpath.1
        have hDlocal := hFminimal D hDproper hDconn
        by_cases hrb : r₀ = b₀
        · obtain ⟨a, haA⟩ := hS.2.1.1
          exact (left_obstruction_nonlocal G A C B a₀ b₀ R₀ D hK
            ⟨f₁, Workspace.ProofLemmas.PathBasics.head_mem hLpath.2.1,
              a, Or.inl haA, hAComplete a haA⟩
            ⟨x₀, hx₀L, r₀, hr₀R, hrb ▸ ha₀b₀.symm, hx₀r⟩) hDlocal
        · exact (right_obstruction_nonlocal G A C B a₀ b₀ R₀ D hK
            ⟨f[i]'hi, Workspace.ProofLemmas.PathBasics.getLast_mem hLpath.2.2,
              yi, hyiBC, hfiyi⟩
            ⟨x₀, hx₀L, r₀, hr₀R, hrb, hx₀r⟩) hDlocal
      have hlast : f[f.length - 1]'(by omega) = fk :=
        Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hPath.2.2 (by omega)
      have hifk : f[i]'hi = fk :=
        (getElem_eq_of_index_eq f hi (by omega) hilast).trans hlast
      have hfkYi : G.Adj fk yi := by simpa [hifk] using hfiyi
      have hbeforeBC : ∀ x ∈ f, x ≠ fk → ∀ y ∈ B ∪ C, ¬ G.Adj x y := by
        intro x hx hxfk y hyBC hxy
        obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hx
        have hji : j < i := by
          by_contra hn
          have hjeq : j = i := by omega
          apply hxfk
          exact hjx.symm.trans (getElem_eq_of_index_eq f hj hi hjeq) |>.trans hifk
        exact hmin j hj hji y hyBC (hjx ▸ hxy)
      have hmemTail : ∀ z : V, z ∈ f.tail ↔ z ∈ f ∧ z ≠ f₁ := by
        intro z
        rcases f with _ | ⟨c, t⟩
        · simp at hLength
        · have hc : c = f₁ := by simpa using hPath.2.1
          have hn : f₁ ∉ t := by
            have := (List.nodup_cons.mp hPath.1.2.1).1
            simpa [hc] using this
          simp only [List.tail_cons, List.mem_cons]
          constructor
          · intro hzt
            exact ⟨Or.inr hzt, fun hzf₁ => hn (hzf₁ ▸ hzt)⟩
          · rintro ⟨hz | hz, hne⟩
            · exact (hne (hz.trans hc)).elim
            · exact hz
      let T : Set V := {z : V | z ∈ f.tail}
      have hTsub : T ⊆ F := by
        intro z hz
        rw [hFvertices]
        exact (hmemTail z).1 hz |>.1
      have hf₁notT : f₁ ∉ T := fun h => (hmemTail f₁).1 h |>.2 rfl
      have hTproper : T ⊂ F := ⟨hTsub, fun hFT => hf₁notT (hFT hf₁F)⟩
      have hTconn : ConnectedSet G T := by
        apply Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList
        simpa [T, List.drop_one] using
          (Workspace.ProofLemmas.PathBasics.isPathList_drop hPath.1 (k := 1) (by omega))
      have hTlocal := hFminimal T hTproper hTconn
      have hfkT : fk ∈ T := (hmemTail fk).2 ⟨hfkmem, hf₁fk.symm⟩
      have htailNoR : ∀ x ∈ f, x ≠ f₁ → ∀ r ∈ R₀, r ≠ b₀ → ¬ G.Adj x r := by
        intro x hxf hxf₁ r hrR hrb hxr
        have hxT : x ∈ T := (hmemTail x).2 ⟨hxf, hxf₁⟩
        exact (right_obstruction_nonlocal G A C B a₀ b₀ R₀ T hK
          ⟨fk, hfkT, yi, hyiBC, hfkYi⟩ ⟨x, hxT, r, hrR, hrb, hxr⟩) hTlocal
      have hfkb₀ : G.Adj fk b₀ := by
        obtain ⟨r, hrR, hrne, hfkr⟩ := hRungAttach
        have hrb : r = b₀ := by
          by_contra hne
          exact htailNoR fk hfkmem hf₁fk.symm r hrR hne hfkr
        simpa [hrb] using hfkr
      have htailAC : ∀ x ∈ f, x ≠ f₁ → ∀ y ∈ A ∪ C, ¬ G.Adj x y := by
        intro x hxf hxf₁ y hyAC hxy
        have hxT : x ∈ T := (hmemTail x).2 ⟨hxf, hxf₁⟩
        exact (left_obstruction_nonlocal G A C B a₀ b₀ R₀ T hK
          ⟨x, hxT, y, hyAC, hxy⟩
          ⟨fk, hfkT, b₀, Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2,
            ha₀b₀.symm, hfkb₀⟩) hTlocal
      have hyiB : yi ∈ B := by
        rcases hyiBC with hyiB | hyiC
        · exact hyiB
        · exact (htailAC fk hfkmem hf₁fk.symm yi (Or.inr hyiC) hfkYi).elim
      have hb₀only : ∀ x ∈ f, G.Adj x b₀ → x = fk := by
        intro x hxf hxb
        exact hRungUnique x (by rw [hFvertices]; exact hxf)
          ⟨b₀, Workspace.ProofLemmas.PathBasics.getLast_mem hban.1.2.2,
            ha₀b₀.symm, hxb⟩
      have hfkB : VertexComplete G fk B := last_vertex_BComplete G hBerge hNoEvenPrism
        A C B a₀ b₀ R₀ hK f f₁ fk hPath hLength hfOut hAComplete hbeforeBC htailAC
        ⟨yi, hyiB, hfkYi⟩ hfkb₀ hb₀only
      have hf₁antiBC : VertexAnticomplete G f₁ (B ∪ C) :=
        hbeforeBC f₁ hf₁mem hf₁fk
      have hfkantiAC : VertexAnticomplete G fk (A ∪ C) :=
        htailAC fk hfkmem hf₁fk.symm
      have hfint : Anticomplete G {x : V | x ∈ interior f} (A ∪ B ∪ C) := by
        intro x hx y hy hxy
        have hxdata := (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hPath).1 hx
        rcases hy with (hyA | hyB) | hyC
        · exact htailAC x hxdata.1 hxdata.2.1 y (Or.inl hyA) hxy
        · exact hbeforeBC x hxdata.1 hxdata.2.2 y (Or.inl hyB) hxy
        · exact htailAC x hxdata.1 hxdata.2.1 y (Or.inr hyC) hxy
      have hbanF : IsBanister G A C B f₁ f fk :=
        ⟨hPath, hfStripOut,
          ⟨hfStripOut f₁ hf₁mem, hAComplete, hf₁antiBC⟩,
          ⟨hfStripOut fk hfkmem, hfkB, hfkantiAC⟩, hfint⟩
      have hdisjR₀f : ∀ z ∈ R₀, z ∉ f := by
        intro z hzR hzf
        exact hfOut z hzf (Or.inl hzR)
      have hvonly : ∀ z ∈ R₀, (G.Adj z fk ↔ z = b₀) := by
        intro z hzR
        constructor
        · intro hzk
          by_contra hzb
          exact htailNoR fk hfkmem hf₁fk.symm z hzR hzb hzk.symm
        · rintro rfl
          exact hfkb₀.symm
      have hnot_a₀fk : ¬ G.Adj a₀ fk := by
        intro hafk
        exact htailNoR fk hfkmem hf₁fk.symm a₀
          (Workspace.ProofLemmas.PathBasics.head_mem hban.1.2.1) ha₀b₀ hafk.symm
      have hnolink : ¬ ((({z : V | z ∈ R₀.tail} ∩ {z : V | z ∈ f.dropLast}).Nonempty) ∨
          ∃ p ∈ R₀.tail, ∃ q ∈ f.dropLast, G.Adj p q) := by
        rintro (hmeet | hedge)
        · obtain ⟨z, hzR, hzf⟩ := hmeet
          exact hdisjR₀f z
            ((Workspace.ProofLemmas.HyperprismRungStructure.mem_tail_iff_of_pathFrom hban.1).1 hzR |>.1)
            ((Workspace.ProofLemmas.HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hbanF.1).1 hzf |>.1)
        · obtain ⟨p, hpR, q, hqf, hpq⟩ := hedge
          have hpdata :=
            (Workspace.ProofLemmas.HyperprismRungStructure.mem_tail_iff_of_pathFrom hban.1).1 hpR
          have hqdata :=
            (Workspace.ProofLemmas.HyperprismRungStructure.mem_dropLast_iff_of_pathFrom hbanF.1).1 hqf
          exact hqdata.2 (hRungUnique q (by rw [hFvertices]; exact hqdata.1)
            ⟨p, hpdata.1, hpdata.2, hpq.symm⟩)
      have haonly : ∀ z ∈ f, (G.Adj a₀ z ↔ z = f₁) :=
        Workspace.ProofLemmas.Thm132BanisterAttachment.left_end_sees_exactly_left_end
          hBerge hNoEvenPrism hS hban hbanF hnot_a₀fk hvonly hnolink hdisjR₀f
      exact (Workspace.ProofLemmas.Thm132AdjoinBanister.attached_banister_contradicts_maximality
        hMaximal hbanF hdisjR₀f hvonly haonly hnolink).elim
  · push Not at hBC
    refine Or.inr (Or.inr ⟨f₁, fk, f, ?_, hPath, Or.inl ⟨?_, hRungAttach, ?_⟩⟩)
    · intro x hx
      exact hFsub (by rw [hFvertices]; exact hx)
    · exact ⟨hfStripOut f₁ hf₁mem, hAComplete,
        fun y hy => hBC f₁ hf₁F y hy⟩
    · intro x hx y hy hxy
      rcases hy with (hyA | hyB) | hyC
      · exact hx.2 (hLeftUnique x (by rw [hFvertices]; exact hx.1) ⟨y, Or.inl hyA, hxy⟩)
      · exact hBC x (by rw [hFvertices]; exact hx.1) y (Or.inl hyB) hxy
      · exact hx.2 (hLeftUnique x (by rw [hFvertices]; exact hx.1) ⟨y, Or.inr hyC, hxy⟩)

end Workspace.ProofLemmas.ACompleteStaircaseAttachmentPathForcesOutcome
