import Workspace.Types.Core
import Workspace.Types.Classes
import Workspace.Statements.S24.Thm_24_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.ConnectedSetUnionAttach

set_option autoImplicit false

namespace Workspace.Types.Thm245YCompleteWitnessFromTwentyFourFour

open Workspace.Types.Core.SPGT
open Workspace.Types.Classes.SPGT

theorem thm245YCompleteWitnessFromTwentyFourFour
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF11 G)
    (X Y : Set V)
    (hXY : Disjoint X Y)
    (hXne : X.Nonempty) (hYne : Y.Nonempty)
    (hX : AnticonnectedSet G X) (hY : AnticonnectedSet G Y)
    (hcomp : Complete G X Y)
    (p : List V) (p₁ pₙ : V)
    (hp : IsPathList G p) (hn : 2 ≤ p.length)
    (hhead : p.head? = some p₁) (hlast : p.getLast? = some pₙ)
    (hpXY : ∀ w ∈ p, w ∉ X ∪ Y)
    (hXuniq : ∀ w ∈ p, (VertexComplete G w X ↔ w = p₁))
    (hYuniq : ∀ w ∈ p, (VertexComplete G w Y ↔ w = pₙ))
    (z : V) (hzX : z ∉ X) (hzY : z ∉ Y) (hzp : z ∉ p)
    (hzcomp : VertexComplete G z (X ∪ Y))
    (hzp₁ : ¬ G.Adj z p₁)
    (Q : List V) (q : V)
    (hQ : IsPathFrom G Q z p₁)
    (hqint : q ∈ interior Q) (hzq : G.Adj z q)
    (hQint : ∀ v ∈ interior Q,
      v ∉ X ∧ ¬ VertexComplete G v X) :
    ∃ f ∈ (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}),
      VertexComplete G f Y ∧ G.Adj f z := by
  classical
  have hp₁mem : p₁ ∈ p :=
    Workspace.ProofLemmas.PathBasics.head_mem hhead
  have hpₙmem : pₙ ∈ p :=
    Workspace.ProofLemmas.PathBasics.getLast_mem hlast
  have hpos : 0 < p.length := by omega
  have hp₁val : p[0]'hpos = p₁ :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hhead hpos
  have hpₙval : p[p.length - 1]'(by omega) = pₙ :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hlast hpos
  have hp₁pₙ : p₁ ≠ pₙ := by
    intro heq
    have hdiff : p[0]'hpos ≠ p[p.length - 1]'(by omega) :=
      Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hp hpos (by omega) (by omega)
    apply hdiff
    rw [hp₁val, hpₙval, heq]
  have hQtail : ∀ w : V, w ∈ Q.tail ↔ (w ∈ Q ∧ w ≠ z) := by
    intro w
    cases Q with
    | nil => exact False.elim (hQ.1.1 rfl)
    | cons a t =>
        have haz : a = z := by simpa using hQ.2.1
        subst a
        have hznot : z ∉ t := (List.nodup_cons.mp hQ.1.2.1).1
        simp only [List.tail_cons, List.mem_cons]
        constructor
        · intro hw
          exact ⟨Or.inr hw, fun heq => hznot (heq ▸ hw)⟩
        · rintro ⟨hw | hw, hne⟩
          · exact False.elim (hne hw)
          · exact hw
  have hQminus : ({v : V | v ∈ Q} \ {z}) = {v : V | v ∈ Q.tail} := by
    ext w
    simp only [Set.mem_diff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact (hQtail w).symm
  have hQconn : ConnectedSet G ({v : V | v ∈ Q} \ {z}) := by
    rw [hQminus]
    exact Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isChain
      (Workspace.ProofLemmas.InducedPathExtraction.isChain_of_isPathList hQ.1).tail
  have hpconn : ConnectedSet G {v : V | v ∈ p} :=
    Workspace.ProofLemmas.InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp
  have hp₁Q : p₁ ∈ Q :=
    (Workspace.ProofLemmas.PathBasics.isPathFrom_ends_mem hQ).2
  have hp₁z : p₁ ≠ z := by
    intro heq
    exact hzp (heq ▸ hp₁mem)
  have hp₁Qminus : p₁ ∈ ({v : V | v ∈ Q} \ {z}) :=
    ⟨hp₁Q, by simpa using hp₁z⟩
  have hFconn : ConnectedSet G
      (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}) :=
    Workspace.ProofLemmas.ConnectedSetUnionAttach.connectedSet_union hQconn hpconn
      (Or.inl ⟨p₁, hp₁Qminus, hp₁mem⟩)
  have hQoutside : ∀ w ∈ ({v : V | v ∈ Q} \ {z}),
      w ∉ X ∧ w ∉ Y ∧ w ≠ z := by
    intro w hw
    obtain ⟨hwQ, hwzset⟩ := hw
    have hwz : w ≠ z := by simpa using hwzset
    by_cases hwp₁ : w = p₁
    · subst w
      have hout := hpXY p₁ hp₁mem
      exact ⟨fun hx => hout (Or.inl hx), fun hy => hout (Or.inr hy), hp₁z⟩
    · have hwint : w ∈ interior Q :=
        (Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mpr
          ⟨hwQ, hwz, hwp₁⟩
      have hwX : w ∉ X := (hQint w hwint).1
      have hwY : w ∉ Y := by
        intro hwY
        apply (hQint w hwint).2
        intro x hx
        exact (hcomp x hx w hwY).symm
      exact ⟨hwX, hwY, hwz⟩
  have hFoutside :
      (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}) ⊆ (X ∪ Y ∪ {z})ᶜ := by
    intro w hw
    show w ∉ X ∪ Y ∪ {z}
    rcases hw with hwQ | hwp
    · obtain ⟨hwX, hwY, hwz⟩ := hQoutside w hwQ
      rintro ((hx | hy) | hz)
      · exact hwX hx
      · exact hwY hy
      · exact hwz (by simpa using hz)
    · have hout := hpXY w hwp
      rintro ((hx | hy) | hz)
      · exact hout (Or.inl hx)
      · exact hout (Or.inr hy)
      · have hwz : w = z := by simpa using hz
        subst w
        exact hzp hwp
  have hXz : Disjoint X ({z} : Set V) := by
    rw [Set.disjoint_left]
    intro x hxX hxz
    have hx : x = z := by simpa using hxz
    exact hzX (hx ▸ hxX)
  have hYz : Disjoint Y ({z} : Set V) := by
    rw [Set.disjoint_left]
    intro y hyY hyz
    have hy : y = z := by simpa using hyz
    exact hzY (hy ▸ hyY)
  have hzanti : AnticonnectedSet G ({z} : Set V) := by
    intro a b
    exact (Subtype.ext (a.2.trans b.2.symm) ▸ SimpleGraph.Reachable.refl a)
  have hXzcomp : Complete G X ({z} : Set V) := by
    intro x hx v hv
    have hvz : v = z := by simpa using hv
    subst v
    exact (hzcomp x (Or.inl hx)).symm
  have hYzcomp : Complete G Y ({z} : Set V) := by
    intro y hy v hv
    have hvz : v = z := by simpa using hv
    subst v
    exact (hzcomp y (Or.inr hy)).symm
  have hp₁X : VertexComplete G p₁ X := (hXuniq p₁ hp₁mem).mpr rfl
  have hpₙY : VertexComplete G pₙ Y := (hYuniq pₙ hpₙmem).mpr rfl
  have hqQ : q ∈ Q :=
    Workspace.ProofLemmas.PathBasics.interior_subset hqint
  have hqz : q ≠ z :=
    ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mp hqint).2.1
  have hqF : q ∈ (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}) :=
    Or.inl ⟨hqQ, by simpa using hqz⟩
  have hqZ : VertexComplete G q ({z} : Set V) := by
    intro v hv
    have hvz : v = z := by simpa using hv
    subst v
    exact hzq.symm
  obtain ⟨f, hfF, hfcase⟩ :=
    Workspace.Statements.S24.SPGT.thm_24_4 G hG X Y ({z} : Set V)
      hXY hXz hYz hXne hYne ⟨z, rfl⟩ hX hY hzanti hcomp hXzcomp hYzcomp
      (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}) hFoutside hFconn
      ⟨p₁, Or.inr hp₁mem, hp₁X⟩ ⟨pₙ, Or.inr hpₙmem, hpₙY⟩
      ⟨q, hqF, hqZ⟩
  have hXonly : ∀ w ∈ (({v : V | v ∈ Q} \ {z}) ∪ {v : V | v ∈ p}),
      VertexComplete G w X → w = p₁ := by
    intro w hw hwX
    rcases hw with hwQ | hwp
    · by_cases hwp₁ : w = p₁
      · exact hwp₁
      · exact False.elim ((hQint w
          ((Workspace.ProofLemmas.PathBasics.mem_interior_iff_of_pathFrom hQ).mpr
            ⟨hwQ.1, (by simpa using hwQ.2), hwp₁⟩)).2 hwX)
    · exact (hXuniq w hwp).mp hwX
  rcases hfcase with hfXY | hfXZ | hfYZ
  · have hfp₁ : f = p₁ := hXonly f hfF hfXY.1
    have hp₁Y : VertexComplete G p₁ Y := by simpa [hfp₁] using hfXY.2
    exact False.elim (hp₁pₙ ((hYuniq p₁ hp₁mem).mp hp₁Y))
  · have hfp₁ : f = p₁ := hXonly f hfF hfXZ.1
    have hfp₁z : G.Adj p₁ z := by simpa [hfp₁] using hfXZ.2 z rfl
    exact False.elim (hzp₁ hfp₁z.symm)
  · exact ⟨f, hfF, hfYZ.1, hfYZ.2 z rfl⟩

end Workspace.Types.Thm245YCompleteWitnessFromTwentyFourFour
