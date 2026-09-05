import Workspace.ProofLemmas.NonCutVertices
import Workspace.ProofLemmas.Thm192Infra
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathGlue

/-! The graph argument in claim (3) of 17.5, in the complement graph. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm175Claim3Structure

open Workspace.Types.Core.SPGT
open Workspace.ProofLemmas

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- PAPER: "By (2), there do not exist two vertices `x₀ ∈ X \ {x}` such
that `X \ {x₀}` is anticonnected; and therefore `X` is an antipath."
An induced path between the only two possible non-cut vertices covers the
connected set: otherwise there is a non-cut vertex outside that path. -/
theorem path_of_two_noncut (H : SimpleGraph V) (S : Set V)
    (hS : ConnectedSet H S) (a b : V) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b)
    (honly : ∀ v ∈ S, ConnectedSet H (S \ {v}) → v = a ∨ v = b) :
    ∃ p : List V, IsPathFrom H p a b ∧ 1 < p.length ∧
      ∀ v, v ∈ p ↔ v ∈ S := by
  obtain ⟨p, hp, hsub⟩ :=
    InducedPathExtraction.exists_isPathFrom_of_connected hS ha hb
  have haP : a ∈ p := PathBasics.head_mem hp.2.1
  have hbP : b ∈ p := PathBasics.getLast_mem hp.2.2
  have hcover : {v | v ∈ p} = S := by
    by_contra hne
    obtain ⟨v, hv, hdel⟩ := Thm192Infra.exists_noncut_outside hS
      (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hp.1)
      hsub hne ⟨a, haP⟩
    rcases honly v hv.1 hdel with rfl | rfl
    · exact hv.2 haP
    · exact hv.2 hbP
  have hlong : 1 < p.length := by
    have hpos := PathBasics.path_length_pos hp.1
    by_contra hn
    have hlen : p.length = 1 := by omega
    obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hlen
    simp only [List.mem_singleton] at haP hbP
    exact hab (haP.trans hbP.symm)
  exact ⟨p, hp, hlong, fun v => Set.ext_iff.mp hcover v⟩

/-- PAPER: "Hence there are at least two vertices `x ∈ X` such that
`X \ {x}` is anticonnected, and from (2), `X ∩ Y = ∅`, and there is a
unique vertex `x ∈ X` with nonneighbours in `Y`."
The same application of (2) locates the two ends of the first block. -/
theorem one_block (G : SimpleGraph V) (X Y : Set V)
    (hX : AnticonnectedSet G X) (hsize : ¬ X.Subsingleton)
    (hc : ∀ a ∈ X, ∀ b ∈ X, a ≠ b →
      AnticonnectedSet G (X \ {a}) → AnticonnectedSet G (X \ {b}) →
      Disjoint X Y ∧
        ((∀ v ∈ X, ((∃ y ∈ Y, ¬ G.Adj v y) ↔ v = a)) ∨
         (∀ v ∈ X, ((∃ y ∈ Y, ¬ G.Adj v y) ↔ v = b)))) :
    ∃ p : List V, ∃ a b : V, IsAntipathFrom G p a b ∧ 1 < p.length ∧
      (∀ v, v ∈ p ↔ v ∈ X) ∧ Disjoint X Y ∧
      (∀ v ∈ X, ((∃ y ∈ Y, ¬ G.Adj v y) ↔ v = b)) := by
  obtain ⟨a, ha, b, hb, hab, hda, hdb⟩ :=
    NonCutVertices.exists_two_nonanticut hX hsize
  obtain ⟨hd, hu⟩ := hc a ha b hb hab hda hdb
  have finish (a b : V) (ha : a ∈ X) (hb : b ∈ X) (hab : a ≠ b)
      (hda : AnticonnectedSet G (X \ {a}))
      (huniq : ∀ v ∈ X, ((∃ y ∈ Y, ¬ G.Adj v y) ↔ v = b)) :
      ∃ p : List V, ∃ a b : V, IsAntipathFrom G p a b ∧ 1 < p.length ∧
        (∀ v, v ∈ p ↔ v ∈ X) ∧ Disjoint X Y ∧
        (∀ v ∈ X, ((∃ y ∈ Y, ¬ G.Adj v y) ↔ v = b)) := by
    have honly : ∀ v ∈ X, AnticonnectedSet G (X \ {v}) → v = a ∨ v = b := by
      intro v hv hdv
      by_cases hva : v = a
      · exact Or.inl hva
      obtain ⟨_, hu'⟩ := hc v hv a ha hva hdv hda
      have hbmiss := (huniq b hb).mpr rfl
      rcases hu' with h | h
      · exact Or.inr ((h b hb).mp hbmiss).symm
      · exact (hab ((h b hb).mp hbmiss).symm).elim
    obtain ⟨p, hp, hl, hverts⟩ := path_of_two_noncut Gᶜ X hX a b ha hb hab honly
    exact ⟨p, a, b, hp, hl, hverts, hd, huniq⟩
  rcases hu with hu | hu
  · exact finish b a hb ha hab.symm hdb hu
  · exact finish a b ha hb hab hda hu

/-- PAPER: "Because of the symmetry between `X,Y`, the same applies for
`Y`, and this proves (3)." The unique missing cross-pair joins the two
antipaths at their distinguished ends. -/
theorem join_blocks (G : SimpleGraph V) (X Y : Set V)
    (p q : List V) (a x b y : V)
    (hp : IsAntipathFrom G p a x) (hq : IsAntipathFrom G q b y)
    (hpX : ∀ v, v ∈ p ↔ v ∈ X) (hqY : ∀ v, v ∈ q ↔ v ∈ Y)
    (hd : Disjoint X Y)
    (hx : ∀ v ∈ X, ((∃ w ∈ Y, ¬ G.Adj v w) ↔ v = x))
    (hy : ∀ v ∈ Y, ((∃ w ∈ X, ¬ G.Adj v w) ↔ v = y)) :
    IsAntipathFrom G (p ++ q.reverse) a b := by
  have hxX : x ∈ X := (hpX x).mp (PathBasics.getLast_mem hp.2.2)
  obtain ⟨w, hwY, hxw⟩ := (hx x hxX).mpr rfl
  have hwy : w = y := (hy w hwY).mp ⟨x, hxX, fun h => hxw h.symm⟩
  have hxy : ¬ G.Adj x y := hwy ▸ hxw
  apply PathGlue.glue_path hp (PathBasics.isPathFrom_reverse hq)
  · intro v hv hvq
    exact Set.disjoint_left.mp hd ((hpX v).mp hv)
      ((hqY v).mp (List.mem_reverse.mp hvq))
  · intro v hv w hw
    have hvX := (hpX v).mp hv
    have hwY := (hqY w).mp (List.mem_reverse.mp hw)
    rw [SimpleGraph.compl_adj]
    constructor
    · rintro ⟨_, h⟩
      exact ⟨(hx v hvX).mp ⟨w, hwY, h⟩,
        (hy w hwY).mp ⟨v, hvX, fun h' => h h'.symm⟩⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun he => Set.disjoint_left.mp hd hvX (he ▸ hwY), hxy⟩

end Workspace.ProofLemmas.Thm175Claim3Structure
