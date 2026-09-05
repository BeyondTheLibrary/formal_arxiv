import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.MajorPrismFirstMissedAntipathIndexInternal
import Workspace.ProofLemmas.FirstMissedAntipathIndexBuildsShorterAdmissibleAntipath

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

theorem GlobalMinimalPrismAntipathThirdTriangleVertexComplete
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Y : Set V)
    (α β : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V)
    (hprism : FormPrism G α β (R 0) (R 1) (R 2))
    (hRoutside : ∀ i v, v ∈ R i → v ∉ Y)
    (hYmajor : ∀ y ∈ Y, MajorForPrism G α β y)
    (hQshape : Q = α 0 :: (q ++ [α 1]))
    (hQantipath : IsAntipathFrom G Q (α 0) (α 1))
    (hqY : ∀ x ∈ q, x ∈ Y)
    (hα0 : ¬ VertexComplete G (α 0) Y)
    (hα1 : ¬ VertexComplete G (α 1) Y)
    (hminimal : ∀ (u v : V) (S : List V),
      u ≠ v →
      ((u ∈ ({α 0, α 1, α 2} : Set V) ∧ v ∈ ({α 0, α 1, α 2} : Set V)) ∨
        (u ∈ ({β 0, β 1, β 2} : Set V) ∧ v ∈ ({β 0, β 1, β 2} : Set V))) →
      ¬ VertexComplete G u Y →
      ¬ VertexComplete G v Y →
      IsAntipathFrom G S u v →
      (∀ x ∈ interior S, x ∈ Y) →
      pathLength Q ≤ pathLength S) :
    VertexComplete G (α 2) {x : V | x ∈ q} := by
  classical
  intro x hxq
  by_contra hxmiss
  obtain ⟨j, hj, hjpos, hjplus, hjmiss, hfirst⟩ :=
    MajorPrismFirstMissedAntipathIndexInternal G Y α β q Q x
      hYmajor hQshape hQantipath hqY hxq hxmiss
  have ha0a2 : G.Adj (α 0) (α 2) := hprism.1 0 2 (by decide)
  have hR2path : IsPathFrom G (R 2) (α 2) (β 2) := hprism.2.2.2.2.2.1
  have ha2memR2 : α 2 ∈ R 2 := List.mem_of_mem_head? hR2path.2.1
  have ha2notY : α 2 ∉ Y := hRoutside 2 (α 2) ha2memR2
  let S := α 0 :: (q.take (j + 1) ++ [α 2])
  have hshorter :
      IsAntipathFrom G S (α 0) (α 2) ∧
      (∀ z ∈ interior S, z ∈ Y) ∧
      ¬ VertexComplete G (α 2) Y ∧
      pathLength S < pathLength Q := by
    simpa [S] using
      (FirstMissedAntipathIndexBuildsShorterAdmissibleAntipath G Y
        (α 0) (α 1) (α 2) q Q j hQshape hQantipath ha0a2 ha2notY
        hqY hj hjplus hjmiss hfirst)
  rcases hshorter with ⟨hS, hSint, ha2notcomplete, hSshort⟩
  have hmin := hminimal (α 0) (α 2) S
    ha0a2.ne
    (Or.inl ⟨by simp, by simp⟩)
    hα0 ha2notcomplete hS hSint
  exact (not_lt_of_ge hmin) hSshort

end Workspace.ProofLemmas
