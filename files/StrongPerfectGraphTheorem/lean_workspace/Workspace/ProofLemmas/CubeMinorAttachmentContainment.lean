import Workspace.ProofLemmas.CubeMinorAttachmentContainmentCore

set_option autoImplicit false

namespace Workspace.ProofLemmas.CubeMinorAttachmentContainment

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.Types.DoubleDiamond Workspace.Types.DoubleDiamond.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT

theorem CubeMinorAttachmentContainment
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : InF5 G)
    (A B C D : Set V) (hcube : MaximalCube G A B C D)
    (F : Set V) (hF : F ⊆ (A ∪ B ∪ C ∪ D)ᶜ) (hFconn : ConnectedSet G F)
    (hFminor : ∀ v ∈ F, MinorForCube G A B C D v)
    (X : Set V) (hX : X = attachments G F (A ∪ B ∪ C ∪ D)) :
    X ⊆ A ∪ B ∨ X ⊆ C ∪ D ∨ X ⊆ A ∪ C ∨ X ⊆ B ∪ D := by
  exact
    CubeMinorAttachmentContainmentCore.cubeMinorAttachmentContainment
      G hG A B C D hcube F hF hFconn hFminor X hX

end Workspace.ProofLemmas.CubeMinorAttachmentContainment
