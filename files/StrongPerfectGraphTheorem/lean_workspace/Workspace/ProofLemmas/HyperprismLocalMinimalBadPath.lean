import Workspace.ProofLemmas.HyperprismClaim2Setup
import Workspace.ProofLemmas.HyperprismTwoAttachments
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.HyperprismLocalMinimalBadPath

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas.HyperprismBasics
open Workspace.ProofLemmas.HyperprismClaim2Setup

private theorem getElem_idx_eq {W : Type*} (l : List W) {i j : ℕ} (hij : i = j)
    (hi : i < l.length) (hj : j < l.length) : l[i]'hi = l[j]'hj := by
  subst hij
  rfl

/-- PAPER (10.6, claim (2), printed p. 61):
*"From the minimality of `F`, there is a path
`x₁-f₁-···-fₙ-x₂` with `F = {f₁,…,fₙ}`."*

The two outside ends are a non-local pair of attachments in different sides of different
strips.  The extra endpoint-neighbour clauses record the induced-path information used by
both parity cases that follow. -/
theorem minimalBadAttachmentPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V)
    (A B C : Fin 3 → Set V)
    (F : Set V)
    (hH : IsHyperprism G A B C)
    (hF : MinimalBad G A B C F)
    (i j : Fin 3)
    (hij : i ≠ j)
    (xA xB : V)
    (hxAatt : xA ∈ attachments G F (hyperVerts A B C))
    (hxAA : xA ∈ A i)
    (hxBatt : xB ∈ attachments G F (hyperVerts A B C))
    (hxBB : xB ∈ B j) :
    ∃ f : List V,
      f ≠ [] ∧
      (∀ v ∈ f, v ∈ F) ∧
      IsPathFrom G (xA :: (f ++ [xB])) xA xB ∧
      (∀ v ∈ f, G.Adj xA v ↔ f.head? = some v) ∧
      (∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v) ∧
      F = {v : V | v ∈ f} := by
  classical
  have hxAS : xA ∈ A i ∪ B i ∪ C i := Or.inl (Or.inl hxAA)
  have hxBS : xB ∈ A j ∪ B j ∪ C j := Or.inl (Or.inr hxBB)
  have hABdisj : ∀ a b : Fin 3, Disjoint (A a) (B b) := hH.2.1
  have hxne : xA ≠ xB := by
    intro h
    exact Set.disjoint_left.mp (hABdisj i j) hxAA (h ▸ hxBB)
  have hnadj : ¬ G.Adj xA xB := by
    intro hadj
    rcases cross hH hij hxAS hxBS hadj with ⟨-, hxBA⟩ | ⟨hxAB, -⟩
    · exact Set.disjoint_left.mp (hABdisj j j) hxBA hxBB
    · exact Set.disjoint_left.mp (hABdisj i i) hxAA hxAB
  have hxAnF : xA ∉ F := fun hx => hF.1.2.1 hx hxAatt.1
  have hxBnF : xB ∉ F := fun hx => hF.1.2.1 hx hxBatt.1
  obtain ⟨p, hp, hplen, hpF, hpconn, ⟨dA, hdAI, hxAdA⟩, ⟨dB, hdBI, hxBdB⟩⟩ :=
    Workspace.ProofLemmas.MinimalConnectedIsPath.exists_path_interior_attached
      hF.1.1 hxne hnadj hxAnF hxBnF hxAatt.2 hxBatt.2
  have hlocal_mono : ∀ {X Y : Set V}, X ⊆ Y → LocalForHyperprism A B C Y →
      LocalForHyperprism A B C X := by
    rintro X Y hXY (h | h | h | h | h)
    · exact Or.inl (hXY.trans h)
    · exact Or.inr (Or.inl (hXY.trans h))
    · exact Or.inr (Or.inr (Or.inl (hXY.trans h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (hXY.trans h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (hXY.trans h))))
  have hIF : {v : V | v ∈ interior p} = F := by
    by_contra hne
    have hlocal := hF.local_of_ssubset (fun v hv => hpF v hv) hne hpconn
    apply HyperprismTwoAttachments.not_local_pair hH hij hxAA hxBB
    refine hlocal_mono ?_ hlocal
    rintro v (rfl | hv)
    · exact ⟨hxAatt.1, dA, hdAI, hxAdA⟩
    · have hvx : v = xB := hv
      subst hvx
      exact ⟨hxBatt.1, dB, hdBI, hxBdB⟩
  have hneI : interior p ≠ [] := PathBasics.interior_ne_nil hp.1 hplen
  have hdecomp : p = xA :: (interior p ++ [xB]) := by
    have hpne : p ≠ [] := hp.1.1
    obtain ⟨a, t, rfl⟩ : ∃ a t, p = a :: t := by
      cases p with
      | nil => exact absurd rfl hpne
      | cons a t => exact ⟨a, t, rfl⟩
    have ha : a = xA := by
      have hh := hp.2.1
      simpa only [List.head?_cons, Option.some.injEq] using hh
    have htne : t ≠ [] := by
      intro ht
      rw [ht] at hplen
      simp at hplen
    have hlast : t.getLast htne = xB := by
      have hh := hp.2.2
      rw [List.getLast?_eq_some_getLast (List.cons_ne_nil a t)] at hh
      have hc : (a :: t).getLast (List.cons_ne_nil a t) = xB := Option.some_injective _ hh
      rw [List.getLast_cons htne] at hc
      exact hc
    have hsplit : t = t.dropLast ++ [t.getLast htne] :=
      (List.dropLast_append_getLast htne).symm
    show a :: t = xA :: (t.dropLast ++ [xB])
    rw [ha, ← hlast, ← hsplit]
  let f : List V := interior p
  have hfpath : IsPathFrom G (xA :: (f ++ [xB])) xA xB := by
    dsimp only [f]
    rw [← hdecomp]
    exact hp
  have hflen : 0 < f.length := List.length_pos_of_ne_nil hneI
  have hfullLen : (xA :: (f ++ [xB])).length = f.length + 2 := by simp
  have hleft : ∀ v ∈ f, G.Adj xA v ↔ f.head? = some v := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    constructor
    · intro hadj
      have hadj' : G.Adj
          ((xA :: (f ++ [xB]))[0]'(by simp))
          ((xA :: (f ++ [xB]))[k + 1]'(by simp; omega)) := by
        simpa only [List.getElem_cons_zero, List.getElem_cons_succ,
          List.getElem_append_left hk] using hadj
      rcases (PathBasics.path_adj_iff hfpath.1 (by simp) (by simp; omega)).mp hadj' with h | h
      · have hk0 : k = 0 := by omega
        subst hk0
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hflen]
      · omega
    · intro hhead
      have h0k : f[0]'hflen = f[k]'hk := by
        rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hflen] at hhead
        exact Option.some_injective _ hhead
      have hk0 : k = 0 := by
        exact (List.Nodup.getElem_inj_iff (PathBasics.path_nodup
          (PathGlue.isPathFrom_interior hp.1 hplen).1)).mp h0k |>.symm
      subst hk0
      have hadj' := PathBasics.path_adj_succ hfpath.1
        (i := 0) (show 0 + 1 < (xA :: (f ++ [xB])).length by simp)
      simpa only [List.getElem_cons_zero, List.getElem_cons_succ,
        List.getElem_append_left hflen] using hadj'
  have hright : ∀ v ∈ f, G.Adj xB v ↔ f.getLast? = some v := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    constructor
    · intro hadj
      have hadj' : G.Adj
          ((xA :: (f ++ [xB]))[f.length + 1]'(by simp))
          ((xA :: (f ++ [xB]))[k + 1]'(by simp; omega)) := by
        rw [List.getElem_cons_succ, List.getElem_concat_length rfl,
          List.getElem_cons_succ, List.getElem_append_left hk]
        exact hadj
      rcases (PathBasics.path_adj_iff hfpath.1 (by simp) (by simp; omega)).mp hadj' with h | h
      · omega
      · rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)]
        apply congrArg some
        exact getElem_idx_eq f (by omega) (by omega) hk
    · intro hlast
      rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
      have heq : f[f.length - 1]'(by omega) = f[k]'hk := Option.some_injective _ hlast
      have hklast : k + 1 = f.length := by
        have := (List.Nodup.getElem_inj_iff (PathBasics.path_nodup
          (PathGlue.isPathFrom_interior hp.1 hplen).1)).mp heq
        omega
      have hadj' : G.Adj
          ((xA :: (f ++ [xB]))[f.length + 1]'(by simp))
          ((xA :: (f ++ [xB]))[k + 1]'(by simp; omega)) :=
        (PathBasics.path_adj_iff hfpath.1 (by simp) (by simp; omega)).mpr (Or.inr (by omega))
      rw [List.getElem_cons_succ, List.getElem_concat_length rfl,
        List.getElem_cons_succ, List.getElem_append_left hk] at hadj'
      exact hadj'
  refine ⟨f, ?_, ?_, hfpath, hleft, hright, ?_⟩
  · exact hneI
  · intro v hv
    rw [← hIF]
    exact hv
  · exact hIF.symm

end Workspace.ProofLemmas.HyperprismLocalMinimalBadPath
