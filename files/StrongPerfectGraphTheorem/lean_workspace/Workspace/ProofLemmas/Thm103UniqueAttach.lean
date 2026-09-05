/-  Proof attempt for `Thm103UniqueAttach.thm103_unique_attach`.

    Printed sentence (10.3, p. 58): *"From the minimality of `F`, `v₁` is the only vertex of
    `F` with a neighbour in `V(R₂) ∪ V(R₃)`."*

    The paper's argument, step for step:
    * minimality first turns `F` into the interior of an induced path `x₁-⋯-x₂`
      (`MinimalConnectedIsPath.exists_path_interior_attached` + `hFmin`);
    * the vertex `v` with the neighbour `y_v ∈ V(R₂) ∪ V(R₃)` must be the end of that
      interior next to `y_v` (non-consecutive vertices of a path are non-adjacent);
    * if a second vertex `w` had a neighbour `y_w ∈ V(R₂) ∪ V(R₃)`, truncating the path at
      `w` gives a connected subset of `F` still attached at `x₁` and attached at
      `y_w ∉ V(R₁)`, so minimality forces the truncation to be all of `F`, which puts `v`
      inside it and hence forces `w = v`.  -/
import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.HyperprismFromPrism

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas.Thm103UniqueAttach

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rewriting the *index* of a `getElem` is a motive error; this is the usable form. -/
private theorem gidx {W : Type*} (q : List W) {α β : ℕ} (h : α = β)
    (ha : α < q.length) (hb : β < q.length) : q[α]'ha = q[β]'hb := by
  subst h; rfl

/-- **"From the minimality of `F`, `v₁` is the only vertex of `F` with a neighbour in
`V(R₂) ∪ V(R₃)`"** (printed p. 58, in the proof of 10.3). -/
theorem thm103_unique_attach (G : SimpleGraph V)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (K F : Set V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hFconn : ConnectedSet G F)
    (x₁ : V) (hx₁ : IsAttachment G F K x₁) (hx₁R : x₁ ∈ SPGT.interior (R 0))
    (hFmin : ∀ F' ⊆ F, ConnectedSet G F' → IsAttachment G F' K x₁ →
      (∃ z, IsAttachment G F' K z ∧ z ∉ R 0) → F' = F) :
    ∀ v ∈ F, ∀ w ∈ F,
      (∃ y, (y ∈ R 1 ∨ y ∈ R 2) ∧ G.Adj v y) →
      (∃ y, (y ∈ R 1 ∨ y ∈ R 2) ∧ G.Adj w y) → v = w := by
  obtain ⟨-, -, -, hpR0, -, -, h01, h02, -⟩ := id hprism
  -- membership bookkeeping for `K`
  have hK1 : ∀ z, z ∈ R 1 → z ∈ K := by intro z hz; rw [hK]; exact Or.inl (Or.inr hz)
  have hK2 : ∀ z, z ∈ R 2 → z ∈ K := by intro z hz; rw [hK]; exact Or.inr hz
  have hKof : ∀ z, (z ∈ R 1 ∨ z ∈ R 2) → z ∈ K := fun z h => h.elim (hK1 z) (hK2 z)
  have hnotR0 : ∀ z, (z ∈ R 1 ∨ z ∈ R 2) → z ∉ R 0 := by
    intro z h
    rcases h with h | h
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 1) (j := 0) (by decide) z h
    · exact HyperprismFromPrism.formPrism_disjoint hprism (i := 2) (j := 0) (by decide) z h
  have hnotF : ∀ z, z ∈ K → z ∉ F := fun z hz hzF => hFK hzF hz
  -- `x₁` lies on `R 0`, is neither end of it, and is not in `F`
  obtain ⟨hx₁R0, hx₁a, hx₁b⟩ := (PathBasics.mem_interior_iff_of_pathFrom hpR0).mp hx₁R
  have hx₁F : x₁ ∉ F := hnotF x₁ hx₁.1
  have hx₁ne : ∀ y, (y ∈ R 1 ∨ y ∈ R 2) → x₁ ≠ y := by
    intro y hy hxy
    exact hnotR0 y hy (hxy ▸ hx₁R0)
  -- the "no other edges" clause of the prism: `x₁` has no neighbour in `R 1 ∪ R 2`
  have hnadj : ∀ y, (y ∈ R 1 ∨ y ∈ R 2) → ¬ G.Adj x₁ y := by
    intro y hy hadj
    rcases hy with hy | hy
    · rcases (h01 x₁ hx₁R0 y hy).mp hadj with ⟨he, -⟩ | ⟨he, -⟩
      · exact hx₁a he
      · exact hx₁b he
    · rcases (h02 x₁ hx₁R0 y hy).mp hadj with ⟨he, -⟩ | ⟨he, -⟩
      · exact hx₁a he
      · exact hx₁b he
  intro v hv w hw hyv hyw
  obtain ⟨yv, hyvR, hadjv⟩ := hyv
  obtain ⟨yw, hywR, hadjw⟩ := hyw
  have hyvF : yv ∉ F := hnotF yv (hKof yv hyvR)
  have hywF : yw ∉ F := hnotF yw (hKof yw hywR)
  -- (1) minimality makes `F` the interior of an induced path from `x₁` to `y_v`
  obtain ⟨p, hp, h3, hpint, hpconn, ⟨d1, hd1, hd1adj⟩, ⟨d2, hd2, hd2adj⟩⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn
      (hx₁ne yv hyvR) (hnadj yv hyvR) hx₁F hyvF hx₁.2 ⟨v, hv, hadjv.symm⟩
  have hFeq : {z : V | z ∈ SPGT.interior p} = F :=
    hFmin _ (fun z hz => hpint z hz) hpconn ⟨hx₁.1, ⟨d1, hd1, hd1adj⟩⟩
      ⟨yv, ⟨hKof yv hyvR, ⟨d2, hd2, hd2adj⟩⟩, hnotR0 yv hyvR⟩
  have hmemF : ∀ z, z ∈ F → z ∈ SPGT.interior p := by
    intro z hz; rw [← hFeq] at hz; exact hz
  have hpos : 0 < p.length := by omega
  have h0 : p[0]'hpos = x₁ := PathBasics.getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = yv :=
    PathBasics.getElem_last_of_getLast? hp.2.2 hpos
  -- index of `v`
  obtain ⟨s, hs, hsv⟩ := List.mem_iff_getElem.mp (PathBasics.interior_subset (hmemF v hv))
  -- index of `w`
  obtain ⟨t, ht, htw⟩ := List.mem_iff_getElem.mp (PathBasics.interior_subset (hmemF w hw))
  have hs0 : s ≠ 0 := by
    intro h; subst h; rw [h0] at hsv; exact hx₁F (hsv ▸ hv)
  have hsl : s ≠ p.length - 1 := by
    intro h
    rw [gidx p h hs (by omega), hlast] at hsv
    exact hyvF (hsv ▸ hv)
  have ht0 : t ≠ 0 := by
    intro h; subst h; rw [h0] at htw; exact hx₁F (htw ▸ hw)
  have htl : t ≠ p.length - 1 := by
    intro h
    rw [gidx p h ht (by omega), hlast] at htw
    exact hyvF (htw ▸ hw)
  -- (2) `v` is the end of the interior next to `y_v`
  have hsn : s = p.length - 2 := by
    by_contra hne
    exact PathBasics.path_not_adj_of_gap hp.1 hs (show p.length - 1 < p.length by omega)
      (by omega) (by omega) (by rw [hsv, hlast]; exact hadjv)
  -- (3) truncate the path at `w`
  have htlen : t < p.length := ht
  have hqpath : IsPathList G ((p.drop 1).take (t - 1 + 1)) :=
    PathBasics.isPathList_take (PathBasics.isPathList_drop hp.1 (show 1 < p.length by omega))
      (show 0 < t - 1 + 1 by omega)
  have hqlen : ((p.drop 1).take (t - 1 + 1)).length = t - 1 + 1 :=
    PathBasics.length_slice p (show 1 ≤ t by omega) ht
  have hqmem : ∀ z ∈ (p.drop 1).take (t - 1 + 1),
      ∃ m, 1 ≤ m ∧ m ≤ t ∧ ∃ hm : m < p.length, p[m]'hm = z := by
    intro z hz
    obtain ⟨k, hk, hkz⟩ := List.mem_iff_getElem.mp hz
    rw [hqlen] at hk
    refine ⟨1 + k, by omega, by omega, by omega, ?_⟩
    exact (PathBasics.getElem_slice p (by rw [hqlen]; omega)).symm.trans hkz
  have hq1 : (p[1]'(show 1 < p.length by omega)) ∈ (p.drop 1).take (t - 1 + 1) := by
    have hk : (0 : ℕ) < ((p.drop 1).take (t - 1 + 1)).length := by rw [hqlen]; omega
    have hmem := List.getElem_mem hk
    rwa [PathBasics.getElem_slice' p hk (show 1 < p.length by omega)
      (show (1 : ℕ) = 1 + 0 by omega)] at hmem
  have hqt : (p[t]'ht) ∈ (p.drop 1).take (t - 1 + 1) := by
    have hk : (t - 1) < ((p.drop 1).take (t - 1 + 1)).length := by rw [hqlen]; omega
    have hmem := List.getElem_mem hk
    rwa [PathBasics.getElem_slice' p hk ht (show t = 1 + (t - 1) by omega)] at hmem
  have hsub : {z : V | z ∈ (p.drop 1).take (t - 1 + 1)} ⊆ F := by
    intro z hz
    obtain ⟨m, hm1, hmt, hmlt, hmz⟩ := hqmem z hz
    rw [← hFeq]
    show z ∈ SPGT.interior p
    rw [PathBasics.mem_interior_iff_of_pathFrom hp]
    refine ⟨hmz ▸ List.getElem_mem hmlt, ?_, ?_⟩
    · rw [← hmz, ← h0]
      exact PathBasics.path_ne_of_ne_index hp.1 hmlt hpos (by omega)
    · rw [← hmz, ← hlast]
      exact PathBasics.path_ne_of_ne_index hp.1 hmlt (by omega) (by omega)
  have hFeq2 : {z : V | z ∈ (p.drop 1).take (t - 1 + 1)} = F := by
    refine hFmin _ hsub (InducedPathExtraction.connectedSet_setOf_mem_of_isPathList hqpath)
      ⟨hx₁.1, ⟨p[1]'(show 1 < p.length by omega), hq1, ?_⟩⟩
      ⟨yw, ⟨hKof yw hywR, ⟨p[t]'ht, hqt, ?_⟩⟩, hnotR0 yw hywR⟩
    · have hadj := PathBasics.path_adj_succ hp.1 (show 0 + 1 < p.length by omega)
      rw [h0] at hadj
      exact hadj
    · rw [htw]; exact hadjw.symm
  -- (4) `v` lies in the truncation, so the truncation reaches index `p.length - 2`
  have hvq : v ∈ (p.drop 1).take (t - 1 + 1) := by
    rw [← hFeq2] at hv; exact hv
  obtain ⟨m, hm1, hmt, hmlt, hmz⟩ := hqmem v hvq
  have hms : m = s :=
    (List.Nodup.getElem_inj_iff (PathBasics.path_nodup hp.1)).mp (hmz.trans hsv.symm)
  have hts : s = t := by omega
  rw [← hsv, ← htw]
  exact gidx p hts hs ht

end Workspace.ProofLemmas.Thm103UniqueAttach
