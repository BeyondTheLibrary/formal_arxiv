import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Pseudowheels
import Workspace.Types.Classes
import Workspace.ProofLemmas.Thm186Setup
import Workspace.Statements.S18.Thm_18_4
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.SubpathIsSlice
import Workspace.ProofLemmas.HoleYEdgeParity
import Workspace.ProofLemmas.MinimalConnectedIsPath
import Workspace.ProofLemmas.PseudowheelBuilder
import Workspace.ProofLemmas.Thm186FSizeTwo

/-!
# 18.6, claim (1) — *"Some vertex in `F` is `X`-complete."*
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

namespace Workspace.ProofLemmas.Thm186Claim1

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Pseudowheels Workspace.Types.Pseudowheels.SPGT
open Workspace.Types.Classes Workspace.Types.Classes.SPGT
open Workspace.ProofLemmas.Thm186Setup

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Greatest index below `n` satisfying `Q`. -/
private theorem exists_greatest {Q : ℕ → Prop} : ∀ n : ℕ, (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
  classical
  intro n
  induction n with
  | zero => rintro ⟨k, hk, -⟩; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
    intro hex
    by_cases hQ : Q n
    · exact ⟨n, by omega, hQ, fun m hm _ => by omega⟩
    · have hex' : ∃ k, k < n ∧ Q k := by
        obtain ⟨k, hk, hQk⟩ := hex
        refine ⟨k, ?_, hQk⟩
        rcases (by omega : k < n ∨ k = n) with h | h
        · exact h
        · exact absurd (h ▸ hQk) hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      refine ⟨k, by omega, hQk, ?_⟩
      intro m hm hQm
      rcases (by omega : m < n ∨ m = n) with h | h
      · exact hmax m h hQm
      · exact absurd (h ▸ hQm) hQ

/-- Every stretch of `p` is a contiguous block of `p`. -/
private theorem slice_infix (p : List V) (i m : ℕ) : (p.drop i).take m <:+: p := by
  refine ⟨p.take i, (p.drop i).drop m, ?_⟩
  rw [List.append_assoc, List.take_append_drop, List.take_append_drop]

/-- A one-vertex stretch is a contiguous block. -/
private theorem singleton_infix {W : Type*} {l : List W} {x : W} (h : x ∈ l) : [x] <:+: l := by
  obtain ⟨s, t, hst⟩ := List.append_of_mem h
  exact ⟨s, t, by rw [hst]; simp⟩

/-- `isPathFrom_slice`, allowing a one-vertex stretch. -/
private theorem isPathFrom_slice_le {G : SimpleGraph V} {p : List V} (h : IsPathList G p)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.length) :
    IsPathFrom G ((p.drop i).take (j - i + 1)) (p[i]'(by omega)) (p[j]'hj) := by
  refine ⟨?_, PathBasics.head?_slice p hij hj, PathBasics.getLast?_slice p hij hj⟩
  rcases eq_or_lt_of_le hij with heq | hlt
  · have hlen1 : ((p.drop i).take (j - i + 1)).length = 1 := by
      rw [PathBasics.length_slice p hij hj]; omega
    obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen1
    rw [hx]
    exact PathBasics.isPathList_singleton G x
  · exact PathBasics.isPathList_slice h hlt hj

/-- The second entry of a list, read off its tail. -/
private theorem tail_head?_getElem {W : Type*} {l : List W} (h : 1 < l.length) :
    l.tail.head? = some (l[1]'h) := by
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (show 0 < l.tail.length by simp; omega)]
  simp

/-- **18.6, claim (1)**: *"Some vertex in `F` is `X`-complete."* -/
theorem claim1 (G : SimpleGraph V) (hG : InF7 G) (X Y : Set V)
    (P : List V) (p₁ pₙ : V) (hopt : OptimalPseudowheel G X Y P)
    (hhead : P.head? = some p₁) (hlast : P.getLast? = some pₙ)
    (F : Set V) (hmin : MinCounterexample G X Y P p₁ pₙ F) :
    ∃ f ∈ F, VertexComplete G f X := by
  classical
  by_contra hcon0
  push_neg at hcon0
  obtain ⟨⟨hXY, hXne, hYne, hXanti, hYanti, hcompl⟩, q₁, q₂, qₙ,
    ⟨hPfrom, hq₂h, hPXY, hPlen⟩, hXuniq0, hq₁Y, hother, hq₂Y, hqₙY0⟩ := hopt.1
  have hP : IsPathList G P := hPfrom.1
  have hBerge : Berge G := hG.1.1.1.1
  have hq₁ : q₁ = p₁ := Option.some_injective _ (hPfrom.2.1.symm.trans hhead)
  have hqn : qₙ = pₙ := Option.some_injective _ (hPfrom.2.2.symm.trans hlast)
  have hXuniq : ∀ v ∈ P, VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
    intro v hv
    rw [← hq₁, ← hqn]
    exact hXuniq0 v hv
  have hp₁Y : VertexComplete G p₁ Y := by rw [← hq₁]; exact hq₁Y
  have hpₙY : ¬ VertexComplete G pₙ Y := by rw [← hqn]; exact hqₙY0
  have h0lt : 0 < P.length := by omega
  have hnlt : P.length - 1 < P.length := by omega
  have h1lt : 1 < P.length := by omega
  have hnd : P.Nodup := PathBasics.path_nodup hP
  have hp0 : P[0]'h0lt = p₁ := PathBasics.getElem_zero_of_head? hhead h0lt
  have hpn : P[P.length - 1]'hnlt = pₙ := PathBasics.getElem_last_of_getLast? hlast h0lt
  have hp1 : P[1]'h1lt = q₂ := by
    have h := hq₂h
    rw [List.head?_eq_getElem?,
      List.getElem?_eq_getElem (show 0 < P.tail.length by simp; omega)] at h
    simpa using h
  have hFP : ∀ f ∈ F, f ∉ P := fun f hf => (hmin.1.1 f hf).2
  have hFXY : ∀ f ∈ F, f ∉ X ∪ Y := fun f hf => (hmin.1.1 f hf).1
  have hFY : ∀ f ∈ F, ¬ VertexComplete G f Y := hmin.1.2.2
  have hFconn : ConnectedSet G F := hmin.1.2.1
  have hPY : ∀ w ∈ P, w ∉ Y := fun w hw => (hPXY w hw).2
  -- the third bullet of `Good` is vacuous, since no vertex of `F` is `X`-complete
  have hthird : ∀ q : List V, (∃ f ∈ F, VertexComplete G f X) →
      ({w : V | w ∈ q} = {p₁} ∨ pₙ ∈ q) := by
    rintro q ⟨f, hf, hfX⟩
    exact absurd hfX (hcon0 f hf)
  have hAdmSub : ∀ F' : Set V, F' ⊆ F → ConnectedSet G F' → Adm G X Y P F' :=
    fun F' hsub hconn => ⟨fun f hf => hmin.1.1 f (hsub hf), hconn,
      fun f hf => hFY f (hsub hf)⟩
  -- ### the engine: *"from the minimality of `F`"*
  -- no proper connected subset of `F` has two attachments straddling a `Y`-complete vertex
  have hstraddle : ∀ F' : Set V, F' ⊆ F → ConnectedSet G F' → F'.ncard < F.ncard →
      ∀ (u v w : ℕ) (hu : u < P.length) (hv : v < P.length) (hw : w < P.length),
        (P[u]'hu) ∈ attachments G F' {z : V | z ∈ P} →
        (P[v]'hv) ∈ attachments G F' {z : V | z ∈ P} →
        u < w → w < v → ¬ VertexComplete G (P[w]'hw) Y := by
    intro F' hsub hconn hlt u v w hu hv hw hatu hatv huw hwv hwY
    obtain ⟨q, hq, hqinf, hqatt, hqint, -⟩ := hmin.2.2 F' (hAdmSub F' hsub hconn) hlt
    have hqsub : ∀ z ∈ q, z ∈ P := by
      obtain ⟨s, t, hst⟩ := hqinf
      intro z hz
      rw [← hst]
      simp [hz]
    obtain ⟨r, hle, hmemq, hor⟩ := SubpathIsSlice.exists_index_of_subpath hP hq hqsub
    have hidx : ∀ (t : ℕ) (ht : t < P.length), (P[t]'ht) ∈ q → r ≤ t ∧ t < r + q.length := by
      intro t ht htq
      obtain ⟨k, hk, h1, h2, h3⟩ := (hmemq _).mp htq
      have hkt : k = t := (List.Nodup.getElem_inj_iff hnd).mp h3
      subst hkt
      exact ⟨h1, h2⟩
    obtain ⟨hru, hur⟩ := hidx u hu (hqatt _ hatu)
    obtain ⟨hrv, hvr⟩ := hidx v hv (hqatt _ hatv)
    have hqj : r + q.length - 1 - r + 1 = q.length := by omega
    have hmemint : (P[w]'hw) ∈ SPGT.interior ((P.drop r).take q.length) := by
      have h := PathBasics.mem_interior_slice_iff (p := P) hP
        (i := r) (j := r + q.length - 1) (by omega) (by omega) (x := P[w]'hw)
      rw [hqj] at h
      exact h.mpr ⟨w, hw, by omega, by omega, rfl⟩
    refine hqint (P[w]'hw) ?_ hwY
    rcases hor with he | he
    · rw [he]; exact hmemint
    · rw [← PathBasics.mem_interior_reverse, he]; exact hmemint
  -- ### `F` has an attachment in `P`
  have hAex : ∃ k, ∃ h : k < P.length, (P[k]'h) ∈ attachments G F {z : V | z ∈ P} := by
    by_contra hno
    refine hmin.2.1 ⟨[p₁], PathBasics.isPathList_singleton G p₁,
      singleton_infix (PathBasics.head_mem hhead), ?_, ?_, hthird _⟩
    · intro w hw
      obtain ⟨hwP, hwf⟩ := hw
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show w ∈ P from hwP)
      exact absurd ⟨k, hk, ⟨hwP, hwf⟩⟩ hno
    · intro w hw
      simp [SPGT.interior] at hw
  obtain ⟨a, halen, haatt, hamin⟩ : ∃ a, ∃ h : a < P.length,
      (P[a]'h) ∈ attachments G F {z : V | z ∈ P} ∧
      ∀ (k : ℕ) (hk : k < P.length), k < a →
        (P[k]'hk) ∉ attachments G F {z : V | z ∈ P} := by
    obtain ⟨h1, h2⟩ := Nat.find_spec hAex
    exact ⟨Nat.find hAex, h1, h2, fun k hk hka hm => Nat.find_min hAex hka ⟨hk, hm⟩⟩
  obtain ⟨c, hcltP, hcQ, hcmax⟩ :=
    exists_greatest
      (Q := fun k => ∃ h : k < P.length, (P[k]'h) ∈ attachments G F {z : V | z ∈ P})
      P.length ⟨a, halen, halen, haatt⟩
  obtain ⟨hclen, hcatt⟩ := hcQ
  have hac_le : a ≤ c := hcmax a halen ⟨halen, haatt⟩
  -- ### the minimal stretch spanning the attachments carries a `Y`-complete interior vertex
  have hac : a < c := by
    rcases lt_or_eq_of_le hac_le with h | h
    · exact h
    · exfalso
      refine hmin.2.1 ⟨[P[a]'halen], PathBasics.isPathList_singleton G _,
        singleton_infix (List.getElem_mem halen), ?_, ?_, hthird _⟩
      · intro w hw
        obtain ⟨hwP, hwf⟩ := hw
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show w ∈ P from hwP)
        have hka : a ≤ k := by
          by_contra hlt'
          exact hamin k hk (by omega) ⟨hwP, hwf⟩
        have hkc : k ≤ c := hcmax k hk ⟨hk, ⟨hwP, hwf⟩⟩
        have hkeq : k = a := by omega
        subst hkeq
        simp
      · intro w hw
        simp [SPGT.interior] at hw
  obtain ⟨b, hblt, hab, hbc, hbY⟩ : ∃ b, ∃ hb : b < P.length,
      a < b ∧ b < c ∧ VertexComplete G (P[b]'hb) Y := by
    by_contra hno
    refine hmin.2.1 ⟨(P.drop a).take (c - a + 1),
      PathBasics.isPathList_slice hP hac hclen, slice_infix P a _, ?_, ?_, hthird _⟩
    · intro w hw
      obtain ⟨hwP, hwf⟩ := hw
      obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (show w ∈ P from hwP)
      have hka : a ≤ k := by
        by_contra hlt'
        exact hamin k hk (by omega) ⟨hwP, hwf⟩
      have hkc : k ≤ c := hcmax k hk ⟨hk, ⟨hwP, hwf⟩⟩
      exact (PathBasics.mem_slice_iff P (le_of_lt hac) hclen).mpr ⟨k, hk, hka, hkc, rfl⟩
    · intro w hw hwY
      obtain ⟨k, hk, h1, h2, rfl⟩ := (PathBasics.mem_interior_slice_iff hP hac hclen).mp hw
      exact hno ⟨k, hk, h1, h2, hwY⟩
  -- ### *"`F` is the interior of a path `p_a-f₁-⋯-f_k-p_c`"*
  have hane : (P[a]'halen) ≠ (P[c]'hclen) :=
    PathBasics.path_ne_of_ne_index hP halen hclen (by omega)
  have hanadj : ¬ G.Adj (P[a]'halen) (P[c]'hclen) :=
    PathBasics.path_not_adj_of_gap hP halen hclen (by omega) (by omega)
  obtain ⟨Q, hQfrom, hQ3, hQint, hQconn, hQu, hQv⟩ :=
    MinimalConnectedIsPath.exists_path_interior_attached hFconn hane hanadj
      (fun hm => hFP _ hm (List.getElem_mem halen))
      (fun hm => hFP _ hm (List.getElem_mem hclen))
      (by obtain ⟨-, f, hf, hadj⟩ := haatt; exact ⟨f, hf, hadj⟩)
      (by obtain ⟨-, f, hf, hadj⟩ := hcatt; exact ⟨f, hf, hadj⟩)
  have hQl : IsPathList G Q := hQfrom.1
  have hQpos : 0 < Q.length := by omega
  have hQ0 : (Q[0]'hQpos) = (P[a]'halen) :=
    PathBasics.getElem_zero_of_head? hQfrom.2.1 hQpos
  have hQlast : (Q[Q.length - 1]'(by omega)) = (P[c]'hclen) :=
    PathBasics.getElem_last_of_getLast? hQfrom.2.2 hQpos
  have hIsub : {z : V | z ∈ SPGT.interior Q} ⊆ F := fun z hz => hQint z hz
  have hQatta : (P[a]'halen) ∈
      attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} := by
    obtain ⟨d, hd, hadj⟩ := hQu
    exact ⟨List.getElem_mem halen, d, hd, hadj⟩
  have hQattc : (P[c]'hclen) ∈
      attachments G {z : V | z ∈ SPGT.interior Q} {z : V | z ∈ P} := by
    obtain ⟨d, hd, hadj⟩ := hQv
    exact ⟨List.getElem_mem hclen, d, hd, hadj⟩
  have hFeq : F = {z : V | z ∈ SPGT.interior Q} := by
    by_contra hne
    exact hstraddle _ hIsub hQconn
      (Set.ncard_lt_ncard (HasSubset.Subset.ssubset_of_ne hIsub (fun h => hne h.symm))
        (Set.toFinite F))
      a c b halen hclen hblt hQatta hQattc hab hbc hbY
  -- ### *"From 18.5, `|F| ≥ 2`"*, so the path `p_a-f₁-⋯-f_k-p_c` has at least four vertices
  have hFcard : 2 ≤ F.ncard :=
    Thm186FSizeTwo.two_le_ncard_of_counterexample G hG X Y P p₁ pₙ hopt hhead hlast F
      hmin.1 hmin.2.1
  have hQ4 : 4 ≤ Q.length := by
    by_contra hlt4
    have hcard : F.ncard ≤ (SPGT.interior Q).length := by
      rw [hFeq, ← List.coe_toFinset, Set.ncard_coe_finset]
      exact List.toFinset_card_le _
    rw [PathBasics.interior_length] at hcard
    omega
  have hQ1lt : 1 < Q.length := by omega
  have hQklt : Q.length - 2 < Q.length := by omega
  have hQnd : Q.Nodup := PathBasics.path_nodup hQl
  have hFmem : ∀ z : V, z ∈ F ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ m + 2 ≤ Q.length ∧ (Q[m]'hm) = z := by
    intro z
    rw [hFeq]
    simp only [Set.mem_setOf_eq]
    constructor
    · exact fun hz => PathBasics.exists_getElem_of_mem_interior hQl hz
    · rintro ⟨m, hm, h1, h2, rfl⟩
      exact PathBasics.getElem_mem_interior hQl hm h1 h2
  have hf1F : (Q[1]'hQ1lt) ∈ F := (hFmem _).mpr ⟨1, hQ1lt, le_rfl, by omega, rfl⟩
  have hfkF : (Q[Q.length - 2]'hQklt) ∈ F :=
    (hFmem _).mpr ⟨Q.length - 2, hQklt, by omega, by omega, rfl⟩
  have hf1fk : (Q[1]'hQ1lt) ≠ (Q[Q.length - 2]'hQklt) :=
    PathBasics.path_ne_of_ne_index hQl hQ1lt hQklt (by omega)
  have hattRange : ∀ (j : ℕ) (hj : j < P.length) (f : V), f ∈ F → G.Adj (P[j]'hj) f →
      a ≤ j ∧ j ≤ c := by
    intro j hj f hf hadj
    have hmem : (P[j]'hj) ∈ attachments G F {z : V | z ∈ P} :=
      ⟨List.getElem_mem hj, f, hf, hadj⟩
    refine ⟨?_, hcmax j hj ⟨hj, hmem⟩⟩
    by_contra hlt'
    exact hamin j hj (by omega) hmem
  -- ### `F \ {f_k}` and `F \ {f₁}` : connected, and strictly smaller
  have hconn1 : ConnectedSet G
      {z : V | z ∈ SPGT.interior ((Q.drop 0).take (Q.length - 2 - 0 + 1))} :=
    MinimalConnectedIsPath.connectedSet_interior
      (PathBasics.isPathFrom_slice hQl (show (0 : ℕ) < Q.length - 2 by omega) hQklt)
  have hset1 : {z : V | z ∈ SPGT.interior ((Q.drop 0).take (Q.length - 2 - 0 + 1))}
      = F \ {Q[Q.length - 2]'hQklt} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    rw [PathBasics.mem_interior_slice_iff hQl (show (0 : ℕ) < Q.length - 2 by omega) hQklt]
    constructor
    · rintro ⟨m, hm, h1, h2, rfl⟩
      exact ⟨(hFmem _).mpr ⟨m, hm, by omega, by omega, rfl⟩,
        PathBasics.path_ne_of_ne_index hQl hm hQklt (by omega)⟩
    · rintro ⟨hzF, hzne⟩
      obtain ⟨m, hm, h1, h2, rfl⟩ := (hFmem z).mp hzF
      refine ⟨m, hm, by omega, ?_, rfl⟩
      by_contra hcon'
      have hmeq : m = Q.length - 2 := by omega
      subst hmeq
      exact hzne rfl
  have hconn2 : ConnectedSet G
      {z : V | z ∈ SPGT.interior ((Q.drop 1).take (Q.length - 1 - 1 + 1))} :=
    MinimalConnectedIsPath.connectedSet_interior
      (PathBasics.isPathFrom_slice hQl (show (1 : ℕ) < Q.length - 1 by omega) (by omega))
  have hset2 : {z : V | z ∈ SPGT.interior ((Q.drop 1).take (Q.length - 1 - 1 + 1))}
      = F \ {Q[1]'hQ1lt} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_singleton_iff]
    rw [PathBasics.mem_interior_slice_iff hQl (show (1 : ℕ) < Q.length - 1 by omega)
      (show Q.length - 1 < Q.length by omega)]
    constructor
    · rintro ⟨m, hm, h1, h2, rfl⟩
      exact ⟨(hFmem _).mpr ⟨m, hm, by omega, by omega, rfl⟩,
        PathBasics.path_ne_of_ne_index hQl hm hQ1lt (by omega)⟩
    · rintro ⟨hzF, hzne⟩
      obtain ⟨m, hm, h1, h2, rfl⟩ := (hFmem z).mp hzF
      refine ⟨m, hm, ?_, by omega, rfl⟩
      by_contra hcon'
      have hmeq : m = 1 := by omega
      subst hmeq
      exact hzne rfl
  have hconnA : ConnectedSet G (F \ {Q[Q.length - 2]'hQklt}) := hset1 ▸ hconn1
  have hconnB : ConnectedSet G (F \ {Q[1]'hQ1lt}) := hset2 ▸ hconn2
  have hcardA : (F \ {Q[Q.length - 2]'hQklt}).ncard < F.ncard :=
    Set.ncard_diff_singleton_lt_of_mem hfkF (Set.toFinite F)
  have hcardB : (F \ {Q[1]'hQ1lt}).ncard < F.ncard :=
    Set.ncard_diff_singleton_lt_of_mem hf1F (Set.toFinite F)
  have hsubA : F \ {Q[Q.length - 2]'hQklt} ⊆ F := Set.diff_subset
  have hsubB : F \ {Q[1]'hQ1lt} ⊆ F := Set.diff_subset
  have hadj_af1 : G.Adj (P[a]'halen) (Q[1]'hQ1lt) := by
    rw [← hQ0]
    exact (PathBasics.path_adj_iff hQl hQpos hQ1lt).mpr (Or.inl rfl)
  have hadj_cfk : G.Adj (P[c]'hclen) (Q[Q.length - 2]'hQklt) := by
    rw [← hQlast]
    exact (PathBasics.path_adj_iff hQl (show Q.length - 1 < Q.length by omega) hQklt).mpr
      (Or.inr (by omega))
  have hattA_a : (P[a]'halen) ∈
      attachments G (F \ {Q[Q.length - 2]'hQklt}) {z : V | z ∈ P} :=
    ⟨List.getElem_mem halen, Q[1]'hQ1lt, ⟨hf1F, hf1fk⟩, hadj_af1⟩
  have hattB_c : (P[c]'hclen) ∈ attachments G (F \ {Q[1]'hQ1lt}) {z : V | z ∈ P} :=
    ⟨List.getElem_mem hclen, Q[Q.length - 2]'hQklt, ⟨hfkF, fun h => hf1fk h.symm⟩, hadj_cfk⟩
  -- ### `P₁`, `P₂` minimal: `b₁` is the last attachment of `F \ {f_k}`, `a₂` the first of
  -- `F \ {f₁}`
  obtain ⟨b₁, hb₁ltP, hb₁Q, hb₁max⟩ :=
    exists_greatest
      (Q := fun k => ∃ h : k < P.length,
        (P[k]'h) ∈ attachments G (F \ {Q[Q.length - 2]'hQklt}) {z : V | z ∈ P})
      P.length ⟨a, halen, halen, hattA_a⟩
  obtain ⟨hb₁lt, hb₁att⟩ := hb₁Q
  have hBex : ∃ k, ∃ h : k < P.length,
      (P[k]'h) ∈ attachments G (F \ {Q[1]'hQ1lt}) {z : V | z ∈ P} := ⟨c, hclen, hattB_c⟩
  obtain ⟨a₂, ha₂lt, ha₂att, ha₂min⟩ : ∃ a₂, ∃ h : a₂ < P.length,
      (P[a₂]'h) ∈ attachments G (F \ {Q[1]'hQ1lt}) {z : V | z ∈ P} ∧
      ∀ (k : ℕ) (hk : k < P.length), k < a₂ →
        (P[k]'hk) ∉ attachments G (F \ {Q[1]'hQ1lt}) {z : V | z ∈ P} := by
    obtain ⟨h1, h2⟩ := Nat.find_spec hBex
    exact ⟨Nat.find hBex, h1, h2, fun k hk hka hm => Nat.find_min hBex hka ⟨hk, hm⟩⟩
  have ha_le_b₁ : a ≤ b₁ := hb₁max a halen ⟨halen, hattA_a⟩
  have ha₂_le_c : a₂ ≤ c := by
    by_contra hlt'
    exact ha₂min c hclen (by omega) hattB_c
  have hb₁_le_b : b₁ ≤ b := by
    by_contra hlt'
    exact hstraddle _ hsubA hconnA hcardA a b₁ b halen hb₁lt hblt hattA_a hb₁att hab
      (by omega) hbY
  have hb_le_a₂ : b ≤ a₂ := by
    by_contra hlt'
    exact hstraddle _ hsubB hconnB hcardB a₂ c b ha₂lt hclen hblt ha₂att hattB_c
      (by omega) hbc hbY
  -- the interior vertices of `f₁-⋯-f_k` attach only inside `[a₂, b₁]`
  have hmid : ∀ (m : ℕ) (hm : m < Q.length), 1 < m → m + 2 < Q.length →
      ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[j]'hj) (Q[m]'hm) → a₂ ≤ j ∧ j ≤ b₁ := by
    intro m hm h1 h2 j hj hadj
    have hmF : (Q[m]'hm) ∈ F := (hFmem _).mpr ⟨m, hm, by omega, by omega, rfl⟩
    have hmA : (Q[m]'hm) ∈ F \ {Q[Q.length - 2]'hQklt} :=
      ⟨hmF, PathBasics.path_ne_of_ne_index hQl hm hQklt (by omega)⟩
    have hmB : (Q[m]'hm) ∈ F \ {Q[1]'hQ1lt} :=
      ⟨hmF, PathBasics.path_ne_of_ne_index hQl hm hQ1lt (by omega)⟩
    constructor
    · by_contra hlt'
      exact ha₂min j hj (by omega) ⟨List.getElem_mem hj, _, hmB, hadj⟩
    · exact hb₁max j hj ⟨hj, ⟨List.getElem_mem hj, _, hmA, hadj⟩⟩
  have hf1range : ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[j]'hj) (Q[1]'hQ1lt) →
      a ≤ j ∧ j ≤ b₁ := by
    intro j hj hadj
    exact ⟨(hattRange j hj _ hf1F hadj).1,
      hb₁max j hj ⟨hj, ⟨List.getElem_mem hj, _, ⟨hf1F, hf1fk⟩, hadj⟩⟩⟩
  have hfkrange : ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[j]'hj) (Q[Q.length - 2]'hQklt) →
      a₂ ≤ j ∧ j ≤ c := by
    intro j hj hadj
    refine ⟨?_, (hattRange j hj _ hfkF hadj).2⟩
    by_contra hlt'
    exact ha₂min j hj (by omega)
      ⟨List.getElem_mem hj, _, ⟨hfkF, fun h => hf1fk h.symm⟩, hadj⟩
  -- ### *"`p₁-⋯-p_{a₁}-f₁-⋯-f_k-p_{b₂}-⋯-p_n` is a path `P'`"*
  have hLfrom : IsPathFrom G ((P.drop 0).take (a - 0 + 1)) (P[0]'h0lt) (P[a]'halen) :=
    isPathFrom_slice_le hP (Nat.zero_le a) halen
  have hRfrom : IsPathFrom G ((P.drop c).take (P.length - 1 - c + 1)) (P[c]'hclen)
      (P[P.length - 1]'hnlt) :=
    isPathFrom_slice_le hP (by omega) hnlt
  have hIQ : IsPathFrom G (SPGT.interior Q) (Q[1]'hQ1lt) (Q[Q.length - 2]'hQklt) :=
    PathGlue.isPathFrom_interior hQl (by omega)
  have hmemL : ∀ x : V, x ∈ (P.drop 0).take (a - 0 + 1) ↔
      ∃ (k : ℕ) (hk : k < P.length), k ≤ a ∧ (P[k]'hk) = x := by
    intro x
    rw [PathBasics.mem_slice_iff P (Nat.zero_le a) halen]
    constructor
    · rintro ⟨k, hk, -, h2, h3⟩; exact ⟨k, hk, h2, h3⟩
    · rintro ⟨k, hk, h2, h3⟩; exact ⟨k, hk, Nat.zero_le k, h2, h3⟩
  have hmemR : ∀ x : V, x ∈ (P.drop c).take (P.length - 1 - c + 1) ↔
      ∃ (k : ℕ) (hk : k < P.length), c ≤ k ∧ (P[k]'hk) = x := by
    intro x
    rw [PathBasics.mem_slice_iff P (show c ≤ P.length - 1 by omega) hnlt]
    constructor
    · rintro ⟨k, hk, h1, -, h3⟩; exact ⟨k, hk, h1, h3⟩
    · rintro ⟨k, hk, h1, h3⟩; exact ⟨k, hk, h1, by omega, h3⟩
  have hmemI : ∀ x : V, x ∈ SPGT.interior Q ↔
      ∃ (m : ℕ) (hm : m < Q.length), 1 ≤ m ∧ m + 2 ≤ Q.length ∧ (Q[m]'hm) = x := by
    intro x
    constructor
    · exact fun hx => PathBasics.exists_getElem_of_mem_interior hQl hx
    · rintro ⟨m, hm, h1, h2, rfl⟩
      exact PathBasics.getElem_mem_interior hQl hm h1 h2
  have hM : IsPathFrom G (SPGT.interior Q ++ (P.drop c).take (P.length - 1 - c + 1))
      (Q[1]'hQ1lt) (P[P.length - 1]'hnlt) := by
    refine PathGlue.glue_path hIQ hRfrom ?_ ?_
    · intro x hx hcon
      obtain ⟨k, hk, -, rfl⟩ := (hmemR _).mp hcon
      exact hFP _ (hQint _ hx) (List.getElem_mem hk)
    · intro x hx y hy
      obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hmemI _).mp hx
      obtain ⟨j, hj, hjc, rfl⟩ := (hmemR _).mp hy
      constructor
      · intro hadj
        have hmF : (Q[m]'hm) ∈ F := (hFmem _).mpr ⟨m, hm, hm1, hm2, rfl⟩
        have hjle : j ≤ c := (hattRange j hj _ hmF hadj.symm).2
        have hjeq : j = c := by omega
        subst hjeq
        have hadjQ : G.Adj (Q[Q.length - 1]'(by omega)) (Q[m]'hm) := by
          rw [hQlast]; exact hadj.symm
        have hidx := (PathBasics.path_adj_iff hQl (show Q.length - 1 < Q.length by omega)
          hm).mp hadjQ
        have hmeq : m = Q.length - 2 := by omega
        subst hmeq
        exact ⟨rfl, rfl⟩
      · rintro ⟨h1, h2⟩
        have hm' : m = Q.length - 2 := (List.Nodup.getElem_inj_iff hQnd).mp h1
        have hj' : j = c := (List.Nodup.getElem_inj_iff hnd).mp h2
        subst hm'
        subst hj'
        exact hadj_cfk.symm
  have hP'from0 : IsPathFrom G ((P.drop 0).take (a - 0 + 1) ++
      (SPGT.interior Q ++ (P.drop c).take (P.length - 1 - c + 1)))
      (P[0]'h0lt) (P[P.length - 1]'hnlt) := by
    refine PathGlue.glue_path hLfrom hM ?_ ?_
    · intro x hx hcon
      obtain ⟨i, hi, hia, rfl⟩ := (hmemL _).mp hx
      rw [List.mem_append] at hcon
      rcases hcon with h | h
      · exact hFP _ (hQint _ h) (List.getElem_mem hi)
      · obtain ⟨k, hk, hkc, hk2⟩ := (hmemR _).mp h
        have hki : k = i := (List.Nodup.getElem_inj_iff hnd).mp hk2
        omega
    · intro x hx y hy
      obtain ⟨i, hi, hia, rfl⟩ := (hmemL _).mp hx
      rw [List.mem_append] at hy
      rcases hy with hy | hy
      · obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hmemI _).mp hy
        constructor
        · intro hadj
          have hmF : (Q[m]'hm) ∈ F := (hFmem _).mpr ⟨m, hm, hm1, hm2, rfl⟩
          have hia' : a ≤ i := (hattRange i hi _ hmF hadj).1
          have hieq : i = a := by omega
          subst hieq
          have hadjQ : G.Adj (Q[0]'hQpos) (Q[m]'hm) := by rw [hQ0]; exact hadj
          have hidx := (PathBasics.path_adj_iff hQl hQpos hm).mp hadjQ
          have hmeq : m = 1 := by omega
          subst hmeq
          exact ⟨rfl, rfl⟩
        · rintro ⟨h1, h2⟩
          have hi' : i = a := (List.Nodup.getElem_inj_iff hnd).mp h1
          have hm' : m = 1 := (List.Nodup.getElem_inj_iff hQnd).mp h2
          subst hi'
          subst hm'
          exact hadj_af1
      · obtain ⟨j, hj, hjc, rfl⟩ := (hmemR _).mp hy
        constructor
        · intro hadj
          exact absurd hadj (PathBasics.path_not_adj_of_gap hP hi hj (by omega) (by omega))
        · rintro ⟨-, h2⟩
          refine absurd hf1F (fun hh => hFP _ hh ?_)
          rw [← h2]
          exact List.getElem_mem hj
  set P' : List V := (P.drop 0).take (a - 0 + 1) ++
      (SPGT.interior Q ++ (P.drop c).take (P.length - 1 - c + 1)) with hP'def
  have hP'from : IsPathFrom G P' p₁ pₙ := by
    rw [← hp0, ← hpn]; exact hP'from0
  have hP'l : IsPathList G P' := hP'from.1
  have hmemP' : ∀ x : V, x ∈ P' ↔
      ((∃ (k : ℕ) (hk : k < P.length), (k ≤ a ∨ c ≤ k) ∧ (P[k]'hk) = x) ∨
        x ∈ SPGT.interior Q) := by
    intro x
    rw [hP'def, List.mem_append, List.mem_append, hmemL x, hmemR x]
    constructor
    · rintro (⟨k, hk, h1, h2⟩ | h | ⟨k, hk, h1, h2⟩)
      · exact Or.inl ⟨k, hk, Or.inl h1, h2⟩
      · exact Or.inr h
      · exact Or.inl ⟨k, hk, Or.inr h1, h2⟩
    · rintro (⟨k, hk, (h1 | h1), h2⟩ | h)
      · exact Or.inl ⟨k, hk, h1, h2⟩
      · exact Or.inr (Or.inr ⟨k, hk, h1, h2⟩)
      · exact Or.inr (Or.inl h)
  have hP'len : P'.length = (a - 0 + 1) + ((Q.length - 2) + (P.length - 1 - c + 1)) := by
    rw [hP'def, List.length_append, List.length_append,
      PathBasics.length_slice P (Nat.zero_le a) halen,
      PathBasics.length_slice P (show c ≤ P.length - 1 by omega) hnlt,
      PathBasics.interior_length]
  -- ### *"contrary to the optimality of `(X,Y,P)`"*
  have hP'Y : ∀ w ∈ P', VertexComplete G w Y → w = p₁ := by
    intro w hw hwY
    by_contra hwne
    have hwF : w ∉ F := fun h => hFY w h hwY
    obtain ⟨jw, hjw, hjwor, rfl⟩ : ∃ (k : ℕ) (hk : k < P.length), (k ≤ a ∨ c ≤ k) ∧
        (P[k]'hk) = w := by
      rcases (hmemP' w).mp hw with h | h
      · exact h
      · exact absurd (hQint w h) hwF
    have hjw0 : jw ≠ 0 := by
      rintro rfl
      exact hwne (by rw [← hp0])
    have hjwn : jw ≠ P.length - 1 := by
      rintro rfl
      exact hpₙY (by rw [← hpn]; exact hwY)
    have hP'5 : 5 ≤ P'.length := by
      rcases hjwor with h | h
      · omega
      · omega
    have hP'1lt : 1 < P'.length := by omega
    have hP'0 : (P'[0]'(by omega)) = (P[0]'h0lt) := by
      rw [PathBasics.getElem_zero_of_head? hP'from.2.1 (by omega), hp0]
    have hadj01 : G.Adj (P'[0]'(by omega : 0 < P'.length)) (P'[1]'hP'1lt) :=
      (PathBasics.path_adj_iff hP'l (by omega) hP'1lt).mpr (Or.inl rfl)
    have hP'2 : ¬ VertexComplete G (P'[1]'hP'1lt) Y := by
      rcases (hmemP' _).mp (List.getElem_mem hP'1lt) with ⟨k, hk, hkor, hkeq⟩ | hint
      · have hadj' : G.Adj (P[0]'h0lt) (P[k]'hk) := by
          rw [← hP'0, hkeq]; exact hadj01
        have hidx := (PathBasics.path_adj_iff hP h0lt hk).mp hadj'
        have hk1 : k = 1 := by omega
        subst hk1
        rw [← hkeq, hp1]
        exact hq₂Y
      · exact hFY _ (hQint _ hint)
    have hout5 : ∀ v ∈ P', v ∉ X ∧ v ∉ Y := by
      intro v hv
      rcases (hmemP' v).mp hv with ⟨k, hk, -, rfl⟩ | hint
      · exact hPXY _ (List.getElem_mem hk)
      · exact ⟨fun h => hFXY _ (hQint _ hint) (Set.mem_union_left _ h),
          fun h => hFXY _ (hQint _ hint) (Set.mem_union_right _ h)⟩
    have hXcompl : ∀ v ∈ P', VertexComplete G v X ↔ (v = p₁ ∨ v = pₙ) := by
      intro v hv
      rcases (hmemP' v).mp hv with ⟨k, hk, -, rfl⟩ | hint
      · exact hXuniq _ (List.getElem_mem hk)
      · constructor
        · intro hvX
          exact absurd hvX (hcon0 _ (hQint _ hint))
        · rintro (rfl | rfl)
          · exact absurd (hQint _ hint) (fun h => hFP _ h (PathBasics.head_mem hhead))
          · exact absurd (hQint _ hint) (fun h => hFP _ h (PathBasics.getLast_mem hlast))
    have hpw : IsPseudowheel G X Y P' :=
      PseudowheelBuilder.isPseudowheel_mk hXY hXne hYne hXanti hYanti hcompl
        hP'from (tail_head?_getElem hP'1lt) hout5 hP'5 hXcompl hp₁Y
        ⟨P[jw]'hjw, hw, hwne, hwY⟩ hP'2 hpₙY
    have hsubset : {v : V | v ∈ P' ∧ VertexComplete G v Y} ⊆
        {v : V | v ∈ P ∧ VertexComplete G v Y} := by
      rintro v ⟨hvP', hvY⟩
      refine ⟨?_, hvY⟩
      rcases (hmemP' v).mp hvP' with ⟨k, hk, -, rfl⟩ | hint
      · exact List.getElem_mem hk
      · exact absurd hvY (hFY _ (hQint _ hint))
    have hbnot : (P[b]'hblt) ∉ {v : V | v ∈ P' ∧ VertexComplete G v Y} := by
      rintro ⟨hbP', -⟩
      rcases (hmemP' _).mp hbP' with ⟨k, hk, hkor, hkeq⟩ | hint
      · have hkb : k = b := (List.Nodup.getElem_inj_iff hnd).mp hkeq
        omega
      · exact hFP _ (hQint _ hint) (List.getElem_mem hblt)
    exact hopt.2.1 ⟨X, Y, P', hpw, Set.ncard_lt_ncard
      ((Set.ssubset_iff_of_subset hsubset).mpr
        ⟨P[b]'hblt, ⟨List.getElem_mem hblt, hbY⟩, hbnot⟩)
      (Set.toFinite _)⟩
  -- ### *"all the `Y`-complete vertices of `P` belong to `{p_{b₁}, …, p_{a₂}}`, except `p₁`"*
  have hloc : ∀ (j : ℕ) (hj : j < P.length), VertexComplete G (P[j]'hj) Y →
      j = 0 ∨ (b₁ ≤ j ∧ j ≤ a₂) := by
    intro j hj hjY
    by_cases hja : j ≤ a
    · left
      have hmem : (P[j]'hj) ∈ P' := (hmemP' _).mpr (Or.inl ⟨j, hj, Or.inl hja, rfl⟩)
      have heq := hP'Y _ hmem hjY
      rw [← hp0] at heq
      exact (List.Nodup.getElem_inj_iff hnd).mp heq
    · by_cases hjc : c ≤ j
      · left
        have hmem : (P[j]'hj) ∈ P' := (hmemP' _).mpr (Or.inl ⟨j, hj, Or.inr hjc, rfl⟩)
        have heq := hP'Y _ hmem hjY
        rw [← hp0] at heq
        exact (List.Nodup.getElem_inj_iff hnd).mp heq
      · right
        constructor
        · by_contra hlt'
          exact hstraddle _ hsubA hconnA hcardA a b₁ j halen hb₁lt hj hattA_a hb₁att
            (by omega) (by omega) hjY
        · by_contra hlt'
          exact hstraddle _ hsubB hconnB hcardB a₂ c j ha₂lt hclen hj ha₂att hattB_c
            (by omega) (by omega) hjY
  -- ### *"By 18.4 there are an odd number, at least 3, of `Y`-complete edges in this path"*
  have h184 := _root_.Workspace.Statements.S18.SPGT.thm_18_4 G hG X Y P hopt.1
  have h3 : 3 ≤ (HoleYEdgeParity.yEdges G Y P).ncard := h184.1.2
  have hoddP : Odd (HoleYEdgeParity.yEdges G Y P).ncard := h184.1.1
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · exfalso
      have hbe : b = 1 := by omega
      subst hbe
      exact hq₂Y (by rw [← hp1]; exact hbY)
    · exact h
  rcases eq_or_lt_of_le (le_trans hb₁_le_b hb_le_a₂) with heq | hltba
  · -- `b₁ = a₂ = b`: `p₁` and `p_b` are the only `Y`-complete vertices, so `P` has no
    -- `Y`-complete edge at all — contrary to 18.4
    have hempty : HoleYEdgeParity.yEdges G Y P = ∅ := by
      ext e
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, v, hv, rfl, hadj, huY, hvY⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
      have hI := hloc i hi huY
      have hJ := hloc j hj hvY
      have hidx := (PathBasics.path_adj_iff hP hi hj).mp hadj
      rcases hI with hI | hI <;> rcases hJ with hJ | hJ <;> omega
    rw [hempty, Set.ncard_empty] at h3
    omega
  · -- `b₁ < a₂`: *"`f₁-⋯-f_k-p_{a₂}-p_{a₂−1}-⋯-p_{b₁}-f₁` is a hole"*
    have hadj_f1b₁ : G.Adj (P[b₁]'hb₁lt) (Q[1]'hQ1lt) := by
      obtain ⟨-, z, ⟨hzF, hzne⟩, hadjz⟩ := hb₁att
      obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hFmem z).mp hzF
      rcases Nat.lt_or_ge 1 m with hlt1 | hle1
      · rcases Nat.lt_or_ge (m + 2) Q.length with hlt2 | hge2
        · exfalso
          have := hmid m hm hlt1 hlt2 b₁ hb₁lt hadjz
          omega
        · exfalso
          have hmeq : m = Q.length - 2 := by omega
          subst hmeq
          exact hzne rfl
      · have hmeq : m = 1 := by omega
        subst hmeq
        exact hadjz
    have hadj_fka₂ : G.Adj (P[a₂]'ha₂lt) (Q[Q.length - 2]'hQklt) := by
      obtain ⟨-, z, ⟨hzF, hzne⟩, hadjz⟩ := ha₂att
      obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hFmem z).mp hzF
      rcases Nat.lt_or_ge (m + 2) Q.length with hlt2 | hge2
      · rcases Nat.lt_or_ge 1 m with hlt1 | hle1
        · exfalso
          have := hmid m hm hlt1 hlt2 a₂ ha₂lt hadjz
          omega
        · exfalso
          have hmeq : m = 1 := by omega
          subst hmeq
          exact hzne rfl
      · have hmeq : m = Q.length - 2 := by omega
        subst hmeq
        exact hadjz
    have hslen : ((P.drop b₁).take (a₂ - b₁ + 1)).length = a₂ - b₁ + 1 :=
      PathBasics.length_slice P (le_of_lt hltba) ha₂lt
    have hSfrom : IsPathFrom G ((P.drop b₁).take (a₂ - b₁ + 1)) (P[b₁]'hb₁lt)
        (P[a₂]'ha₂lt) :=
      PathBasics.isPathFrom_slice hP hltba ha₂lt
    have hSrev : IsPathFrom G (((P.drop b₁).take (a₂ - b₁ + 1)).reverse) (P[a₂]'ha₂lt)
        (P[b₁]'hb₁lt) :=
      PathBasics.isPathFrom_reverse hSfrom
    have hmemS : ∀ x : V, x ∈ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse ↔
        ∃ (k : ℕ) (hk : k < P.length), b₁ ≤ k ∧ k ≤ a₂ ∧ (P[k]'hk) = x := by
      intro x
      rw [List.mem_reverse, PathBasics.mem_slice_iff P (le_of_lt hltba) ha₂lt]
    have hHole : IsHoleList G
        (SPGT.interior Q ++ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse) := by
      refine PathGlue.glue_hole hIQ hSrev ?_ ?_ ?_
      · intro x hx hcon
        obtain ⟨k, hk, -, -, rfl⟩ := (hmemS _).mp hcon
        exact hFP _ (hQint _ hx) (List.getElem_mem hk)
      · intro x hx y hy
        obtain ⟨m, hm, hm1, hm2, rfl⟩ := (hmemI _).mp hx
        obtain ⟨j, hj, hj1, hj2, rfl⟩ := (hmemS _).mp hy
        constructor
        · intro hadj
          rcases Nat.lt_or_ge 1 m with hlt1 | hle1
          · rcases Nat.lt_or_ge (m + 2) Q.length with hlt2 | hge2
            · exfalso
              have := hmid m hm hlt1 hlt2 j hj hadj.symm
              omega
            · have hmeq : m = Q.length - 2 := by omega
              subst hmeq
              have hja := (hfkrange j hj hadj.symm).1
              have hjeq : j = a₂ := by omega
              subst hjeq
              exact Or.inl ⟨rfl, rfl⟩
          · have hmeq : m = 1 := by omega
            subst hmeq
            have hjb := (hf1range j hj hadj.symm).2
            have hjeq : j = b₁ := by omega
            subst hjeq
            exact Or.inr ⟨rfl, rfl⟩
        · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
          · have hm' : m = Q.length - 2 := (List.Nodup.getElem_inj_iff hQnd).mp h1
            have hj' : j = a₂ := (List.Nodup.getElem_inj_iff hnd).mp h2
            subst hm'
            subst hj'
            exact hadj_fka₂.symm
          · have hm' : m = 1 := (List.Nodup.getElem_inj_iff hQnd).mp h1
            have hj' : j = b₁ := (List.Nodup.getElem_inj_iff hnd).mp h2
            subst hm'
            subst hj'
            exact hadj_f1b₁.symm
      · rw [PathBasics.interior_length, List.length_reverse, hslen]
        omega
    have hHY : ∀ w ∈ (SPGT.interior Q ++ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse), w ∉ Y := by
      intro w hw
      rw [List.mem_append] at hw
      rcases hw with h | h
      · exact fun hc => hFXY _ (hQint _ h) (Set.mem_union_right _ hc)
      · obtain ⟨k, hk, -, -, rfl⟩ := (hmemS _).mp h
        exact hPY _ (List.getElem_mem hk)
    -- *"the `Y`-complete edges in it are precisely the `Y`-complete edges in `P`"*
    have hIn : ∀ (i : ℕ) (hi : i < P.length), VertexComplete G (P[i]'hi) Y →
        ∀ (j : ℕ) (hj : j < P.length), G.Adj (P[i]'hi) (P[j]'hj) →
        VertexComplete G (P[j]'hj) Y →
        (P[i]'hi) ∈ (SPGT.interior Q ++ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse) := by
      intro i hi hiY j hj hadj hjY
      rcases hloc i hi hiY with hi0 | hib
      · exfalso
        subst hi0
        have hidx := (PathBasics.path_adj_iff hP hi hj).mp hadj
        have hj1 : j = 1 := by omega
        subst hj1
        exact hq₂Y (by rw [← hp1]; exact hjY)
      · rw [List.mem_append]
        exact Or.inr ((hmemS _).mpr ⟨i, hi, hib.1, hib.2, rfl⟩)
    have hyeq : HoleYEdgeParity.yEdges G Y
        (SPGT.interior Q ++ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse)
        = HoleYEdgeParity.yEdges G Y P := by
      have hto : ∀ w ∈ (SPGT.interior Q ++ ((P.drop b₁).take (a₂ - b₁ + 1)).reverse),
          VertexComplete G w Y → w ∈ P := by
        intro w hw hwY
        rw [List.mem_append] at hw
        rcases hw with h | h
        · exact absurd hwY (hFY _ (hQint _ h))
        · obtain ⟨k, hk, -, -, rfl⟩ := (hmemS _).mp h
          exact List.getElem_mem hk
      ext e
      constructor
      · rintro ⟨u, hu, v, hv, rfl, hadj, huY, hvY⟩
        exact ⟨u, hto u hu huY, v, hto v hv hvY, rfl, hadj, huY, hvY⟩
      · rintro ⟨u, hu, v, hv, rfl, hadj, huY, hvY⟩
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hv
        exact ⟨_, hIn i hi huY j hj hadj hvY, _, hIn j hj hvY i hi hadj.symm huY, rfl,
          hadj, huY, hvY⟩
    exact HoleYEdgeParity.not_odd_ge_three_yEdges' hBerge hYanti hHole hHY
      (by rw [hyeq]; exact hoddP) (by rw [hyeq]; exact h3)

end Workspace.ProofLemmas.Thm186Claim1
