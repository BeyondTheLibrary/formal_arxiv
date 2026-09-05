import Mathlib
import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Prisms
import Workspace.ProofLemmas.Thm101Assembly
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.Statements.S02.Thm_2_4

/-!
# 10.1, claim (2): `X₁ ⊆ A` and `X₂ ⊆ V(R₁)`

PAPER (proof of 10.1, printed p. 57):

> *"We may therefore assume that `n ≥ 2`.  Let `X₁` be the set of attachments of `F \ {f₁}`,
> and `X₂` the set of attachments of `F \ {fₙ}`.  From the minimality of `F`, both `X₁` and
> `X₂` are local.  Moreover, `X = X₁ ∪ X₂`, and for `2 ≤ i ≤ n − 1`, every neighbour of `fᵢ` in
> `K` belongs to `X₁ ∩ X₂`."*
>
> **(2) If `X₁ ⊆ A` and `X₂ ⊆ V(R₁)` then the theorem holds.**
>
> *"For then `f₁` has at least one neighbour in `R₁ \ a₁`, and `fₙ` is adjacent to at least one
> of `a₂, a₃`, and there are no other edges between `F` and `V(K) \ {a₁}`.  If `fₙ` is adjacent
> to both `a₂, a₃` then statement 4 of the theorem holds, so we assume it is not adjacent to
> `a₃`.  But then `a₂` can be linked onto the triangle `B`, via
> `a₂-fₙ-fₙ₋₁-⋯-f₁-d₁-D₁-b₁`, `a₂-R₂-b₂`, `a₂-a₃-R₃-b₃`, contrary to 2.4.  This proves (2)."*

`X₁` and `X₂` are `attachments G (F \ {f₁}) K` and `attachments G (F \ {fₙ}) K`; the two
identities the paper records just before the claim (`X = X₁ ∪ X₂`, and every `K`-neighbour of
an interior vertex of the path lies in `X₁ ∩ X₂`) are automatic from those definitions once
`n ≥ 2`, so they are not hypotheses.  The single appeal to 2.4 is
`Workspace.Statements.S02.SPGT.thm_2_4`, fed through
`Workspace.ProofLemmas.Thm101LinkOntoTriangle.linkedOntoTriangle_of_sectors` with the three
sectors `F ∪ V(D₁)`, `V(R₂) \ {a₂}` and `V(R₃)`.

## Deviation from the scoping lane's signature: `hFloc` is load-bearing

The scoped signature omitted the non-locality hypothesis
`¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K)`.  Without it the statement is
false, and the printed proof uses it twice, in its very first sentence:

* *"`f₁` has at least one neighbour in `R₁ \ a₁`"* — otherwise `X₂ ⊆ {a₁} ⊆ A`, hence
  `X = X₁ ∪ X₂ ⊆ A` is local;
* *"`fₙ` is adjacent to at least one of `a₂, a₃`"* — otherwise `X₁ ⊆ {a₁} ⊆ V(R₁)`, hence
  `X ⊆ V(R₁)` is local.

(Concretely: take `F = {f₁, fₙ}` with `f₁fₙ` an edge and `a₁` the only `K`-neighbour of either.
Then `X₁ = X₂ = {a₁}`, satisfying `X₁ ⊆ A` and `X₂ ⊆ V(R₁)`, neither vertex is major — but no
alternative of 10.1 holds, since each of 10.1.1–10.1.4 asks `f₁` for two neighbours in `V(K)`.)
So `hFloc` is stated here exactly as in `Thm101ClaimThree` and `Thm101Endgame`; the 10.1 call
site has it available verbatim.

**Call site**: the proof of `Workspace.Statements.S10.SPGT.thm_10_1`, the `n ≥ 2` branch.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace Workspace.ProofLemmas.Thm101ClaimTwo

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.Appearances Workspace.Types.Appearances.SPGT
open Workspace.Types.Prisms Workspace.Types.Prisms.SPGT
open Workspace.ProofLemmas
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem fin3_cases : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2 := by decide

private theorem perm_of_three : ∀ i j m : Fin 3, i ≠ j → i ≠ m → j ≠ m →
    ∃ σ : Equiv.Perm (Fin 3), σ 0 = i ∧ σ 1 = j ∧ σ 2 = m := by decide

private theorem two_le_length {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (h : FormPrism G a b (R 0) (R 1) (R 2)) (k : Fin 3) :
    2 ≤ (R k).length := by
  obtain ⟨-, -, hAB, hp, -⟩ := PrismSymmetry.formPrism_family.mp h
  by_contra hcon
  have hne : R k ≠ [] := (hp k).1.1
  have hpos : 0 < (R k).length := List.length_pos_of_ne_nil hne
  have hone : (R k).length = 1 := by omega
  obtain ⟨c, hc⟩ := List.length_eq_one_iff.mp hone
  have ha := (hp k).2.1
  have hb := (hp k).2.2
  rw [hc] at ha hb
  simp only [List.head?_cons, List.getLast?_singleton, Option.some.injEq] at ha hb
  exact hAB k k (ha.symm.trans hb)

private theorem tri_own_path {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (h : FormPrism G a b (R 0) (R 1) (R 2))
    (i k : Fin 3) (hk : a k ∈ R i) : k = i := by
  obtain ⟨hA, -, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  have hthird : ∀ i k : Fin 3, i ≠ k → ∃ m : Fin 3, m ≠ i ∧ m ≠ k := by decide
  by_contra hne
  obtain ⟨m, hmi, hmk⟩ := hthird i k (fun hc => hne hc.symm)
  have ham : a m ∈ R m := PathBasics.head_mem (hp m).2.1
  rcases (hedge i m (Ne.symm hmi) (a k) hk (a m) ham).mp
      (hA k m (Ne.symm hmk)) with hki | hkb
  · have hadj := hA k i hne
    rw [hki.1] at hadj
    exact G.irrefl hadj
  · exact hAB k i hkb.1

private theorem tri_own_path' {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (h : FormPrism G a b (R 0) (R 1) (R 2))
    (i k : Fin 3) (hk : b k ∈ R i) : k = i := by
  obtain ⟨-, hB, hAB, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  have hthird : ∀ i k : Fin 3, i ≠ k → ∃ m : Fin 3, m ≠ i ∧ m ≠ k := by decide
  by_contra hne
  obtain ⟨m, hmi, hmk⟩ := hthird i k (fun hc => hne hc.symm)
  have hbm : b m ∈ R m := PathBasics.getLast_mem (hp m).2.2
  rcases (hedge i m (Ne.symm hmi) (b k) hk (b m) hbm).mp
      (hB k m (Ne.symm hmk)) with hba | hki
  · exact hAB i k hba.1.symm
  · have hadj := hB k i hne
    rw [hki.1] at hadj
    exact G.irrefl hadj

private theorem paths_disjoint {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (h : FormPrism G a b (R 0) (R 1) (R 2))
    {i j : Fin 3} (hij : i ≠ j) {x : V} (hxi : x ∈ R i) (hxj : x ∈ R j) : False := by
  obtain ⟨-, -, -, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp h
  obtain ⟨z, hzj, hxz⟩ : ∃ z : V, z ∈ R j ∧ G.Adj x z := by
    obtain ⟨t, ht, hxt⟩ := List.getElem_of_mem hxj
    have hL := two_le_length h j
    by_cases hc : t + 1 < (R j).length
    · refine ⟨(R j)[t + 1], List.getElem_mem _, ?_⟩
      have hh := (PathBasics.path_adj_iff (hp j).1 ht hc).mpr (Or.inl rfl)
      rw [hxt] at hh
      exact hh
    · have ht1 : 1 ≤ t := by omega
      have hlt : t - 1 < (R j).length := by omega
      refine ⟨(R j)[t - 1], List.getElem_mem _, ?_⟩
      have hh := (PathBasics.path_adj_iff (hp j).1 ht hlt).mpr (Or.inr (by omega))
      rw [hxt] at hh
      exact hh
  rcases (hedge i j hij x hxi z hzj).mp hxz with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hij (tri_own_path h j i (h1 ▸ hxj))
  · exact hij (tri_own_path' h j i (h1 ▸ hxj))

private theorem exists_greatest {Q : ℕ → Prop} : ∀ n : ℕ, (∃ k, k < n ∧ Q k) →
    ∃ k, k < n ∧ Q k ∧ ∀ m, m < n → Q m → m ≤ k := by
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
        rcases (by omega : k < n ∨ k = n) with hlt | rfl
        · exact hlt
        · exact absurd hQk hQ
      obtain ⟨k, hk, hQk, hmax⟩ := ih hex'
      exact ⟨k, by omega, hQk, fun m hm hQm => by
        rcases (by omega : m < n ∨ m = n) with hlt | rfl
        · exact hmax m hlt hQm
        · exact absurd hQm hQ⟩

private theorem mem_drop_iff {p : List V} {k : ℕ} {y : V} :
    y ∈ p.drop k ↔ ∃ (s : ℕ) (hs : k + s < p.length), p[k + s]'hs = y := by
  constructor
  · intro hy
    obtain ⟨t, ht, hty⟩ := List.getElem_of_mem hy
    have htlen : t < p.length - k := by simpa using ht
    exact ⟨t, by omega, by rw [← hty]; exact (List.getElem_drop ..).symm⟩
  · rintro ⟨s, hs, rfl⟩
    have hlt : s < (p.drop k).length := by rw [List.length_drop]; omega
    have he : (p.drop k)[s]'hlt = p[k + s]'hs := List.getElem_drop ..
    rw [← he]
    exact List.getElem_mem _

private theorem drop_pathFrom {G : SimpleGraph V} {p : List V} {u w : V}
    (hp : IsPathFrom G p u w) {k : ℕ} (hk : k < p.length) :
    IsPathFrom G (p.drop k) (p[k]'hk) w :=
  ⟨PathBasics.isPathList_drop hp.1 hk,
    by rw [List.head?_drop, List.getElem?_eq_getElem hk],
    by rw [List.getLast?_drop, if_neg (by omega)]; exact hp.2.2⟩

private theorem last_attach {G : SimpleGraph V} {p : List V} {u w v : V}
    (hp : IsPathFrom G p u w) (hex : ∃ x ∈ p, G.Adj v x) :
    ∃ (k : ℕ) (hk : k < p.length),
      IsPathFrom G (p.drop k) (p[k]'hk) w ∧ G.Adj v (p[k]'hk) ∧
      (∀ y ∈ p.drop k, y ∈ p) ∧
      (∀ y ∈ p.drop k, G.Adj v y → y = p[k]'hk) ∧
      (∀ t : ℕ, ∀ ht : t < p.length, G.Adj v (p[t]'ht) → t ≤ k) := by
  classical
  obtain ⟨k, hk, ⟨hk', hadj⟩, hmax⟩ :
      ∃ k, k < p.length ∧ (∃ hk : k < p.length, G.Adj v (p[k]'hk)) ∧
        ∀ m, m < p.length → (∃ hm : m < p.length, G.Adj v (p[m]'hm)) → m ≤ k := by
    apply exists_greatest p.length
    obtain ⟨x, hxp, hadjx⟩ := hex
    obtain ⟨j, hj, hjx⟩ := List.getElem_of_mem hxp
    exact ⟨j, hj, ⟨hj, by rwa [hjx]⟩⟩
  refine ⟨k, hk, drop_pathFrom hp hk, hadj, fun y hy => List.mem_of_mem_drop hy, ?_, ?_⟩
  · intro y hy hadjy
    obtain ⟨s, hs, hsy⟩ := mem_drop_iff.mp hy
    have hle := hmax (k + s) hs ⟨hs, by rwa [hsy]⟩
    have hs0 : s = 0 := by omega
    subst s
    simpa using hsy.symm
  · intro t ht hadjt
    exact hmax t ht ⟨ht, hadjt⟩

private theorem link_direct {G : SimpleGraph V} {v a₁ a₂ a₃ : V}
    {p₁ p₂ p₃ : List V}
    (h1 : IsPathList G p₁) (h2 : IsPathList G p₂) (h3 : IsPathList G p₃)
    (d12 : ∀ x ∈ p₁, x ∉ p₂) (d13 : ∀ x ∈ p₁, x ∉ p₃) (d23 : ∀ x ∈ p₂, x ∉ p₃)
    (e1 : p₁.head? = some a₁ ∨ p₁.getLast? = some a₁)
    (e2 : p₂.head? = some a₂ ∨ p₂.getLast? = some a₂)
    (e3 : p₃.head? = some a₃ ∨ p₃.getLast? = some a₃)
    (t12 : G.Adj a₁ a₂) (t13 : G.Adj a₁ a₃) (t23 : G.Adj a₂ a₃)
    (c12 : ∀ x ∈ p₁, ∀ y ∈ p₂, G.Adj x y → x = a₁ ∧ y = a₂)
    (c13 : ∀ x ∈ p₁, ∀ y ∈ p₃, G.Adj x y → x = a₁ ∧ y = a₃)
    (c23 : ∀ x ∈ p₂, ∀ y ∈ p₃, G.Adj x y → x = a₂ ∧ y = a₃)
    (n1 : ∃ x ∈ p₁, G.Adj v x) (n2 : ∃ x ∈ p₂, G.Adj v x)
    (n3 : ∃ x ∈ p₃, G.Adj v x) :
    VertexCanBeLinkedOntoTriangle G v a₁ a₂ a₃ :=
  ⟨p₁, p₂, p₃, ⟨h1, h2, h3⟩, ⟨d12, d13, d23⟩, ⟨e1, e2, e3⟩,
    ⟨fun x hx y hy => ⟨c12 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t12⟩,
      fun x hx y hy => ⟨c13 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t13⟩,
      fun x hx y hy => ⟨c23 x hx y hy, by rintro ⟨rfl, rfl⟩; exact t23⟩⟩,
    ⟨n1, n2, n3⟩⟩

private theorem mem_aTriple_on_path_eq {G : SimpleGraph V} {a b : Fin 3 → V}
    {R : Fin 3 → List V} (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (i : Fin 3) {x : V} (hxA : x ∈ ({a 0, a 1, a 2} : Set V)) (hxi : x ∈ R i) :
    x = a i := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxA
  rcases hxA with rfl | rfl | rfl
  · exact congrArg a (tri_own_path hprism i 0 hxi)
  · exact congrArg a (tri_own_path hprism i 1 hxi)
  · exact congrArg a (tri_own_path hprism i 2 hxi)

/-- Claim (2) after choosing the non-`R 0` corner adjacent to `fn` to be `a 1`. -/
private theorem claim_two_core (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V)
    (R : Fin 3 → List V) (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ) (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f})
    (hn : 2 ≤ f.length)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R 0})
    (hfn1 : G.Adj fn (a 1)) :
    Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  classical
  obtain ⟨hAtri, hBtri, hABne, hp, hedge⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hlen2 := two_le_length hprism
  have hnd0 : (R 0).Nodup := (hp 0).1.2.1
  have hnd1 : (R 1).Nodup := (hp 1).1.2.1
  have hfne : f₁ ≠ fn :=
    PathBasics.isPathFrom_ends_ne hf (by change 1 ≤ f.length - 1; omega)
  have hf₁F : f₁ ∈ F := by rw [hfF]; exact PathBasics.head_mem hf.2.1
  have hfnF : fn ∈ F := by rw [hfF]; exact PathBasics.getLast_mem hf.2.2
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hfK : ∀ x ∈ f, ∀ i : Fin 3, x ∉ R i := by
    intro x hx i hxi
    exact (hFK (by rw [hfF]; exact hx)) (hRK i x hxi)
  have hextra : ∃ x ∈ R 0, x ≠ a 0 ∧ G.Adj f₁ x := by
    by_contra hex
    apply hFloc
    exact Or.inr (Or.inr (Or.inr (Or.inl (by
      rintro x ⟨hxK, w, hwF, hadj⟩
      by_cases hw : w = f₁
      · subst w
        have hx0 : x ∈ R 0 :=
          hX2 ⟨hxK, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj⟩
        have hxa : x = a 0 := by
          by_contra hxa
          exact hex ⟨x, hx0, hxa, hadj.symm⟩
        simp [hxa]
      · exact hX1 ⟨hxK, w, ⟨hwF, by simpa using hw⟩, hadj⟩))))
  have hmeet0 : ∃ x ∈ R 0, G.Adj f₁ x := by
    obtain ⟨x, hx, -, hadj⟩ := hextra
    exact ⟨x, hx, hadj⟩
  obtain ⟨k, hk, hD0, hd, hD0sub, hD0unique, hkmax⟩ := last_attach (hp 0) hmeet0
  have hfirst0 : (R 0)[0]'(by have := hlen2 0; omega) = a 0 :=
    PathBasics.getElem_zero_of_head? (hp 0).2.1 (by have := hlen2 0; omega)
  have hkpos : 0 < k := by
    obtain ⟨d, hdR, hdne, hdadj⟩ := hextra
    obtain ⟨t, ht, htd⟩ := List.getElem_of_mem hdR
    have htpos : 0 < t := by
      by_contra ht0
      apply hdne
      rw [← htd]
      simpa only [show t = 0 by omega] using hfirst0
    have hdt : G.Adj f₁ ((R 0)[t]'ht) := by rwa [htd]
    exact lt_of_lt_of_le htpos (hkmax t ht hdt)
  have ha0D : a 0 ∉ (R 0).drop k := by
    intro ha
    obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp ha
    have hzero : k + s = 0 := hnd0.getElem_inj_iff.mp (by rw [hse, hfirst0])
    omega
  have hdne : (R 0)[k]'hk ≠ a 0 := by
    intro heq
    have hzero := hnd0.getElem_inj_iff.mp (heq.trans hfirst0.symm)
    omega
  by_cases hfn2 : G.Adj fn (a 2)
  · obtain ⟨σ, hσ0, hσ1, hσ2⟩ :=
      perm_of_three (1 : Fin 3) (2 : Fin 3) (0 : Fin 3) (by decide) (by decide) (by decide)
    refine ⟨fun i => a (σ i), fun i => b (σ i), fun i => R (σ i), σ,
      rfl, Or.inl ⟨rfl, rfl⟩, Or.inr (Or.inr (Or.inr ?_))⟩
    refine ⟨by simpa only [hσ0] using hfn1, by simpa only [hσ1] using hfn2,
      ⟨(R 0)[k]'hk, by simpa only [hσ2] using List.getElem_mem hk,
        by simpa only [hσ2] using hdne, hd⟩, ?_⟩
    intro x hx q hqK hqne hadj
    rw [List.mem_reverse] at hx
    have hxF : x ∈ F := by rw [hfF]; exact hx
    by_cases hxn : x = fn
    · subst x
      have hqA : q ∈ ({a 0, a 1, a 2} : Set V) :=
        hX1 ⟨hqK, fn, ⟨hfnF, by simp [hfne.symm]⟩, hadj.symm⟩
      left
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hqA
      rcases hqA with hq0 | hq1 | hq2
      · exact False.elim (hqne (by simpa only [hσ2] using hq0))
      · exact Or.inl (by simpa only [hσ0] using hq1)
      · exact Or.inr (by simpa only [hσ1] using hq2)
    · by_cases hx1 : x = f₁
      · subst x
        right
        refine ⟨rfl, ?_⟩
        have hq0 : q ∈ R 0 :=
          hX2 ⟨hqK, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj.symm⟩
        simpa only [hσ2] using hq0
      · exfalso
        have hqA : q ∈ ({a 0, a 1, a 2} : Set V) :=
          hX1 ⟨hqK, x, ⟨hxF, by simpa using hx1⟩, hadj.symm⟩
        have hq0 : q ∈ R 0 :=
          hX2 ⟨hqK, x, ⟨hxF, by simpa using hxn⟩, hadj.symm⟩
        exact hqne (by
          simpa only [hσ2] using mem_aTriple_on_path_eq hprism 0 hqA hq0)
  · have hmemP1 : ∀ x : V, x ∈ f.reverse ++ (R 0).drop k ↔
        (x ∈ f ∨ x ∈ (R 0).drop k) := by
      intro x
      rw [List.mem_append, List.mem_reverse]
    have hdisjFD : ∀ x ∈ f.reverse, x ∉ (R 0).drop k := by
      intro x hx hxd
      rw [List.mem_reverse] at hx
      exact hfK x hx 0 (List.mem_of_mem_drop hxd)
    have hcrossFD : ∀ x ∈ f.reverse, ∀ y ∈ (R 0).drop k,
        (G.Adj x y ↔ (x = f₁ ∧ y = (R 0)[k]'hk)) := by
      intro x hx y hy
      rw [List.mem_reverse] at hx
      constructor
      · intro hadj
        by_cases hx1 : x = f₁
        · subst x
          exact ⟨rfl, hD0unique y hy hadj⟩
        · have hxF : x ∈ F := by rw [hfF]; exact hx
          have hyA : y ∈ ({a 0, a 1, a 2} : Set V) :=
            hX1 ⟨hRK 0 y (List.mem_of_mem_drop hy), x,
              ⟨hxF, by simpa using hx1⟩, hadj.symm⟩
          have hya : y = a 0 :=
            mem_aTriple_on_path_eq hprism 0 hyA (List.mem_of_mem_drop hy)
          exact False.elim (ha0D (hya ▸ hy))
      · rintro ⟨rfl, rfl⟩
        exact hd
    have hP1 : IsPathFrom G (f.reverse ++ (R 0).drop k) fn (b 0) :=
      PathGlue.glue_path (PathBasics.isPathFrom_reverse hf) hD0 hdisjFD hcrossFD
    have h1lt : 1 < (R 1).length := by have := hlen2 1; omega
    have hP2 : IsPathFrom G ((R 1).drop 1) ((R 1)[1]'h1lt) (b 1) :=
      drop_pathFrom (hp 1) h1lt
    have hfirst1 : (R 1)[0]'(by have := hlen2 1; omega) = a 1 :=
      PathBasics.getElem_zero_of_head? (hp 1).2.1 (by have := hlen2 1; omega)
    have ha1P2 : a 1 ∉ (R 1).drop 1 := by
      intro ha
      obtain ⟨s, hs, hse⟩ := mem_drop_iff.mp ha
      have hzero : 1 + s = 0 := hnd1.getElem_inj_iff.mp (by rw [hse, hfirst1])
      omega
    have ha1next : G.Adj (a 1) ((R 1)[1]'h1lt) := by
      have h := PathBasics.path_adj_succ (hp 1).1 h1lt
      rwa [hfirst1] at h
    have hlink : VertexCanBeLinkedOntoTriangle G (a 1) (b 0) (b 1) (b 2) :=
      link_direct hP1.1 hP2.1 (hp 2).1
        (fun x hx hx2 => by
          rcases (hmemP1 x).mp hx with hxf | hx0
          · exact hfK x hxf 1 (List.mem_of_mem_drop hx2)
          · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
              (List.mem_of_mem_drop hx0) (List.mem_of_mem_drop hx2))
        (fun x hx hx2 => by
          rcases (hmemP1 x).mp hx with hxf | hx0
          · exact hfK x hxf 2 hx2
          · exact paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2)
              (List.mem_of_mem_drop hx0) hx2)
        (fun x hx hx2 =>
          paths_disjoint hprism (by decide : (1 : Fin 3) ≠ 2)
            (List.mem_of_mem_drop hx) hx2)
        (Or.inr hP1.2.2) (Or.inr hP2.2.2) (Or.inr (hp 2).2.2)
        (hBtri 0 1 (by decide)) (hBtri 0 2 (by decide)) (hBtri 1 2 (by decide))
        (fun x hx y hy hadj => by
          rcases (hmemP1 x).mp hx with hxf | hx0
          · have hxF : x ∈ F := by rw [hfF]; exact hxf
            by_cases hx1 : x = f₁
            · subst x
              have hy0 : y ∈ R 0 :=
                hX2 ⟨hRK 1 y (List.mem_of_mem_drop hy), f₁,
                  ⟨hf₁F, by simp [hfne]⟩, hadj.symm⟩
              exact False.elim (paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 1)
                hy0 (List.mem_of_mem_drop hy))
            · have hyA : y ∈ ({a 0, a 1, a 2} : Set V) :=
                hX1 ⟨hRK 1 y (List.mem_of_mem_drop hy), x,
                  ⟨hxF, by simpa using hx1⟩, hadj.symm⟩
              have hya : y = a 1 :=
                mem_aTriple_on_path_eq hprism 1 hyA (List.mem_of_mem_drop hy)
              exact False.elim (ha1P2 (hya ▸ hy))
          · rcases (hedge 0 1 (by decide) x (List.mem_of_mem_drop hx0) y
                (List.mem_of_mem_drop hy)).mp hadj with ha | hb
            · exact False.elim (ha0D (ha.1 ▸ hx0))
            · exact hb)
        (fun x hx y hy hadj => by
          rcases (hmemP1 x).mp hx with hxf | hx0
          · have hxF : x ∈ F := by rw [hfF]; exact hxf
            by_cases hx1 : x = f₁
            · subst x
              have hy0 : y ∈ R 0 :=
                hX2 ⟨hRK 2 y hy, f₁, ⟨hf₁F, by simp [hfne]⟩, hadj.symm⟩
              exact False.elim (paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) hy0 hy)
            · have hyA : y ∈ ({a 0, a 1, a 2} : Set V) :=
                hX1 ⟨hRK 2 y hy, x, ⟨hxF, by simpa using hx1⟩, hadj.symm⟩
              have hya : y = a 2 := mem_aTriple_on_path_eq hprism 2 hyA hy
              by_cases hxn : x = fn
              · subst x
                exact False.elim (hfn2 (by rwa [hya] at hadj))
              · have hy0 : y ∈ R 0 :=
                  hX2 ⟨hRK 2 y hy, x, ⟨hxF, by simpa using hxn⟩, hadj.symm⟩
                exact False.elim
                  (paths_disjoint hprism (by decide : (0 : Fin 3) ≠ 2) hy0 hy)
          · rcases (hedge 0 2 (by decide) x (List.mem_of_mem_drop hx0) y hy).mp hadj with
              ha | hb
            · exact False.elim (ha0D (ha.1 ▸ hx0))
            · exact hb)
        (fun x hx y hy hadj => by
          rcases (hedge 1 2 (by decide) x (List.mem_of_mem_drop hx) y hy).mp hadj with
            ha | hb
          · exact False.elim (ha1P2 (ha.1 ▸ hx))
          · exact hb)
        ⟨fn, (hmemP1 fn).mpr (Or.inl (PathBasics.getLast_mem hf.2.2)), hfn1.symm⟩
        ⟨(R 1)[1]'h1lt, PathBasics.head_mem hP2.2.1, ha1next⟩
        ⟨a 2, PathBasics.head_mem (hp 2).2.1, hAtri 1 2 (by decide)⟩
    have hnotB : ∀ i : Fin 3, i ≠ 1 → ¬ G.Adj (a 1) (b i) := by
      intro i hi hadj
      rcases (hedge 1 i (Ne.symm hi) (a 1) (PathBasics.head_mem (hp 1).2.1)
          (b i) (PathBasics.getLast_mem (hp i).2.2)).mp hadj with ha | hb
      · exact hABne i i ha.2.symm
      · exact hABne 1 1 hb.1
    exfalso
    rcases _root_.Workspace.Statements.S02.SPGT.thm_2_4 G hG (a 1)
        (b 0) (b 1) (b 2) hlink with h | h | h
    exacts [hnotB 0 (by decide) h.1, hnotB 0 (by decide) h.1,
      hnotB 2 (by decide) h.2]

/-- **10.1, claim (2)**: *"If `X₁ ⊆ A` and `X₂ ⊆ V(R₁)` then the theorem holds."*  Here `X₁` is
the attachment set of `F \ {f₁}` and `X₂` that of `F \ {fₙ}`.

**Orientation.**  `Thm101Assembly.Concl G a b R K f f₁ fn` pins the *head* `f₁` of the path as
the endpoint carrying the two constrained triangle-neighbours, but in claim (2)'s configuration
the printed proof says *"If `fₙ` is adjacent to both `a₂, a₃` then statement 4 of the theorem
holds"* while *"`f₁` has at least one neighbour in `R₁ \ a₁`"* — i.e. it is `fₙ`, not `f₁`, that
acquires the two triangle neighbours; since 10.1 binds `f₁` and `fₙ` existentially and holds
*"up to symmetry"*, the faithful conclusion is `Concl … f.reverse fn f₁`, literally "statement 4
holds for the path `fₙ-⋯-f₁`". -/
theorem claim_two (G : SimpleGraph V) (hG : Berge G) (a b : Fin 3 → V) (R : Fin 3 → List V)
    (K F : Set V) (f : List V) (f₁ fn : V)
    (hprism : FormPrism G a b (R 0) (R 1) (R 2))
    (hK : K = {v : V | v ∈ R 0} ∪ {v : V | v ∈ R 1} ∪ {v : V | v ∈ R 2})
    (hFK : F ⊆ Kᶜ)
    (hf : IsPathFrom G f f₁ fn) (hfF : F = {x : V | x ∈ f}) (hn : 2 ≤ f.length)
    (hFmaj : ∀ w ∈ F, ¬ MajorForPrism G a b w)
    (hFloc : ¬ LocalForPrism a b (R 0) (R 1) (R 2) (attachments G F K))
    (hX1 : attachments G (F \ {f₁}) K ⊆ ({a 0, a 1, a 2} : Set V))
    (hX2 : attachments G (F \ {fn}) K ⊆ {v : V | v ∈ R 0}) :
    Thm101Assembly.Concl G a b R K f.reverse fn f₁ := by
  classical
  obtain ⟨-, -, -, hp, -⟩ := PrismSymmetry.formPrism_family.mp hprism
  have hfne : f₁ ≠ fn :=
    PathBasics.isPathFrom_ends_ne hf (by change 1 ≤ f.length - 1; omega)
  have hf₁F : f₁ ∈ F := by rw [hfF]; exact PathBasics.head_mem hf.2.1
  have hfnF : fn ∈ F := by rw [hfF]; exact PathBasics.getLast_mem hf.2.2
  have _hfnNotMajor : ¬ MajorForPrism G a b fn := hFmaj fn hfnF
  have hRK : ∀ i : Fin 3, ∀ x : V, x ∈ R i → x ∈ K := by
    intro i x hx
    rw [hK]
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rcases fin3_cases i with rfl | rfl | rfl
    exacts [Or.inl (Or.inl hx), Or.inl (Or.inr hx), Or.inr hx]
  have hfnA : G.Adj fn (a 1) ∨ G.Adj fn (a 2) := by
    by_contra hnone
    simp only [not_or] at hnone
    apply hFloc
    exact Or.inl (by
      rintro x ⟨hxK, w, hwF, hadj⟩
      by_cases hw : w = fn
      · subst w
        have hxA : x ∈ ({a 0, a 1, a 2} : Set V) :=
          hX1 ⟨hxK, fn, ⟨hfnF, by simp [hfne.symm]⟩, hadj⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxA
        rcases hxA with rfl | rfl | rfl
        · exact PathBasics.head_mem (hp 0).2.1
        · exact False.elim (hnone.1 hadj.symm)
        · exact False.elim (hnone.2 hadj.symm)
      · exact hX2 ⟨hxK, w, ⟨hwF, by simpa using hw⟩, hadj⟩)
  rcases hfnA with hfn1 | hfn2
  · exact claim_two_core G hG a b R K F f f₁ fn hprism hK hFK hf hfF hn hFloc hX1 hX2 hfn1
  · obtain ⟨τ, hτ0, hτ1, -⟩ :=
      perm_of_three (0 : Fin 3) (2 : Fin 3) (1 : Fin 3) (by decide) (by decide) (by decide)
    refine Thm101Assembly.concl_perm τ ?_
    refine claim_two_core G hG (fun i => a (τ i)) (fun i => b (τ i))
      (fun i => R (τ i)) K F f f₁ fn (PrismSymmetry.formPrism_perm hprism τ) ?_
      hFK hf hfF hn (fun h => hFloc ((PrismSymmetry.localForPrism_perm τ).mp h)) ?_ ?_ ?_
    · rw [hK]
      exact (PrismSymmetry.prismVertices_perm R τ).symm
    · show attachments G (F \ {f₁}) K ⊆
          ({a (τ 0), a (τ 1), a (τ 2)} : Set V)
      rw [PrismSymmetry.triple_perm a τ]
      exact hX1
    · intro x hx
      have := hX2 hx
      simpa only [Set.mem_setOf_eq, hτ0] using this
    · simpa only [hτ1] using hfn2

end Workspace.ProofLemmas.Thm101ClaimTwo
