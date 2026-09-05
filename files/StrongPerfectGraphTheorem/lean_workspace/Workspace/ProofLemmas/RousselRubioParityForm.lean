import Mathlib
import Workspace.Types.Core
import Workspace.Types.RousselRubio
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.PathAttach
import Workspace.ProofLemmas.PrismBasics
import Workspace.ProofLemmas.PathCompleteEdgeIndexEquiv
import Workspace.ProofLemmas.RousselRubioParityBase
import Workspace.ProofLemmas.RousselRubioInternalCompleteSplit
import Workspace.ProofLemmas.RousselRubioNonstableParityOrAntipath

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

namespace RRParityFormAux


open Workspace.Types.Core Workspace.Types.Core.SPGT
open Workspace.Types.RousselRubio Workspace.Types.RousselRubio.SPGT

/-! ### (a) The marked-index gap parity -/

/-- If every odd gap between consecutive marked indices has length one, then the number of
length-one gaps inside `[a,b)` has the parity of `b - a`. -/
private theorem marked_parity (Mk : ℕ → Prop) [DecidablePred Mk]
    (good : ∀ a c : ℕ, a < c → Mk a → Mk c → (∀ i, a < i → i < c → ¬ Mk i) →
      (c - a) % 2 = 1 → c = a + 1) :
    ∀ (d a b : ℕ), b - a ≤ d → a ≤ b → Mk a → Mk b →
      (b - a) % 2 =
        ((Finset.Ico a b).filter (fun i => Mk i ∧ Mk (i + 1))).card % 2 := by
  intro d
  induction d with
  | zero =>
      intro a b hd hab ha hb
      have : a = b := by omega
      subst this
      simp
  | succ n ih =>
      intro a b hd hab ha hb
      rcases eq_or_lt_of_le hab with rfl | hlt
      · simp
      -- the least marked index strictly above `a`
      have hne : ((Finset.Ioc a b).filter Mk).Nonempty := by
        refine ⟨b, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        exact ⟨⟨hlt, le_rfl⟩, hb⟩
      obtain ⟨c, hcmem, hcmin⟩ : ∃ c, c ∈ (Finset.Ioc a b).filter Mk ∧
          ∀ x ∈ (Finset.Ioc a b).filter Mk, c ≤ x :=
        ⟨_, Finset.min'_mem _ hne, fun x hx => Finset.min'_le _ _ hx⟩
      rw [Finset.mem_filter, Finset.mem_Ioc] at hcmem
      obtain ⟨⟨hac, hcb⟩, hMc⟩ := hcmem
      have hbetween : ∀ i, a < i → i < c → ¬ Mk i := by
        intro i hi hic hMi
        have : c ≤ i := by
          refine hcmin i ?_
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨hi, by omega⟩, hMi⟩
        omega
      -- the filter over `[a,c)` is `{a}` when `c = a+1`, and empty otherwise
      have hsplit : (Finset.Ico a b).filter (fun i => Mk i ∧ Mk (i + 1)) =
          ((Finset.Ico a c).filter (fun i => Mk i ∧ Mk (i + 1))) ∪
            ((Finset.Ico c b).filter (fun i => Mk i ∧ Mk (i + 1))) := by
        rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
      have hdisj : Disjoint ((Finset.Ico a c).filter (fun i => Mk i ∧ Mk (i + 1)))
          ((Finset.Ico c b).filter (fun i => Mk i ∧ Mk (i + 1))) := by
        exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive a c b)
      have hIco : ((Finset.Ico a c).filter (fun i => Mk i ∧ Mk (i + 1))).card % 2 =
          (c - a) % 2 := by
        by_cases hc1 : c = a + 1
        · have hMa1 : Mk (a + 1) := by rw [← hc1]; exact hMc
          have : (Finset.Ico a c).filter (fun i => Mk i ∧ Mk (i + 1)) = {a} := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
            constructor
            · rintro ⟨⟨h1, h2⟩, -⟩; omega
            · rintro rfl; exact ⟨⟨le_rfl, by omega⟩, ha, hMa1⟩
          rw [this]
          simp [hc1]
        · have hempty : (Finset.Ico a c).filter (fun i => Mk i ∧ Mk (i + 1)) = ∅ := by
            ext i
            simp only [Finset.mem_filter, Finset.mem_Ico, Finset.notMem_empty, iff_false]
            rintro ⟨⟨h1, h2⟩, hMi, hMi1⟩
            by_cases hia : i = a
            · exact hbetween (i + 1) (by omega) (by omega) hMi1
            · exact hbetween i (by omega) h2 hMi
          have heven : (c - a) % 2 = 0 := by
            by_contra hodd
            exact hc1 (good a c hac ha hMc hbetween (by omega))
          rw [hempty, heven]
          simp
      have hrec := ih c b (by omega) (by omega) hMc hb
      rw [hsplit, Finset.card_union_of_disjoint hdisj]
      omega

/-! ### (b) Inclusion–exclusion modulo two -/

private theorem ie_mod_two {ι : Type*} [DecidableEq ι] (Tf : Finset ι) (R : Finset ℕ)
    (N : ℕ → Finset ι) (hN : ∀ i, N i ⊆ Tf) :
    (∑ S ∈ Tf.powerset.filter (fun S => S.Nonempty),
        (R.filter (fun i => S ⊆ N i)).card) % 2
      = (R.filter (fun i => (N i).Nonempty)).card % 2 := by
  classical
  have hswap : (∑ S ∈ Tf.powerset.filter (fun S => S.Nonempty),
      (R.filter (fun i => S ⊆ N i)).card) =
      ∑ i ∈ R, ((Tf.powerset.filter (fun S => S.Nonempty)).filter
        (fun S => S ⊆ N i)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  have hinner : ∀ i : ℕ, ((Tf.powerset.filter (fun S => S.Nonempty)).filter
      (fun S => S ⊆ N i)).card = 2 ^ (N i).card - 1 := by
    intro i
    have hset : (Tf.powerset.filter (fun S => S.Nonempty)).filter (fun S => S ⊆ N i) =
        (N i).powerset.erase ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase,
        Finset.nonempty_iff_ne_empty]
      constructor
      · rintro ⟨⟨-, hne⟩, hsub⟩; exact ⟨hne, hsub⟩
      · rintro ⟨hne, hsub⟩; exact ⟨⟨hsub.trans (hN i), hne⟩, hsub⟩
    rw [hset, Finset.card_erase_of_mem (Finset.empty_mem_powerset _),
      Finset.card_powerset]
  rw [hswap]
  simp only [hinner]
  rw [Finset.sum_nat_mod]
  have hterm : ∀ i ∈ R, (2 ^ (N i).card - 1) % 2 =
      (if (N i).Nonempty then 1 else 0) := by
    intro i _
    by_cases h : (N i).Nonempty
    · have hpos : 0 < (N i).card := Finset.card_pos.mpr h
      have : 2 ^ (N i).card % 2 = 0 := by
        obtain ⟨k, hk⟩ : ∃ k, (N i).card = k + 1 := ⟨(N i).card - 1, by omega⟩
        rw [hk, pow_succ]
        omega
      have h2 : 2 ≤ 2 ^ (N i).card := by
        calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (N i).card := Nat.pow_le_pow_right (by norm_num) hpos
      simp only [h, if_true]
      omega
    · have : (N i).card = 0 := by
        rw [Finset.card_eq_zero]
        exact Finset.not_nonempty_iff_eq_empty.mp h
      simp [this, h]
  have hcard : (∑ i ∈ R, (if (N i).Nonempty then (1 : ℕ) else 0)) =
      (R.filter (fun i => (N i).Nonempty)).card := by
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl hterm, hcard]

/-! ### The positional complete-edge index set -/

variable {V : Type*}

private def EIdx (G : SimpleGraph V) (S : Set V) (P : List V) : Set ℕ :=
  {i | i + 1 < P.length ∧ ∃ a b : V, P[i]? = some a ∧ P[i + 1]? = some b ∧
    EdgeComplete G S a b}

private theorem EIdx_lt {G : SimpleGraph V} {S : Set V} {P : List V} {i : ℕ}
    (h : i ∈ EIdx G S P) : i + 1 < P.length := h.1

private theorem mem_EIdx_iff {G : SimpleGraph V} {S : Set V} {P : List V} {i : ℕ}
    (hP : IsPathList G P) (hi : i + 1 < P.length) :
    i ∈ EIdx G S P ↔
      (VertexComplete G (P[i]'(by omega)) S ∧ VertexComplete G (P[i + 1]'hi) S) := by
  constructor
  · rintro ⟨-, a, b, ha, hb, hab⟩
    rw [List.getElem?_eq_getElem (show i < P.length by omega)] at ha
    rw [List.getElem?_eq_getElem hi] at hb
    cases Option.some.inj ha
    cases Option.some.inj hb
    exact ⟨hab.2.1, hab.2.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨hi, _, _, ?_, ?_, ?_, h1, h2⟩
    · exact List.getElem?_eq_getElem (show i < P.length by omega)
    · exact List.getElem?_eq_getElem hi
    · exact PathBasics.path_adj_succ hP hi

/-! ### (c) Steps 4.1 and 4.2: an odd marked interval has a common neighbour -/

private theorem gidx (P : List V) {n n' : ℕ} (hn : n < P.length) (hn' : n' < P.length)
    (h : n = n') : (P[n]'hn) = (P[n']'hn') := by subst h; rfl

private theorem interval_core [Fintype V] {G : SimpleGraph V} (hG : Berge G) {T : Set V}
    (hstable : Set.Pairwise T (fun x y => ¬ G.Adj x y))
    {P : List V} {r s : V} (hP : IsPathFrom G P r s) (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoLeap : ¬ (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b))
    {a c : ℕ} (hac : a < c) (hc : c < P.length)
    (hbetween : ∀ (i : ℕ) (hi : i < P.length), a < i → i < c → ∀ t ∈ T,
      ¬ G.Adj (P[i]'hi) t)
    (hodd : (c - a) % 2 = 1)
    (hu : ∃ t ∈ T, G.Adj (P[a]'(by omega)) t)
    (hv : ∃ t ∈ T, G.Adj (P[c]'hc) t) :
    ∃ t ∈ T, G.Adj (P[a]'(by omega)) t ∧ G.Adj (P[c]'hc) t := by
  classical
  by_contra hnc
  have hba : a < P.length := by omega
  have hPl : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  obtain ⟨u, huT, hua⟩ := hu
  obtain ⟨v, hvT, hvc⟩ := hv
  have hnoCommon : ∀ t ∈ T, ¬ (G.Adj (P[a]'hba) t ∧ G.Adj (P[c]'hc) t) :=
    fun t ht h => hnc ⟨t, ht, h⟩
  have huc : ¬ G.Adj (P[c]'hc) u := fun h => hnoCommon u huT ⟨hua, h⟩
  have hva : ¬ G.Adj (P[a]'hba) v := fun h => hnoCommon v hvT ⟨h, hvc⟩
  have huv : u ≠ v := by rintro rfl; exact huc hvc
  have huvnadj : ¬ G.Adj u v := hstable huT hvT huv
  have hPnot : ∀ (n : ℕ) (hn : n < P.length), (P[n]'hn) ∉ T := fun n hn =>
    hPT _ (List.getElem_mem hn)
  have hr0 : (P[0]'(by omega)) = r :=
    PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hslast : (P[P.length - 1]'(by omega)) = s :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  have hgapadj : ∀ (n n' : ℕ) (hn : n < P.length) (hn' : n' < P.length),
      n + 1 ≠ n' → n' + 1 ≠ n → ¬ G.Adj (P[n]'hn) (P[n']'hn') := fun n n' hn hn' h1 h2 =>
    PathBasics.path_not_adj_of_gap hP.1 hn hn' h1 h2
  -- the interval cannot start at `p₀` nor end at `pₘ`
  have ha0 : a ≠ 0 := by
    intro h
    refine hva ?_
    rw [gidx P hba (show 0 < P.length by omega) h, hr0]
    exact hr v hvT
  have hcm1 : c ≠ P.length - 1 := by
    intro h
    refine huc ?_
    rw [gidx P hc (show P.length - 1 < P.length by omega) h, hslast]
    exact hs u huT
  -- the interval as a slice, with the two attached `T`-vertices
  set sl : List V := (P.drop a).take (c - a + 1) with hsldef
  have hsl : IsPathFrom G sl (P[a]'hba) (P[c]'hc) :=
    PathBasics.isPathFrom_slice hP.1 hac hc
  have hsllen : sl.length = c - a + 1 := PathBasics.length_slice P (le_of_lt hac) hc
  have hslmem : ∀ x ∈ sl, ∃ (k : ℕ) (hk : k < P.length), a ≤ k ∧ k ≤ c ∧
      (P[k]'hk) = x := fun x hx =>
    (PathBasics.mem_slice_iff P (le_of_lt hac) hc).mp hx
  have hslnotT : ∀ x ∈ sl, x ∉ T := by
    intro x hx
    obtain ⟨k, hk, -, -, rfl⟩ := hslmem x hx
    exact hPnot k hk
  have huother : ∀ x ∈ sl, x ≠ (P[a]'hba) → ¬ G.Adj u x := by
    intro x hx hxa hadj
    obtain ⟨k, hk, h1, h2, rfl⟩ := hslmem x hx
    rcases eq_or_lt_of_le h2 with rfl | hkc
    · exact huc hadj.symm
    · have hka : a < k := by
        rcases eq_or_lt_of_le h1 with h | h
        · exact absurd (gidx P hba hk h) (fun he => hxa he.symm)
        · exact h
      exact hbetween k hk hka hkc u huT hadj.symm
  have hvother : ∀ x ∈ sl, x ≠ (P[c]'hc) → ¬ G.Adj v x := by
    intro x hx hxc hadj
    obtain ⟨k, hk, h1, h2, rfl⟩ := hslmem x hx
    rcases eq_or_lt_of_le h1 with rfl | hak
    · exact hva hadj.symm
    · have hkc : k < c := by
        rcases eq_or_lt_of_le h2 with h | h
        · exact absurd (gidx P hk hc h) hxc
        · exact h
      exact hbetween k hk hak hkc v hvT hadj.symm
  have hpath1 : IsPathFrom G (u :: (sl ++ [v])) u v :=
    PathAttach.isPathFrom_cons_concat hsl hua.symm hvc.symm huvnadj huv
      (fun h => hslnotT u h huT) (fun h => hslnotT v h hvT) huother hvother
  have hint1 : SPGT.interior (u :: (sl ++ [v])) = sl := by simp [SPGT.interior]
  have hlen1 : (u :: (sl ++ [v])).length = c - a + 3 := by simp [hsllen]
  have hplen1 : pathLength (u :: (sl ++ [v])) = c - a + 2 := by
    simp only [pathLength, hlen1]; omega
  -- the mirrored path
  have hpath2 : IsPathFrom G (v :: (sl.reverse ++ [u])) v u :=
    PathAttach.isPathFrom_cons_concat (PathBasics.isPathFrom_reverse hsl) hvc.symm hua.symm
      (fun h => huvnadj h.symm) huv.symm
      (fun h => hslnotT v (List.mem_reverse.mp h) hvT)
      (fun h => hslnotT u (List.mem_reverse.mp h) huT)
      (fun x hx hxc => hvother x (List.mem_reverse.mp hx) hxc)
      (fun x hx hxa => huother x (List.mem_reverse.mp hx) hxa)
  have hint2 : SPGT.interior (v :: (sl.reverse ++ [u])) = sl.reverse := by
    simp [SPGT.interior]
  have hlen2 : (v :: (sl.reverse ++ [u])).length = c - a + 3 := by simp [hsllen]
  have hplen2 : pathLength (v :: (sl.reverse ++ [u])) = c - a + 2 := by
    simp only [pathLength, hlen2]; omega
  -- the interval starts at `p₁`
  have ha1 : a = 1 := by
    by_contra ha1
    have ha2 : 2 ≤ a := by omega
    have hhole : IsHoleList G ((P[0]'(by omega)) :: (u :: (sl ++ [v]))) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hpath1 (by omega) ?_ ?_ ?_ ?_
      · rw [hr0]; exact hr u huT
      · rw [hr0]; exact hr v hvT
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact hPnot 0 (by omega) (h ▸ huT)
        · rcases List.mem_append.mp h with h' | h'
          · obtain ⟨k, hk, h1, h2, he⟩ := hslmem _ h'
            have : k = 0 := (PathBasics.path_nodup hP.1).getElem_inj_iff.mp he
            omega
          · exact hPnot 0 (by omega) ((List.mem_singleton.mp h') ▸ hvT)
      · intro x hx
        rw [hint1] at hx
        obtain ⟨k, hk, h1, h2, rfl⟩ := hslmem x hx
        exact hgapadj 0 k (by omega) hk (by omega) (by omega)
    have heven := hG.1 _ hhole
    simp only [holeLength, List.length_cons, hlen1] at heven
    obtain ⟨t, ht⟩ := heven
    omega
  -- the interval ends at `p_{m-1}`
  have hcm : c = P.length - 2 := by
    by_contra hcm
    have hc2 : c + 2 < P.length := by omega
    have hhole : IsHoleList G ((P[P.length - 1]'(by omega)) :: (v :: (sl.reverse ++ [u]))) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hpath2 (by omega) ?_ ?_ ?_ ?_
      · rw [hslast]; exact hs v hvT
      · rw [hslast]; exact hs u huT
      · intro hmem
        rcases List.mem_cons.mp hmem with h | h
        · exact hPnot (P.length - 1) (by omega) (h ▸ hvT)
        · rcases List.mem_append.mp h with h' | h'
          · obtain ⟨k, hk, h1, h2, he⟩ := hslmem _ (List.mem_reverse.mp h')
            have : k = P.length - 1 :=
              (PathBasics.path_nodup hP.1).getElem_inj_iff.mp he
            omega
          · exact hPnot (P.length - 1) (by omega) ((List.mem_singleton.mp h') ▸ huT)
      · intro x hx
        rw [hint2] at hx
        obtain ⟨k, hk, h1, h2, rfl⟩ := hslmem x (List.mem_reverse.mp hx)
        exact hgapadj (P.length - 1) k (by omega) hk (by omega) (by omega)
    have heven := hG.1 _ hhole
    simp only [holeLength, List.length_cons, hlen2] at heven
    obtain ⟨t, ht⟩ := heven
    omega
  -- `u, v` is a leap for `P`
  refine hnoLeap ⟨?_, ?_, u, huT, v, hvT, hP.1, by omega, huv, huvnadj, ?_, ?_⟩
  · exact Nat.odd_iff.mpr (by omega)
  · omega
  · intro i hi
    constructor
    · intro hadj
      by_contra hcon
      have h1 : 2 ≤ i := by omega
      have h2 : i ≤ c := by omega
      rcases eq_or_lt_of_le h2 with rfl | hic
      · exact huc hadj.symm
      · exact hbetween i hi (by omega) hic u huT hadj.symm
    · rintro (rfl | rfl | h)
      · rw [gidx P hi (show 0 < P.length by omega) rfl, hr0]
        exact (hr u huT).symm
      · exact (gidx P hba hi (by omega) ▸ hua).symm
      · rw [gidx P hi (show P.length - 1 < P.length by omega) h, hslast]
        exact (hs u huT).symm
  · intro i hi
    constructor
    · intro hadj
      by_contra hcon
      have h1 : 1 ≤ i := by omega
      have h2 : i ≤ c := by omega
      rcases eq_or_lt_of_le h1 with h | hai
      · exact hva (by rw [gidx P hba hi (show a = i by omega)]; exact hadj.symm)
      · exact hbetween i hi (by omega) (by omega) v hvT hadj.symm
    · rintro (rfl | rfl | h)
      · rw [gidx P hi (show 0 < P.length by omega) rfl, hr0]
        exact (hr v hvT).symm
      · exact (gidx P hc hi (by omega) ▸ hvc).symm
      · rw [gidx P hi (show P.length - 1 < P.length by omega) h, hslast]
        exact (hs v hvT).symm

/-! ### (d) Step 4: the stable-set case -/

private theorem stableParity [Fintype V] [DecidableEq V] {G : SimpleGraph V} (hG : Berge G)
    {T : Set V} (hTne : T.Nonempty) (hstable : Set.Pairwise T (fun x y => ¬ G.Adj x y))
    {P : List V} {r s : V} (hP : IsPathFrom G P r s) (hPT : ∀ x ∈ P, x ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T)
    (hnoLeap : ¬ (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
        ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b))
    (hIH : ∀ S : Set V, S.Nonempty → S ⊂ T →
      (EIdx G S P).ncard % 2 = pathLength P % 2) :
    (EIdx G T P).ncard % 2 = pathLength P % 2 := by
  classical
  have hPl : P.length = pathLength P + 1 :=
    PathBasics.length_eq_pathLength_add_one hP.1
  have hPnot : ∀ (n : ℕ) (hn : n < P.length), (P[n]'hn) ∉ T := fun n hn =>
    hPT _ (List.getElem_mem hn)
  have hr0 : (P[0]'(by omega)) = r :=
    PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
  have hslast : (P[P.length - 1]'(by omega)) = s :=
    PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
  obtain ⟨t₀, ht₀⟩ := hTne
  -- the marked predicate
  set Mk : ℕ → Prop := fun i => ∃ x, P[i]? = some x ∧ ∃ t ∈ T, G.Adj x t with hMkdef
  haveI : DecidablePred Mk := Classical.decPred _
  have hMk_iff : ∀ (i : ℕ) (hi : i < P.length), (Mk i ↔ ∃ t ∈ T, G.Adj (P[i]'hi) t) := by
    intro i hi
    simp only [hMkdef]
    constructor
    · rintro ⟨x, hx, t, ht, hadj⟩
      rw [List.getElem?_eq_getElem hi] at hx
      cases Option.some.inj hx
      exact ⟨t, ht, hadj⟩
    · rintro ⟨t, ht, hadj⟩
      exact ⟨_, List.getElem?_eq_getElem hi, t, ht, hadj⟩
  have hMk_lt : ∀ i, Mk i → i < P.length := by
    rintro i ⟨x, hx, -⟩
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at hx
    simp at hx
  have hMk0 : Mk 0 :=
    (hMk_iff 0 (by omega)).mpr ⟨t₀, ht₀, by rw [hr0]; exact hr t₀ ht₀⟩
  have hMkm : Mk (pathLength P) :=
    (hMk_iff (pathLength P) (by omega)).mpr ⟨t₀, ht₀, by
      rw [gidx P (show pathLength P < P.length by omega)
        (show P.length - 1 < P.length by omega) (by omega), hslast]
      exact hs t₀ ht₀⟩
  -- Step 4.1 + 4.2, packaged for `marked_parity`
  have good : ∀ a c : ℕ, a < c → Mk a → Mk c → (∀ i, a < i → i < c → ¬ Mk i) →
      (c - a) % 2 = 1 → c = a + 1 := by
    intro a c hac hMa hMc hbet hoddac
    have hcP : c < P.length := hMk_lt c hMc
    have haP : a < P.length := by omega
    have hbetween : ∀ (i : ℕ) (hi : i < P.length), a < i → i < c → ∀ t ∈ T,
        ¬ G.Adj (P[i]'hi) t := by
      intro i hi h1 h2 t ht hadj
      exact hbet i h1 h2 ((hMk_iff i hi).mpr ⟨t, ht, hadj⟩)
    obtain ⟨t, htT, hta, htc⟩ :=
      interval_core hG hstable hP hPT hr hs hnoLeap hac hcP hbetween hoddac
        ((hMk_iff a haP).mp hMa) ((hMk_iff c hcP).mp hMc)
    by_contra hne
    have hsl : IsPathFrom G ((P.drop a).take (c - a + 1)) (P[a]'haP) (P[c]'hcP) :=
      PathBasics.isPathFrom_slice hP.1 hac hcP
    have hsllen : ((P.drop a).take (c - a + 1)).length = c - a + 1 :=
      PathBasics.length_slice P (le_of_lt hac) hcP
    have hhole : IsHoleList G (t :: (P.drop a).take (c - a + 1)) := by
      refine PrismBasics.isHoleList_of_path_add_vertex hsl ?_ hta.symm htc.symm ?_ ?_
      · simp only [pathLength, hsllen]; omega
      · intro hmem
        obtain ⟨k, hk, h1, h2, he⟩ := (PathBasics.mem_slice_iff P (le_of_lt hac) hcP).mp hmem
        exact hPnot k hk (by rw [he]; exact htT)
      · intro x hx hadj
        obtain ⟨k, hk, h1, h2, rfl⟩ := (PathBasics.mem_interior_slice_iff hP.1 hac hcP).mp hx
        exact hbetween k hk h1 h2 t htT hadj.symm
    have heven := hG.1 _ hhole
    simp only [holeLength, List.length_cons, hsllen] at heven
    obtain ⟨q, hq⟩ := heven
    omega
  have common : ∀ (i : ℕ) (hi : i + 1 < P.length), Mk i → Mk (i + 1) →
      ∃ t ∈ T, G.Adj (P[i]'(by omega)) t ∧ G.Adj (P[i + 1]'hi) t := by
    intro i hi hMi hMi1
    exact interval_core hG hstable hP hPT hr hs hnoLeap (show i < i + 1 by omega) hi
      (fun k hk h1 h2 => absurd h1 (by omega)) (by omega)
      ((hMk_iff i (by omega)).mp hMi) ((hMk_iff (i + 1) hi).mp hMi1)
  have hparity := marked_parity Mk good (pathLength P) 0 (pathLength P)
    (by omega) (by omega) hMk0 hMkm
  -- the singleton edge families
  have hTfin : T.Finite := Set.toFinite T
  set Tf : Finset V := hTfin.toFinset with hTfdef
  have hTfmem : ∀ x, x ∈ Tf ↔ x ∈ T := fun x => hTfin.mem_toFinset
  have hTfcoe : (↑Tf : Set V) = T := hTfin.coe_toFinset
  set N : ℕ → Finset V := fun i => Tf.filter
    (fun t => ∃ x y : V, P[i]? = some x ∧ P[i + 1]? = some y ∧ G.Adj x t ∧ G.Adj y t)
    with hNdef
  have hNsub : ∀ i, N i ⊆ Tf := fun i => by rw [hNdef]; exact Finset.filter_subset _ _
  have hNmem : ∀ (i : ℕ) (hi : i + 1 < P.length) (t : V),
      (t ∈ N i ↔ (t ∈ T ∧ G.Adj (P[i]'(by omega)) t ∧ G.Adj (P[i + 1]'hi) t)) := by
    intro i hi t
    rw [hNdef]
    simp only [Finset.mem_filter, hTfmem]
    constructor
    · rintro ⟨ht, x, y, hx, hy, h1, h2⟩
      rw [List.getElem?_eq_getElem (show i < P.length by omega)] at hx
      rw [List.getElem?_eq_getElem hi] at hy
      cases Option.some.inj hx
      cases Option.some.inj hy
      exact ⟨ht, h1, h2⟩
    · rintro ⟨ht, h1, h2⟩
      exact ⟨ht, _, _, List.getElem?_eq_getElem (show i < P.length by omega),
        List.getElem?_eq_getElem hi, h1, h2⟩
  have hie := ie_mod_two Tf (Finset.range (pathLength P)) N hNsub
  have hDeq : (Finset.range (pathLength P)).filter (fun i => (N i).Nonempty) =
      (Finset.Ico 0 (pathLength P)).filter (fun i => Mk i ∧ Mk (i + 1)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨him, t, htN⟩
      have hi : i + 1 < P.length := by omega
      obtain ⟨htT, h1, h2⟩ := (hNmem i hi t).mp htN
      exact ⟨⟨Nat.zero_le _, him⟩, (hMk_iff i (by omega)).mpr ⟨t, htT, h1⟩,
        (hMk_iff (i + 1) hi).mpr ⟨t, htT, h2⟩⟩
    · rintro ⟨⟨-, him⟩, hMi, hMi1⟩
      have hi : i + 1 < P.length := by omega
      obtain ⟨t, htT, h1, h2⟩ := common i hi hMi hMi1
      exact ⟨him, t, (hNmem i hi t).mpr ⟨htT, h1, h2⟩⟩
  rw [hDeq] at hie
  -- each family is the complete-edge index set of the corresponding subset
  have hfS : ∀ S : Finset V, S ⊆ Tf →
      ((Finset.range (pathLength P)).filter (fun i => S ⊆ N i)).card =
        (EIdx G (↑S : Set V) P).ncard := by
    intro S hSsub
    have hset : EIdx G (↑S : Set V) P =
        ↑((Finset.range (pathLength P)).filter (fun i => S ⊆ N i)) := by
      ext i
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      constructor
      · intro hmem
        have hi := EIdx_lt hmem
        obtain ⟨h1, h2⟩ := (mem_EIdx_iff hP.1 hi).mp hmem
        refine ⟨by omega, fun t htS => (hNmem i hi t).mpr
          ⟨(hTfmem t).mp (hSsub htS), h1 t (by exact htS), h2 t (by exact htS)⟩⟩
      · rintro ⟨him, hsub⟩
        have hi : i + 1 < P.length := by omega
        refine (mem_EIdx_iff hP.1 hi).mpr ⟨fun t htS => ?_, fun t htS => ?_⟩
        · exact ((hNmem i hi t).mp (hsub (by exact htS))).2.1
        · exact ((hNmem i hi t).mp (hsub (by exact htS))).2.2
    rw [hset, Set.ncard_coe_finset]
  have hTfA : Tf ∈ Tf.powerset.filter (fun S => S.Nonempty) := by
    simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, ⟨t₀, (hTfmem t₀).mpr ht₀⟩⟩
  have hsplit := Finset.add_sum_erase (Tf.powerset.filter (fun S => S.Nonempty))
    (fun S => ((Finset.range (pathLength P)).filter (fun i => S ⊆ N i)).card) hTfA
  have hTop : ((Finset.range (pathLength P)).filter (fun i => Tf ⊆ N i)).card =
      (EIdx G T P).ncard := by
    rw [hfS Tf (Finset.Subset.refl _), hTfcoe]
  have hAerase : ∀ S ∈ (Tf.powerset.filter (fun S => S.Nonempty)).erase Tf,
      ((Finset.range (pathLength P)).filter (fun i => S ⊆ N i)).card % 2 =
        pathLength P % 2 := by
    intro S hS
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_powerset] at hS
    obtain ⟨hSne, hSsub, hSnonempty⟩ := hS
    rw [hfS S hSsub]
    have hcoesub : (↑S : Set V) ⊆ T := by
      rw [← hTfcoe]; exact Finset.coe_subset.mpr hSsub
    refine hIH (↑S) ?_ ⟨hcoesub, ?_⟩
    · obtain ⟨x, hx⟩ := hSnonempty
      exact ⟨x, by exact hx⟩
    · intro hcon
      refine hSne (Finset.coe_injective ?_)
      rw [hTfcoe]
      exact Set.Subset.antisymm hcoesub hcon
  have hAcard : (Tf.powerset.filter (fun S => S.Nonempty)).card = 2 ^ Tf.card - 1 := by
    have hEq : Tf.powerset.filter (fun S => S.Nonempty) = Tf.powerset.erase ∅ := by
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_erase,
        Finset.nonempty_iff_ne_empty]
      tauto
    rw [hEq, Finset.card_erase_of_mem (Finset.empty_mem_powerset _), Finset.card_powerset]
  have hTfpos : 0 < Tf.card := Finset.card_pos.mpr ⟨t₀, (hTfmem t₀).mpr ht₀⟩
  have heven : ((Tf.powerset.filter (fun S => S.Nonempty)).erase Tf).card % 2 = 0 := by
    rw [Finset.card_erase_of_mem hTfA, hAcard]
    have h2 : 2 ^ Tf.card % 2 = 0 := by
      obtain ⟨k, hk⟩ : ∃ k, Tf.card = k + 1 := ⟨Tf.card - 1, by omega⟩
      rw [hk, pow_succ]
      omega
    have h2le : 2 ≤ 2 ^ Tf.card := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ Tf.card := Nat.pow_le_pow_right (by norm_num) hTfpos
    omega
  have hsum0 : (∑ S ∈ (Tf.powerset.filter (fun S => S.Nonempty)).erase Tf,
      ((Finset.range (pathLength P)).filter (fun i => S ⊆ N i)).card) % 2 = 0 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl hAerase, Finset.sum_const, smul_eq_mul,
      Nat.mul_mod, heven]
    simp
  rw [← hsplit] at hie
  simp only [] at hie
  rw [hTop] at hie
  omega

/-! ### Section 1: the strengthened trichotomy, by strong induction -/

private def RR (G : SimpleGraph V) (T : Set V) (P : List V) : Prop :=
  ((EIdx G T P).ncard % 2 = pathLength P % 2) ∨
  (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
    ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b) ∨
  (pathLength P = 3 ∧
    ∃ c d : V, SPGT.interior P = [c, d] ∧
      ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
        ∀ w ∈ SPGT.interior Q, w ∈ T)

private theorem parityFormAux [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) :
    ∀ (n : ℕ) (T : Set V) (P : List V) (r s : V), P.length + T.ncard ≤ n →
      AnticonnectedSet G T → IsPathFrom G P r s → (∀ w ∈ P, w ∉ T) →
      VertexComplete G r T → VertexComplete G s T → RR G T P := by
  classical
  intro n
  induction n with
  | zero =>
      intro T P r s hmeas hT hP hPT hr hs
      exact absurd hmeas (by
        have := PathBasics.path_length_pos hP.1
        omega)
  | succ n ih =>
      intro T P r s hmeas hT hP hPT hr hs
      have hPl : P.length = pathLength P + 1 :=
        PathBasics.length_eq_pathLength_add_one hP.1
      have hTfin : T.Finite := Set.toFinite T
      by_cases hbase : T = ∅ ∨ pathLength P ≤ 2
      · exact Or.inl (RousselRubioParityBase G T P r s hP hPT hr hs hbase)
      have hTne : T.Nonempty := by
        rcases Set.eq_empty_or_nonempty T with h | h
        · exact absurd (Or.inl h) hbase
        · exact h
      have hm3 : 3 ≤ pathLength P := by
        by_contra h
        exact hbase (Or.inr (by omega))
      by_cases hleap : Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
          ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b
      · exact Or.inr (Or.inl hleap)
      by_cases hanti : pathLength P = 3 ∧
          ∃ c d : V, SPGT.interior P = [c, d] ∧
            ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
              ∀ w ∈ SPGT.interior Q, w ∈ T
      · exact Or.inr (Or.inr hanti)
      have hr0 : (P[0]'(by omega)) = r :=
        PathBasics.getElem_zero_of_head? hP.2.1 (by omega)
      have hslast : (P[P.length - 1]'(by omega)) = s :=
        PathBasics.getElem_last_of_getLast? hP.2.2 (by omega)
      by_cases hcase : ∃ z ∈ SPGT.interior P, VertexComplete G z T
      · -- Section 3: an internal vertex is `T`-complete
        obtain ⟨z, hzint, hzc⟩ := hcase
        obtain ⟨k, hk, hk1, hk2, he⟩ := PathBasics.exists_getElem_of_mem_interior hP.1 hzint
        have hzsome : P[k]? = some z := by
          rw [List.getElem?_eq_getElem hk, he]
        have htake : IsPathFrom G (P.take (k + 1)) r z := by
          have hsl := PathBasics.isPathFrom_slice hP.1 (show (0 : ℕ) < k by omega) hk
          rw [List.drop_zero, Nat.sub_zero, hr0, he] at hsl
          exact hsl
        have hdroplen : (P.drop k).length = P.length - k := by simp
        have hdrop : IsPathFrom G (P.drop k) z s := by
          have hsl := PathBasics.isPathFrom_slice hP.1 (show k < P.length - 1 by omega)
            (show P.length - 1 < P.length by omega)
          have hred : (P.drop k).take (P.length - 1 - k + 1) = P.drop k := by
            refine List.take_of_length_le ?_
            rw [hdroplen]; omega
          rw [hred, he, hslast] at hsl
          exact hsl
        have htakelen : (P.take (k + 1)).length = k + 1 := by
          rw [List.length_take]; omega
        have hLeft : RR G T (P.take (k + 1)) :=
          ih T (P.take (k + 1)) r z (by rw [htakelen]; omega) hT htake
            (fun w hw => hPT w (List.take_subset _ _ hw)) hr hzc
        have hRight : RR G T (P.drop k) :=
          ih T (P.drop k) z s (by rw [hdroplen]; omega) hT hdrop
            (fun w hw => hPT w (List.drop_subset _ _ hw)) hzc hs
        exact Or.inl (RousselRubioInternalCompleteSplit G hG T hT P r s hP hPT hr hs
          hleap hanti k (by omega) (by omega) z hzsome hzc hLeft hRight)
      · have hnoInt : ∀ z ∈ SPGT.interior P, ¬ VertexComplete G z T :=
          fun z hz hc => hcase ⟨z, hz, hc⟩
        by_cases hstable : Set.Pairwise T (fun x y => ¬ G.Adj x y)
        · -- Section 4: `T` is stable
          have hsubAnti : ∀ S : Set V, S ⊆ T → AnticonnectedSet G S := by
            intro S hsub x y
            by_cases hxy : (x : V) = y
            · have hxy' : x = y := Subtype.ext hxy
              rw [hxy']
            · exact SimpleGraph.Adj.reachable
                (show Gᶜ.Adj (x : V) (y : V) from ⟨hxy, hstable (hsub x.2) (hsub y.2) hxy⟩)
          have hIH : ∀ S : Set V, S.Nonempty → S ⊂ T →
              (EIdx G S P).ncard % 2 = pathLength P % 2 := by
            intro S hSne hSss
            have hcard : S.ncard < T.ncard := Set.ncard_lt_ncard hSss hTfin
            rcases ih S P r s (by omega) (hsubAnti S hSss.1) hP
              (fun w hw => fun hc => hPT w hw (hSss.1 hc))
              (fun x hx => hr x (hSss.1 hx)) (fun x hx => hs x (hSss.1 hx)) with h | h | h
            · exact h
            · obtain ⟨h1, h2, a, ha, b, hb, hlp⟩ := h
              exact absurd ⟨h1, h2, a, hSss.1 ha, b, hSss.1 hb, hlp⟩ hleap
            · obtain ⟨h1, c, d, hcd, Q, hQ, hQodd, hQint⟩ := h
              exact absurd ⟨h1, c, d, hcd, Q, hQ, hQodd,
                fun w hw => hSss.1 (hQint w hw)⟩ hanti
          exact Or.inl (stableParity hG hTne hstable hP hPT hr hs hleap hIH)
        · -- Section 5: `T` is not stable
          have hproper : ∀ S : Set V, S ⊂ T → AnticonnectedSet G S → RR G S P := by
            intro S hSss hSanti
            have hcard : S.ncard < T.ncard := Set.ncard_lt_ncard hSss hTfin
            exact ih S P r s (by omega) hSanti hP
              (fun w hw => fun hc => hPT w hw (hSss.1 hc))
              (fun x hx => hr x (hSss.1 hx)) (fun x hx => hs x (hSss.1 hx))
          rcases RousselRubioNonstableParityOrAntipath G hG T hTne hT hstable P r s hP hPT
            hr hs hnoInt hleap hproper with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)


end RRParityFormAux

open RRParityFormAux

/-- The strengthened parity form of the Roussel--Rubio lemma. -/
theorem RousselRubioParityForm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (T : Set V)
    (hT : AnticonnectedSet G T) (P : List V) (r s : V)
    (hP : IsPathFrom G P r s) (hPT : ∀ w ∈ P, w ∉ T)
    (hr : VertexComplete G r T) (hs : VertexComplete G s T) :
    let completeEdgeIndices : Set ℕ :=
      {i | i + 1 < P.length ∧
        ∃ u v : V, P[i]? = some u ∧ P[i + 1]? = some v ∧
          EdgeComplete G T u v}
    completeEdgeIndices.ncard % 2 = pathLength P % 2 ∨
    (Odd (pathLength P) ∧ 3 ≤ pathLength P ∧
      ∃ a ∈ T, ∃ b ∈ T, IsLeapForPath G P a b) ∨
    (pathLength P = 3 ∧
      ∃ c d : V, SPGT.interior P = [c, d] ∧
        ∃ Q : List V, IsAntipathFrom G Q c d ∧ Odd (pathLength Q) ∧
          ∀ w ∈ SPGT.interior Q, w ∈ T) := by
  exact parityFormAux G hG (P.length + T.ncard) T P r s le_rfl hT hP hPT hr hs

end Workspace.ProofLemmas
