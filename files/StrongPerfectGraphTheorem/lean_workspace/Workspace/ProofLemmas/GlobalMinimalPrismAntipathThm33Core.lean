import Workspace.Types.Core
import Workspace.Types.Prisms
import Workspace.ProofLemmas.GlobalMinimalPrismAntipathThirdTriangleVertexComplete
import Workspace.ProofLemmas.GlobalMinimalPrismAntipathOppositeTriangleCompleteAndEven
import Workspace.Statements.S03.Thm_3_3
import Workspace.ProofLemmas.PathGlue
import Workspace.ProofLemmas.HyperprismFromPrism
import Workspace.ProofLemmas.PrismSymmetry
import Workspace.ProofLemmas.PathAttach

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

private def truncatedInteriorCandidate {V : Type*}
    (G : SimpleGraph V) (x : V) (q : List V) : Prop :=
  VertexComplete G x {v : V | v ∈ q.dropLast} ∨
    VertexComplete G x {v : V | v ∈ q.tail}

private theorem antipathEndsCompleteToTruncatedInterior
    {V : Type*} {G : SimpleGraph V} {a b : V} {q Q : List V}
    (hshape : Q = a :: (q ++ [b])) (hQ : IsAntipathFrom G Q a b) :
    VertexComplete G a {x : V | x ∈ q.tail} ∧
      VertexComplete G b {x : V | x ∈ q.dropLast} := by
  classical
  subst Q
  constructor
  · intro x hx
    obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hx
    have htt : t < q.length - 1 := by simpa [List.length_tail] using ht
    have hpos : t + 2 < (a :: (q ++ [b])).length := by
      simp
      omega
    have h0 : (a :: (q ++ [b]))[0]'(by omega) = a :=
      PathBasics.getElem_zero_of_head? hQ.2.1 (by omega)
    have he : (a :: (q ++ [b]))[t + 2]'hpos = x := by
      simp only [List.getElem_cons_succ]
      have htq : t + 1 < q.length := by omega
      rw [List.getElem_append_left htq]
      simpa only [List.getElem_tail] using htx
    have hne : a ≠ x := by
      rw [← h0, ← he]
      intro hc
      have hind := hQ.1.2.1.getElem_inj_iff.mp hc
      omega
    have hncomp : ¬ Gᶜ.Adj a x := by
      rw [← h0, ← he, PathBasics.path_adj_iff hQ.1 (by omega) hpos]
      omega
    by_contra hn
    exact hncomp ((G.compl_adj a x).mpr ⟨hne, hn⟩)
  · intro x hx
    obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hx
    have htq : t < q.length := by
      rw [List.length_dropLast] at ht
      omega
    have hpos : t + 1 < (a :: (q ++ [b])).length := by simp; omega
    have hlastpos : (a :: (q ++ [b])).length - 1 < (a :: (q ++ [b])).length := by
      have := PathBasics.path_length_pos hQ.1
      omega
    have he : (a :: (q ++ [b]))[t + 1]'hpos = x := by
      simp only [List.getElem_cons_succ]
      rw [List.getElem_append_left htq]
      simpa only [List.getElem_dropLast] using htx
    have hb : (a :: (q ++ [b]))[(a :: (q ++ [b])).length - 1]'hlastpos = b :=
      PathBasics.getElem_last_of_getLast? hQ.2.2 (by omega)
    have hne : b ≠ x := by
      rw [← hb, ← he]
      intro hc
      have hind := hQ.1.2.1.getElem_inj_iff.mp hc
      have hneidx : (a :: (q ++ [b])).length - 1 ≠ t + 1 := by
        rw [List.length_dropLast] at ht
        simp only [List.length_cons, List.length_append, List.length_singleton]
        omega
      exact hneidx hind
    have hncomp : ¬ Gᶜ.Adj b x := by
      rw [← hb, ← he, PathBasics.path_adj_iff hQ.1 hlastpos hpos]
      rw [List.length_dropLast] at ht
      simp only [List.length_cons, List.length_append, List.length_singleton]
      omega
    by_contra hn
    exact hncomp ((G.compl_adj b x).mpr ⟨hne, hn⟩)

private theorem longPrismThm33ForbidsOppositeEnds
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G)
    (a b : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V)
    (hp : FormPrism G a b (R 0) (R 1) (R 2))
    (hRlen : ∀ i, 1 < pathLength (R i))
    (hQshape : Q = a 0 :: (q ++ [a 1]))
    (hQa : IsAntipathFrom G Q (a 0) (a 1))
    (hQ4 : 4 ≤ pathLength Q) (hQeven : Even (pathLength Q))
    (ha2q : VertexComplete G (a 2) {x : V | x ∈ q}) :
    ¬ truncatedInteriorCandidate G (b 0) q ∧
      ¬ truncatedInteriorCandidate G (b 1) q := by
  classical
  have hpath : ∀ i, IsPathFrom G (R i) (a i) (b i) :=
    HyperprismFromPrism.formPrism_path hp
  have hlen : ∀ i, 3 ≤ (R i).length := by
    intro i
    have heq := PathBasics.length_eq_pathLength_add_one (hpath i).1
    have hh := hRlen i
    omega
  let p3 : V := (R 1)[1]'(by have := hlen 1; omega)
  let pm : V := (R 0)[1]'(by have := hlen 0; omega)
  let rest : List V := (R 1).drop 2 ++ (R 0).tail.reverse
  let C : List V := a 0 :: (R 1 ++ (R 0).tail.reverse)
  have ht1 : (R 1).tail = p3 :: (R 1).drop 2 := by
    have hd := List.drop_eq_getElem_cons (l := R 1) (i := 1)
      (show 1 < (R 1).length by have := hlen 1; omega)
    simpa [List.drop_one, p3] using hd
  have hs1 : R 1 = a 1 :: p3 :: (R 1).drop 2 := by
    calc
      R 1 = a 1 :: (R 1).tail := (List.cons_head?_tail (hpath 1).2.1).symm
      _ = a 1 :: p3 :: (R 1).drop 2 := by rw [ht1]
  have hCdef : C = a 0 :: a 1 :: p3 :: rest := by
    change a 0 :: (R 1 ++ (R 0).tail.reverse) =
      a 0 :: a 1 :: p3 :: ((R 1).drop 2 ++ (R 0).tail.reverse)
    exact (congrArg (fun l => a 0 :: (l ++ (R 0).tail.reverse)) hs1).trans rfl
  have htail0 : (R 0).tail ≠ [] := by
    intro he
    have heq : (R 0).length = 1 := by
      rw [← List.cons_head?_tail (hpath 0).2.1]
      simp [he]
    have := hlen 0
    omega
  have hpm : C.getLast? = some pm := by
    have hCrewrite : C = (a 0 :: R 1) ++ (R 0).tail.reverse := by simp [C]
    have hrevne : (R 0).tail.reverse ≠ [] := by simpa
    rw [hCrewrite, List.getLast?_append_of_ne_nil _ hrevne,
      List.getLast?_reverse, List.head?_tail,
      List.getElem?_eq_getElem (show 1 < (R 0).length by have := hlen 0; omega)]
  have hbase : IsHoleList G ((R 0).reverse ++ R 1) := by
    refine PathGlue.glue_hole (PathBasics.isPathFrom_reverse (hpath 0)) (hpath 1) ?_ ?_ ?_
    · intro x hx hx1
      exact HyperprismFromPrism.formPrism_disjoint hp (i := 0) (j := 1) (by decide)
        x (List.mem_reverse.mp hx) hx1
    · intro x hx y hy
      exact HyperprismFromPrism.formPrism_cross hp (i := 0) (j := 1) (by decide)
        x (List.mem_reverse.mp hx) y hy
    · have h0 := hlen 0
      have h1 := hlen 1
      simp only [List.length_reverse]
      omega
  have hrot : ((R 0).reverse ++ R 1).rotate ((R 0).length - 1) = C := by
    have hs : a 0 :: (R 0).tail = R 0 := List.cons_head?_tail (hpath 0).2.1
    have hr : (R 0).reverse = (R 0).tail.reverse ++ [a 0] := by
      rw [← hs]
      simp
    rw [List.rotate_eq_drop_append_take]
    · rw [hr]
      simp
      rfl
    · simp
      omega
  have hC : IsHoleList G C := by
    rw [← hrot]
    exact HoleBasics.isHoleList_rotate hbase ((R 0).length - 1)
  have hC6 : 6 ≤ holeLength C := by
    have h0 := hlen 0
    have h1 := hlen 1
    simp [holeLength, C]
    omega
  have ha2Q : VertexComplete G (a 2) {x : V | x ∈ Q} := by
    intro x hx
    have hx' : x = a 0 ∨ x ∈ q ∨ x = a 1 := by simpa [hQshape] using hx
    rcases hx' with rfl | hx | rfl
    · exact hp.1 2 0 (by decide)
    · exact ha2q x hx
    · exact hp.1 2 1 (by decide)
  have ha2C : VertexAnticomplete G (a 2) {x : V | x ∈ C.drop 2} := by
    intro x hx
    have hxTail : x ∈ p3 :: rest := by simpa [hCdef] using hx
    have hnd : (a 0 :: a 1 :: p3 :: rest).Nodup := hCdef ▸ hC.2.1
    have ha0not : a 0 ∉ a 1 :: p3 :: rest := (List.nodup_cons.mp hnd).1
    have ha1not : a 1 ∉ p3 :: rest :=
      (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1
    have hxne0 : x ≠ a 0 := by
      intro he
      exact ha0not (he ▸ List.mem_cons.mpr (Or.inr hxTail))
    have hxne1 : x ≠ a 1 := by
      intro he
      exact ha1not (he ▸ hxTail)
    have hxC : x ∈ C := List.mem_of_mem_drop hx
    have hxpaths : x ∈ R 0 ∨ x ∈ R 1 := by
      simp only [C, List.mem_cons, List.mem_append, List.mem_reverse] at hxC
      rcases hxC with he | hx1 | hx0
      · exact (hxne0 he).elim
      · exact Or.inr hx1
      · exact Or.inl (List.mem_of_mem_tail hx0)
    intro hadj
    rcases hxpaths with hx0 | hx1
    · have hc := (HyperprismFromPrism.formPrism_cross hp (i := 2) (j := 0)
          (by decide) (a 2) (PathBasics.head_mem (hpath 2).2.1) x hx0).mp hadj
      rcases hc with ⟨_, he⟩ | ⟨he, _⟩
      · exact hxne0 he
      · exact hp.2.2.1 2 2 he
    · have hc := (HyperprismFromPrism.formPrism_cross hp (i := 2) (j := 1)
          (by decide) (a 2) (PathBasics.head_mem (hpath 2).2.1) x hx1).mp hadj
      rcases hc with ⟨_, he⟩ | ⟨he, _⟩
      · exact hxne1 he
      · exact hp.2.2.1 2 2 he
  have h33 := Workspace.Statements.S03.SPGT.thm_3_3 G hG C (a 0) (a 1) p3 pm rest
    hC hC6 hCdef hpm q Q hQshape hQa hQ4 hQeven (a 2) ha2Q ha2C
  have hb0mem : b 0 ∈ R 0 := PathBasics.getLast_mem (hpath 0).2.2
  have hb1mem : b 1 ∈ R 1 := PathBasics.getLast_mem (hpath 1).2.2
  have hb0tail : b 0 ∈ (R 0).tail := by
    have hm := hb0mem
    rw [← List.cons_head?_tail (hpath 0).2.1] at hm
    rcases List.mem_cons.mp hm with he | he
    · exact (hp.2.2.1 0 0 he.symm).elim
    · exact he
  have hb1drop : b 1 ∈ (R 1).drop 2 := by
    rw [hs1] at hb1mem
    simp only [List.mem_cons] at hb1mem
    rcases hb1mem with he | he | he
    · exact (hp.2.2.1 1 1 he.symm).elim
    · have hlast := PathBasics.getElem_last_of_getLast? (hpath 1).2.2
          (PathBasics.path_length_pos (hpath 1).1)
      have hnd1 := (hpath 1).1.2.1
      have helem : (R 1)[(R 1).length - 1]'(by have := hlen 1; omega) =
          (R 1)[1]'(by have := hlen 1; omega) := by
        rw [hlast, he]
      have hind := hnd1.getElem_inj_iff.mp helem
      have := hlen 1
      omega
    · exact he
  have hb0Drop : b 0 ∈ C.drop 2 := by
    rw [hCdef]
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons]
    exact Or.inr (by simp [rest, hb0tail])
  have hb1Drop : b 1 ∈ C.drop 2 := by
    rw [hCdef]
    simp only [List.drop_succ_cons, List.drop_zero, List.mem_cons]
    exact Or.inr (by simp [rest, hb1drop])
  have hb0nep3 : b 0 ≠ p3 := by
    intro he
    exact HyperprismFromPrism.formPrism_disjoint hp (i := 0) (j := 1) (by decide)
      (b 0) hb0mem (he ▸ List.getElem_mem (show 1 < (R 1).length by have := hlen 1; omega))
  have hb1nepm : b 1 ≠ pm := by
    intro he
    exact HyperprismFromPrism.formPrism_disjoint hp (i := 1) (j := 0) (by decide)
      (b 1) hb1mem (he ▸ List.getElem_mem (show 1 < (R 0).length by have := hlen 0; omega))
  have hb0nepm : b 0 ≠ pm := by
    intro he
    have hlast := PathBasics.getElem_last_of_getLast? (hpath 0).2.2
      (PathBasics.path_length_pos (hpath 0).1)
    have helem : (R 0)[(R 0).length - 1]'(by have := hlen 0; omega) =
        (R 0)[1]'(by have := hlen 0; omega) := by
      rw [hlast, he]
    have hind := (hpath 0).1.2.1.getElem_inj_iff.mp helem
    have := hlen 0
    omega
  have hb1nep3 : b 1 ≠ p3 := by
    intro he
    have hlast := PathBasics.getElem_last_of_getLast? (hpath 1).2.2
      (PathBasics.path_length_pos (hpath 1).1)
    have helem : (R 1)[(R 1).length - 1]'(by have := hlen 1; omega) =
        (R 1)[1]'(by have := hlen 1; omega) := by
      rw [hlast, he]
    have hind := (hpath 1).1.2.1.getElem_inj_iff.mp helem
    have := hlen 1
    omega
  constructor
  · intro hc
    rcases h33.2 (b 0) hb0Drop hc with he | he
    · exact hb0nep3 he
    · exact hb0nepm he
  · intro hc
    rcases h33.2 (b 1) hb1Drop hc with he | he
    · exact hb1nep3 he
    · exact hb1nepm he

end Workspace.ProofLemmas

namespace Workspace.ProofLemmas

open Workspace.Types.Core.SPGT
open Workspace.Types.Prisms.SPGT

theorem globalMinimalPrismAntipathContradictionCore
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : Berge G) (Y : Set V)
    (alpha beta : Fin 3 → V) (R : Fin 3 → List V) (q Q : List V)
    (hprism : FormPrism G alpha beta (R 0) (R 1) (R 2))
    (hRoutside : ∀ i v, v ∈ R i → v ∉ Y)
    (hRlength : ∀ i, 1 < pathLength (R i))
    (hYmajor : ∀ y ∈ Y, MajorForPrism G alpha beta y)
    (hQ : Q = alpha 0 :: (q ++ [alpha 1]))
    (hQantipath : IsAntipathFrom G Q (alpha 0) (alpha 1))
    (hqY : ∀ x ∈ q, x ∈ Y)
    (halpha0 : ¬ VertexComplete G (alpha 0) Y)
    (halpha1 : ¬ VertexComplete G (alpha 1) Y)
    (hminimal : ∀ (u v : V) (S : List V),
      u ≠ v →
      ((u ∈ ({alpha 0, alpha 1, alpha 2} : Set V) ∧
          v ∈ ({alpha 0, alpha 1, alpha 2} : Set V)) ∨
        (u ∈ ({beta 0, beta 1, beta 2} : Set V) ∧
          v ∈ ({beta 0, beta 1, beta 2} : Set V))) →
      ¬ VertexComplete G u Y →
      ¬ VertexComplete G v Y →
      IsAntipathFrom G S u v →
      (∀ x ∈ interior S, x ∈ Y) →
      pathLength Q ≤ pathLength S) :
    False := by
  classical
  have ha2q := GlobalMinimalPrismAntipathThirdTriangleVertexComplete G Y alpha beta R q Q
    hprism hRoutside hYmajor hQ hQantipath hqY halpha0 halpha1 hminimal
  obtain ⟨hex, hQ4, hQeven⟩ :=
    GlobalMinimalPrismAntipathOppositeTriangleCompleteAndEven G hG Y alpha beta R q Q
      hprism hRoutside hRlength hYmajor hQ hQantipath hqY halpha0 halpha1 hminimal
  have hbnot := longPrismThm33ForbidsOppositeEnds G hG alpha beta R q Q hprism hRlength hQ hQantipath
    hQ4 hQeven ha2q
  obtain ⟨i, hiq⟩ := hex
  have hb2q : VertexComplete G (beta 2) {x : V | x ∈ q} := by
    rcases HyperprismBasics.fin3_cases i with rfl | rfl | rfl
    · exfalso
      exact hbnot.1 (Or.inl (fun x hx => hiq x (List.mem_of_mem_dropLast hx)))
    · exfalso
      exact hbnot.2 (Or.inl (fun x hx => hiq x (List.mem_of_mem_dropLast hx)))
    · exact hiq
  have hb0notq : ¬ VertexComplete G (beta 0) {x : V | x ∈ q} := by
    intro hc
    exact hbnot.1 (Or.inl (fun x hx => hc x (List.mem_of_mem_dropLast hx)))
  have hb1notq : ¬ VertexComplete G (beta 1) {x : V | x ∈ q} := by
    intro hc
    exact hbnot.2 (Or.inl (fun x hx => hc x (List.mem_of_mem_dropLast hx)))
  let Bad : Fin 3 → ℕ → Prop :=
    fun k t => ∃ ht : t < q.length, ¬ G.Adj (beta k) (q[t]'ht)
  have hbad0 : ∃ t : ℕ, Bad 0 t := by
    simp only [VertexComplete, Set.mem_setOf_eq] at hb0notq
    push Not at hb0notq
    obtain ⟨x, hxq, hxadj⟩ := hb0notq
    obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hxq
    refine ⟨t, ht, ?_⟩
    rw [htx]
    exact hxadj
  have hbad1 : ∃ t : ℕ, Bad 1 t := by
    simp only [VertexComplete, Set.mem_setOf_eq] at hb1notq
    push Not at hb1notq
    obtain ⟨x, hxq, hxadj⟩ := hb1notq
    obtain ⟨t, ht, htx⟩ := List.mem_iff_getElem.mp hxq
    refine ⟨t, ht, ?_⟩
    rw [htx]
    exact hxadj
  have hbad_unique : ∀ (i j : Fin 3) (t : ℕ), i ≠ j →
      Bad i t → Bad j t → False := by
    intro i j t hij hbi hbj
    obtain ⟨ht, hni⟩ := hbi
    obtain ⟨ht', hnj⟩ := hbj
    have hty : q[t]'ht ∈ Y := hqY _ (List.getElem_mem ht)
    have hnj' : ¬ G.Adj (beta j) (q[t]'ht) := by simpa using hnj
    exact saturation_forbids_two_misses G beta (q[t]'ht) (hYmajor _ hty).2
      i j hij hni hnj'
  let Pair : ℕ → Prop := fun e =>
    ∃ (i j : Fin 3) (r s : ℕ), i ≠ j ∧ r < s ∧ s - r = e ∧ Bad i r ∧ Bad j s
  have hpair_exists : ∃ e : ℕ, Pair e := by
    obtain ⟨r0, hr0⟩ := hbad0
    obtain ⟨r1, hr1⟩ := hbad1
    have h01 : r0 ≠ r1 := by
      intro he
      subst r1
      exact hbad_unique 0 1 r0 (by decide) hr0 hr1
    rcases lt_or_gt_of_ne h01 with hlt | hgt
    · exact ⟨r1 - r0, 0, 1, r0, r1, by decide, hlt, rfl, hr0, hr1⟩
    · exact ⟨r0 - r1, 1, 0, r1, r0, by decide, hgt, rfl, hr1, hr0⟩
  let d : ℕ := Nat.find hpair_exists
  have hd_spec : Pair d := Nat.find_spec hpair_exists
  obtain ⟨i, j, r, s, hij, hrs, hdist, hbr, hbs⟩ := hd_spec
  obtain ⟨hrlt, hnibr⟩ := hbr
  obtain ⟨hslt, hnibs⟩ := hbs
  have hbr : Bad i r := ⟨hrlt, hnibr⟩
  have hbs : Bad j s := ⟨hslt, hnibs⟩
  have hdmin : ∀ e : ℕ, Pair e → d ≤ e := by
    intro e he
    exact Nat.find_min' hpair_exists he
  have hno_bad_between : ∀ (k : Fin 3) (t : ℕ), r < t → t < s → ¬ Bad k t := by
    intro k t hrt hts hbt
    by_cases hki : k = i
    · subst k
      have hp : Pair (s - t) := ⟨i, j, t, s, hij, hts, rfl, hbt, hbs⟩
      have hle := hdmin (s - t) hp
      have hlt : s - t < d := by omega
      omega
    · have hp : Pair (t - r) :=
        ⟨i, k, r, t, (fun he => hki he.symm), hrt, rfl, hbr, hbt⟩
      have hle := hdmin (t - r) hp
      have hlt : t - r < d := by omega
      omega
  have hqpath : IsPathList Gᶜ q := by
    have hslice := PathBasics.isPathList_slice hQantipath.1 (i := 1) (j := q.length)
      (by omega) (by simp [hQ])
    have hlen : q.length - 1 + 1 = q.length := by omega
    rw [hlen] at hslice
    simpa [hQ] using hslice
  let sl : List V := (q.drop r).take (s - r + 1)
  have hslpath : IsPathFrom Gᶜ sl (q[r]'hrlt) (q[s]'hslt) := by
    exact PathBasics.isPathFrom_slice hqpath hrs hslt
  let S : List V := beta i :: (sl ++ [beta j])
  have hS : IsAntipathFrom G S (beta i) (beta j) := by
    change IsPathFrom Gᶜ S (beta i) (beta j)
    dsimp only [S]
    refine PathAttach.isPathFrom_cons_concat hslpath ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · refine (G.compl_adj _ _).mpr ⟨?_, hnibr⟩
      intro he
      apply hRoutside i (beta i)
        (PathBasics.getLast_mem (HyperprismFromPrism.formPrism_path hprism i).2.2)
      rw [he]
      exact hqY _ (List.getElem_mem hrlt)
    · refine (G.compl_adj _ _).mpr ⟨?_, hnibs⟩
      intro he
      apply hRoutside j (beta j)
        (PathBasics.getLast_mem (HyperprismFromPrism.formPrism_path hprism j).2.2)
      rw [he]
      exact hqY _ (List.getElem_mem hslt)
    · intro hc
      exact ((G.compl_adj _ _).mp hc).2 (hprism.2.1 i j hij)
    · exact (hprism.2.1 i j hij).ne
    · intro hx
      obtain ⟨u, hu, hru, hus, hux⟩ :=
        (PathBasics.mem_slice_iff q (i := r) (j := s) (x := beta i)
          (le_of_lt hrs) hslt).mp hx
      apply hRoutside i (beta i)
        (PathBasics.getLast_mem (HyperprismFromPrism.formPrism_path hprism i).2.2)
      rw [← hux]
      exact hqY _ (List.getElem_mem hu)
    · intro hx
      obtain ⟨u, hu, hru, hus, hux⟩ :=
        (PathBasics.mem_slice_iff q (i := r) (j := s) (x := beta j)
          (le_of_lt hrs) hslt).mp hx
      apply hRoutside j (beta j)
        (PathBasics.getLast_mem (HyperprismFromPrism.formPrism_path hprism j).2.2)
      rw [← hux]
      exact hqY _ (List.getElem_mem hu)
    · intro x hx hxne hcx
      have hni : ¬ G.Adj (beta i) x := ((G.compl_adj _ _).mp hcx).2
      obtain ⟨u, hu, hru, hus, hux⟩ :=
        (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
          (le_of_lt hrs) hslt).mp hx
      have hbu : Bad i u := by
        refine ⟨hu, ?_⟩
        rw [hux]
        exact hni
      by_cases hur : u = r
      · subst u
        exact hxne (by simpa using hux.symm)
      by_cases hus' : u = s
      · subst u
        exact hbad_unique i j s hij hbu hbs
      exact hno_bad_between i u (by omega) (by omega) hbu
    · intro x hx hxne hcx
      have hni : ¬ G.Adj (beta j) x := ((G.compl_adj _ _).mp hcx).2
      obtain ⟨u, hu, hru, hus, hux⟩ :=
        (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
          (le_of_lt hrs) hslt).mp hx
      have hbu : Bad j u := by
        refine ⟨hu, ?_⟩
        rw [hux]
        exact hni
      by_cases hus' : u = s
      · subst u
        exact hxne (by simpa using hux.symm)
      by_cases hur : u = r
      · subst u
        exact hbad_unique i j r hij hbr hbu
      exact hno_bad_between j u (by omega) (by omega) hbu
  have hSint : ∀ x ∈ Workspace.Types.Core.SPGT.interior S, x ∈ Y := by
    intro x hx
    have hxsl : x ∈ sl := by
      simpa [S, Workspace.Types.Core.SPGT.interior] using hx
    obtain ⟨u, hu, hru, hus, hux⟩ :=
      (PathBasics.mem_slice_iff q (i := r) (j := s) (x := x)
        (le_of_lt hrs) hslt).mp hxsl
    rw [← hux]
    exact hqY _ (List.getElem_mem hu)
  have hbeta_tri : ∀ k : Fin 3, beta k ∈ ({beta 0, beta 1, beta 2} : Set V) := by
    intro k
    rcases HyperprismBasics.fin3_cases k with rfl | rfl | rfl <;> simp
  have hbi_notY : ¬ VertexComplete G (beta i) Y := by
    intro hc
    exact hnibr (hc _ (hqY _ (List.getElem_mem hrlt)))
  have hbj_notY : ¬ VertexComplete G (beta j) Y := by
    intro hc
    exact hnibs (hc _ (hqY _ (List.getElem_mem hslt)))
  have hmin := hminimal (beta i) (beta j) S (hprism.2.1 i j hij).ne
    (Or.inr ⟨hbeta_tri i, hbeta_tri j⟩) hbi_notY hbj_notY hS hSint
  have hSlen : pathLength S = s - r + 2 := by
    dsimp only [S, sl]
    rw [PathAttach.pathLength_cons_append_singleton]
    rw [PathBasics.length_slice q (le_of_lt hrs) hslt]
  have hQlen : pathLength Q = q.length + 1 := by simp [hQ, pathLength]
  have hr0 : r = 0 := by
    rw [hQlen, hSlen] at hmin
    omega
  have hslast : s = q.length - 1 := by
    rw [hQlen, hSlen] at hmin
    omega
  have hslice : sl = q := by
    dsimp only [sl]
    rw [hr0, List.drop_zero, hslast]
    have he : q.length - 1 - 0 + 1 = q.length := by omega
    rw [he, List.take_length]
  have hSshape : S = beta i :: (q ++ [beta j]) := by simp [S, hslice]
  have hlenEq : pathLength S = pathLength Q := by
    rw [hSlen, hQlen, hr0, hslast]
    omega
  have hS4 : 4 ≤ pathLength S := by rw [hlenEq]; exact hQ4
  have hSeven : Even (pathLength S) := by rw [hlenEq]; exact hQeven
  have hi2 : i ≠ 2 := by
    intro he
    subst i
    exact hnibr (hb2q _ (List.getElem_mem hrlt))
  have hj2 : j ≠ 2 := by
    intro he
    subst j
    exact hnibs (hb2q _ (List.getElem_mem hslt))
  have hswap : FormPrism G beta alpha (R 0).reverse (R 1).reverse (R 2).reverse :=
    PrismSymmetry.formPrism_swap hprism
  let RR : Fin 3 → List V := fun k => (R k).reverse
  have hswap' : FormPrism G beta alpha (RR 0) (RR 1) (RR 2) := by simpa [RR] using hswap
  have hRRlen : ∀ k, 1 < pathLength (RR k) := by
    intro k
    simpa [RR, pathLength] using hRlength k
  obtain ⟨ha0tail, ha1drop⟩ := antipathEndsCompleteToTruncatedInterior hQ hQantipath
  rcases HyperprismBasics.fin3_cases i with rfl | rfl | rfl
  · rcases HyperprismBasics.fin3_cases j with rfl | rfl | rfl
    · exact (hij rfl).elim
    · have hforbid := longPrismThm33ForbidsOppositeEnds G hG beta alpha RR q S hswap' hRRlen hSshape hS
          hS4 hSeven hb2q
      exact hforbid.1 (Or.inr ha0tail)
    · exact (hj2 rfl).elim
  · rcases HyperprismBasics.fin3_cases j with rfl | rfl | rfl
    · have hSrev : IsAntipathFrom G S.reverse (beta 0) (beta 1) := by
        simpa using PathBasics.isPathFrom_reverse hS
      have hrevshape : S.reverse = beta 0 :: (q.reverse ++ [beta 1]) := by
        rw [hSshape]
        simp
      have hb2qrev : VertexComplete G (beta 2) {x : V | x ∈ q.reverse} := by
        intro x hx
        exact hb2q x (List.mem_reverse.mp hx)
      have hforbid := longPrismThm33ForbidsOppositeEnds G hG beta alpha RR q.reverse S.reverse hswap' hRRlen
        hrevshape hSrev (by simpa [pathLength] using hS4)
        (by simpa [pathLength] using hSeven) hb2qrev
      have ha0rev : VertexComplete G (alpha 0) {x : V | x ∈ q.reverse.dropLast} := by
        intro x hx
        apply ha0tail x
        rw [List.dropLast_reverse] at hx
        exact List.mem_reverse.mp hx
      exact hforbid.1 (Or.inl ha0rev)
    · exact (hij rfl).elim
    · exact (hj2 rfl).elim
  · exact (hi2 rfl).elim

end Workspace.ProofLemmas
