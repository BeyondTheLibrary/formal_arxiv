import Mathlib
import Workspace.Types.Core
import Workspace.Types.Replication
import Workspace.ProofLemmas.PathBasics
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.PerfectInducedSubgraph
import Workspace.ProofLemmas.CliqueNumOfInducedSet
import Workspace.ProofLemmas.OccurrenceIndexedCliqueReplicationPerfect
import Workspace.ProofLemmas.EdgeDeletedReplicationPerfect

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace OddChainEngine

open Workspace.Types.Core

/-- **The §8 blow-up engine.**  `L` is a perfect graph whose vertex set is the
disjoint union of a side `T` and a chain `x 0, …, x (M-1)`; the chain is induced,
`x 0` is complete to `AA ⊆ T`, `x (M-1)` is complete to `BB ⊆ T`, and every other
chain vertex is anticomplete to `T`.  Blowing `x i` up into a clique of `f i`
twins (side vertices keep multiplicity one) yields a perfect graph of clique
number at most `n`, hence an `n`-colouring, whose class palettes `Pal i` have the
prescribed sizes, are pairwise disjoint along the chain, and avoid the palettes
of the boundary sets they are complete to. -/
theorem chain_engine
    {V : Type*} [Fintype V] [DecidableEq V]
    (L : SimpleGraph V) (hL : SPGT.IsPerfect L)
    (T AA BB : Set V) (hAA : AA ⊆ T) (hBB : BB ⊆ T) (hABd : Disjoint AA BB)
    (M : ℕ) (hM : 2 ≤ M) (x : ℕ → V)
    (SB : Set ℕ) (h0SB : (0 : ℕ) ∉ SB) (hSBlt : ∀ i, i ∈ SB → i < M)
    (hxT : ∀ i, i < M → x i ∉ T)
    (hxinj : ∀ i, i < M → ∀ j, j < M → x i = x j → i = j)
    (hchain : ∀ i, i < M → ∀ j, j < M → (L.Adj (x i) (x j) ↔ (i + 1 = j ∨ j + 1 = i)))
    (hcross : ∀ i, i < M → ∀ t, t ∈ T →
      (L.Adj (x i) t ↔ ((i = 0 ∧ t ∈ AA) ∨ (i ∈ SB ∧ t ∈ BB))))
    (hcover : ∀ v : V, v ∈ T ∨ ∃ i, i < M ∧ v = x i)
    (n : ℕ) (f : ℕ → ℕ)
    (hTn : (L.induce T).cliqueNum ≤ n)
    (hfle : ∀ i, i < M → f i ≤ n)
    (hfpair : ∀ i, i + 1 < M → f i + f (i + 1) ≤ n)
    (hfA : f 0 + (L.induce AA).cliqueNum ≤ n)
    (hfB1 : ∀ i, i ∈ SB → f i + (L.induce BB).cliqueNum ≤ n)
    (hfB2 : ∀ i, i ∈ SB → (i + 1) ∈ SB → f i + f (i + 1) + (L.induce BB).cliqueNum ≤ n) :
    ∃ (col : (L.induce T).Coloring (Fin n)) (Pal : ℕ → Set (Fin n)),
      (∀ i, i < M → (Pal i).ncard = f i) ∧
      (∀ i, i + 1 < M → Disjoint (Pal i) (Pal (i + 1))) ∧
      Disjoint (col '' {v : T | (v : V) ∈ AA}) (Pal 0) ∧
      (∀ i, i ∈ SB → Disjoint (col '' {v : T | (v : V) ∈ BB}) (Pal i)) := by
  classical
  -- ## 0. index and multiplicity functions
  set idx : V → ℕ := fun v => if h : ∃ i, i < M ∧ v = x i then h.choose else 0 with hidxdef
  have hidxspec : ∀ v : V, (∃ i, i < M ∧ v = x i) → (idx v < M ∧ v = x (idx v)) := by
    intro v h
    simp only [hidxdef, dif_pos h]
    exact h.choose_spec
  have hidxx : ∀ i, i < M → idx (x i) = i := by
    intro i hi
    obtain ⟨h1, h2⟩ := hidxspec (x i) ⟨i, hi, rfl⟩
    exact (hxinj i hi _ h1 h2).symm
  set mult : V → ℕ := fun v => if v ∈ T then 1 else f (idx v) with hmultdef
  have hmultT : ∀ v : V, v ∈ T → mult v = 1 := by
    intro v hv; simp [hmultdef, hv]
  have hmultx : ∀ i, i < M → mult (x i) = f i := by
    intro i hi; simp [hmultdef, hxT i hi, hidxx i hi]
  have hmultle : ∀ v : V, mult v ≤ n + 1 := by
    intro v
    rcases hcover v with hv | ⟨i, hi, rfl⟩
    · rw [hmultT v hv]; omega
    · rw [hmultx i hi]; have := hfle i hi; omega
  -- ## 1. the occurrence graph
  set AS : Fin (n + 1) → Set V := fun i => {v : V | (i : ℕ) < mult v} with hASdef
  have hΩ := Workspace.ProofLemmas.OccurrenceIndexedCliqueReplicationPerfect
    L (n + 1) (by omega) AS hL
  let Ω : Type _ := {p : Fin (n + 1) × V // p.2 ∈ AS p.1}
  let π : Ω → V := fun p => p.1.2
  let KΩ : SimpleGraph Ω :=
    { Adj := fun a b => a ≠ b ∧ (π a = π b ∨ L.Adj (π a) (π b))
      symm := by
        intro a b h
        exact ⟨h.1.symm, h.2.elim (fun h' => Or.inl h'.symm) (fun h' => Or.inr h'.symm)⟩
      loopless := by
        refine ⟨?_⟩
        intro a h
        exact h.1 rfl }
  have hperfΩ : SPGT.IsPerfect KΩ := hΩ
  haveI : Fintype Ω := Fintype.ofFinite Ω
  haveI : DecidableEq Ω := Classical.decEq Ω
  have hKΩadj : ∀ a b : Ω, KΩ.Adj a b ↔ (a ≠ b ∧ (π a = π b ∨ L.Adj (π a) (π b))) :=
    fun a b => Iff.rfl
  -- ## 2. fibers
  have hFinlt : ∀ m : ℕ, m ≤ n + 1 → ({i : Fin (n + 1) | (i : ℕ) < m}).ncard = m := by
    intro m hm
    have heq : {i : Fin (n + 1) | (i : ℕ) < m} = Set.range (Fin.castLE hm) := by
      ext i
      constructor
      · intro hi
        exact ⟨⟨(i : ℕ), hi⟩, Fin.ext rfl⟩
      · rintro ⟨j, rfl⟩
        exact j.2
    have hcinj : Function.Injective (Fin.castLE hm) :=
      fun a b hab => Fin.ext (congrArg (fun i : Fin (n + 1) => (i : ℕ)) hab)
    rw [heq, ← Set.image_univ, Set.ncard_image_of_injective Set.univ hcinj,
      Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  set fib : V → Set Ω := fun v => {q : Ω | π q = v} with hfibdef
  have hfibcard : ∀ v : V, (fib v).ncard = mult v := by
    intro v
    have hinj : Set.InjOn (fun q : Ω => q.1.1) (fib v) := by
      intro q hq q' hq' h
      have h2 : q.1.2 = q'.1.2 := by
        have e1 : π q = v := hq
        have e2 : π q' = v := hq'
        exact e1.trans e2.symm
      exact Subtype.ext (Prod.ext h h2)
    have himg : (fun q : Ω => q.1.1) '' (fib v) = {i : Fin (n + 1) | (i : ℕ) < mult v} := by
      ext i
      constructor
      · rintro ⟨q, hq, rfl⟩
        have hq2 : q.1.2 ∈ AS q.1.1 := q.2
        have : (q.1.1 : ℕ) < mult q.1.2 := hq2
        have e1 : π q = v := hq
        rw [show q.1.2 = v from e1] at this
        exact this
      · intro hi
        refine ⟨⟨(i, v), hi⟩, rfl, rfl⟩
    calc (fib v).ncard = ((fun q : Ω => q.1.1) '' (fib v)).ncard :=
          (Set.ncard_image_of_injOn hinj).symm
      _ = mult v := by rw [himg, hFinlt (mult v) (hmultle v)]
  have hfibclique : ∀ v : V, KΩ.IsClique (fib v) := by
    intro v q hq q' hq' hne
    exact ⟨hne, Or.inl ((hq : π q = v).trans (hq' : π q' = v).symm)⟩
  have hfibmem : ∀ (v : V) (q : Ω), q ∈ fib v ↔ π q = v := fun v q => Iff.rfl
  -- ## 3. the clique-number bound
  have hcliqueΩ : KΩ.cliqueNum ≤ n := by
    obtain ⟨Q, hQ⟩ := SimpleGraph.exists_isNClique_cliqueNum (G := KΩ)
    have hQc : KΩ.IsClique (↑Q : Set Ω) := hQ.1
    have hQcard : Q.card = KΩ.cliqueNum := hQ.2
    set S : Finset V := Q.image π with hS
    have hSadj : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → L.Adj u v := by
      intro u hu v hv huv
      rw [hS, Finset.mem_image] at hu hv
      obtain ⟨q, hqQ, rfl⟩ := hu
      obtain ⟨q', hq'Q, rfl⟩ := hv
      have hne : q ≠ q' := fun h => huv (by rw [h])
      rcases (hQc (Finset.mem_coe.mpr hqQ) (Finset.mem_coe.mpr hq'Q) hne).2 with h | h
      · exact absurd h huv
      · exact h
    have hQsum : Q.card ≤ ∑ v ∈ S, mult v := by
      have hmap : ∀ q ∈ Q, π q ∈ S := by
        intro q hq; rw [hS, Finset.mem_image]; exact ⟨q, hq, rfl⟩
      rw [Finset.card_eq_sum_card_fiberwise hmap]
      refine Finset.sum_le_sum ?_
      intro v _
      have hsub : (↑(Q.filter (fun q => π q = v)) : Set Ω) ⊆ fib v := by
        intro q hq
        exact (Finset.mem_filter.mp (Finset.mem_coe.mp hq)).2
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      rwa [Set.ncard_coe_finset, hfibcard v] at this
    set ST : Finset V := S.filter (fun v => v ∈ T) with hST
    set SM : Finset V := S.filter (fun v => v ∉ T) with hSM
    have hSTsub : (↑ST : Set V) ⊆ T := by
      intro v hv
      exact (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    have hSTclique : L.IsClique (↑ST : Set V) := by
      intro u hu v hv huv
      exact hSadj u (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).1
        v (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1 huv
    have hSTle : ST.card ≤ (L.induce T).cliqueNum :=
      Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce L hSTsub hSTclique
    have hsplit : ∑ v ∈ S, mult v = (∑ v ∈ ST, mult v) + ∑ v ∈ SM, mult v := by
      rw [hST, hSM]
      exact (Finset.sum_filter_add_sum_filter_not S (fun v => v ∈ T) mult).symm
    have hSTsum : ∑ v ∈ ST, mult v = ST.card := by
      rw [Finset.sum_congr rfl (fun v hv => hmultT v (hSTsub (Finset.mem_coe.mpr hv))),
        Finset.sum_const, smul_eq_mul, mul_one]
    -- the marker part
    have hSMx : ∀ v ∈ SM, idx v < M ∧ v = x (idx v) := by
      intro v hv
      have hvT : v ∉ T := (Finset.mem_filter.mp hv).2
      rcases hcover v with h | h
      · exact absurd h hvT
      · exact hidxspec v h
    set I : Finset ℕ := SM.image idx with hI
    have hIinj : ∀ u ∈ SM, ∀ v ∈ SM, idx u = idx v → u = v := by
      intro u hu v hv h
      rw [(hSMx u hu).2, (hSMx v hv).2, h]
    have hSMsum : ∑ v ∈ SM, mult v = ∑ i ∈ I, f i := by
      rw [hI, Finset.sum_image hIinj]
      refine Finset.sum_congr rfl ?_
      intro v hv
      have hvT : v ∉ T := (Finset.mem_filter.mp hv).2
      simp [hmultdef, hvT]
    have hIlt : ∀ i ∈ I, i < M := by
      intro i hi
      rw [hI, Finset.mem_image] at hi
      obtain ⟨v, hv, rfl⟩ := hi
      exact (hSMx v hv).1
    have hIcons : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → (i + 1 = j ∨ j + 1 = i) := by
      intro i hi j hj hij
      have hi' := hi; have hj' := hj
      rw [hI, Finset.mem_image] at hi' hj'
      obtain ⟨u, hu, rfl⟩ := hi'
      obtain ⟨v, hv, rfl⟩ := hj'
      have hune : u ≠ v := fun h => hij (by rw [h])
      have hadj : L.Adj u v :=
        hSadj u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 hune
      have hux := (hSMx u hu).2
      have hvx := (hSMx v hv).2
      rw [hux, hvx] at hadj
      exact (hchain _ (hSMx u hu).1 _ (hSMx v hv).1).mp hadj
    -- membership of `ST` forces adjacency to every marker class in `I`
    have hSTadj : ∀ t ∈ ST, ∀ i ∈ I, L.Adj (x i) t := by
      intro t ht i hi
      have hi' := hi
      rw [hI, Finset.mem_image] at hi'
      obtain ⟨v, hv, rfl⟩ := hi'
      have hvT : v ∉ T := (Finset.mem_filter.mp hv).2
      have htT : t ∈ T := hSTsub (Finset.mem_coe.mpr ht)
      have hne : v ≠ t := fun h => hvT (h ▸ htT)
      have := hSadj v (Finset.mem_filter.mp hv).1 t (Finset.mem_filter.mp ht).1 hne
      rwa [← (hSMx v hv).2]
    rcases Finset.eq_empty_or_nonempty I with hIe | hIne
    · have : ∑ i ∈ I, f i = 0 := by rw [hIe]; simp
      omega
    · set i₀ : ℕ := I.min' hIne with hi₀
      have hi₀I : i₀ ∈ I := I.min'_mem hIne
      have hi₀M : i₀ < M := hIlt i₀ hi₀I
      have hIsub : ∀ j ∈ I, j = i₀ ∨ j = i₀ + 1 := by
        intro j hj
        have hle : i₀ ≤ j := I.min'_le j hj
        rcases eq_or_ne j i₀ with rfl | hne
        · exact Or.inl rfl
        · rcases hIcons i₀ hi₀I j hj (Ne.symm hne) with h | h
          · exact Or.inr h.symm
          · omega
      by_cases h2 : i₀ + 1 ∈ I
      · -- two consecutive classes
        have hIeq : I = {i₀, i₀ + 1} := by
          apply Finset.Subset.antisymm
          · intro j hj
            rcases hIsub j hj with rfl | rfl <;> simp
          · intro j hj
            simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl
            · exact hi₀I
            · exact h2
        have h1M : i₀ + 1 < M := hIlt _ h2
        have hIsum : ∑ i ∈ I, f i = f i₀ + f (i₀ + 1) := by
          rw [hIeq, Finset.sum_insert (by simp), Finset.sum_singleton]
        by_cases hboth : i₀ ∈ SB ∧ (i₀ + 1) ∈ SB
        · have hSTB : (↑ST : Set V) ⊆ BB := by
            intro t ht
            have htT : t ∈ T := hSTsub ht
            rcases (hcross (i₀ + 1) h1M t htT).mp
                (hSTadj t (Finset.mem_coe.mp ht) (i₀ + 1) h2) with ⟨he, -⟩ | ⟨-, hb⟩
            · omega
            · exact hb
          have hle := Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce
            L hSTB hSTclique
          have hb2 := hfB2 i₀ hboth.1 hboth.2
          omega
        · have hSTempty : ST = ∅ := by
            rw [Finset.eq_empty_iff_forall_notMem]
            intro t ht
            have htT : t ∈ T := hSTsub (Finset.mem_coe.mpr ht)
            have ha0 := (hcross i₀ hi₀M t htT).mp (hSTadj t ht i₀ hi₀I)
            have ha1 := (hcross (i₀ + 1) h1M t htT).mp (hSTadj t ht (i₀ + 1) h2)
            rcases ha1 with ⟨he, -⟩ | ⟨hs1, hb⟩
            · omega
            · rcases ha0 with ⟨he0, ha⟩ | ⟨hs0, -⟩
              · exact (Set.disjoint_left.mp hABd ha) hb
              · exact hboth ⟨hs0, hs1⟩
          have hzc : ST.card = 0 := by rw [hSTempty]; simp
          have hpair := hfpair i₀ h1M
          omega
      · -- a single class
        have hIeq : I = {i₀} := by
          apply Finset.Subset.antisymm
          · intro j hj
            rcases hIsub j hj with rfl | rfl
            · simp
            · exact absurd hj h2
          · intro j hj
            simp only [Finset.mem_singleton] at hj
            exact hj ▸ hi₀I
        have hIsum : ∑ i ∈ I, f i = f i₀ := by rw [hIeq, Finset.sum_singleton]
        by_cases hz : i₀ = 0
        · -- boundary class at `A`
          have hSTA : (↑ST : Set V) ⊆ AA := by
            intro t ht
            have htT : t ∈ T := hSTsub ht
            rcases (hcross i₀ hi₀M t htT).mp
                (hSTadj t (Finset.mem_coe.mp ht) i₀ hi₀I) with ⟨-, ha⟩ | ⟨hs, -⟩
            · exact ha
            · exact absurd (hz ▸ hs) h0SB
          have hSTAle : ST.card ≤ (L.induce AA).cliqueNum :=
            Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce L hSTA hSTclique
          rw [hz] at hIsum
          omega
        · by_cases hz' : i₀ ∈ SB
          · -- boundary class at `B`
            have hSTB : (↑ST : Set V) ⊆ BB := by
              intro t ht
              have htT : t ∈ T := hSTsub ht
              rcases (hcross i₀ hi₀M t htT).mp
                  (hSTadj t (Finset.mem_coe.mp ht) i₀ hi₀I) with ⟨he, -⟩ | ⟨-, hb⟩
              · exact absurd he hz
              · exact hb
            have hSTBle : ST.card ≤ (L.induce BB).cliqueNum :=
              Workspace.ProofLemmas.CliqueNumOfInducedSet.card_le_cliqueNum_induce L hSTB hSTclique
            have hb1 := hfB1 i₀ hz'
            omega
          · -- internal class: anticomplete to the side
            have hSTempty : ST = ∅ := by
              rw [Finset.eq_empty_iff_forall_notMem]
              intro t ht
              have htT : t ∈ T := hSTsub (Finset.mem_coe.mpr ht)
              rcases (hcross i₀ hi₀M t htT).mp (hSTadj t ht i₀ hi₀I) with ⟨he, -⟩ | ⟨hs, -⟩
              · exact hz he
              · exact hz' hs
            have : ST.card = 0 := by rw [hSTempty]; simp
            have := hfle i₀ hi₀M
            omega
  -- ## 4. the colouring
  obtain ⟨colΩ⟩ : KΩ.Colorable n :=
    SimpleGraph.Colorable.mono hcliqueΩ
      (Workspace.ProofLemmas.CliqueNumOfInducedSet.colorable_cliqueNum_of_isPerfect KΩ hperfΩ)
  have hocc : ∀ t : V, t ∈ T → ((0 : Fin (n + 1)) , t).2 ∈ AS ((0 : Fin (n + 1)), t).1 := by
    intro t ht
    show ((0 : Fin (n + 1)) : ℕ) < mult t
    rw [hmultT t ht]
    simp
  set occ : ↥T → Ω := fun t => ⟨((0 : Fin (n + 1)), (t : V)), hocc (t : V) t.2⟩ with hoccdef
  have hoccπ : ∀ t : ↥T, π (occ t) = (t : V) := fun _ => rfl
  obtain ⟨col, hcolapp⟩ :
      ∃ col : (L.induce T).Coloring (Fin n), ∀ t : ↥T, col t = colΩ (occ t) := by
    refine ⟨SimpleGraph.Coloring.mk (fun t => colΩ (occ t)) ?_, fun _ => rfl⟩
    intro s t hst
    refine colΩ.valid ?_
    refine ⟨?_, Or.inr ?_⟩
    · intro h
      exact hst.ne (Subtype.ext (by
        have := congrArg π h
        simpa [hoccπ] using this))
    · exact hst
  refine ⟨col, fun i => colΩ '' (fib (x i)), ?_, ?_, ?_, ?_⟩
  · -- palette sizes
    intro i hi
    have hinj : Set.InjOn colΩ (fib (x i)) := by
      intro q hq q' hq' h
      by_contra hne
      exact colΩ.valid (hfibclique (x i) hq hq' hne) h
    rw [Set.ncard_image_of_injOn hinj, hfibcard, hmultx i hi]
  · -- consecutive classes have disjoint palettes
    intro i hi
    rw [Set.disjoint_left]
    rintro y ⟨q, hq, rfl⟩ ⟨q', hq', hy⟩
    have hxadj : L.Adj (x i) (x (i + 1)) :=
      (hchain i (by omega) (i + 1) hi).mpr (Or.inl rfl)
    have e1 : π q = x i := hq
    have e2 : π q' = x (i + 1) := hq'
    have hne : q ≠ q' := by
      intro h
      rw [h, e2] at e1
      exact hxadj.ne e1.symm
    have hadj : KΩ.Adj q q' := ⟨hne, Or.inr (by rw [e1, e2]; exact hxadj)⟩
    exact colΩ.valid hadj hy.symm
  · -- the `A` palette avoids the first class
    rw [Set.disjoint_left]
    rintro y ⟨t, ht, rfl⟩ ⟨q, hq, hy⟩
    have htT : (t : V) ∈ T := t.2
    have hxadj : L.Adj (x 0) (t : V) :=
      (hcross 0 (by omega) (t : V) htT).mpr (Or.inl ⟨rfl, ht⟩)
    have e1 : π q = x 0 := hq
    have hne : q ≠ occ t := by
      intro h
      have h2 : π q = (t : V) := by rw [h]
      rw [e1] at h2
      exact hxadj.ne h2
    have hadj : KΩ.Adj q (occ t) := ⟨hne, Or.inr (by rw [e1, hoccπ t]; exact hxadj)⟩
    have hyy : colΩ q = colΩ (occ t) := by rw [← hcolapp t]; exact hy
    exact colΩ.valid hadj hyy
  · -- the `B` palette avoids every class complete to `BB`
    intro i hiSB
    rw [Set.disjoint_left]
    rintro y ⟨t, ht, rfl⟩ ⟨q, hq, hy⟩
    have htT : (t : V) ∈ T := t.2
    have hxadj : L.Adj (x i) (t : V) :=
      (hcross i (hSBlt i hiSB) (t : V) htT).mpr (Or.inr ⟨hiSB, ht⟩)
    have e1 : π q = x i := hq
    have hne : q ≠ occ t := by
      intro h
      have h2 : π q = (t : V) := by rw [h]
      rw [e1] at h2
      exact hxadj.ne h2
    have hadj : KΩ.Adj q (occ t) := ⟨hne, Or.inr (by rw [e1, hoccπ t]; exact hxadj)⟩
    have hyy : colΩ q = colΩ (occ t) := by rw [← hcolapp t]; exact hy
    exact colΩ.valid hadj hyy

end OddChainEngine

namespace Workspace.ProofLemmas

open Workspace.Types.Core

/-- Perfection is inherited by an induced subgraph on a *subset* of the ambient
vertex set. -/
theorem perfect_induce_subset {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y S : Set W) (hSY : S ⊆ Y)
    (h : SPGT.IsPerfect (K.induce Y)) : SPGT.IsPerfect (K.induce S) := by
  classical
  have h2 := Workspace.ProofLemmas.PerfectInducedSubgraph (K.induce Y)
    {y : ↥Y | (y : W) ∈ S} h
  let e : (K.induce Y).induce {y : ↥Y | (y : W) ∈ S} ≃g
      K.induce (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) :=
    { Equiv.Set.image (Subtype.val : ↥Y → W) {y : ↥Y | (y : W) ∈ S} Subtype.val_injective with
      map_rel_iff' := by intro a b; rfl }
  have himg : (Subtype.val '' {y : ↥Y | (y : W) ∈ S}) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hSY hx⟩, hx, rfl⟩
  have hfin := Workspace.ProofLemmas.IsoTransport.isPerfect_of_iso e h2
  rwa [himg] at hfin

/-- Clique numbers are unchanged by passing to the subtype presentation. -/
theorem cliqueNum_induce_sub {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (Y S : Set W) (hSY : S ⊆ Y) :
    ((K.induce Y).induce {v : ↥Y | (v : W) ∈ S}).cliqueNum = (K.induce S).cliqueNum := by
  classical
  let e : (K.induce Y).induce {v : ↥Y | (v : W) ∈ S} ≃g
      K.induce (Subtype.val '' {v : ↥Y | (v : W) ∈ S}) :=
    { Equiv.Set.image (Subtype.val : ↥Y → W) {v : ↥Y | (v : W) ∈ S} Subtype.val_injective with
      map_rel_iff' := by intro a b; rfl }
  have himg : (Subtype.val '' {v : ↥Y | (v : W) ∈ S}) = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hSY hx⟩, hx, rfl⟩
  rw [Workspace.ProofLemmas.IsoTransport.cliqueNum_iso e, himg]

/-- Any proper colouring of `K[T]` uses at least `ω(K[C ∩ T])` colours on `C`. -/
theorem palette_ge {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W) (T C : Set W) (n : ℕ)
    (col : (K.induce T).Coloring (Fin n)) :
    (K.induce (C ∩ T)).cliqueNum ≤ (col '' {v : T | (v : W) ∈ C}).ncard := by
  classical
  obtain ⟨Q, hQsub, hQclique, hQcard⟩ :=
    Workspace.ProofLemmas.CliqueNumOfInducedSet.exists_clique_card_eq_cliqueNum K (C ∩ T)
  set Q' : Finset ↥T :=
    Q.attach.map ⟨fun a => ⟨a.1, (hQsub (Finset.mem_coe.mpr a.2)).2⟩,
      by intro a b hab; exact Subtype.ext (by simpa using hab)⟩ with hQ'
  have hcard' : Q'.card = Q.card := by rw [hQ', Finset.card_map, Finset.card_attach]
  have hmem : ∀ a : ↥T, a ∈ (↑Q' : Set ↥T) → (a : W) ∈ (↑Q : Set W) := by
    intro a ha
    simp only [hQ', Finset.coe_map, Function.Embedding.coeFn_mk, Set.mem_image,
      Finset.mem_coe, Finset.mem_attach] at ha
    obtain ⟨x, -, rfl⟩ := ha
    exact Finset.mem_coe.mpr x.2
  have hsub : (↑Q' : Set ↥T) ⊆ {v : T | (v : W) ∈ C} := fun a ha => (hQsub (hmem a ha)).1
  have hinj : Set.InjOn col (↑Q' : Set ↥T) := by
    intro a ha b hb hcol
    by_contra hne
    have hne' : (a : W) ≠ (b : W) := fun h => hne (Subtype.ext h)
    exact col.valid (hQclique (hmem a ha) (hmem b hb) hne') hcol
  calc (K.induce (C ∩ T)).cliqueNum = Q.card := hQcard.symm
    _ = Q'.card := hcard'.symm
    _ = (col '' (↑Q' : Set ↥T)).ncard := by
        rw [Set.ncard_image_of_injOn hinj, Set.ncard_coe_finset]
    _ ≤ (col '' {v : T | (v : W) ∈ C}).ncard :=
        Set.ncard_le_ncard (Set.image_mono hsub) (Set.toFinite _)



/-- Clique numbers transfer along a map that is a bijection between the two
vertex sets and preserves adjacency on them. -/
theorem cliqueNum_map {V₁ V₂ : Type*} [Fintype V₁] [DecidableEq V₁] [Fintype V₂] [DecidableEq V₂]
    (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂)
    (S₁ : Set V₁) (S₂ : Set V₂) (φ : V₁ → V₂)
    (hmaps : ∀ p, p ∈ S₁ → φ p ∈ S₂)
    (hinj : ∀ p ∈ S₁, ∀ q ∈ S₁, φ p = φ q → p = q)
    (hsurj : ∀ z ∈ S₂, ∃ p ∈ S₁, φ p = z)
    (hadj : ∀ p ∈ S₁, ∀ q ∈ S₁, (G₂.Adj (φ p) (φ q) ↔ G₁.Adj p q)) :
    (G₁.induce S₁).cliqueNum = (G₂.induce S₂).cliqueNum := by
  classical
  have hbij : Set.BijOn φ S₁ S₂ :=
    ⟨hmaps, hinj, fun z hz => by obtain ⟨p, hp, hpz⟩ := hsurj z hz; exact ⟨p, hp, hpz⟩⟩
  let e : (G₁.induce S₁) ≃g (G₂.induce S₂) :=
    { hbij.equiv φ with
      map_rel_iff' := by
        intro α β
        exact hadj α.1 α.2 β.1 β.2 }
  exact Workspace.ProofLemmas.IsoTransport.cliqueNum_iso e

/-- **§8.1, odd marker.**  When the marker path has odd length, the side `K[T]` has
a proper `n`-coloring whose two boundary palettes have cardinalities
`a = ω(K[A ∩ T])` and `b = ω(K[B ∩ T])` and meet in exactly `a + b - n` colors
(truncated subtraction, i.e. `max 0 (a + b - n)`). -/
theorem PerfectBlockOddMarkerPalette
    {W : Type*} [Fintype W] [DecidableEq W]
    (K : SimpleGraph W)
    (X A B : Set W)
    (hA : A ⊆ X) (hB : B ⊆ X) (hAB : Disjoint A B)
    (P : List W) (pA pB : W)
    (hP : SPGT.IsPathFrom K P pA pB)
    (hPpos : 1 ≤ SPGT.pathLength P)
    (hPX : Disjoint X {v : W | v ∈ P})
    (hpA : ∀ x ∈ X, K.Adj pA x ↔ x ∈ A)
    (hpB : ∀ x ∈ X, K.Adj pB x ↔ x ∈ B)
    (hinternal : ∀ v ∈ SPGT.interior P, ∀ x ∈ X, ¬ K.Adj v x)
    (hperfect : SPGT.IsPerfect (K.induce (X ∪ {v : W | v ∈ P})))
    (T : Set W) (hT : T ⊆ X) (n : ℕ)
    (hn : (K.induce (T ∪ {v : W | v ∈ P})).cliqueNum ≤ n)
    (hodd : Odd (SPGT.pathLength P)) :
    ∃ col : (K.induce T).Coloring (Fin n),
      (col '' {v : T | (v : W) ∈ A}).ncard = (K.induce (A ∩ T)).cliqueNum ∧
      (col '' {v : T | (v : W) ∈ B}).ncard = (K.induce (B ∩ T)).cliqueNum ∧
      ((col '' {v : T | (v : W) ∈ A}) ∩ (col '' {v : T | (v : W) ∈ B})).ncard
        = (K.induce (A ∩ T)).cliqueNum + (K.induce (B ∩ T)).cliqueNum - n := by
  classical
  set Y : Set W := T ∪ {v : W | v ∈ P} with hY
  haveI : Fintype ↥Y := Fintype.ofFinite _
  haveI : DecidableEq ↥Y := Classical.decEq _
  have hYmem : ∀ w : W, (w ∈ T ∨ w ∈ P) → w ∈ Y := by
    intro w h; rw [hY]; exact h
  have hYcases : ∀ v : ↥Y, (v : W) ∈ T ∨ (v : W) ∈ P := by
    intro v
    have h : (v : W) ∈ T ∪ {w : W | w ∈ P} := by rw [← hY]; exact v.2
    exact h
  have hYsub : Y ⊆ X ∪ {v : W | v ∈ P} := by
    intro w hw
    rcases hYcases ⟨w, hw⟩ with h | h
    · exact Or.inl (hT h)
    · exact Or.inr h
  have hLperf : SPGT.IsPerfect (K.induce Y) :=
    perfect_induce_subset K (X ∪ {v : W | v ∈ P}) Y hYsub hperfect
  set M : ℕ := P.length with hMdef
  have hplen : 0 < M := Workspace.ProofLemmas.PathBasics.path_length_pos hP.1
  have hlen : SPGT.pathLength P = M - 1 := rfl
  have hMpar : M % 2 = 0 := by obtain ⟨r, hr⟩ := hodd; omega
  have hM2 : 2 ≤ M := by obtain ⟨r, hr⟩ := hodd; omega
  have hM1lt : M - 1 < M := by omega
  have hM2lt : M - 2 < M := by omega
  have hmemP : ∀ (i : ℕ) (hi : i < M), (P[i]'hi) ∈ Y :=
    fun i hi => hYmem _ (Or.inr (List.getElem_mem hi))
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ↥Y, ∀ (i : ℕ) (hi : i < M), ((x i : ↥Y) : W) = P[i]'hi := by
    refine ⟨fun i => if h : i < M then ⟨P[i]'h, hmemP i h⟩ else ⟨P[0]'hplen, hmemP 0 hplen⟩, ?_⟩
    intro i hi
    dsimp only
    rw [dif_pos hi]
  set T' : Set ↥Y := {v : ↥Y | (v : W) ∈ T} with hT'def
  set AA : Set ↥Y := {v : ↥Y | (v : W) ∈ A ∩ T} with hAAdef
  set BB : Set ↥Y := {v : ↥Y | (v : W) ∈ B ∩ T} with hBBdef
  set a : ℕ := (K.induce (A ∩ T)).cliqueNum with hadef
  set b : ℕ := (K.induce (B ∩ T)).cliqueNum with hbdef
  have hAAT : AA ⊆ T' := fun v hv => (hv : ((v : ↥Y) : W) ∈ A ∩ T).2
  have hBBT : BB ⊆ T' := fun v hv => (hv : ((v : ↥Y) : W) ∈ B ∩ T).2
  have hABd : Disjoint AA BB := by
    rw [Set.disjoint_left]
    intro v hv hv2
    exact (Set.disjoint_left.mp hAB (hv : ((v : ↥Y) : W) ∈ A ∩ T).1)
      (hv2 : ((v : ↥Y) : W) ∈ B ∩ T).1
  have hTsubY : T ⊆ Y := by rw [hY]; exact Set.subset_union_left
  have hAsubY : A ∩ T ⊆ Y := Set.inter_subset_right.trans hTsubY
  have hBsubY : B ∩ T ⊆ Y := Set.inter_subset_right.trans hTsubY
  have hcnT : ((K.induce Y).induce T').cliqueNum = (K.induce T).cliqueNum :=
    cliqueNum_induce_sub K Y T hTsubY
  have hcnA : ((K.induce Y).induce AA).cliqueNum = a := cliqueNum_induce_sub K Y (A ∩ T) hAsubY
  have hcnB : ((K.induce Y).induce BB).cliqueNum = b := cliqueNum_induce_sub K Y (B ∩ T) hBsubY
  have hTn' : (K.induce T).cliqueNum ≤ n :=
    le_trans (Workspace.ProofLemmas.CliqueNumOfInducedSet.cliqueNum_induce_mono K hTsubY) hn
  have han : a ≤ n :=
    le_trans (Workspace.ProofLemmas.CliqueNumOfInducedSet.cliqueNum_induce_mono K hAsubY) hn
  have hbn : b ≤ n :=
    le_trans (Workspace.ProofLemmas.CliqueNumOfInducedSet.cliqueNum_induce_mono K hBsubY) hn
  have hxT : ∀ i, i < M → x i ∉ T' := by
    intro i hi hmem
    have h1 : ((x i : ↥Y) : W) ∈ T := hmem
    have h2 : ((x i : ↥Y) : W) ∈ P := by rw [hx i hi]; exact List.getElem_mem hi
    exact (Set.disjoint_left.mp hPX (hT h1)) h2
  have hxinj : ∀ i, i < M → ∀ j, j < M → x i = x j → i = j := by
    intro i hi j hj h
    by_contra hij
    have h1 : (P[i]'hi) = (P[j]'hj) := by rw [← hx i hi, ← hx j hj, h]
    exact (Workspace.ProofLemmas.PathBasics.path_ne_of_ne_index hP.1 hi hj hij) h1
  have hchain : ∀ i, i < M → ∀ j, j < M →
      ((K.induce Y).Adj (x i) (x j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
    intro i hi j hj
    show K.Adj ((x i : ↥Y) : W) ((x j : ↥Y) : W) ↔ _
    rw [hx i hi, hx j hj]
    exact hP.1.2.2 i j hi hj
  have hcover : ∀ v : ↥Y, v ∈ T' ∨ ∃ i, i < M ∧ v = x i := by
    intro v
    rcases hYcases v with h | h
    · exact Or.inl h
    · obtain ⟨i, hi, hiv⟩ := List.mem_iff_getElem.mp h
      exact Or.inr ⟨i, hi, Subtype.ext (by rw [hx i hi]; exact hiv.symm)⟩
  have h0P : (P[0]'hplen) = pA :=
    Workspace.ProofLemmas.PathBasics.getElem_zero_of_head? hP.2.1 hplen
  have hlastP : (P[M - 1]'(by omega)) = pB :=
    Workspace.ProofLemmas.PathBasics.getElem_last_of_getLast? hP.2.2 hplen
  have hcross0 : ∀ i, i < M → ∀ t, t ∈ T' →
      ((K.induce Y).Adj (x i) t ↔ ((i = 0 ∧ t ∈ AA) ∨ (i = M - 1 ∧ t ∈ BB))) := by
    intro i hi t ht
    have htT : ((t : ↥Y) : W) ∈ T := ht
    have htX : ((t : ↥Y) : W) ∈ X := hT htT
    have hshow : (K.induce Y).Adj (x i) t ↔ K.Adj (P[i]'hi) ((t : ↥Y) : W) := by
      show K.Adj ((x i : ↥Y) : W) ((t : ↥Y) : W) ↔ _
      rw [hx i hi]
    rw [hshow]
    rcases Nat.eq_zero_or_pos i with rfl | hipos
    · rw [show (P[0]'hi) = pA from h0P]
      constructor
      · intro hadj
        exact Or.inl ⟨rfl, ⟨(hpA _ htX).mp hadj, htT⟩⟩
      · intro hor
        rcases hor with ⟨-, hmem⟩ | ⟨he, -⟩
        · exact (hpA _ htX).mpr (hmem : ((t : ↥Y) : W) ∈ A ∩ T).1
        · omega
    · by_cases hlc : i = M - 1
      · subst hlc
        rw [show (P[M - 1]'hi) = pB from hlastP]
        constructor
        · intro hadj
          exact Or.inr ⟨rfl, ⟨(hpB _ htX).mp hadj, htT⟩⟩
        · intro hor
          rcases hor with ⟨he, -⟩ | ⟨-, hmem⟩
          · omega
          · exact (hpB _ htX).mpr (hmem : ((t : ↥Y) : W) ∈ B ∩ T).1
      · have hint : (P[i]'hi) ∈ SPGT.interior P :=
          Workspace.ProofLemmas.PathBasics.getElem_mem_interior hP.1 hi (by omega) (by omega)
        constructor
        · intro hadj
          exact absurd hadj (hinternal _ hint _ htX)
        · intro hor
          rcases hor with ⟨he, -⟩ | ⟨he, -⟩
          · omega
          · exact absurd he hlc
  -- generic helpers about `Fin n` palettes
  have hsum2 : ∀ S U : Set (Fin n), Disjoint S U → S.ncard + U.ncard ≤ n := by
    intro S U hd
    have h1 := Set.ncard_union_eq hd (Set.toFinite S) (Set.toFinite U)
    have h2 : (S ∪ U).ncard ≤ (Set.univ : Set (Fin n)).ncard :=
      Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h2
    omega
  have hncompl : ∀ U : Set (Fin n), U.ncard + Uᶜ.ncard = n := by
    intro U
    have h1 := Set.ncard_union_eq (disjoint_compl_right (a := U)) (Set.toFinite U)
      (Set.toFinite Uᶜ)
    rw [Set.union_compl_self, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    omega
  have heqcompl : ∀ S U : Set (Fin n), Disjoint S U → S.ncard + U.ncard = n → S = Uᶜ := by
    intro S U hd hsum
    have hsub : S ⊆ Uᶜ := fun z hz => Set.disjoint_left.mp hd hz
    have h1 := hncompl U
    exact Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)
  rcases lt_or_ge (a + b) n with hlt | hge
  · -- ## Case 8.1.a : `a + b < n` — replicate `x (M-1)` and delete the edge to `x (M-2)`
    have huv : (K.induce Y).Adj (x (M - 2)) (x (M - 1)) :=
      (hchain (M - 2) hM2lt (M - 1) hM1lt).mpr (Or.inl (by omega))
    have hnocommon : ∀ w : ↥Y, (K.induce Y).Adj w (x (M - 2)) →
        ¬ (K.induce Y).Adj w (x (M - 1)) := by
      intro w hwu hwv
      rcases hcover w with hwT | ⟨j, hj, rfl⟩
      · have h1 := (hcross0 (M - 2) hM2lt w hwT).mp hwu.symm
        have h2 := (hcross0 (M - 1) hM1lt w hwT).mp hwv.symm
        rcases h1 with ⟨e1, ha⟩ | ⟨e1, -⟩
        · rcases h2 with ⟨e2, -⟩ | ⟨-, hb⟩
          · omega
          · exact (Set.disjoint_left.mp hABd ha) hb
        · omega
      · have h1 := (hchain j hj (M - 2) hM2lt).mp hwu
        have h2 := (hchain j hj (M - 1) hM1lt).mp hwv
        omega
    set L2 : SimpleGraph (↥Y ⊕ Unit) :=
      (Workspace.Types.Replication.SPGT.replicateVertex (K.induce Y) (x (M - 1))).deleteEdges
        {s(Sum.inl (x (M - 2)), Sum.inr ())} with hL2def
    have hLperf2 : SPGT.IsPerfect L2 :=
      EdgeDeletedReplicationPerfect (K.induce Y) (x (M - 2)) (x (M - 1)) huv hnocommon hLperf
    have hinl : ∀ p q : ↥Y, L2.Adj (Sum.inl p) (Sum.inl q) ↔ (K.induce Y).Adj p q := by
      intro p q
      rw [hL2def, SimpleGraph.deleteEdges_adj]
      constructor
      · rintro ⟨h1, -⟩; exact h1
      · intro h
        refine ⟨h, ?_⟩
        simp [Sym2.eq_iff]
    have hinr : ∀ p : ↥Y, L2.Adj (Sum.inl p) (Sum.inr ()) ↔
        ((p = x (M - 1) ∨ (K.induce Y).Adj p (x (M - 1))) ∧ p ≠ x (M - 2)) := by
      intro p
      rw [hL2def, SimpleGraph.deleteEdges_adj]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro hc
        exact h2 (by rw [hc]; rfl)
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        intro hc
        apply h2
        have hc' : s(Sum.inl p, (Sum.inr () : ↥Y ⊕ Unit)) = s(Sum.inl (x (M - 2)), Sum.inr ()) :=
          hc
        rw [Sym2.eq_iff] at hc'
        rcases hc' with ⟨e1, -⟩ | ⟨e1, -⟩
        · exact Sum.inl_injective e1
        · exact absurd e1 (by simp)
    obtain ⟨y, hy1, hy2⟩ : ∃ y : ℕ → (↥Y ⊕ Unit),
        (∀ i, i < M → y i = Sum.inl (x i)) ∧ y M = Sum.inr () := by
      refine ⟨fun i => if i < M then Sum.inl (x i) else Sum.inr (), fun i hi => ?_, ?_⟩
      · dsimp only; rw [if_pos hi]
      · dsimp only; rw [if_neg (by omega)]
    obtain ⟨T2, hT2inl, hT2inr⟩ : ∃ S : Set (↥Y ⊕ Unit),
        (∀ w : ↥Y, (Sum.inl w ∈ S) ↔ w ∈ T') ∧ (Sum.inr () : ↥Y ⊕ Unit) ∉ S :=
      ⟨{z | Sum.elim (fun w : ↥Y => w ∈ T') (fun _ => False) z}, fun _ => Iff.rfl, fun h => h⟩
    obtain ⟨AA2, hAA2inl, hAA2inr⟩ : ∃ S : Set (↥Y ⊕ Unit),
        (∀ w : ↥Y, (Sum.inl w ∈ S) ↔ w ∈ AA) ∧ (Sum.inr () : ↥Y ⊕ Unit) ∉ S :=
      ⟨{z | Sum.elim (fun w : ↥Y => w ∈ AA) (fun _ => False) z}, fun _ => Iff.rfl, fun h => h⟩
    obtain ⟨BB2, hBB2inl, hBB2inr⟩ : ∃ S : Set (↥Y ⊕ Unit),
        (∀ w : ↥Y, (Sum.inl w ∈ S) ↔ w ∈ BB) ∧ (Sum.inr () : ↥Y ⊕ Unit) ∉ S :=
      ⟨{z | Sum.elim (fun w : ↥Y => w ∈ BB) (fun _ => False) z}, fun _ => Iff.rfl, fun h => h⟩
    have hmemT2 : ∀ z : ↥Y ⊕ Unit, z ∈ T2 → ∃ w : ↥Y, w ∈ T' ∧ Sum.inl w = z := by
      rintro (w | ⟨⟩) h
      · exact ⟨w, (hT2inl w).mp h, rfl⟩
      · exact absurd h hT2inr
    have hAA2T2 : AA2 ⊆ T2 := by
      rintro (w | ⟨⟩) h
      · exact (hT2inl w).mpr (hAAT ((hAA2inl w).mp h))
      · exact absurd h hAA2inr
    have hBB2T2 : BB2 ⊆ T2 := by
      rintro (w | ⟨⟩) h
      · exact (hT2inl w).mpr (hBBT ((hBB2inl w).mp h))
      · exact absurd h hBB2inr
    have hABd2 : Disjoint AA2 BB2 := by
      rw [Set.disjoint_left]
      rintro (w | ⟨⟩) h1 h2
      · exact (Set.disjoint_left.mp hABd ((hAA2inl w).mp h1)) ((hBB2inl w).mp h2)
      · exact hAA2inr h1
    -- clique numbers transfer along `Sum.inl`
    have hcn2 : ∀ (S₁ : Set ↥Y) (S₂ : Set (↥Y ⊕ Unit)),
        (∀ w : ↥Y, (Sum.inl w ∈ S₂) ↔ w ∈ S₁) → (Sum.inr () : ↥Y ⊕ Unit) ∉ S₂ →
        ((K.induce Y).induce S₁).cliqueNum = (L2.induce S₂).cliqueNum := by
      intro S₁ S₂ hin hout
      refine cliqueNum_map (K.induce Y) L2 S₁ S₂ Sum.inl
        (fun p hp => (hin p).mpr hp)
        (fun p _ q _ h => Sum.inl_injective h) ?_ (fun p _ q _ => hinl p q)
      rintro (w | ⟨⟩) h
      · exact ⟨w, (hin w).mp h, rfl⟩
      · exact absurd h hout
    have hcnT2 : (L2.induce T2).cliqueNum = (K.induce T).cliqueNum := by
      rw [← hcn2 T' T2 hT2inl hT2inr, hcnT]
    have hcnA2 : (L2.induce AA2).cliqueNum = a := by
      rw [← hcn2 AA AA2 hAA2inl hAA2inr, hcnA]
    have hcnB2 : (L2.induce BB2).cliqueNum = b := by
      rw [← hcn2 BB BB2 hBB2inl hBB2inr, hcnB]
    -- chain hypotheses on the enlarged graph
    have hxT2 : ∀ i, i < M + 1 → y i ∉ T2 := by
      intro i hi hmem
      by_cases hiM : i < M
      · rw [hy1 i hiM] at hmem
        exact hxT i hiM ((hT2inl (x i)).mp hmem)
      · have he : i = M := by omega
        subst he
        rw [hy2] at hmem
        exact hT2inr hmem
    have hxinj2 : ∀ i, i < M + 1 → ∀ j, j < M + 1 → y i = y j → i = j := by
      intro i hi j hj h
      by_cases hiM : i < M <;> by_cases hjM : j < M
      · rw [hy1 i hiM, hy1 j hjM] at h
        exact hxinj i hiM j hjM (Sum.inl_injective h)
      · have hje : j = M := by omega
        subst hje
        rw [hy1 i hiM, hy2] at h
        exact absurd h (by simp)
      · have hie : i = M := by omega
        subst hie
        rw [hy2, hy1 j hjM] at h
        exact absurd h (by simp)
      · omega
    have hchain2 : ∀ i, i < M + 1 → ∀ j, j < M + 1 →
        (L2.Adj (y i) (y j) ↔ (i + 1 = j ∨ j + 1 = i)) := by
      intro i hi j hj
      by_cases hiM : i < M
      · by_cases hjM : j < M
        · rw [hy1 i hiM, hy1 j hjM, hinl (x i) (x j)]
          exact hchain i hiM j hjM
        · have hje : j = M := by omega
          subst hje
          rw [hy1 i hiM, hy2, hinr (x i)]
          constructor
          · rintro ⟨h1, h2⟩
            left
            rcases h1 with he | hadj
            · have := hxinj i hiM (M - 1) hM1lt he
              omega
            · have h3 := (hchain i hiM (M - 1) hM1lt).mp hadj
              have hne : i ≠ M - 2 := fun hc => h2 (by rw [hc])
              omega
          · intro h
            have hie : i = M - 1 := by omega
            refine ⟨Or.inl (by rw [hie]), ?_⟩
            intro hc
            have := hxinj i hiM (M - 2) hM2lt hc
            omega
      · have hie : i = M := by omega
        subst hie
        by_cases hjM : j < M
        · rw [hy2, hy1 j hjM, SimpleGraph.adj_comm, hinr (x j)]
          constructor
          · rintro ⟨h1, h2⟩
            right
            rcases h1 with he | hadj
            · have := hxinj j hjM (M - 1) hM1lt he
              omega
            · have h3 := (hchain j hjM (M - 1) hM1lt).mp hadj
              have hne : j ≠ M - 2 := fun hc => h2 (by rw [hc])
              omega
          · intro h
            have hje : j = M - 1 := by omega
            refine ⟨Or.inl (by rw [hje]), ?_⟩
            intro hc
            have := hxinj j hjM (M - 2) hM2lt hc
            omega
        · have hje : j = M := by omega
          subst hje
          rw [hy2]
          constructor
          · intro h; exact ((h.ne) rfl).elim
          · intro h; exact absurd h (by omega)
    have hcover2 : ∀ z : ↥Y ⊕ Unit, z ∈ T2 ∨ ∃ i, i < M + 1 ∧ z = y i := by
      rintro (w | ⟨⟩)
      · rcases hcover w with h | ⟨i, hi, rfl⟩
        · exact Or.inl ((hT2inl w).mpr h)
        · exact Or.inr ⟨i, by omega, by rw [hy1 i hi]⟩
      · exact Or.inr ⟨M, by omega, by rw [hy2]⟩
    have hcross2 : ∀ i, i < M + 1 → ∀ t, t ∈ T2 →
        (L2.Adj (y i) t ↔ ((i = 0 ∧ t ∈ AA2) ∨ (i ∈ ({M - 1, M} : Set ℕ) ∧ t ∈ BB2))) := by
      intro i hi t ht
      obtain ⟨w, hw, rfl⟩ := hmemT2 t ht
      by_cases hiM : i < M
      · rw [hy1 i hiM, hinl (x i) w, hcross0 i hiM w hw]
        constructor
        · rintro (⟨e, ha⟩ | ⟨e, hb⟩)
          · exact Or.inl ⟨e, (hAA2inl w).mpr ha⟩
          · exact Or.inr ⟨Or.inl e, (hBB2inl w).mpr hb⟩
        · rintro (⟨e, ha⟩ | ⟨e, hb⟩)
          · exact Or.inl ⟨e, (hAA2inl w).mp ha⟩
          · refine Or.inr ⟨?_, (hBB2inl w).mp hb⟩
            have e' : i = M - 1 ∨ i = M := e
            rcases e' with e' | e'
            · exact e'
            · omega
      · have hie : i = M := by omega
        subst hie
        have hwv : w ≠ x (M - 1) := by
          intro hc
          apply hxT (M - 1) hM1lt
          rw [← hc]; exact hw
        have hwu : w ≠ x (M - 2) := by
          intro hc
          apply hxT (M - 2) hM2lt
          rw [← hc]; exact hw
        rw [hy2, SimpleGraph.adj_comm, hinr w]
        constructor
        · rintro ⟨h1 | h1, -⟩
          · exact absurd h1 hwv
          · refine Or.inr ⟨Or.inr rfl, (hBB2inl w).mpr ?_⟩
            rcases (hcross0 (M - 1) hM1lt w hw).mp h1.symm with ⟨e, -⟩ | ⟨-, hb⟩
            · omega
            · exact hb
        · rintro (⟨e, -⟩ | ⟨-, hb⟩)
          · omega
          · exact ⟨Or.inr ((hcross0 (M - 1) hM1lt w hw).mpr
              (Or.inr ⟨rfl, (hBB2inl w).mp hb⟩)).symm, hwu⟩
    -- the multiplicity schedule of 8.1.a
    obtain ⟨g, hgeq⟩ : ∃ g : ℕ → ℕ, ∀ i,
        g i = (if i = M then n - a - b else if i % 2 = 0 then n - a else a) := ⟨_, fun _ => rfl⟩
    have hg0 : g 0 = n - a := by rw [hgeq, if_neg (by omega), if_pos (by norm_num)]
    have hgM : g M = n - a - b := by rw [hgeq, if_pos rfl]
    have hgM1 : g (M - 1) = a := by rw [hgeq, if_neg (by omega), if_neg (by omega)]
    have hgeven : ∀ i, i ≠ M → i % 2 = 0 → g i = n - a := by
      intro i h1 h2; rw [hgeq, if_neg h1, if_pos h2]
    have hgodd : ∀ i, i ≠ M → i % 2 ≠ 0 → g i = a := by
      intro i h1 h2; rw [hgeq, if_neg h1, if_neg h2]
    have hgle : ∀ i, i < M + 1 → g i ≤ n := by
      intro i _
      rw [hgeq]
      by_cases h1 : i = M
      · rw [if_pos h1]; omega
      · rw [if_neg h1]
        by_cases h2 : i % 2 = 0
        · rw [if_pos h2]; omega
        · rw [if_neg h2]; omega
    have hgpairEq : ∀ i, i + 1 ≤ M - 1 → g i + g (i + 1) = n := by
      intro i hi
      have h1 : i ≠ M := by omega
      have h2 : i + 1 ≠ M := by omega
      by_cases he : i % 2 = 0
      · rw [hgeven i h1 he, hgodd (i + 1) h2 (by omega)]; omega
      · rw [hgodd i h1 he, hgeven (i + 1) h2 (by omega)]; omega
    have hgpair : ∀ i, i + 1 < M + 1 → g i + g (i + 1) ≤ n := by
      intro i hi
      by_cases hlc : i + 1 = M
      · have hie : i = M - 1 := by omega
        have hsucc : M - 1 + 1 = M := by omega
        rw [hie, hgM1, hsucc, hgM]
        omega
      · have := hgpairEq i (by omega); omega
    obtain ⟨col, Pal, hsize, hdisjP, hdisjA, hdisjB⟩ :=
      OddChainEngine.chain_engine L2 hLperf2 T2 AA2 BB2 hAA2T2 hBB2T2 hABd2
        (M + 1) (by omega) y ({M - 1, M} : Set ℕ)
        (by intro hc; have hc' : (0 : ℕ) = M - 1 ∨ (0 : ℕ) = M := hc; omega)
        (by intro i hi; have hi' : i = M - 1 ∨ i = M := hi; omega)
        hxT2 hxinj2 hchain2 hcross2 hcover2 n g
        (by rw [hcnT2]; exact hTn') hgle hgpair
        (by rw [hg0, hcnA2]; omega)
        (by
          rintro i (h | h) <;> subst h
          · rw [hgM1, hcnB2]; omega
          · rw [hgM, hcnB2]; omega)
        (by
          rintro i (h | h) hi2 <;> subst h
          · rw [hgM1, show M - 1 + 1 = M from by omega, hgM, hcnB2]; omega
          · have h2 : M + 1 = M - 1 ∨ M + 1 = M := hi2
            omega)
    -- transport the colouring back to `K.induce T`
    obtain ⟨ι, hι⟩ : ∃ ι : ↥T → ↥T2, ∀ t : ↥T,
        ((ι t : ↥T2) : ↥Y ⊕ Unit) = Sum.inl ⟨(t : W), hYmem _ (Or.inl t.2)⟩ :=
      ⟨fun t => ⟨Sum.inl ⟨(t : W), hYmem _ (Or.inl t.2)⟩, (hT2inl _).mpr t.2⟩, fun _ => rfl⟩
    obtain ⟨colT, hcolT⟩ :
        ∃ colT : (K.induce T).Coloring (Fin n), ∀ t : ↥T, colT t = col (ι t) := by
      refine ⟨SimpleGraph.Coloring.mk (fun t => col (ι t)) ?_, fun _ => rfl⟩
      intro s t hst
      refine col.valid ?_
      show L2.Adj ((ι s : ↥T2) : ↥Y ⊕ Unit) ((ι t : ↥T2) : ↥Y ⊕ Unit)
      rw [hι s, hι t, hinl]
      exact hst
    have himg : ∀ (C : Set W) (CC : Set (↥Y ⊕ Unit)),
        (∀ w : ↥Y, (Sum.inl w ∈ CC) ↔ ((w : W) ∈ C ∩ T)) →
        (Sum.inr () : ↥Y ⊕ Unit) ∉ CC →
        colT '' {v : T | (v : W) ∈ C} = col '' {z : T2 | (z : ↥Y ⊕ Unit) ∈ CC} := by
      intro C CC hin hout
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨ι t, ?_, (hcolT t).symm⟩
        show ((ι t : ↥T2) : ↥Y ⊕ Unit) ∈ CC
        rw [hι t]
        exact (hin _).mpr ⟨ht, t.2⟩
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨w, hw, hwq⟩ := hmemT2 (q : ↥Y ⊕ Unit) q.2
        have hqCC : ((q : ↥T2) : ↥Y ⊕ Unit) ∈ CC := hq
        rw [← hwq] at hqCC
        have hwC := (hin w).mp hqCC
        refine ⟨⟨(w : W), hwC.2⟩, hwC.1, ?_⟩
        rw [hcolT]
        refine congrArg col (Subtype.ext ?_)
        rw [hι]
        rw [← hwq]
    have himgA : colT '' {v : T | (v : W) ∈ A} = col '' {z : T2 | (z : ↥Y ⊕ Unit) ∈ AA2} :=
      himg A AA2 (fun w => hAA2inl w) hAA2inr
    have himgB : colT '' {v : T | (v : W) ∈ B} = col '' {z : T2 | (z : ↥Y ⊕ Unit) ∈ BB2} :=
      himg B BB2 (fun w => hBB2inl w) hBB2inr
    -- palette arithmetic
    have hdA : Disjoint (colT '' {v : T | (v : W) ∈ A}) (Pal 0) := by rw [himgA]; exact hdisjA
    have hdB1 : Disjoint (colT '' {v : T | (v : W) ∈ B}) (Pal (M - 1)) := by
      rw [himgB]; exact hdisjB (M - 1) (Or.inl rfl)
    have hdB2 : Disjoint (colT '' {v : T | (v : W) ∈ B}) (Pal M) := by
      rw [himgB]; exact hdisjB M (Or.inr rfl)
    have hAge : a ≤ (colT '' {v : T | (v : W) ∈ A}).ncard := palette_ge K T A n colT
    have hBge : b ≤ (colT '' {v : T | (v : W) ∈ B}).ncard := palette_ge K T B n colT
    have hPal0 : (Pal 0).ncard = n - a := by rw [hsize 0 (by omega), hg0]
    have hPalM1 : (Pal (M - 1)).ncard = a := by rw [hsize (M - 1) (by omega), hgM1]
    have hPalM : (Pal M).ncard = n - a - b := by rw [hsize M (by omega), hgM]
    have hAcard : (colT '' {v : T | (v : W) ∈ A}).ncard = a := by
      have := hsum2 _ _ hdA; omega
    have hddM : Disjoint (Pal (M - 1)) (Pal M) := by
      have h := hdisjP (M - 1) (by omega)
      rwa [show M - 1 + 1 = M from by omega] at h
    have hBcard : (colT '' {v : T | (v : W) ∈ B}).ncard = b := by
      have hdu : Disjoint (colT '' {v : T | (v : W) ∈ B}) (Pal (M - 1) ∪ Pal M) :=
        Disjoint.union_right hdB1 hdB2
      have h1 := Set.ncard_union_eq hddM (Set.toFinite _) (Set.toFinite _)
      have h2 := hsum2 _ _ hdu
      omega
    have hAeq : colT '' {v : T | (v : W) ∈ A} = (Pal 0)ᶜ :=
      heqcompl _ _ hdA (by rw [hAcard, hPal0]; omega)
    have halt : ∀ i, i ≤ M - 1 →
        (i % 2 = 0 → Pal i = Pal 0) ∧ (i % 2 ≠ 0 → Pal i = (Pal 0)ᶜ) := by
      intro i
      induction i with
      | zero =>
          intro _
          exact ⟨fun _ => rfl, fun h => absurd (by norm_num : (0 : ℕ) % 2 = 0) h⟩
      | succ j ih =>
          intro hj
          obtain ⟨ihe, iho⟩ := ih (by omega)
          have hstep : Pal (j + 1) = (Pal j)ᶜ := by
            refine heqcompl _ _ (hdisjP j (by omega)).symm ?_
            rw [hsize (j + 1) (by omega), hsize j (by omega)]
            have hpe := hgpairEq j (by omega)
            omega
          refine ⟨?_, ?_⟩
          · intro he
            rw [hstep, iho (by omega), compl_compl]
          · intro ho
            rw [hstep, ihe (by omega)]
    have hPalM1eq : Pal (M - 1) = (Pal 0)ᶜ := (halt (M - 1) (by omega)).2 (by omega)
    refine ⟨colT, hAcard, hBcard, ?_⟩
    have hinter : (colT '' {v : T | (v : W) ∈ A}) ∩ (colT '' {v : T | (v : W) ∈ B}) = ∅ := by
      rw [hAeq, ← hPalM1eq]
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      exact (Set.disjoint_right.mp hdB1) hz.1 hz.2
    rw [hinter]
    simp only [Set.ncard_empty]
    omega
  · -- ## Case 8.1.b : `n ≤ a + b` — no edge deletion
    obtain ⟨f, hfeq⟩ : ∃ f : ℕ → ℕ, ∀ i,
        f i = (if i = M - 1 then n - b else if i % 2 = 0 then n - a else a) := ⟨_, fun _ => rfl⟩
    have hf0 : f 0 = n - a := by rw [hfeq, if_neg (by omega), if_pos (by norm_num)]
    have hflast : f (M - 1) = n - b := by rw [hfeq, if_pos rfl]
    have hfle : ∀ i, i < M → f i ≤ n := by
      intro i _
      rw [hfeq]
      by_cases h1 : i = M - 1
      · rw [if_pos h1]; omega
      · rw [if_neg h1]
        by_cases h2 : i % 2 = 0
        · rw [if_pos h2]; omega
        · rw [if_neg h2]; omega
    have hfeven : ∀ i, i ≠ M - 1 → i % 2 = 0 → f i = n - a := by
      intro i h1 h2; rw [hfeq, if_neg h1, if_pos h2]
    have hfodd : ∀ i, i ≠ M - 1 → i % 2 ≠ 0 → f i = a := by
      intro i h1 h2; rw [hfeq, if_neg h1, if_neg h2]
    have hfpairEq : ∀ i, i + 1 ≤ M - 2 → f i + f (i + 1) = n := by
      intro i hi
      have h1 : i ≠ M - 1 := by omega
      have h2 : i + 1 ≠ M - 1 := by omega
      by_cases he : i % 2 = 0
      · rw [hfeven i h1 he, hfodd (i + 1) h2 (by omega)]; omega
      · rw [hfodd i h1 he, hfeven (i + 1) h2 (by omega)]; omega
    have hfpair : ∀ i, i + 1 < M → f i + f (i + 1) ≤ n := by
      intro i hi
      by_cases hlc : i + 1 = M - 1
      · have h1 : i ≠ M - 1 := by omega
        have h2 : i % 2 = 0 := by omega
        rw [hfeven i h1 h2, hlc, hflast]; omega
      · have := hfpairEq i (by omega); omega
    obtain ⟨col, Pal, hsize, hdisjP, hdisjA, hdisjB⟩ :=
      OddChainEngine.chain_engine (K.induce Y) hLperf T' AA BB hAAT hBBT hABd
        M (by omega) x ({M - 1} : Set ℕ)
        (by intro hc; have h0 : (0 : ℕ) = M - 1 := hc; omega)
        (by intro i hi; have h0 : i = M - 1 := hi; omega)
        hxT hxinj hchain hcross0 hcover n f
        (by rw [hcnT]; exact hTn') hfle hfpair
        (by rw [hf0, hcnA]; omega)
        (by intro i hi; have h0 : i = M - 1 := hi; rw [h0, hflast, hcnB]; omega)
        (by intro i hi hi2; have h0 : i = M - 1 := hi; have h1 : i + 1 = M - 1 := hi2; omega)
    obtain ⟨ι, hι⟩ : ∃ ι : ↥T → ↥T', ∀ t : ↥T, (((ι t : ↥T') : ↥Y) : W) = (t : W) :=
      ⟨fun t => ⟨⟨(t : W), hYmem _ (Or.inl t.2)⟩, t.2⟩, fun _ => rfl⟩
    obtain ⟨colT, hcolT⟩ :
        ∃ colT : (K.induce T).Coloring (Fin n), ∀ t : ↥T, colT t = col (ι t) := by
      refine ⟨SimpleGraph.Coloring.mk (fun t => col (ι t)) ?_, fun _ => rfl⟩
      intro s t hst
      refine col.valid ?_
      show K.Adj (((ι s : ↥T') : ↥Y) : W) (((ι t : ↥T') : ↥Y) : W)
      rw [hι s, hι t]
      exact hst
    have himgA : colT '' {v : T | (v : W) ∈ A} = col '' {v : T' | (v : ↥Y) ∈ AA} := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨ι t, ?_, (hcolT t).symm⟩
        show (((ι t : ↥T') : ↥Y) : W) ∈ A ∩ T
        rw [hι t]
        exact ⟨ht, t.2⟩
      · rintro ⟨v, hv, rfl⟩
        have hv' : (((v : ↥T') : ↥Y) : W) ∈ A ∩ T := hv
        refine ⟨⟨_, hv'.2⟩, hv'.1, ?_⟩
        rw [hcolT]
        exact congrArg col (Subtype.ext (Subtype.ext (hι ⟨_, hv'.2⟩)))
    have himgB : colT '' {v : T | (v : W) ∈ B} = col '' {v : T' | (v : ↥Y) ∈ BB} := by
      ext z
      constructor
      · rintro ⟨t, ht, rfl⟩
        refine ⟨ι t, ?_, (hcolT t).symm⟩
        show (((ι t : ↥T') : ↥Y) : W) ∈ B ∩ T
        rw [hι t]
        exact ⟨ht, t.2⟩
      · rintro ⟨v, hv, rfl⟩
        have hv' : (((v : ↥T') : ↥Y) : W) ∈ B ∩ T := hv
        refine ⟨⟨_, hv'.2⟩, hv'.1, ?_⟩
        rw [hcolT]
        exact congrArg col (Subtype.ext (Subtype.ext (hι ⟨_, hv'.2⟩)))
    have hdA : Disjoint (colT '' {v : T | (v : W) ∈ A}) (Pal 0) := by rw [himgA]; exact hdisjA
    have hdB : Disjoint (colT '' {v : T | (v : W) ∈ B}) (Pal (M - 1)) := by
      rw [himgB]; exact hdisjB (M - 1) rfl
    have hAge : a ≤ (colT '' {v : T | (v : W) ∈ A}).ncard := palette_ge K T A n colT
    have hBge : b ≤ (colT '' {v : T | (v : W) ∈ B}).ncard := palette_ge K T B n colT
    have hPal0 : (Pal 0).ncard = n - a := by rw [hsize 0 (by omega), hf0]
    have hPalL : (Pal (M - 1)).ncard = n - b := by rw [hsize (M - 1) (by omega), hflast]
    have hAcard : (colT '' {v : T | (v : W) ∈ A}).ncard = a := by
      have := hsum2 _ _ hdA; omega
    have hBcard : (colT '' {v : T | (v : W) ∈ B}).ncard = b := by
      have := hsum2 _ _ hdB; omega
    have hAeq : colT '' {v : T | (v : W) ∈ A} = (Pal 0)ᶜ :=
      heqcompl _ _ hdA (by rw [hAcard, hPal0]; omega)
    have hBeq : colT '' {v : T | (v : W) ∈ B} = (Pal (M - 1))ᶜ :=
      heqcompl _ _ hdB (by rw [hBcard, hPalL]; omega)
    have halt : ∀ i, i ≤ M - 2 →
        (i % 2 = 0 → Pal i = Pal 0) ∧ (i % 2 ≠ 0 → Pal i = (Pal 0)ᶜ) := by
      intro i
      induction i with
      | zero =>
          intro _
          exact ⟨fun _ => rfl, fun h => absurd (by norm_num : (0 : ℕ) % 2 = 0) h⟩
      | succ j ih =>
          intro hj
          obtain ⟨ihe, iho⟩ := ih (by omega)
          have hstep : Pal (j + 1) = (Pal j)ᶜ := by
            refine heqcompl _ _ (hdisjP j (by omega)).symm ?_
            rw [hsize (j + 1) (by omega), hsize j (by omega)]
            have hpe := hfpairEq j (by omega)
            omega
          refine ⟨?_, ?_⟩
          · intro he
            rw [hstep, iho (by omega), compl_compl]
          · intro ho
            rw [hstep, ihe (by omega)]
    have hPalM2 : Pal (M - 2) = Pal 0 := (halt (M - 2) (by omega)).1 (by omega)
    have hdd : Disjoint (Pal (M - 2)) (Pal (M - 1)) := by
      have h := hdisjP (M - 2) (by omega)
      rwa [show M - 2 + 1 = M - 1 from by omega] at h
    have hsubBA : Pal (M - 1) ⊆ colT '' {v : T | (v : W) ∈ A} := by
      rw [hAeq, ← hPalM2]
      intro z hz
      exact (Set.disjoint_right.mp hdd) hz
    refine ⟨colT, hAcard, hBcard, ?_⟩
    have hinter : (colT '' {v : T | (v : W) ∈ A}) ∩ (colT '' {v : T | (v : W) ∈ B})
        = (colT '' {v : T | (v : W) ∈ A}) \ Pal (M - 1) := by
      rw [hBeq, Set.diff_eq]
    rw [hinter, Set.ncard_diff hsubBA (Set.toFinite _), hAcard, hPalL]
    omega

end Workspace.ProofLemmas
