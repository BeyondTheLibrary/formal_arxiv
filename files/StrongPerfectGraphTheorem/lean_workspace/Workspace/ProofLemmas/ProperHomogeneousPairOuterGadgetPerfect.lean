import Workspace.Types.Core
import Workspace.Types.Decompositions
import Workspace.ProofLemmas.IsoTransport
import Workspace.ProofLemmas.NoDominatedPairInCriticalImperfect
import Workspace.ProofLemmas.SmallerBergeGraphIsPerfect

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Workspace.ProofLemmas

open Workspace.Types.Core Workspace.Types.Decompositions

/-- The four-tag outer gadget associated with a proper homogeneous pair is
perfect.  Tags `0,1,2,3` are respectively `u1,v1,u2,v2`; the tag edges form
the path `u1-v2-v1-u2`, so in particular `v1-v2` is an edge. -/
theorem ProperHomogeneousPairOuterGadgetPerfect
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : SPGT.MinimumImperfect G)
    (A B : Set V) (hAB : SPGT.IsProperHomogeneousPair G A B)
    (H : SimpleGraph (↥((A ∪ B)ᶜ) ⊕ Fin 4))
    (hH : ∀ x y, H.Adj x y ↔
      match x, y with
      | Sum.inl c, Sum.inl d => G.Adj c.1 d.1
      | Sum.inl c, Sum.inr i =>
          (((i = 0 ∨ i = 1) ∧ SPGT.VertexComplete G c.1 A) ∨
            ((i = 2 ∨ i = 3) ∧ SPGT.VertexComplete G c.1 B))
      | Sum.inr i, Sum.inl c =>
          (((i = 0 ∨ i = 1) ∧ SPGT.VertexComplete G c.1 A) ∨
            ((i = 2 ∨ i = 3) ∧ SPGT.VertexComplete G c.1 B))
      | Sum.inr i, Sum.inr j =>
          (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
          (i = 3 ∧ j = 1) ∨ (i = 1 ∧ j = 3) ∨
          (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) :
    SPGT.IsPerfect H := by
  classical
  rcases hAB with
    ⟨hABdisj, hAne, hBne, hAcover, hBcover, hCC, hCA, hAC, hAA⟩
  obtain ⟨a₀, ha₀A⟩ := hAne
  have ha₀B : a₀ ∉ B := fun ha₀B ↦ Set.disjoint_left.mp hABdisj ha₀A ha₀B
  have ha₀C : a₀ ∉ (A ∪ B)ᶜ := by simp [ha₀A]
  have ha₀_not_B_complete : ¬ SPGT.VertexComplete G a₀ B := by
    intro h
    have hm : a₀ ∈
        {v : V | SPGT.VertexComplete G v B} ∪
          {v : V | v ∉ B ∧ SPGT.VertexAnticomplete G v B} :=
      Or.inl h
    rw [hBcover] at hm
    exact ha₀C hm
  have ha₀_not_B_anticomplete : ¬ SPGT.VertexAnticomplete G a₀ B := by
    intro h
    have hm : a₀ ∈
        {v : V | SPGT.VertexComplete G v B} ∪
          {v : V | v ∉ B ∧ SPGT.VertexAnticomplete G v B} :=
      Or.inr ⟨ha₀B, h⟩
    rw [hBcover] at hm
    exact ha₀C hm
  simp only [SPGT.VertexComplete, not_forall] at ha₀_not_B_complete
  obtain ⟨bminus, hbminusB, ha₀bminus⟩ := ha₀_not_B_complete
  simp only [SPGT.VertexAnticomplete, not_forall, not_not] at ha₀_not_B_anticomplete
  obtain ⟨bplus, hbplusB, ha₀bplus⟩ := ha₀_not_B_anticomplete
  have hbplusA : bplus ∉ A := fun hbplusA ↦ Set.disjoint_left.mp hABdisj hbplusA hbplusB
  have hbplusC : bplus ∉ (A ∪ B)ᶜ := by simp [hbplusB]
  have hbplus_not_A_complete : ¬ SPGT.VertexComplete G bplus A := by
    intro h
    have hm : bplus ∈
        {v : V | SPGT.VertexComplete G v A} ∪
          {v : V | v ∉ A ∧ SPGT.VertexAnticomplete G v A} :=
      Or.inl h
    rw [hAcover] at hm
    exact hbplusC hm
  simp only [SPGT.VertexComplete, not_forall] at hbplus_not_A_complete
  obtain ⟨a₁, ha₁A, hbplusa₁⟩ := hbplus_not_A_complete
  have ha₀a₁ : a₀ ≠ a₁ := by
    intro h
    subst a₁
    exact hbplusa₁ ha₀bplus.symm
  have ha₀_ne_bplus : a₀ ≠ bplus := by
    intro h
    exact Set.disjoint_left.mp hABdisj ha₀A (h ▸ hbplusB)
  have ha₀_ne_bminus : a₀ ≠ bminus := by
    intro h
    exact Set.disjoint_left.mp hABdisj ha₀A (h ▸ hbminusB)
  have hbplus_ne_bminus : bplus ≠ bminus := by
    intro h
    subst bminus
    exact ha₀bminus ha₀bplus
  have hadjA (c : ↥((A ∪ B)ᶜ)) (a : V) (ha : a ∈ A) :
      G.Adj c.1 a ↔ SPGT.VertexComplete G c.1 A := by
    constructor
    · intro hca
      have hm : c.1 ∈
          {v : V | SPGT.VertexComplete G v A} ∪
            {v : V | v ∉ A ∧ SPGT.VertexAnticomplete G v A} := by
        rw [hAcover]
        exact c.2
      rcases hm with hc | ⟨-, hc⟩
      · exact hc
      · exact False.elim (hc a ha hca)
    · intro hc
      exact hc a ha
  have hadjB (c : ↥((A ∪ B)ᶜ)) (b : V) (hb : b ∈ B) :
      G.Adj c.1 b ↔ SPGT.VertexComplete G c.1 B := by
    constructor
    · intro hcb
      have hm : c.1 ∈
          {v : V | SPGT.VertexComplete G v B} ∪
            {v : V | v ∉ B ∧ SPGT.VertexAnticomplete G v B} := by
        rw [hBcover]
        exact c.2
      rcases hm with hc | ⟨-, hc⟩
      · exact hc
      · exact False.elim (hc b hb hcb)
    · intro hc
      exact hc b hb
  let motive := fun n : ℕ ↦
    ∀ X : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4), Nat.card X = n →
      SPGT.IsPerfect (H.induce X)
  have hcritical : ∀ n : ℕ, motive n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro X hXcard
      by_contra hXnonperfect
      have hXproper : ∀ Y : Set X, Y ≠ Set.univ →
          SPGT.IsPerfect ((H.induce X).induce Y) := by
        intro Y hY
        let Z : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4) := Subtype.val '' Y
        have hZX : Z ⊆ X := by
          rintro z ⟨y, hy, rfl⟩
          exact y.2
        have hZXstrict : Z ⊂ X := by
          refine ⟨hZX, ?_⟩
          intro hXZ
          apply hY
          ext y
          simp only [Set.mem_univ, iff_true]
          have hyZ : (y : ↥((A ∪ B)ᶜ) ⊕ Fin 4) ∈ Z := hXZ y.2
          rcases hyZ with ⟨z, hzY, hz⟩
          have : z = y := Subtype.ext hz
          simpa [this] using hzY
        have hZcard : Nat.card Z < n := by
          rw [← hXcard]
          exact Set.Finite.card_lt_card (Set.toFinite X) hZXstrict
        have hZperfect : SPGT.IsPerfect (H.induce Z) :=
          ih (Nat.card Z) hZcard Z rfl
        let e : (H.induce X).induce Y ≃g H.induce Z :=
          { Equiv.Set.image (Subtype.val : X → (↥((A ∪ B)ᶜ) ⊕ Fin 4)) Y
              Subtype.val_injective with
            map_rel_iff' := by
              intro x y
              rfl }
        exact IsoTransport.isPerfect_of_iso e.symm hZperfect
      have hnot01 : ¬ (Sum.inr (0 : Fin 4) ∈ X ∧ Sum.inr (1 : Fin 4) ∈ X) := by
        rintro ⟨h0, h1⟩
        let p : X := ⟨Sum.inr 1, h1⟩
        let q : X := ⟨Sum.inr 0, h0⟩
        have hpq : p ≠ q := by
          intro hpq
          have := congrArg (fun z : X ↦ z.1) hpq
          simp [p, q] at this
        apply NoDominatedPairInCriticalImperfect (H.induce X) hXnonperfect hXproper p q hpq
        intro z hz
        rcases hz with ⟨hzq, hzp⟩
        have hzq' : (H.induce X).Adj q z := by
          simpa only [SimpleGraph.mem_neighborSet] using hzq
        have hzp' : z ≠ p := by
          simpa only [Set.mem_singleton_iff] using hzp
        refine ⟨?_, ?_⟩
        · simp only [SimpleGraph.mem_neighborSet]
          change H.Adj (Sum.inr 1) z.1
          change H.Adj (Sum.inr 0) z.1 at hzq'
          rcases z with ⟨(c | i), hiX⟩
          · rw [hH] at hzq' ⊢
            simpa using hzq'
          · rw [hH] at hzq' ⊢
            fin_cases i <;> simp_all
        · simp only [Set.mem_singleton_iff]
          intro hzqeq
          subst z
          exact (H.induce X).irrefl hzq'
      have hnot23 : ¬ (Sum.inr (2 : Fin 4) ∈ X ∧ Sum.inr (3 : Fin 4) ∈ X) := by
        rintro ⟨h2, h3⟩
        let p : X := ⟨Sum.inr 3, h3⟩
        let q : X := ⟨Sum.inr 2, h2⟩
        have hpq : p ≠ q := by
          intro hpq
          have := congrArg (fun z : X ↦ z.1) hpq
          simp [p, q] at this
        apply NoDominatedPairInCriticalImperfect (H.induce X) hXnonperfect hXproper p q hpq
        intro z hz
        rcases hz with ⟨hzq, hzp⟩
        have hzq' : (H.induce X).Adj q z := by
          simpa only [SimpleGraph.mem_neighborSet] using hzq
        have hzp' : z ≠ p := by
          simpa only [Set.mem_singleton_iff] using hzp
        refine ⟨?_, ?_⟩
        · simp only [SimpleGraph.mem_neighborSet]
          change H.Adj (Sum.inr 3) z.1
          change H.Adj (Sum.inr 2) z.1 at hzq'
          rcases z with ⟨(c | i), hiX⟩
          · rw [hH] at hzq' ⊢
            simpa using hzq'
          · rw [hH] at hzq' ⊢
            fin_cases i <;> simp_all
        · simp only [Set.mem_singleton_iff]
          intro hzqeq
          subst z
          exact (H.induce X).irrefl hzq'
      have htag (i : Fin 4) : (i = 0 ∨ i = 1) ∨ (i = 2 ∨ i = 3) := by
        fin_cases i <;> simp
      have htag_disjoint (i : Fin 4) :
          (i = 0 ∨ i = 1) → (i = 2 ∨ i = 3) → False := by
        intro hi hj
        rcases hi with rfl | rfl <;> rcases hj with h | h <;> simp at h
      have hfirst_unique (i j : Fin 4)
          (hi : i = 0 ∨ i = 1) (hj : j = 0 ∨ j = 1)
          (hiX : Sum.inr i ∈ X) (hjX : Sum.inr j ∈ X) : i = j := by
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · rfl
        · exact False.elim (hnot01 ⟨hiX, hjX⟩)
        · exact False.elim (hnot01 ⟨hjX, hiX⟩)
        · rfl
      have hsecond_unique (i j : Fin 4)
          (hi : i = 2 ∨ i = 3) (hj : j = 2 ∨ j = 3)
          (hiX : Sum.inr i ∈ X) (hjX : Sum.inr j ∈ X) : i = j := by
        rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
        · rfl
        · exact False.elim (hnot23 ⟨hiX, hjX⟩)
        · exact False.elim (hnot23 ⟨hjX, hiX⟩)
        · rfl
      let f : X → V := fun x ↦
        match x.1 with
        | Sum.inl c => c.1
        | Sum.inr i =>
            if i = 0 ∨ i = 1 then a₀
            else if
              (Sum.inr (0 : Fin 4) ∈ X ∧
                  H.Adj (Sum.inr (0 : Fin 4)) (Sum.inr i)) ∨
                (Sum.inr (1 : Fin 4) ∈ X ∧
                  H.Adj (Sum.inr (1 : Fin 4)) (Sum.inr i))
            then bplus else bminus
      have hf_injective : Function.Injective f := by
        rintro ⟨(c | i), hci⟩ ⟨(d | j), hdj⟩ hfd
        · apply Subtype.ext
          exact congrArg Sum.inl (Subtype.ext hfd)
        · simp only [f] at hfd
          split at hfd
          · exact False.elim (c.2 (Or.inl (by simpa [hfd] using ha₀A)))
          · split at hfd
            · exact False.elim (c.2 (Or.inr (by simpa [hfd] using hbplusB)))
            · exact False.elim (c.2 (Or.inr (by simpa [hfd] using hbminusB)))
        · simp only [f] at hfd
          split at hfd
          · exact False.elim (d.2 (Or.inl (by simpa [hfd.symm] using ha₀A)))
          · split at hfd
            · exact False.elim (d.2 (Or.inr (by simpa [hfd.symm] using hbplusB)))
            · exact False.elim (d.2 (Or.inr (by simpa [hfd.symm] using hbminusB)))
        · have hij : i = j := by
            rcases htag i with hi | hi <;> rcases htag j with hj | hj
            · exact hfirst_unique i j hi hj hci hdj
            · dsimp only [f] at hfd
              rw [if_pos hi, if_neg (fun h ↦ htag_disjoint j h hj)] at hfd
              split at hfd
              · exact False.elim (ha₀_ne_bplus hfd)
              · exact False.elim (ha₀_ne_bminus hfd)
            · dsimp only [f] at hfd
              rw [if_neg (fun h ↦ htag_disjoint i h hi), if_pos hj] at hfd
              split at hfd
              · exact False.elim (ha₀_ne_bplus hfd.symm)
              · exact False.elim (ha₀_ne_bminus hfd.symm)
            · exact hsecond_unique i j hi hj hci hdj
          subst j
          rfl
      have hf_tag_cross (i j : Fin 4)
          (hi : i = 0 ∨ i = 1) (hj : j = 2 ∨ j = 3)
          (hiX : Sum.inr i ∈ X) (hjX : Sum.inr j ∈ X) :
          H.Adj (Sum.inr i) (Sum.inr j) ↔
            G.Adj (f ⟨Sum.inr i, hiX⟩) (f ⟨Sum.inr j, hjX⟩) := by
        have hfi : f ⟨Sum.inr i, hiX⟩ = a₀ := by
          simp [f, hi]
        have hjnot : ¬ (j = 0 ∨ j = 1) := fun h ↦ htag_disjoint j h hj
        have hchoose :
            ((Sum.inr (0 : Fin 4) ∈ X ∧
                H.Adj (Sum.inr (0 : Fin 4)) (Sum.inr j)) ∨
              (Sum.inr (1 : Fin 4) ∈ X ∧
                H.Adj (Sum.inr (1 : Fin 4)) (Sum.inr j))) ↔
              H.Adj (Sum.inr i) (Sum.inr j) := by
          constructor
          · rintro (⟨h0X, h0j⟩ | ⟨h1X, h1j⟩)
            · have heq : (0 : Fin 4) = i :=
                hfirst_unique 0 i (Or.inl rfl) hi h0X hiX
              simpa [heq] using h0j
            · have heq : (1 : Fin 4) = i :=
                hfirst_unique 1 i (Or.inr rfl) hi h1X hiX
              simpa [heq] using h1j
          · intro hij
            rcases hi with rfl | rfl
            · exact Or.inl ⟨hiX, hij⟩
            · exact Or.inr ⟨hiX, hij⟩
        have hfj : f ⟨Sum.inr j, hjX⟩ =
            if H.Adj (Sum.inr i) (Sum.inr j) then bplus else bminus := by
          dsimp only [f]
          rw [if_neg hjnot]
          by_cases hij : H.Adj (Sum.inr i) (Sum.inr j)
          · rw [if_pos hij, if_pos (hchoose.mpr hij)]
          · rw [if_neg hij, if_neg (fun h ↦ hij (hchoose.mp h))]
        rw [hfi, hfj]
        by_cases hij : H.Adj (Sum.inr i) (Sum.inr j)
        · simp [hij, ha₀bplus]
        · simp [hij, ha₀bminus]
      have hf_adj : ∀ x y : X,
          (H.induce X).Adj x y ↔ G.Adj (f x) (f y) := by
        rintro ⟨(c | i), hci⟩ ⟨(d | j), hdj⟩
        · simpa [f] using hH (Sum.inl c) (Sum.inl d)
        · change H.Adj (Sum.inl c) (Sum.inr j) ↔ _
          rw [hH]
          fin_cases j
          · simpa [f] using (hadjA c a₀ ha₀A).symm
          · simpa [f] using (hadjA c a₀ ha₀A).symm
          · simp [f]
            split
            · exact (hadjB c bplus hbplusB).symm
            · exact (hadjB c bminus hbminusB).symm
          · simp [f]
            split
            · exact (hadjB c bplus hbplusB).symm
            · exact (hadjB c bminus hbminusB).symm
        · change H.Adj (Sum.inr i) (Sum.inl d) ↔ _
          rw [hH]
          fin_cases i
          · simpa [f, G.adj_comm] using (hadjA d a₀ ha₀A).symm
          · simpa [f, G.adj_comm] using (hadjA d a₀ ha₀A).symm
          · simp [f]
            split
            · simpa only [G.adj_comm] using (hadjB d bplus hbplusB).symm
            · simpa only [G.adj_comm] using (hadjB d bminus hbminusB).symm
          · simp [f]
            split
            · simpa only [G.adj_comm] using (hadjB d bplus hbplusB).symm
            · simpa only [G.adj_comm] using (hadjB d bminus hbminusB).symm
        · change H.Adj (Sum.inr i) (Sum.inr j) ↔ _
          rcases htag i with hi | hi <;> rcases htag j with hj | hj
          · have hij := hfirst_unique i j hi hj hci hdj
            subst j
            simp
          · exact hf_tag_cross i j hi hj hci hdj
          · rw [H.adj_comm, G.adj_comm]
            exact hf_tag_cross j i hj hi hdj hci
          · have hij := hsecond_unique i j hi hj hci hdj
            subst j
            simp
      let F : X → {v : V | v ∈ Set.range f} := fun x ↦ ⟨f x, x, rfl⟩
      have hFbij : Function.Bijective F := by
        constructor
        · intro x y hxy
          apply hf_injective
          exact congrArg Subtype.val hxy
        · rintro ⟨v, x, rfl⟩
          exact ⟨x, rfl⟩
      let e₀ : X ≃ {v : V | v ∈ Set.range f} := Equiv.ofBijective F hFbij
      let e : H.induce X ≃g G.induce (Set.range f) :=
        { e₀ with
          map_rel_iff' := by
            intro x y
            exact (hf_adj x y).symm }
      have ha₁range : a₁ ∉ Set.range f := by
        rintro ⟨⟨(c | i), hci⟩, hi⟩
        · have hc : c.1 = a₁ := by simpa only [f] using hi
          exact c.2 (Or.inl (hc ▸ ha₁A))
        · simp only [f] at hi
          split at hi
          · exact ha₀a₁ hi
          · split at hi
            · exact Set.disjoint_left.mp hABdisj ha₁A (by simpa [hi.symm] using hbplusB)
            · exact Set.disjoint_left.mp hABdisj ha₁A (by simpa [hi.symm] using hbminusB)
      have hrange_ne : Set.range f ≠ (Set.univ : Set V) := by
        intro h
        exact ha₁range (h.symm ▸ Set.mem_univ a₁)
      have hrangePerfect : SPGT.IsPerfect (G.induce (Set.range f)) :=
        SmallerBergeGraphIsPerfect.isPerfect_induce_of_ne_univ hG hrange_ne
      exact hXnonperfect (IsoTransport.isPerfect_of_iso e.symm hrangePerfect)
  have hAll : ∀ X : Set (↥((A ∪ B)ᶜ) ⊕ Fin 4),
      SPGT.IsPerfect (H.induce X) := fun X ↦ hcritical (Nat.card X) X rfl
  intro X
  have h := hAll X Set.univ
  rw [IsoTransport.chromaticNumber_iso (SimpleGraph.induceUnivIso (H.induce X)),
    IsoTransport.cliqueNum_iso (SimpleGraph.induceUnivIso (H.induce X))] at h
  exact h

end Workspace.ProofLemmas

