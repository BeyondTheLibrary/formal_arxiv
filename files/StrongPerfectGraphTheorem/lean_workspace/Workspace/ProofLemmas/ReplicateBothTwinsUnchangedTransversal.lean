import Workspace.Types.Replication

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Replication.SPGT

/-- When both replicated twins occur and replication leaves the clique number
unchanged, the replicated induced graph has an independent set meeting every
maximum clique. -/
theorem ReplicateBothTwinsUnchangedTransversal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (v : V) (X : Set (V ⊕ Unit))
    (h_oldv : Sum.inl v ∈ X) (h_w : Sum.inr () ∈ X)
    (h_chromatic :
      (G.induce {a : V | Sum.inl a ∈ X}).chromaticNumber =
        ((G.induce {a : V | Sum.inl a ∈ X}).cliqueNum : ℕ∞))
    (h_clique :
      ((replicateVertex G v).induce X).cliqueNum =
        (G.induce {a : V | Sum.inl a ∈ X}).cliqueNum) :
    ∃ S : Set X,
      ((replicateVertex G v).induce X).IsIndepSet S ∧
        ∀ Q : Finset X,
          ((replicateVertex G v).induce X).IsClique (↑Q : Set X) →
            Q.card = ((replicateVertex G v).induce X).cliqueNum →
              ∃ q : X, q ∈ Q ∧ q ∈ S := by
  classical
  let A : Set V := {a : V | Sum.inl a ∈ X}
  let H0 : SimpleGraph A := G.induce A
  let H : SimpleGraph X := (replicateVertex G v).induce X
  let vA : A := ⟨v, h_oldv⟩
  let vX : X := ⟨Sum.inl v, h_oldv⟩
  let wX : X := ⟨Sum.inr (), h_w⟩
  let oldLift : A → X := fun a => ⟨Sum.inl a.1, a.2⟩
  have hcol : H0.Colorable H0.cliqueNum := by
    rw [← SimpleGraph.chromaticNumber_le_iff_colorable]
    simpa [H0, A] using le_of_eq h_chromatic
  obtain ⟨c⟩ := hcol
  let S : Set X := {x | x = wX ∨ ∃ a : A, a ≠ vA ∧ c a = c vA ∧ x = oldLift a}
  refine ⟨S, ?_, ?_⟩
  · rintro x hx y hy hxy hAdj
    rcases hx with rfl | ⟨a, hav, hca, rfl⟩
    · rcases hy with rfl | ⟨b, hbv, hcb, rfl⟩
      · exact hxy rfl
      · have hbval : b.1 ≠ v := by
          intro h
          apply hbv
          apply Subtype.ext
          exact h
        have hnadj : ¬G.Adj b.1 v := by
          intro hb
          have hb0 : H0.Adj b vA := hb
          exact c.valid hb0 hcb
        simpa [H, wX, oldLift, replicateVertex, hbval, hnadj] using hAdj
    · rcases hy with rfl | ⟨b, hbv, hcb, rfl⟩
      · have haval : a.1 ≠ v := by
          intro h
          apply hav
          apply Subtype.ext
          exact h
        have hnadj : ¬G.Adj a.1 v := by
          intro ha
          have ha0 : H0.Adj a vA := ha
          exact c.valid ha0 hca
        simpa [H, wX, oldLift, replicateVertex, haval, hnadj] using hAdj
      · have hab : H0.Adj a b := by
          simpa [H, H0, oldLift, replicateVertex] using hAdj
        exact c.valid hab (hca.trans hcb.symm)
  · intro Q hQ hQcard
    by_cases hwQ : wX ∈ Q
    · exact ⟨wX, hwQ, Or.inl rfl⟩
    · let p : X → A := fun q =>
        match h : q.1 with
        | Sum.inl a => ⟨a, by change Sum.inl a ∈ X; rw [← h]; exact q.2⟩
        | Sum.inr _ => vA
      have hp_old (q : X) (hq : q ∈ Q) : q = oldLift (p q) := by
        rcases q with ⟨a | u, ha⟩
        · rfl
        · obtain rfl : u = () := Subsingleton.elim _ _
          exfalso
          apply hwQ
          simpa [wX] using hq
      have hp_adj {q r : X} (hq : q ∈ Q) (hr : r ∈ Q) (hqr : q ≠ r) :
          H0.Adj (p q) (p r) := by
        have hadj := hQ hq hr hqr
        rw [hp_old q hq, hp_old r hr] at hadj
        simpa [H, H0, oldLift, p, replicateVertex] using hadj
      have hinj : ∀ q r, q ∈ Q → r ∈ Q → c (p q) = c (p r) → q = r := by
        intro q r hq hr hc
        by_contra hne
        exact c.valid (hp_adj hq hr hne) hc
      have hcard : (Finset.univ : Finset (Fin H0.cliqueNum)).card ≤ Q.card := by
        simp only [Fintype.card_fin, Finset.card_univ]
        rw [hQcard, h_clique]
      have hsurj :=
        Finset.surj_on_of_inj_on_of_card_le
          (s := Q) (t := (Finset.univ : Finset (Fin H0.cliqueNum)))
          (fun q (_ : q ∈ Q) => c (p q))
          (fun _ _ => Finset.mem_univ _)
          hinj hcard
      obtain ⟨q, hq, hcq⟩ := hsurj (c vA) (Finset.mem_univ _)
      have hc : c (p q) = c vA := hcq.symm
      have hpv : p q ≠ vA := by
        intro hpv
        have hqv : q = vX := by
          rw [hp_old q hq, hpv]
        have hvQ : vX ∈ Q := hqv ▸ hq
        have hins : H.IsClique (↑(insert wX Q) : Set X) := by
          rw [Finset.coe_insert]
          apply hQ.insert
          intro b hb hwb
          have hb_old := hp_old b hb
          by_cases hbv : b = vX
          · subst b
            simp [H, wX, vX, replicateVertex]
          · have hbv_adj : H.Adj b vX := hQ hb hvQ hbv
            rw [hb_old] at hbv_adj
            have hbase : G.Adj (p b).1 v := by
              simpa [H, vX, oldLift, p, replicateVertex] using hbv_adj
            rw [hb_old]
            simpa [H, wX, oldLift, replicateVertex] using
              (Or.inr hbase : (p b).1 = v ∨ G.Adj (p b).1 v)
        have hle : (insert wX Q).card ≤ H.cliqueNum := hins.card_le_cliqueNum
        have heq : H.cliqueNum = Q.card := by simpa [H] using hQcard.symm
        rw [Finset.card_insert_of_notMem hwQ, heq] at hle
        omega
      refine ⟨q, hq, ?_⟩
      exact Or.inr ⟨p q, hpv, hc, hp_old q hq⟩

end Workspace.ProofLemmas
