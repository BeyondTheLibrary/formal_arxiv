import Workspace.Types.Tracks

set_option autoImplicit false

namespace Workspace.ProofLemmas

open Workspace.Types.Tracks.SPGT

theorem TrackGlueAtCommonEndpoint
    {V : Type*} (H : SimpleGraph V) (P Q : List V) (a r b : V)
    (hP : IsTrackFrom H P a r)
    (hQ : IsTrackFrom H Q r b)
    (hcommon : ∀ z : V, z ∈ P → z ∈ Q → z = r) :
    let R : List V := P ++ Q.tail
    IsTrackFrom H R a b ∧ ∀ z ∈ R, z ∈ P ∨ z ∈ Q := by
  show IsTrackFrom H (P ++ Q.tail) a b ∧ ∀ z ∈ P ++ Q.tail, z ∈ P ∨ z ∈ Q
  obtain ⟨⟨hPne, hPnd, hPadj⟩, hPhead, hPlast⟩ := hP
  obtain ⟨hQt, hQhead, hQlast⟩ := hQ
  have hPlen : 0 < P.length := List.length_pos_of_ne_nil hPne
  -- the last vertex of `P` is the common end `r`
  have hPlastElem : P[P.length - 1]'(by omega) = r := by
    have h : P.getLast? = some (P.getLast hPne) := List.getLast?_eq_some_getLast hPne
    rw [h] at hPlast
    have hr : P.getLast hPne = r := Option.some_inj.mp hPlast
    rw [← hr, List.getLast_eq_getElem]
  -- write `Q = r :: t`
  obtain ⟨t, rfl⟩ : ∃ t : List V, Q = r :: t := by
    cases Q with
    | nil => simp at hQhead
    | cons c s =>
      exact ⟨s, by simp only [List.head?_cons, Option.some_inj] at hQhead; rw [hQhead]⟩
  obtain ⟨-, hQnd, hQadj⟩ := hQt
  have hrt : r ∉ t := (List.nodup_cons.mp hQnd).1
  have htnd : t.Nodup := (List.nodup_cons.mp hQnd).2
  simp only [List.tail_cons]
  have hglue : IsTrackList H (P ++ t) := by
    refine ⟨by simp [hPne], ?_, ?_⟩
    · -- `Nodup`: the two lists meet only in `r`, which is not in `t`
      refine List.nodup_append.mpr ⟨hPnd, htnd, ?_⟩
      intro x hxP y hyt hxy
      have hxt : x ∈ t := by rw [hxy]; exact hyt
      have hxr : x = r := hcommon x hxP (List.mem_cons_of_mem _ hxt)
      exact hrt (by rw [← hxr]; exact hxt)
    · -- adjacency of consecutive entries
      intro i hi
      rw [List.length_append] at hi
      rcases Nat.lt_or_ge (i + 1) P.length with hlt | hge
      · have h0 : i < P.length := by omega
        rw [List.getElem_append_left h0, List.getElem_append_left hlt]
        exact hPadj i hlt
      rcases Nat.lt_or_ge i P.length with hiP | hiP
      · -- the junction: `P` ends at `r`, and the next vertex is `t[0]`
        have ht0 : 0 < t.length := by omega
        have hfirst : (P ++ t)[i]'(by rw [List.length_append]; omega) = r := by
          rw [List.getElem_append_left hiP, ← hPlastElem]
          congr 1
          omega
        have hsecond : (P ++ t)[i + 1]'(by rw [List.length_append]; omega) = t[0]'ht0 := by
          rw [List.getElem_append_right (by omega)]
          congr 1
          omega
        rw [hfirst, hsecond]
        have := hQadj 0 (by simpa using ht0)
        simpa using this
      · -- both indices inside `t`
        have h1 : i - P.length < t.length := by omega
        rw [List.getElem_append_right hiP, List.getElem_append_right (by omega)]
        have := hQadj (i - P.length + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getElem_cons_succ] at this
        have hidx : i + 1 - P.length = (i - P.length) + 1 := by omega
        simp only [hidx]
        exact this
  refine ⟨⟨hglue, ?_, ?_⟩, ?_⟩
  · -- the first vertex is still `a`
    simp [List.head?_append, hPhead]
  · -- the last vertex is `b`
    have hcons : (r :: t).getLast? = t.getLast?.or (some r) := by
      rw [show (r :: t) = [r] ++ t from rfl, List.getLast?_append]
      simp
    rw [hcons] at hQlast
    rw [List.getLast?_append, hPlast]
    exact hQlast
  · -- membership
    intro z hz
    rcases List.mem_append.mp hz with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

end Workspace.ProofLemmas
