import Workspace.ProofLemmas.TwoVertexSplitNetwork

set_option autoImplicit false

namespace Workspace.ProofLemmas.TwoVertexSplitRoute

open Workspace.ProofLemmas.TwoVertexSplitNetwork

def edgeTargets {U : Type*} : List (Arc U) → List U
  | [] => []
  | .inl _ :: r => edgeTargets r
  | .inr xy :: r => xy.2 :: edgeTargets r

@[simp] theorem edgeTargets_nil {U : Type*} : edgeTargets ([] : List (Arc U)) = [] := rfl
@[simp] theorem edgeTargets_split {U : Type*} (x : U) (r : List (Arc U)) :
    edgeTargets (Sum.inl x :: r) = edgeTargets r := rfl
@[simp] theorem edgeTargets_edge {U : Type*} (x y : U) (r : List (Arc U)) :
    edgeTargets (Sum.inr (x, y) :: r) = y :: edgeTargets r := rfl

def Usable {U : Type*} (G : SimpleGraph U) : Arc U → Prop
  | .inl _ => True
  | .inr xy => G.Adj xy.1 xy.2

theorem route_list_data
    {U : Type*} [Fintype U] (G : SimpleGraph U) (u v : U) :
    ∀ ρ : List (Arc U),
      ρ ≠ [] →
      (∃ a, ρ.head? = some a ∧ tail a = (u, true)) →
      (∃ a, ρ.getLast? = some a ∧ head a = (v, false)) →
      (∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2) →
      (∀ a ∈ ρ, Usable G a) →
      (u :: edgeTargets ρ).head? = some u ∧
      (u :: edgeTargets ρ).getLast? = some v ∧
      (u :: edgeTargets ρ).IsChain G.Adj ∧
      ∀ w ∈ u :: edgeTargets ρ, w ≠ u → w ≠ v → Sum.inl w ∈ ρ := by
  classical
  intro ρ
  induction ρ using List.twoStepInduction generalizing u v with
  | nil => simp
  | singleton a =>
      intro _ hfirst hlast _ hcap
      obtain ⟨a', ha', htail⟩ := hfirst
      simp only [List.head?_singleton, Option.some.injEq] at ha'
      subst a'
      obtain ⟨a', ha', hhead⟩ := hlast
      simp only [List.getLast?_singleton, Option.some.injEq] at ha'
      subst a'
      cases a with
      | inl x =>
          have := congrArg Prod.snd htail
          simp [tail] at this
      | inr xy =>
          rcases xy with ⟨x, y⟩
          have hxu : x = u := congrArg Prod.fst htail
          have hyv : y = v := congrArg Prod.fst hhead
          subst x
          subst y
          have hadj : G.Adj u v := by
            have hc := hcap (Sum.inr (u, v)) (by simp)
            simpa [Usable] using hc
          refine ⟨by simp, by simp, ?_, ?_⟩
          · simpa using hadj
          · intro w hw hwu hwv
            simp only [edgeTargets_edge, List.mem_cons] at hw
            rcases hw with rfl | hw
            · exact (hwu rfl).elim
            · simp at hw
              exact (hwv hw).elim
  | cons_cons a b r ihr ihr₂ =>
      intro _ hfirst hlast hlink hcap
      obtain ⟨a', ha', htaila⟩ := hfirst
      simp only [List.head?_cons, Option.some.injEq] at ha'
      subst a'
      cases a with
      | inl x =>
          have := congrArg Prod.snd htaila
          simp [tail] at this
      | inr xy =>
          rcases xy with ⟨x, y⟩
          have hxu : x = u := congrArg Prod.fst htaila
          subst x
          have hab : head (Sum.inr (u, y)) = tail b :=
            hlink (Sum.inr (u, y), b) (by simp)
          cases b with
          | inr zw =>
              have := congrArg Prod.snd hab
              simp [head, tail] at this
          | inl z =>
              have hzy : z = y := (congrArg Prod.fst hab).symm
              subst z
              have huy : G.Adj u y := by
                have hc := hcap (Sum.inr (u, y)) (by simp)
                simpa [Usable] using hc
              cases r with
              | nil =>
                  obtain ⟨a', ha', hheada'⟩ := hlast
                  simp only [List.getLast?_cons, List.getLast?_singleton,
                    Option.some.injEq] at ha'
                  subst a'
                  simp [head] at hheada'
              | cons c r' =>
                  have hbc : head (Sum.inl y) = tail c :=
                    hlink (Sum.inl y, c) (by simp)
                  have htailc : tail c = (y, true) := hbc.symm
                  have hrestne : c :: r' ≠ [] := by simp
                  have hrestlast : ∃ d, (c :: r').getLast? = some d ∧
                      head d = (v, false) := by
                    simpa using hlast
                  have hrestlink : ∀ de ∈ (c :: r').zip (c :: r').tail,
                      head de.1 = tail de.2 := by
                    intro de hde
                    exact hlink de (by simpa using Or.inr (Or.inr hde))
                  have hrestcap : ∀ d ∈ c :: r', Usable G d := by
                    intro d hd
                    exact hcap d (by simp [hd])
                  have hrestfirst : ∃ d, (c :: r').head? = some d ∧
                      tail d = (y, true) := ⟨c, rfl, htailc⟩
                  have hrec := ihr y v (by simp) hrestfirst hrestlast hrestlink hrestcap
                  rcases hrec with ⟨hheadP, hlastP, hchainP, hinterP⟩
                  refine ⟨by simp, ?_, ?_, ?_⟩
                  · simpa using hlastP
                  · exact hchainP.cons_cons huy
                  · intro w hw hwu hwv
                    simp only [edgeTargets_edge, edgeTargets_split, List.mem_cons] at hw
                    rcases hw with hwu' | hw
                    · exact (hwu hwu').elim
                    · rcases hw with hwy | hw
                      · subst w
                        simp
                      · have hwP : w ∈ y :: edgeTargets (c :: r') := by simp [hw]
                        by_cases hwy : w = y
                        · subst w
                          simp
                        · have := hinterP w hwP hwy hwv
                          exact by simp [this]

theorem exists_walk_support_eq_of_chain
    {U : Type*} (G : SimpleGraph U) :
    ∀ (P : List U) (u v : U),
      P.head? = some u → P.getLast? = some v → P.IsChain G.Adj →
      ∃ p : G.Walk u v, p.support = P := by
  intro P
  induction P with
  | nil => intro u v hu; simp at hu
  | cons x r ih =>
      intro u v hu hv hchain
      have hux : u = x := by simpa using hu.symm
      subst u
      cases r with
      | nil =>
          have hvx : v = x := by simpa using hv.symm
          subst v
          exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | cons y r' =>
          have hxy : G.Adj x y := (List.isChain_cons_cons.mp hchain).1
          have htail : (y :: r').IsChain G.Adj := (List.isChain_cons_cons.mp hchain).2
          obtain ⟨q, hq⟩ := ih y v (by simp) (by simpa using hv) htail
          exact ⟨SimpleGraph.Walk.cons hxy q, by simp [hq]⟩

theorem route_to_walk
    {U : Type*} [Fintype U] (G : SimpleGraph U) (u v : U)
    (ρ : List (Arc U)) (ρne : ρ ≠ [])
    (hfirst : ∃ a, ρ.head? = some a ∧ tail a = (u, true))
    (hlast : ∃ a, ρ.getLast? = some a ∧ head a = (v, false))
    (hlink : ∀ ab ∈ ρ.zip ρ.tail, head ab.1 = tail ab.2)
    (hcap : ∀ a ∈ ρ, 0 < capacity G u v a) :
    ∃ p : G.Walk u v,
      p.support = u :: edgeTargets ρ ∧
      ∀ w ∈ p.support, w ≠ u → w ≠ v → Sum.inl w ∈ ρ := by
  have husable : ∀ a ∈ ρ, Usable G a := by
    intro a ha
    have hc := hcap a ha
    cases a with
    | inl x => trivial
    | inr xy =>
        by_contra hn
        have hn' : ¬ G.Adj xy.1 xy.2 := by simpa [Usable] using hn
        simp [capacity, hn'] at hc
  obtain ⟨hhead, hlastP, hchain, hinter⟩ :=
    route_list_data G u v ρ ρne hfirst hlast hlink husable
  obtain ⟨p, hp⟩ := exists_walk_support_eq_of_chain G _ u v hhead hlastP hchain
  exact ⟨p, hp, fun w hw => hinter w (hp ▸ hw)⟩

end Workspace.ProofLemmas.TwoVertexSplitRoute
