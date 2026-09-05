import Workspace.Types.Core
import Workspace.Types.Appearances
import Workspace.Types.Staircases
import Workspace.ProofLemmas.InducedPathExtraction
import Workspace.ProofLemmas.PathBasics

set_option autoImplicit false

namespace Workspace.ProofLemmas.MinimalNonlocalStaircaseAttachmentPath

open Workspace.Types.Core.SPGT
open Workspace.Types.Appearances.SPGT
open Workspace.Types.Staircases.SPGT
open Workspace.ProofLemmas.InducedPathExtraction
open Workspace.ProofLemmas.PathBasics

private theorem nonlocal_of_left_obstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (D : Set V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hleft : ∃ x ∈ D, ∃ u ∈ A ∪ C, G.Adj x u)
    (hrung : ∃ x ∈ D, ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r) :
    ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G D (staircaseVertices A C B R₀)) := by
  obtain ⟨x, hxD, u, hu, hxu⟩ := hleft
  obtain ⟨y, hyD, r, hrR, hrne, hyr⟩ := hrung
  have hban := hK.2.1
  have hRout : ∀ v ∈ R₀, v ∉ A ∪ B ∪ C := hban.2.1
  have huS : u ∈ A ∪ B ∪ C := by
    rcases hu with huA | huC
    · exact Or.inl (Or.inl huA)
    · exact Or.inr huC
  have huR : u ∉ R₀ := by
    intro huR
    exact hRout u huR huS
  have hrS : r ∉ A ∪ B ∪ C := hRout r hrR
  have huB : u ∉ B := by
    rcases hu with huA | huC
    · exact Set.disjoint_left.mp hK.1.1.1 huA
    · exact fun huB => Set.disjoint_left.mp hK.1.1.2.2 huB huC
  have hbR : b₀ ∈ R₀ := getLast_mem hban.1.2.2
  have hub : u ≠ b₀ := by
    intro hub
    exact hRout b₀ hbR (hub ▸ huS)
  have huatt : u ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inr huS, x, hxD, hxu.symm⟩
  have hratt : r ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inl hrR, y, hyD, hyr.symm⟩
  rintro (hloc | hloc | hloc | hloc)
  · exact hrS (hloc hratt)
  · exact huR (hloc huatt)
  · rcases hloc hratt with hrA | hra
    · exact hrS (Or.inl (Or.inl hrA))
    · exact hrne hra
  · rcases hloc huatt with huB' | hub'
    · exact huB huB'
    · exact hub hub'

private theorem nonlocal_of_right_obstruction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (D : Set V) (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hright : ∃ x ∈ D, ∃ u ∈ B ∪ C, G.Adj x u)
    (hrung : ∃ x ∈ D, ∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj x r) :
    ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G D (staircaseVertices A C B R₀)) := by
  obtain ⟨x, hxD, u, hu, hxu⟩ := hright
  obtain ⟨y, hyD, r, hrR, hrne, hyr⟩ := hrung
  have hban := hK.2.1
  have hRout : ∀ v ∈ R₀, v ∉ A ∪ B ∪ C := hban.2.1
  have huS : u ∈ A ∪ B ∪ C := by
    rcases hu with huB | huC
    · exact Or.inl (Or.inr huB)
    · exact Or.inr huC
  have huR : u ∉ R₀ := by
    intro huR
    exact hRout u huR huS
  have hrS : r ∉ A ∪ B ∪ C := hRout r hrR
  have huA : u ∉ A := by
    rcases hu with huB | huC
    · exact fun huA => Set.disjoint_left.mp hK.1.1.1 huA huB
    · exact fun huA => Set.disjoint_left.mp hK.1.1.2.1 huA huC
  have haR : a₀ ∈ R₀ := head_mem hban.1.2.1
  have hua : u ≠ a₀ := by
    intro hua
    exact hRout a₀ haR (hua ▸ huS)
  have huatt : u ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inr huS, x, hxD, hxu.symm⟩
  have hratt : r ∈ attachments G D (staircaseVertices A C B R₀) :=
    ⟨Or.inl hrR, y, hyD, hyr.symm⟩
  rintro (hloc | hloc | hloc | hloc)
  · exact hrS (hloc hratt)
  · exact huR (hloc huatt)
  · rcases hloc huatt with huA' | hua'
    · exact huA huA'
    · exact hua hua'
  · rcases hloc hratt with hrB | hrb
    · exact hrS (Or.inl (Or.inr hrB))
    · exact hrne hrb

private theorem exists_endpoint_clean_path
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (F : Set V) (L R : V → Prop)
    (hFconn : ConnectedSet G F)
    (hL : ∃ x ∈ F, L x) (hR : ∃ x ∈ F, R x)
    (hspan : ∀ D : Set V, D ⊆ F → ConnectedSet G D →
      (∃ x ∈ D, L x) → (∃ x ∈ D, R x) → D = F) :
    ∃ (p : List V) (f₁ fk : V),
      F = {v : V | v ∈ p} ∧ IsPathFrom G p f₁ fk ∧
      (∀ x ∈ F, L x → x = f₁) ∧ (∀ x ∈ F, R x → x = fk) := by
  classical
  obtain ⟨l, hlF, hl⟩ := hL
  obtain ⟨r, hrF, hr⟩ := hR
  obtain ⟨p₀, hp₀, hp₀F⟩ :=
    exists_isPathFrom_of_connected (G := G) hFconn hlF hrF
  have hex : ∃ n : ℕ, ∃ f₁ : V, f₁ ∈ F ∧ L f₁ ∧ ∃ fk : V, fk ∈ F ∧ R fk ∧
      ∃ p : List V, IsPathFrom G p f₁ fk ∧ (∀ z ∈ p, z ∈ F) ∧ p.length = n :=
    ⟨p₀.length, l, hlF, hl, r, hrF, hr, p₀, hp₀, hp₀F, rfl⟩
  obtain ⟨f₁, hf₁F, hf₁L, fk, hfkF, hfkR, p, hp, hpF, hplen⟩ := Nat.find_spec hex
  have hmin : ∀ (u v : V) (q : List V), u ∈ F → L u → v ∈ F → R v →
      IsPathFrom G q u v → (∀ z ∈ q, z ∈ F) → p.length ≤ q.length := by
    intro u v q huF huL hvF hvR hq hqF
    rw [hplen]
    exact Nat.find_min' hex ⟨u, huF, huL, v, hvF, hvR, q, hq, hqF, rfl⟩
  have hpSetConn : ConnectedSet G {z : V | z ∈ p} :=
    connectedSet_setOf_mem_of_isPathList hp.1
  have hpSetEq : {z : V | z ∈ p} = F :=
    hspan _ hpF hpSetConn
      ⟨f₁, isPathFrom_ends_mem hp |>.1, hf₁L⟩
      ⟨fk, isPathFrom_ends_mem hp |>.2, hfkR⟩
  have hpos : 0 < p.length := path_length_pos hp.1
  have hzero : p[0]'hpos = f₁ := getElem_zero_of_head? hp.2.1 hpos
  have hlast : p[p.length - 1]'(by omega) = fk :=
    getElem_last_of_getLast? hp.2.2 hpos
  have hleftUnique : ∀ x ∈ F, L x → x = f₁ := by
    intro x hxF hxL
    have hxp : x ∈ p := by
      rw [← hpSetEq] at hxF
      exact hxF
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxp
    by_cases hi0 : i = 0
    · subst i
      exact hix.symm.trans hzero
    by_cases hilast : i = p.length - 1
    · have hxfk : x = fk := hix.symm.trans (by simpa only [hilast] using hlast)
      have hxR : R x := by simpa only [hxfk] using hfkR
      have hsingle : IsPathFrom G [x] x x :=
        ⟨isPathList_singleton G x, by simp, by simp⟩
      have hle := hmin x x [x] hxF hxL hxF hxR hsingle (by simpa using hxF)
      simp only [List.length_singleton] at hle
      omega
    · have hilast' : i < p.length - 1 := by omega
      let q := (p.drop i).take (p.length - 1 - i + 1)
      have hq : IsPathFrom G q x fk := by
        have hs := isPathFrom_slice hp.1 hilast' (show p.length - 1 < p.length by omega)
        simpa only [q, hix, hlast] using hs
      have hqF : ∀ z ∈ q, z ∈ F := by
        intro z hz
        exact hpF z (List.drop_subset i p (List.take_subset _ _ hz))
      have hle := hmin x fk q hxF hxL hfkF hfkR hq hqF
      have hqlen : q.length = p.length - 1 - i + 1 := by
        dsimp only [q]
        exact length_slice p (by omega) (by omega)
      omega
  have hrightUnique : ∀ x ∈ F, R x → x = fk := by
    intro x hxF hxR
    have hxp : x ∈ p := by
      rw [← hpSetEq] at hxF
      exact hxF
    obtain ⟨i, hi, hix⟩ := List.getElem_of_mem hxp
    by_cases hilast : i = p.length - 1
    · exact hix.symm.trans (by simpa only [hilast] using hlast)
    · have hilt : i + 1 < p.length := by omega
      have hpre : IsPathFrom G (p.take (i + 1)) f₁ x := by
        refine ⟨isPathList_take hp.1 (by omega), ?_, ?_⟩
        · rw [List.head?_take, if_neg (by omega)]
          exact hp.2.1
        · rw [List.getLast?_take, if_neg (by omega)]
          simp only [Nat.add_sub_cancel, List.getElem?_eq_getElem hi, hix, Option.some_or]
      have hpreF : ∀ z ∈ p.take (i + 1), z ∈ F := by
        intro z hz
        exact hpF z (List.take_subset _ _ hz)
      have hle := hmin f₁ x (p.take (i + 1)) hf₁F hf₁L hxF hxR hpre hpreF
      rw [List.length_take] at hle
      omega
  exact ⟨p, f₁, fk, hpSetEq.symm, hp, hleftUnique, hrightUnique⟩

/-- The minimal connected nonlocal-attachment reduction in the proof of 12.2. -/
theorem minimalNonlocalStaircaseAttachmentPath
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A C B : Set V) (a₀ b₀ : V) (R₀ : List V)
    (F_orig : Set V)
    (hK : IsStaircase G A C B a₀ R₀ b₀)
    (hFoutside : F_orig ⊆ (staircaseVertices A C B R₀)ᶜ)
    (hFconn : ConnectedSet G F_orig)
    (hFnonlocal : ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G F_orig (staircaseVertices A C B R₀))) :
    ∃ (F : Set V) (f : List V) (f₁ fk : V),
      F ⊆ F_orig ∧
      F ⊆ (staircaseVertices A C B R₀)ᶜ ∧
      ConnectedSet G F ∧
      ¬ LocalForStaircase A C B a₀ R₀ b₀
        (attachments G F (staircaseVertices A C B R₀)) ∧
      (∀ D : Set V, D ⊂ F → ConnectedSet G D →
        LocalForStaircase A C B a₀ R₀ b₀
          (attachments G D (staircaseVertices A C B R₀))) ∧
      F = {v : V | v ∈ f} ∧
      IsPathFrom G f f₁ fk ∧
      (((∃ u ∈ A ∪ C, G.Adj f₁ u) ∧
          (∀ x ∈ F, (∃ u ∈ A ∪ C, G.Adj x u) → x = f₁) ∧
          (∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj fk r) ∧
          (∀ x ∈ F, (∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r) → x = fk)) ∨
        ((∃ u ∈ B ∪ C, G.Adj f₁ u) ∧
          (∀ x ∈ F, (∃ u ∈ B ∪ C, G.Adj x u) → x = f₁) ∧
          (∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj fk r) ∧
          (∀ x ∈ F, (∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj x r) → x = fk))) := by
  classical
  let Good : Set V → Prop := fun D =>
    D ⊆ F_orig ∧ ConnectedSet G D ∧
      ¬ LocalForStaircase A C B a₀ R₀ b₀
        (attachments G D (staircaseVertices A C B R₀))
  obtain ⟨F, hFgood, hFmin⟩ :=
    Set.exists_min_image {D : Set V | Good D} Set.ncard (Set.toFinite _)
      ⟨F_orig, subset_rfl, hFconn, hFnonlocal⟩
  have hFsub : F ⊆ F_orig := hFgood.1
  have hFconn' : ConnectedSet G F := hFgood.2.1
  have hFnonlocal' : ¬ LocalForStaircase A C B a₀ R₀ b₀
      (attachments G F (staircaseVertices A C B R₀)) := hFgood.2.2
  have hproperLocal : ∀ D : Set V, D ⊂ F → ConnectedSet G D →
      LocalForStaircase A C B a₀ R₀ b₀
        (attachments G D (staircaseVertices A C B R₀)) := by
    intro D hDF hDconn
    by_contra hDnonlocal
    have heq : D = F := Set.eq_of_subset_of_ncard_le hDF.1
      (hFmin D ⟨hDF.1.trans hFsub, hDconn, hDnonlocal⟩) (Set.toFinite _)
    exact hDF.2 (heq ▸ subset_rfl)
  have hab : a₀ ≠ b₀ :=
    isPathFrom_ends_ne hK.2.1.1 (le_trans (by decide : 1 ≤ 3) hK.2.2)
  have horient :
      (((∃ x ∈ F, ∃ u ∈ A ∪ C, G.Adj x u) ∧
        (∃ x ∈ F, ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r)) ∨
       ((∃ x ∈ F, ∃ u ∈ B ∪ C, G.Adj x u) ∧
        (∃ x ∈ F, ∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj x r))) := by
    by_cases hleft : ∃ x ∈ F, ∃ u ∈ A ∪ C, G.Adj x u
    · by_cases hrung : ∃ x ∈ F, ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r
      · exact Or.inl ⟨hleft, hrung⟩
      · right
        have hnotA : ¬ attachments G F (staircaseVertices A C B R₀) ⊆ A ∪ {a₀} := by
          intro hsubA
          exact hFnonlocal' (Or.inr (Or.inr (Or.inl hsubA)))
        obtain ⟨u, huatt, huout⟩ := Set.not_subset.mp hnotA
        obtain ⟨huK, x, hxF, hux⟩ := huatt
        have huBC : u ∈ B ∪ C := by
          rcases huK with huR | huS
          · have hua : u = a₀ := by
              by_contra hne
              exact hrung ⟨x, hxF, u, huR, hne, hux.symm⟩
            exact absurd (Or.inr hua) huout
          · rcases huS with huAB | huC
            · rcases huAB with huA | huB
              · exact absurd (Or.inl huA) huout
              · exact Or.inl huB
            · exact Or.inr huC
        refine ⟨⟨x, hxF, u, huBC, hux.symm⟩, ?_⟩
        have hnotS : ¬ attachments G F (staircaseVertices A C B R₀) ⊆ A ∪ B ∪ C := by
          intro hsubS
          exact hFnonlocal' (Or.inl hsubS)
        obtain ⟨r, hratt, hrout⟩ := Set.not_subset.mp hnotS
        obtain ⟨hrK, y, hyF, hry⟩ := hratt
        rcases hrK with hrR | hrS
        · have hra : r = a₀ := by
            by_contra hne
            exact hrung ⟨y, hyF, r, hrR, hne, hry.symm⟩
          exact ⟨y, hyF, r, hrR, hra ▸ hab, hry.symm⟩
        · exact absurd hrS hrout
    · right
      have hnotR : ¬ attachments G F (staircaseVertices A C B R₀) ⊆ {v : V | v ∈ R₀} := by
        intro hsubR
        exact hFnonlocal' (Or.inr (Or.inl hsubR))
      obtain ⟨u, huatt, huout⟩ := Set.not_subset.mp hnotR
      obtain ⟨huK, x, hxF, hux⟩ := huatt
      have huBC : u ∈ B ∪ C := by
        rcases huK with huR | huS
        · exact absurd huR huout
        · rcases huS with huAB | huC
          · rcases huAB with huA | huB
            · exact absurd ⟨x, hxF, u, Or.inl huA, hux.symm⟩ hleft
            · exact Or.inl huB
          · exact Or.inr huC
      refine ⟨⟨x, hxF, u, huBC, hux.symm⟩, ?_⟩
      have hnotB : ¬ attachments G F (staircaseVertices A C B R₀) ⊆ B ∪ {b₀} := by
        intro hsubB
        exact hFnonlocal' (Or.inr (Or.inr (Or.inr hsubB)))
      obtain ⟨r, hratt, hrout⟩ := Set.not_subset.mp hnotB
      obtain ⟨hrK, y, hyF, hry⟩ := hratt
      rcases hrK with hrR | hrS
      · have hrne : r ≠ b₀ := fun hrb => hrout (Or.inr hrb)
        exact ⟨y, hyF, r, hrR, hrne, hry.symm⟩
      · rcases hrS with hrAB | hrC
        · rcases hrAB with hrA | hrB
          · exact absurd ⟨y, hyF, r, Or.inl hrA, hry.symm⟩ hleft
          · exact absurd (Or.inl hrB) hrout
        · exact absurd ⟨y, hyF, r, Or.inr hrC, hry.symm⟩ hleft
  refine ⟨F, ?_⟩
  rcases horient with hleft | hright
  · let L : V → Prop := fun x => ∃ u ∈ A ∪ C, G.Adj x u
    let R : V → Prop := fun x => ∃ r ∈ R₀, r ≠ a₀ ∧ G.Adj x r
    obtain ⟨f, f₁, fk, hFf, hf, huniqL, huniqR⟩ :=
      exists_endpoint_clean_path G F L R hFconn' hleft.1 hleft.2 (by
        intro D hDF hDconn hDL hDR
        apply Set.eq_of_subset_of_ncard_le hDF
          (hFmin D ⟨hDF.trans hFsub, hDconn, ?_⟩) (Set.toFinite _)
        exact nonlocal_of_left_obstruction G A C B a₀ b₀ R₀ D hK hDL hDR)
    refine ⟨f, f₁, fk, hFsub, hFsub.trans hFoutside, hFconn', hFnonlocal',
      hproperLocal, hFf, hf, Or.inl ?_⟩
    have hf₁L : L f₁ := by
      obtain ⟨x, hxF, hxL⟩ := hleft.1
      simpa only [huniqL x hxF hxL] using hxL
    have hfkR : R fk := by
      obtain ⟨x, hxF, hxR⟩ := hleft.2
      simpa only [huniqR x hxF hxR] using hxR
    exact ⟨(by simpa only [L] using hf₁L),
      (by simpa only [L] using huniqL),
      (by simpa only [R] using hfkR),
      (by simpa only [R] using huniqR)⟩
  · let L : V → Prop := fun x => ∃ u ∈ B ∪ C, G.Adj x u
    let R : V → Prop := fun x => ∃ r ∈ R₀, r ≠ b₀ ∧ G.Adj x r
    obtain ⟨f, f₁, fk, hFf, hf, huniqL, huniqR⟩ :=
      exists_endpoint_clean_path G F L R hFconn' hright.1 hright.2 (by
        intro D hDF hDconn hDL hDR
        apply Set.eq_of_subset_of_ncard_le hDF
          (hFmin D ⟨hDF.trans hFsub, hDconn, ?_⟩) (Set.toFinite _)
        exact nonlocal_of_right_obstruction G A C B a₀ b₀ R₀ D hK hDL hDR)
    refine ⟨f, f₁, fk, hFsub, hFsub.trans hFoutside, hFconn', hFnonlocal',
      hproperLocal, hFf, hf, Or.inr ?_⟩
    have hf₁L : L f₁ := by
      obtain ⟨x, hxF, hxL⟩ := hright.1
      simpa only [huniqL x hxF hxL] using hxL
    have hfkR : R fk := by
      obtain ⟨x, hxF, hxR⟩ := hright.2
      simpa only [huniqR x hxF hxR] using hxR
    exact ⟨(by simpa only [L] using hf₁L),
      (by simpa only [L] using huniqL),
      (by simpa only [R] using hfkR),
      (by simpa only [R] using huniqR)⟩

end Workspace.ProofLemmas.MinimalNonlocalStaircaseAttachmentPath
