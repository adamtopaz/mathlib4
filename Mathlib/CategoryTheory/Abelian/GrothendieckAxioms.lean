import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Tactic


import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Tactic

import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.CompleteLattice

namespace CategoryTheory
open Limits
open Classical

universe v u

class AB4 (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] where
  preservesFiniteLimits :
    ∀ (α : Type v), PreservesFiniteLimits (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐)

instance (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] [AB4 𝓐]
    (α : Type v) : PreservesFiniteLimits (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) :=
  AB4.preservesFiniteLimits _

class AB5 (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] where
  preservesFiniteLimits :
    ∀ (J : Type v) [SmallCategory J] [IsFiltered J],
    PreservesFiniteLimits (colim : (J ⥤ 𝓐) ⥤ 𝓐)

instance (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] [AB5 𝓐]
    (J : Type v) [SmallCategory J] [IsFiltered J] :
    PreservesFiniteLimits (colim : (J ⥤ 𝓐) ⥤ 𝓐) :=
  AB5.preservesFiniteLimits _

/-- The diagram of all finite coproducts corresponding to subsets of α-/
@[simps]
noncomputable
def finsetCoproductColimitDiagram {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐]
  (X : α → 𝓐) [HasFiniteCoproducts 𝓐] : Finset α ⥤ 𝓐 where
    obj S := ∐ (fun s : S => X s)
    map {S T : Finset α} (i : S ⟶ T) :=
      Sigma.desc fun s => Sigma.ι (fun t : T => X t) ⟨s.1, i.le s.2⟩

@[simps]
noncomputable
def finsetCoproductColimitCocone {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] (X : α → 𝓐)
  [HasColimits 𝓐] :
    Cocone (finsetCoproductColimitDiagram X) where
  pt := ∐ X
  ι := {
    app := fun S => Sigma.desc fun i => Sigma.ι _ i.1 }


@[simps]
noncomputable
def finsetCoproductColimitCoconeIsColimit {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐]
  [HasColimits 𝓐] (X : α → 𝓐) :
    IsColimit (finsetCoproductColimitCocone X) where
  desc S :=
    Sigma.desc fun a => (Sigma.ι (fun b : ({a} : Finset α) => X b) ⟨a, by simp⟩) ≫ S.ι.app {a}
  fac := fun c S => by
    apply Sigma.hom_ext ; rintro ⟨b,hb⟩
    let e : ({b} : Finset α) ⟶ S := homOfLE (by simpa using hb)
    simp [← c.w e]
  uniq :=  fun _ _ h => by
    apply Sigma.hom_ext ; intro s
    simp [←(h {s})]

/-- Colimit of finsetCoproductColimitDiagram is infact a coproduct-/
@[simps!]
noncomputable
def coproductIsoFinsetCoproductColimitDiagramColimit {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐]
    (X : α → 𝓐) [HasColimits 𝓐] : ∐ X ≅ colimit (finsetCoproductColimitDiagram X) :=
  (finsetCoproductColimitCoconeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

@[simps]
noncomputable
def finsetCoproductDiagramNatTrans {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐]
  {X Y : α → 𝓐} (η : X ⟶ Y) :
    finsetCoproductColimitDiagram X ⟶ finsetCoproductColimitDiagram Y where
  app S := Limits.Sigma.map fun b => η b


--*** should this be put into discrete or finset, left here or moved to some other place?

/-- Functor sending a functor inducing a colimit in 𝓐 indexed by α to the functor from Finset α
    sending all finite sets to finite coproducts-/
@[simps]
noncomputable
def discreteToFinset (α : Type v) (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] :
    (Discrete α ⥤ 𝓐) ⥤ (Finset α ⥤ 𝓐) where
  obj := fun F => finsetCoproductColimitDiagram (fun j => F.obj ⟨j⟩)
  map := fun {F G} f => finsetCoproductDiagramNatTrans (fun j => f.app _)


namespace preservesLimitAux

open CategoryTheory Limits


-- *** I am not sure if this should be left here or moved to Biproducts

noncomputable
abbrev Sigma.isoBiproduct {C : Type _} [Category C] {α : Type _}
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X]:
    ∐ X ≅ ⨁ X :=
  colimit.isColimit _ |>.coconePointUniqueUpToIso (biproduct.isColimit _)

noncomputable
abbrev Sigma.lift {C : Type _} [Category C] {α : Type _}
  {X : α → C} [HasZeroMorphisms C] [HasBiproduct X] {P : C} (p : ∀ (a : α), P ⟶ X a) :
    P ⟶ ∐ X :=
  biproduct.lift p ≫ (Sigma.isoBiproduct _).inv

noncomputable
def Sigma.π {C : Type _} [Category C] {α : Type _}
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] (a : α) : ∐ X ⟶ X a :=
  (Sigma.isoBiproduct _).hom ≫ biproduct.π _ _

lemma Sigma.ι_π {C : Type _} [Category C] [HasZeroMorphisms C] {α : Type _} (X : α → C) (a : α)
  [HasBiproduct X] : Sigma.ι X a ≫ Sigma.π X a = 𝟙 _ := by {dsimp only [Sigma.π] ; simp}

@[reassoc (attr := simp)]
lemma Sigma.lift_π {C : Type _} [Category C] {α : Type _}
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] {Z : C} (f : (a : α) → (Z ⟶ X a)) (a) :
   Sigma.lift f ≫ Sigma.π _ a = f _ := by simp [Sigma.lift, Sigma.π]

lemma Sigma.hom_ext' {C : Type _} [Category C] {α : Type _}
  (X : α → C) [HasZeroMorphisms C] [HasBiproduct X] {Z : C} (f g : Z ⟶ ∐ X)
  (h : ∀ a, f ≫ Sigma.π _ a = g ≫ Sigma.π _ a) : f = g := by
    rw [← cancel_mono (Sigma.isoBiproduct _).hom]
    apply biproduct.hom_ext
    intro j
    simpa using h j


/--
    *** Thus K ⋙ discreteToFinset α 𝓐 sends j to "K j q" effectively
    Cone where our maps -/
@[simps]
noncomputable
def evalCone {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] {J : Type} [SmallCategory J]
  [FinCategory J] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] {K : J ⥤ Discrete α ⥤ 𝓐}
  (T : Cone (K ⋙ discreteToFinset α 𝓐)) {A : Finset α} (q : α) (hq : q ∈ A) :
    Cone (K ⋙ (evaluation (Discrete α) 𝓐).obj ⟨q⟩) where
    --***removed _ _ to make more readable
  pt := T.pt.obj A
  π := {
    app := fun j => (T.π.app j).app A ≫ Sigma.π (fun s : A => (K.obj j).obj ⟨s⟩) ⟨q, hq⟩
    naturality := fun i j f => by
      have Tw := T.w f
      apply_fun (fun e => e.app A) at Tw
      simp [← Tw, Sigma.π]
      congr 1
      apply Sigma.hom_ext ; intro b
      simp [biproduct.ι_π, biproduct.ι_π_assoc]
      split_ifs with h
      · subst h ; simp
      · simp
  }

@[simps]
noncomputable
def lift {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] [HasFiniteLimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] {J : Type} [SmallCategory J] [FinCategory J]
  {K : J ⥤ Discrete α ⥤ 𝓐} {E : Cone K} (hE : IsLimit E) (T : Cone (K ⋙ discreteToFinset α 𝓐)) :
    T.pt ⟶ ((discreteToFinset α 𝓐).mapCone E).pt where
  app := fun A => Sigma.lift fun ⟨q, hq⟩ =>
    (isLimitOfPreserves ((evaluation (Discrete α) 𝓐).obj { as := q }) hE).lift (evalCone T q hq)
  naturality := fun i j f => by
    dsimp
    apply Sigma.hom_ext' ; rintro ⟨a, ha⟩
    let E' := ((evaluation (Discrete α) 𝓐).obj { as := a }).mapCone E
    let hE' : IsLimit E' := (isLimitOfPreserves ((evaluation (Discrete α) 𝓐).obj { as := a }) hE)
    apply hE'.hom_ext
    intro jj
    simp only [hE'.fac, hE'.fac_assoc, Sigma.π, evaluation_obj_obj, evaluation_obj_map,
      Category.assoc, biproduct.isoCoproduct_hom, Iso.inv_hom_id_assoc, biproduct.lift_π_assoc,
      Iso.inv_hom_id_assoc, biproduct.lift_π_assoc, isLimitOfPreserves]
    dsimp [Sigma.isoBiproduct, IsColimit.coconePointUniqueUpToIso]
    have := (PreservesLimit.preserves hE).fac (evalCone T a ha) jj
    dsimp at this
    rw [this]
    sorry




end preservesLimitAux

namespace preservesColimitAux

/--
    *** K ⋙ discreteToFinset α 𝓐 sends j to "K j q" effectively
    Cocone given cocone T, where our maps come from the -/
@[simps]
noncomputable
def evalCocone {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] {J : Type} [SmallCategory J]
  [FinCategory J] {K : J ⥤ Discrete α ⥤ 𝓐} (T : Cocone (K ⋙ discreteToFinset α 𝓐))
  {A : Finset α} (q : α) (hq : q ∈ A) :
    Cocone (K ⋙ (evaluation (Discrete α) 𝓐).obj ⟨q⟩) where
    --***removed _ _ to make more readable
  pt := T.pt.obj A
  ι := {
    app := fun j => Sigma.ι (fun (s : A) => (K.obj j).obj ⟨s⟩) ⟨q,hq⟩ ≫ (T.ι.app j).app A
    naturality := fun i j f => by simp [← (T.w f)]
  }

@[simps]
noncomputable
def desc {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] {J : Type} [SmallCategory J]
  [FinCategory J] {K : J ⥤ Discrete α ⥤ 𝓐} {E : Cocone K} (hE : IsColimit E)
  (T : Cocone (K ⋙ discreteToFinset α 𝓐)) :
    ((discreteToFinset α 𝓐).mapCocone E).pt ⟶ T.pt where
  app := fun A => Sigma.desc fun ⟨q, hq⟩ =>
    (isColimitOfPreserves ((evaluation (Discrete α) 𝓐).obj { as := q }) hE).desc (evalCocone T q hq)
  naturality := fun A B f => by
    dsimp only [Functor.mapCocone_pt, discreteToFinset_obj, finsetCoproductColimitDiagram_map]
    apply Sigma.hom_ext ; rintro ⟨a,ha⟩
    simp only [colimit.ι_desc_assoc, Cofan.mk_ι_app, colimit.ι_desc]
    let E' := ((evaluation (Discrete α) 𝓐).obj { as := a }).mapCocone E
    let hE' : IsColimit E' := (isColimitOfPreserves _ hE)
    apply hE'.hom_ext ; intro j
    simp only [hE'.fac, hE'.fac_assoc]
    simp [← NatTrans.naturality]

end preservesColimitAux

noncomputable
instance preservesLimitsOfShapeDiscreteToFinset (α : Type v) {𝓐 : Type u} [Category.{v} 𝓐]
  [HasColimits 𝓐] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐]
  (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (discreteToFinset α 𝓐) where
  preservesLimit {K} := {
    preserves := fun E {hE} => {
      lift := fun T => preservesLimitAux.lift hE T
      fac := sorry
      uniq := sorry
    }
  }

noncomputable
instance preservesColimitsOfShapeDiscreteToFinset (α : Type v) {𝓐 : Type u} [Category.{v} 𝓐]
  [HasColimits 𝓐] (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesColimitsOfShape J (discreteToFinset α 𝓐) where
  preservesColimit {K} := {
    preserves := fun {E} hE => {
      desc := fun T => preservesColimitAux.desc _ _
      fac := fun S j => by
        ext A
        apply colimit.hom_ext ; rintro ⟨a,ha⟩
        simp only [Functor.mapCocone_ι_app, discreteToFinset_map, NatTrans.comp_app,
          finsetCoproductDiagramNatTrans_app, preservesColimitAux.desc_app, colimit.map_desc,
          colimit.ι_desc]
        dsimp only [Cocones.precompose_obj_ι, NatTrans.comp_app, Cofan.mk_ι_app]
        let E' := ((evaluation (Discrete α) 𝓐).obj { as := a }).mapCocone E
        let hE' : IsColimit E' := (isColimitOfPreserves _ hE)
        change E'.ι.app _ ≫ _ = _
        rw [hE'.fac]
        simp
      uniq := fun S m hm => by
        ext A
        dsimp only [preservesColimitAux.desc_app]
        apply Sigma.hom_ext ; rintro ⟨a,ha⟩
        simp only [colimit.ι_desc]
        dsimp only [Cofan.mk_ι_app]
        let E' := ((evaluation (Discrete α) 𝓐).obj { as := a }).mapCocone E
        let hE' : IsColimit E' := (isColimitOfPreserves _ hE)
        apply hE'.hom_ext ; intro j
        rw [hE'.fac]
        simp [← hm]
    }
  }

noncomputable
instance (α : Type v) {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] [HasZeroMorphisms 𝓐]
  [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐] :
    PreservesFiniteLimits (discreteToFinset α 𝓐) where
  preservesFiniteLimits := fun _ => inferInstance

noncomputable
def colimDiscreteToFinsetCompColimIso (α : Type v) (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐]:
    (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) ≅
    discreteToFinset α 𝓐 ⋙ colim :=
    NatIso.ofComponents (fun F =>
    HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))
    ≪≫ coproductIsoFinsetCoproductColimitDiagramColimit _) <| by
  rintro ⟨x⟩ ⟨y⟩ f
  apply colimit.hom_ext
  rintro ⟨j⟩
  dsimp [Function.comp]
  simp

noncomputable
instance (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐] [AB5 𝓐] : AB4 𝓐 where
    preservesFiniteLimits := fun α => {
      preservesFiniteLimits := fun _ => {
        preservesLimit :=
          fun {K} => preservesLimitOfNatIso K (colimDiscreteToFinsetCompColimIso α 𝓐).symm
      }
    }

end CategoryTheory
