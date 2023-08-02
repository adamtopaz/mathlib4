import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Filtered
import Mathlib.CategoryTheory.Limits.FunctorCategory
import Mathlib.Tactic

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
def finsetBiproductDiagram {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐]
  (X : α → 𝓐) [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐]: Finset α ⥤ 𝓐 where
    obj S := ⨁ (fun s : S => X s)
    map {S T : Finset α} (i : S ⟶ T) :=
      biproduct.desc fun s => biproduct.ι (fun t : T => X t) ⟨s.1, i.le s.2⟩

@[simps]
noncomputable
def finsetBiproductColimitCocone {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] (X : α → 𝓐)
  [HasColimits 𝓐] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] :
    Cocone (finsetBiproductDiagram X) where
  pt := ∐ X
  ι := {
    app := fun S => biproduct.desc fun ⟨x, hx ⟩  => Sigma.ι _ _ }

@[simps]
noncomputable
def finsetCoproductColimitCoconeIsColimit {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐]
  [HasColimits 𝓐] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] (X : α → 𝓐) :
    IsColimit (finsetBiproductColimitCocone X) where
  desc S :=
    Sigma.desc fun a => (biproduct.ι (fun b : ({a} : Finset α) => X b) ⟨a, by simp⟩) ≫ S.ι.app {a}
  fac := fun c S => by
    apply biproduct.hom_ext' ; rintro ⟨b,hb⟩
    let e : ({b} : Finset α) ⟶ S := homOfLE (by simpa using hb)
    simp [← c.w e]
  uniq :=  fun _ _ h => by
    apply Sigma.hom_ext ; intro s
    simp [←(h {s})]

/-- Colimit of finsetBiproductDiagram is infact a coproduct-/
@[simps!]
noncomputable
def coproductIsoColimitFinsetBiproduct {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] (X : α → 𝓐) [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] :
    ∐ X ≅ colimit (finsetBiproductDiagram X) :=
  (finsetCoproductColimitCoconeIsColimit X).coconePointUniqueUpToIso (colimit.isColimit _)

@[simps]
noncomputable
def finsetBiproductDiagramNatTrans {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] {X Y : α → 𝓐} (η : X ⟶ Y) :
    finsetBiproductDiagram X ⟶ finsetBiproductDiagram Y where
  app S := biproduct.map fun b => η b
  naturality := fun X Y f => by
    simp only [finsetBiproductDiagram_obj]
    ext i j
    simp [biproduct.ι_π, biproduct.ι_π_assoc]
    split_ifs with h
    · subst h ; simp
    · simp


/-- Functor sending a functor inducing a colimit in 𝓐 indexed by α to the functor from Finset α
    sending all finite sets to finite coproducts-/
@[simps]
noncomputable
def discreteToFinset (α : Type v) (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] :
    (Discrete α ⥤ 𝓐) ⥤ (Finset α ⥤ 𝓐) where
  obj := fun F => finsetBiproductDiagram (fun j => F.obj ⟨j⟩)
  map := fun {F G} f => finsetBiproductDiagramNatTrans (fun j => f.app _)

namespace preservesLimitAux

/--
    *** Thus K ⋙ discreteToFinset α 𝓐 sends j to "K j q" effectively
    Cone where our maps -/
@[simps]
noncomputable
def evalCone {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] {J : Type}
  [SmallCategory J] [FinCategory J] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐]
  {K : J ⥤ Discrete α ⥤ 𝓐} (T : Cone (K ⋙ discreteToFinset α 𝓐)) {A : Finset α} (q : α)
  (hq : q ∈ A) :
    Cone (K ⋙ (evaluation _ _).obj ⟨q⟩) where
  pt := T.pt.obj A
  π := {
    app := fun j => (T.π.app j).app A ≫ biproduct.π (fun s : A => (K.obj j).obj ⟨s⟩) ⟨q, hq⟩
    naturality := fun i j f => by simp [← T.w f]
  }

@[simps]
noncomputable
def lift {α : Type v} {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] [HasFiniteLimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] {J : Type} [SmallCategory J] [FinCategory J]
  {K : J ⥤ Discrete α ⥤ 𝓐} {E : Cone K} (hE : IsLimit E) (T : Cone (K ⋙ discreteToFinset α 𝓐)) :
    T.pt ⟶ ((discreteToFinset α 𝓐).mapCone E).pt where
  app := fun A => biproduct.lift fun ⟨q, hq⟩ =>
    (isLimitOfPreserves ((evaluation (Discrete α) 𝓐).obj { as := q }) hE).lift (evalCone T q hq)
  naturality := fun i j f => sorry

end preservesLimitAux

noncomputable
instance preservesLimitsOfShapeDiscreteToFinset (α : Type v) {𝓐 : Type u} [Category.{v} 𝓐]
  [HasColimits 𝓐] [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐]
  (J : Type) [SmallCategory J] [FinCategory J] :
    PreservesLimitsOfShape J (discreteToFinset α 𝓐) where
  preservesLimit {K} := {
    preserves := fun E {hE} => {
      lift := fun T => preservesLimitAux.lift hE T
      fac := fun s j => by
        ext A
        apply biproduct.hom_ext ; rintro ⟨a, ha⟩
        have := (PreservesLimit.preserves hE).fac (preservesLimitAux.evalCone s a ha) j
        dsimp at this
        rw [←this]
        simp only [NatTrans.comp_app, preservesLimitAux.lift_app]
        dsimp only [isLimitOfPreserves]
        simp
      uniq := fun s m hh => by
        ext A
        simp only [preservesLimitAux.lift_app]
        dsimp only [isLimitOfPreserves]
        apply biproduct.hom_ext ; rintro ⟨a, ha⟩
        let E' := ((evaluation (Discrete α) 𝓐).obj { as := a }).mapCone E
        let hE' : IsLimit E' :=
          (isLimitOfPreserves ((evaluation (Discrete α) 𝓐).obj { as := a }) hE)
        apply hE'.hom_ext ; intro jj
        simp only [Functor.mapCone_π_app, evaluation_obj_map, biproduct.lift_π]
        have := (PreservesLimit.preserves hE).fac (preservesLimitAux.evalCone s a ha) jj
        dsimp at this
        rw [this]
        simp [← (hh jj)]
    }
  }

noncomputable
instance (α : Type v) {𝓐 : Type u} [Category.{v} 𝓐] [HasColimits 𝓐] [HasZeroMorphisms 𝓐]
  [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐] :
    PreservesFiniteLimits (discreteToFinset α 𝓐) where
  preservesFiniteLimits := fun _ => inferInstance

noncomputable
def colimIsoDiscreteToFinsetCompColim (α : Type v) (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] :
    (colim : (Discrete α ⥤ 𝓐) ⥤ 𝓐) ≅ discreteToFinset α 𝓐 ⋙ colim :=
  NatIso.ofComponents (fun F => HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := F))
  ≪≫ coproductIsoColimitFinsetBiproduct _) <| by
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
        preservesLimit := fun {K} =>
          preservesLimitOfNatIso K (colimIsoDiscreteToFinsetCompColim α 𝓐).symm
      }
    }

end CategoryTheory
