--import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib

namespace CategoryTheory
open Limits

universe v u

instance {C : Type u} [Category.{v} C] {J : Type v} [SmallCategory J]
  [HasColimitsOfShape J C] :
  PreservesColimits (colim : (J ⥤ C) ⥤ C) := inferInstance

class AB4 (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐] where
  preservesFiniteLimits :
    ∀ (α : Type v), PreservesFiniteLimits (colim : (Discrete α ⥤ 𝓐)  ⥤ 𝓐)

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

instance (𝓐 : Type u) [Category.{v} 𝓐] [HasColimits 𝓐]
  [HasZeroMorphisms 𝓐] [HasFiniteBiproducts 𝓐] [HasFiniteLimits 𝓐] [AB5 𝓐] : AB4 𝓐 := sorry

end CategoryTheory
