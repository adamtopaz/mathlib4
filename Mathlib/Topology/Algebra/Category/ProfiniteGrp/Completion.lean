/-
Copyright (c) 2026
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Profinite completion of a group
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace ProfiniteGrp

/-- A normal subgroup of finite index. -/
@[ext]
structure FiniteIndexNormalSubgroup (G : Type u) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal := by infer_instance
  finiteIndex' : toSubgroup.FiniteIndex := by infer_instance

namespace FiniteIndexNormalSubgroup

variable {G : Type u} [Group G]

instance : Coe (FiniteIndexNormalSubgroup G) (Subgroup G) :=
  ⟨fun H => H.toSubgroup⟩

instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.Normal := H.isNormal'

instance (H : FiniteIndexNormalSubgroup G) : H.toSubgroup.FiniteIndex := H.finiteIndex'

instance : LE (FiniteIndexNormalSubgroup G) :=
  ⟨fun H K => (H.toSubgroup ≤ K.toSubgroup)⟩

instance : Preorder (FiniteIndexNormalSubgroup G) where
  le H K := (H.toSubgroup ≤ K.toSubgroup)
  le_refl _ := le_rfl
  le_trans _ _ _ h₁ h₂ := le_trans h₁ h₂

instance : SmallCategory (FiniteIndexNormalSubgroup G) :=
  Preorder.smallCategory (FiniteIndexNormalSubgroup G)

end FiniteIndexNormalSubgroup

/-- The functor sending a finite-index normal subgroup to the corresponding finite quotient. -/
def finiteQuotientFunctor (G : Type u) [Group G] :
    FiniteIndexNormalSubgroup G ⥤ FiniteGrp where
  obj N := FiniteGrp.of (G ⧸ (N : Subgroup G))
  map f := FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom f))
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <|
    (QuotientGroup.map_comp_map _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm

variable (G : Type u) [Group G]

abbrev completionDiagram : FiniteIndexNormalSubgroup G ⥤ ProfiniteGrp :=
  finiteQuotientFunctor G ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The profinite completion of a group. -/
abbrev profiniteCompletion : ProfiniteGrp :=
  limit (completionDiagram G)

abbrev proj (N : FiniteIndexNormalSubgroup G) :
    profiniteCompletion G ⟶ (completionDiagram G).obj N :=
  (limitCone (completionDiagram G)).π.app N

/-- The canonical map into the profinite completion. -/
def eta : G →* profiniteCompletion G where
  toFun g := ⟨fun N => QuotientGroup.mk (s := (N : Subgroup G)) g, fun _ ↦ fun _ _ ↦ rfl⟩
  map_one' := Subtype.val_inj.mp rfl
  map_mul' _ _ := Subtype.val_inj.mp rfl

@[simp]
lemma proj_eta (N : FiniteIndexNormalSubgroup G) (g : G) :
    proj G N (eta G g) = QuotientGroup.mk (s := (N : Subgroup G)) g := rfl

@[simp]
lemma proj_hom_apply (N : FiniteIndexNormalSubgroup G) (x : profiniteCompletion G) :
    (proj G N).hom x = proj G N x := rfl

theorem denseRange_eta : DenseRange (eta G) := by
  classical
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M : Subgroup G := iInf fun (j : J) => (j.1 : Subgroup G)
  have hM : M.Normal :=
    Subgroup.normal_iInf_normal fun j => (inferInstance : (j.1 : Subgroup G).Normal)
  have hMFI : M.FiniteIndex :=
    Subgroup.finiteIndex_iInf fun j => (inferInstance : (j.1 : Subgroup G).FiniteIndex)
  let m : FiniteIndexNormalSubgroup G := { M with isNormal' := hM, finiteIndex' := hMFI }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use eta G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a := (iInf_le (fun (j : J) => (j.1 : Subgroup G)) ⟨a, a_in_J⟩).hom
  rw [← (eta G origin).property M_to_Na]
  change (finiteQuotientFunctor G).map M_to_Na (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

variable {G}

/-- The universal map to a finite target. -/
def liftFinite (F : FiniteGrp) (f : G →* F) :
    profiniteCompletion G ⟶ (forget₂ FiniteGrp ProfiniteGrp).obj F := by
  classical
  haveI : Finite f.range := inferInstance
  let N : FiniteIndexNormalSubgroup G :=
    { toSubgroup := f.ker
      isNormal' := by infer_instance
      finiteIndex' := by infer_instance }
  let Q : FiniteGrp := (finiteQuotientFunctor G).obj N
  letI : TopologicalSpace Q := ⊥
  letI : DiscreteTopology Q := ⟨rfl⟩
  letI : IsTopologicalGroup Q := {}
  letI : CompactSpace Q := inferInstance
  letI : TotallySeparatedSpace Q := inferInstance
  letI : TotallyDisconnectedSpace Q := inferInstance
  letI : TopologicalSpace F := ⊥
  letI : DiscreteTopology F := ⟨rfl⟩
  letI : IsTopologicalGroup F := {}
  letI : CompactSpace F := inferInstance
  letI : TotallySeparatedSpace F := inferInstance
  letI : TotallyDisconnectedSpace F := inferInstance
  let fbar : Q →* F := by
    simpa using (QuotientGroup.kerLift f)
  let fbar_cont : Q →ₜ* F := { fbar with continuous_toFun := by continuity }
  exact proj G N ≫ ofHom fbar_cont

@[simp]
lemma liftFinite_eta (F : FiniteGrp) (f : G →* F) (g : G) :
    liftFinite (G := G) F f (eta G g) = f g := by
  classical
  haveI : Finite f.range := inferInstance
  let N : FiniteIndexNormalSubgroup G :=
    { toSubgroup := f.ker
      isNormal' := by infer_instance
      finiteIndex' := by infer_instance }
  have hproj : (proj G N).hom (eta G g) =
      QuotientGroup.mk (s := (N : Subgroup G)) g := by
    simpa [proj_hom_apply (G := G) N] using (proj_eta (G := G) N g)
  change (QuotientGroup.kerLift f) ((proj G N).hom (eta G g)) = f g
  rw [hproj]
  simp [N]

@[simp]
lemma liftFinite_hom_eta (F : FiniteGrp) (f : G →* F) (g : G) :
    (Hom.hom (liftFinite (G := G) F f)) (eta G g) = f g := by
  simpa using (liftFinite_eta (G := G) F f g)

theorem liftFinite_unique (F : FiniteGrp) (f : G →* F)
    (α : profiniteCompletion G ⟶ (forget₂ FiniteGrp ProfiniteGrp).obj F)
    (hα : ∀ g, α (eta G g) = f g) :
    α = liftFinite (G := G) F f := by
  apply hom_ext
  apply DFunLike.ext
  have hη : Dense (Set.range (eta G)) := by
    simpa [DenseRange] using (denseRange_eta (G := G))
  have hfun : (fun x => α x) = fun x => liftFinite (G := G) F f x := by
    refine Continuous.ext_on (s := Set.range (eta G)) hη
      α.hom.continuous_toFun (liftFinite (G := G) F f).hom.continuous_toFun ?_
    rintro _ ⟨g, rfl⟩
    calc
      α (eta G g) = f g := hα g
      _ = liftFinite (G := G) F f (eta G g) := by
        symm
        exact liftFinite_eta (G := G) F f g
  intro x
  exact congrArg (fun h => h x) hfun

variable (G)

def liftToFiniteQuotient {P : ProfiniteGrp.{u}} (f : G →* P) (U : OpenNormalSubgroup P) :
    profiniteCompletion G ⟶
      (forget₂ FiniteGrp ProfiniteGrp).obj ((toFiniteQuotientFunctor P).obj U) :=
  liftFinite (G := G) ((toFiniteQuotientFunctor P).obj U)
    ((QuotientGroup.mk' U.toSubgroup).comp f)

@[simp]
lemma toFiniteQuotientFunctor_forget_map_apply {P : ProfiniteGrp.{u}}
    {U V : OpenNormalSubgroup P} (h : U ⟶ V)
    (x : (toFiniteQuotientFunctor P).obj U) :
    ((forget₂ FiniteGrp ProfiniteGrp).map ((toFiniteQuotientFunctor P).map h)) x =
      (QuotientGroup.map _ _ (.id _) (leOfHom h)) x := rfl

@[simp]
lemma forget₂_map_ofHom_apply {X Y : Type u} [Group X] [Finite X] [Group Y] [Finite Y]
    (f : X →* Y) (x : X) :
    ((forget₂ FiniteGrp ProfiniteGrp).map (FiniteGrp.ofHom f)) x = f x := rfl

def coneToFiniteQuotients {P : ProfiniteGrp.{u}} (f : G →* P) :
    Limits.Cone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) where
  pt := profiniteCompletion G
  π :=
  { app := fun U => liftToFiniteQuotient (G := G) f U
    naturality := by
      intro U V h
      simp only [Functor.const_obj_obj, Functor.comp_obj, Functor.const_obj_map,
        Category.id_comp, Functor.comp_map]
      symm
      apply liftFinite_unique (G := G)
        ((toFiniteQuotientFunctor P).obj V)
        ((QuotientGroup.mk' V.toSubgroup).comp f)
      intro g
      have h_lift :
          (liftToFiniteQuotient (G := G) f U) (eta G g) =
            ((QuotientGroup.mk' U.toSubgroup).comp f) g := by
        simpa [liftToFiniteQuotient] using (liftFinite_eta (G := G)
          ((toFiniteQuotientFunctor P).obj U)
          ((QuotientGroup.mk' U.toSubgroup).comp f) g)
      calc
        (liftToFiniteQuotient (G := G) f U ≫
            (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp).map h)
            (eta G g) =
          ((forget₂ FiniteGrp ProfiniteGrp).map
              ((toFiniteQuotientFunctor P).map h))
            (liftToFiniteQuotient (G := G) f U (eta G g)) := by
          simp
        _ = (QuotientGroup.map _ _ (.id _) (leOfHom h))
              (((QuotientGroup.mk' U.toSubgroup).comp f) g) := by
          simpa using congrArg (QuotientGroup.map _ _ (.id _) (leOfHom h)) h_lift
        _ = ((QuotientGroup.mk' V.toSubgroup).comp f) g := by
          simp [MonoidHom.comp_apply] }

def liftToLimit {P : ProfiniteGrp.{u}} (f : G →* P) :
    profiniteCompletion G ⟶
      limit (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp) :=
  (limitConeIsLimit
      (F := toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).lift
    (coneToFiniteQuotients (G := G) f)

def lift {P : ProfiniteGrp.{u}} (f : G →* P) : profiniteCompletion G ⟶ P :=
  liftToLimit (G := G) f ≫ inv (toLimit P)

theorem lift_eta {P : ProfiniteGrp.{u}} (f : G →* P) (g : G) :
    lift (G := G) f (eta G g) = f g := by
  classical
  have hproj : (liftToLimit (G := G) f) (eta G g) =
      toLimit P (f g) := by
    apply limit_ext
    intro U
    have hfac :
        liftToLimit (G := G) f ≫
            (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U =
          liftToFiniteQuotient (G := G) f U := by
      simpa [liftToLimit] using
        (limitConeIsLimit
          (F := toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).fac
          (coneToFiniteQuotients (G := G) f) U
    have hfac' :
        (liftToLimit (G := G) f ≫
            (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U)
            (eta G g) =
          (liftToFiniteQuotient (G := G) f U) (eta G g) := by
      simpa [comp_apply] using
        congrArg (fun h => h (eta G g)) hfac
    calc
      (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U
          (liftToLimit (G := G) f (eta G g)) =
        (liftToFiniteQuotient (G := G) f U) (eta G g) := by
          simpa [comp_apply] using hfac'
      _ = ((QuotientGroup.mk' U.toSubgroup).comp f) g := by
        simpa [liftToFiniteQuotient] using
          (liftFinite_eta (G := G)
            ((toFiniteQuotientFunctor P).obj U)
            ((QuotientGroup.mk' U.toSubgroup).comp f) g)
      _ = (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U
          (toLimit P (f g)) := rfl
  have hcomp_morph :
      lift (G := G) f ≫ toLimit P = liftToLimit (G := G) f := by
    simp [lift, Category.assoc]
  have hcomp :
      (toLimit P) (lift (G := G) f (eta G g)) =
        (liftToLimit (G := G) f) (eta G g) := by
    simpa [comp_apply] using
      congrArg (fun h => h (eta G g)) hcomp_morph
  have hcomp' :
      (toLimit P) (lift (G := G) f (eta G g)) =
        (toLimit P) (f g) := by
    simpa [hproj] using hcomp
  exact (toLimit_injective P) hcomp'

@[simp]
theorem lift_hom_eta {P : ProfiniteGrp.{u}} (f : G →* P) (g : G) :
    (Hom.hom (lift (G := G) f)) (eta G g) = f g := by
  simpa using (lift_eta (G := G) (P := P) f g)

theorem lift_unique {P : ProfiniteGrp.{u}} (f : G →* P)
  (α : profiniteCompletion G ⟶ P) (hα : ∀ g, α (eta G g) = f g) :
    α = lift (G := G) f := by
  apply hom_ext
  apply DFunLike.ext
  intro x
  apply (toLimit_injective P)
  have h₁ : (toLimit P) (α x) =
      (liftToLimit (G := G) f) x := by
    apply limit_ext
    intro U
    have hcomp' :
        (α ≫ toLimit P ≫
          (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U) =
        (liftToFiniteQuotient (G := G) f U) := by
      apply liftFinite_unique (G := G)
        ((toFiniteQuotientFunctor P).obj U)
        ((QuotientGroup.mk' U.toSubgroup).comp f)
      intro g
      calc
        (α ≫ toLimit P ≫
            (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U)
            (eta G g) =
          (toLimit P ≫
            (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U)
            (α (eta G g)) := by
          simp
        _ = (toLimit P ≫
            (limitCone (toFiniteQuotientFunctor P ⋙ forget₂ FiniteGrp ProfiniteGrp)).π.app U)
            (f g) := by
          rw [hα g]
        _ = ((QuotientGroup.mk' U.toSubgroup).comp f) g := by
          rfl
    simpa [comp_apply] using congrArg (fun h => h x) hcomp'
  have h₂ :
      (toLimit P) (lift (G := G) f x) =
        (liftToLimit (G := G) f) x := by
    have hcomp_morph :
        lift (G := G) f ≫ toLimit P = liftToLimit (G := G) f := by
      simp [lift, Category.assoc]
    simpa [comp_apply] using congrArg (fun h => h x) hcomp_morph
  calc
    (toLimit P) (α x) = (liftToLimit (G := G) f) x := h₁
    _ = (toLimit P) (lift (G := G) f x) := by
      symm
      exact h₂

end ProfiniteGrp

namespace GrpCat

open ProfiniteGrp

/-- The profinite completion functor. -/
def profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  obj G := ProfiniteGrp.profiniteCompletion (G := (G : Type u))
  map := fun {G H} f =>
    lift (G := (G : Type u))
      ((eta (G := (H : Type u))).comp f.hom)
  map_id := by
    intro G
    symm
    apply lift_unique (G := (G : Type u))
      (P := ProfiniteGrp.profiniteCompletion (G := (G : Type u)))
      (f := eta (G := (G : Type u)))
    intro g
    simp
  map_comp := by
    intro G H K f g
    symm
    apply lift_unique (G := (G : Type u))
      (P := ProfiniteGrp.profiniteCompletion (G := (K : Type u)))
      (f := (eta (G := (K : Type u))).comp (g.hom.comp f.hom))
    intro x
    have h₁ :
        lift (G := (G : Type u))
            ((eta (G := (H : Type u))).comp f.hom)
            (eta (G := (G : Type u)) x) =
          eta (G := (H : Type u)) (f.hom x) := by
      simpa using
        (lift_hom_eta (G := (G : Type u))
          (P := ProfiniteGrp.profiniteCompletion (G := (H : Type u)))
          ((eta (G := (H : Type u))).comp f.hom) x)
    have h₂ :
        lift (G := (H : Type u))
            ((eta (G := (K : Type u))).comp g.hom)
            (eta (G := (H : Type u)) (f.hom x)) =
          eta (G := (K : Type u)) (g.hom (f.hom x)) := by
      simpa using
        (lift_hom_eta (G := (H : Type u))
          (P := ProfiniteGrp.profiniteCompletion (G := (K : Type u)))
          ((eta (G := (K : Type u))).comp g.hom) (f.hom x))
    calc
      (lift (G := (G : Type u))
          ((eta (G := (H : Type u))).comp f.hom) ≫
        lift (G := (H : Type u))
          ((eta (G := (K : Type u))).comp g.hom))
          (eta (G := (G : Type u)) x) =
        lift (G := (H : Type u))
          ((eta (G := (K : Type u))).comp g.hom)
          (eta (G := (H : Type u)) (f.hom x)) := by
        simpa [comp_apply] using
          congrArg
            (ProfiniteGrp.Hom.hom (lift (G := (H : Type u))
              ((eta (G := (K : Type u))).comp g.hom))) h₁
      _ = eta (G := (K : Type u)) (g.hom (f.hom x)) := h₂

/-- The unit of the profinite completion adjunction. -/
def profiniteCompletionUnit (G : GrpCat.{u}) :
    G ⟶ (forget₂ ProfiniteGrp GrpCat).obj (profiniteCompletion.obj G) :=
  GrpCat.ofHom (eta (G := (G : Type u)))

def profiniteCompletionHomEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) :
    (profiniteCompletion.obj G ⟶ P) ≃
      (G ⟶ (forget₂ ProfiniteGrp GrpCat).obj P) where
  toFun α := profiniteCompletionUnit G ≫ (forget₂ ProfiniteGrp GrpCat).map α
  invFun f := lift (G := (G : Type u)) f.hom
  left_inv α := by
    symm
    apply lift_unique (G := (G : Type u)) (P := P)
      (f := (profiniteCompletionUnit G ≫ (forget₂ ProfiniteGrp GrpCat).map α).hom)
    intro g
    rfl
  right_inv f := by
    apply GrpCat.ext
    intro g
    change (ProfiniteGrp.Hom.hom (lift (G := (G : Type u)) f.hom))
        (eta (G := (G : Type u)) g) = f.hom g
    simpa using (lift_hom_eta (G := (G : Type u)) (P := P) f.hom g)

/-- The profinite completion adjunction. -/
def profiniteCompletionAdj : profiniteCompletion.{u} ⊣ forget₂ ProfiniteGrp GrpCat :=
  Adjunction.mkOfHomEquiv
    { homEquiv := profiniteCompletionHomEquiv
      homEquiv_naturality_left_symm := by
        intro G H P f g
        symm
        apply lift_unique (G := (G : Type u)) (P := P)
          (f := g.hom.comp f.hom)
        intro x
        have h₁ :
            profiniteCompletion.map f (eta (G := (G : Type u)) x) =
              eta (G := (H : Type u)) (f.hom x) := by
          simpa [profiniteCompletion] using
            (lift_hom_eta (G := (G : Type u))
              (P := ProfiniteGrp.profiniteCompletion (G := (H : Type u)))
              ((eta (G := (H : Type u))).comp f.hom) x)
        have h₂ :
            (H.profiniteCompletionHomEquiv P).symm g
                (eta (G := (H : Type u)) (f.hom x)) =
              (g.hom.comp f.hom) x := by
          simpa [profiniteCompletionHomEquiv, MonoidHom.comp_apply] using
            (lift_hom_eta (G := (H : Type u)) (P := P) g.hom (f.hom x))
        calc
          (profiniteCompletion.map f ≫ (H.profiniteCompletionHomEquiv P).symm g)
              (eta (G := (G : Type u)) x) =
            (H.profiniteCompletionHomEquiv P).symm g
              (profiniteCompletion.map f (eta (G := (G : Type u)) x)) := by
            simp
          _ = (H.profiniteCompletionHomEquiv P).symm g
              (eta (G := (H : Type u)) (f.hom x)) := by
            simpa using
              congrArg (fun y => (H.profiniteCompletionHomEquiv P).symm g y) h₁
          _ = (g.hom.comp f.hom) x := h₂ }

end GrpCat
