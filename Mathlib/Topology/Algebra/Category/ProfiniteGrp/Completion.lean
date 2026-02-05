module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Profinite completion of groups

We define the profinite completion of a group as the projective limit of its finite quotients,
construct the canonical map `eta`, and establish the universal property via an adjunction.
-/

@[expose] public section

namespace ProfiniteGrp

open CategoryTheory

universe u

/-- A normal subgroup of `G` of finite index. -/
structure FiniteIndexSubgroup (G : Type*) [Group G] extends Subgroup G where
  isNormal' : toSubgroup.Normal
  isFiniteIndex' : toSubgroup.FiniteIndex

instance (G : Type*) [Group G] : Coe (FiniteIndexSubgroup G) (Subgroup G) where
  coe G := G.toSubgroup

instance (G : Type*) [Group G] (H : FiniteIndexSubgroup G) : (H : Subgroup G).Normal := 
  H.isNormal'

instance (G : Type*) [Group G] (H : FiniteIndexSubgroup G) : (H : Subgroup G).FiniteIndex := 
  H.isFiniteIndex'

instance (G : Type*) [Group G] : Preorder (FiniteIndexSubgroup G) where
  le A B := A.toSubgroup ≤ B.toSubgroup
  le_refl _ := le_refl _
  le_trans _ _ _ h1 h2 := le_trans h1 h2
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

namespace ProfiniteCompletion

variable (G : GrpCat.{u})

/-- The diagram of finite quotients indexed by finite-index normal subgroups of `G`. -/
def finiteGrpDiagram : FiniteIndexSubgroup G ⥤ FiniteGrp.{u} where
  obj H := FiniteGrp.of <| G ⧸ H.toSubgroup
  map f := FiniteGrp.ofHom <| QuotientGroup.map _ _ (MonoidHom.id _) f.le
  map_id H := by ext ⟨x⟩ ; rfl
  map_comp f g := by ext ⟨x⟩ ; rfl

/-- The finite-quotient diagram viewed in `ProfiniteGrp`. -/
def diagram : FiniteIndexSubgroup G ⥤ ProfiniteGrp.{u} :=
  finiteGrpDiagram _ ⋙ forget₂ _ _

/-- The profinite completion of `G` as a projective limit. -/
def completion : ProfiniteGrp.{u} := limit (diagram G)

/-- The canonical map from `G` to its profinite completion, as a function. -/
def etaFn (x : G) : completion G := ⟨fun _ => QuotientGroup.mk x, fun _ _ _ => rfl⟩

/-- The canonical morphism from `G` to its profinite completion. -/
def eta : G ⟶ GrpCat.of (completion G) := GrpCat.ofHom {
  toFun := etaFn G
  map_one' := rfl
  map_mul' _ _ := rfl
}

lemma denseRange : DenseRange (etaFn G) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  simp_rw [← hsv, Set.mem_preimage] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  classical
  let M : Subgroup G := iInf fun (j : J) => (j.1 : Subgroup G)
  have hM : M.Normal :=
    Subgroup.normal_iInf_normal fun j => (inferInstance : (j.1 : Subgroup G).Normal)
  have hMFinite : M.FiniteIndex := by
    simpa [M] using
      (Subgroup.finiteIndex_iInf (ι := J) (f := fun j : J => (j.1 : Subgroup G))
        (hf := fun j => (inferInstance : (j.1 : Subgroup G).FiniteIndex)))
  let m : FiniteIndexSubgroup G := { toSubgroup := M, isNormal' := hM, isFiniteIndex' := hMFinite }
  rcases QuotientGroup.mk'_surjective M (spc m) with ⟨origin, horigin⟩
  use etaFn G origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) => (j.1 : Subgroup G)) ⟨a, a_in_J⟩).hom
  rw [← (etaFn G origin).property M_to_Na]
  change (diagram G).map M_to_Na (QuotientGroup.mk' M origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

variable {G}
variable {P : ProfiniteGrp.{u}}

/-- The preimage of an open normal subgroup under a morphism to a profinite group. -/
def preimage (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) : FiniteIndexSubgroup G where
  toSubgroup := H.toSubgroup.comap f.hom
  isNormal' := Subgroup.normal_comap (GrpCat.Hom.hom f)
  isFiniteIndex' := by
    classical
    let g : G →* (P ⧸ H.toSubgroup) := (QuotientGroup.mk' H.toSubgroup).comp f.hom
    have hker : (H.toSubgroup.comap f.hom) = g.ker := by
      simpa [g, QuotientGroup.ker_mk'] using
        (MonoidHom.comap_ker (g := QuotientGroup.mk' H.toSubgroup) (f := f.hom))
    haveI : Finite g.range := by infer_instance
    simpa [hker] using (inferInstance : g.ker.FiniteIndex)

/-- Monotonicity of `preimage` in the subgroup argument. -/
def preimage_le {f : G ⟶ GrpCat.of P} {H K : OpenNormalSubgroup P}
    (h : H ≤ K) : preimage f H ≤ preimage f K := fun _ hx => h hx

/-- The induced map on finite quotients coming from a morphism to `P`. -/
def quotientMap (f : G ⟶ GrpCat.of P) (H : OpenNormalSubgroup P) :
    FiniteGrp.of (G ⧸ (preimage f H).toSubgroup) ⟶ FiniteGrp.of (P ⧸ H.toSubgroup) :=
  FiniteGrp.ofHom <| QuotientGroup.map _ _ f.hom <| fun _ h => h

/-- The universal morphism from the profinite completion to `P`. -/
noncomputable
def lift (f : G ⟶ GrpCat.of P) : completion G ⟶ P :=
  P.isLimitCone.lift ⟨_, {
    app H := (limitCone (diagram G)).π.app _ ≫ (ofFiniteGrpHom <| quotientMap f H)
    naturality := by
      intro X Y g
      ext ⟨x,hx⟩
      change quotientMap f Y (x <| preimage f Y) = 
        P.diagram.map g (quotientMap _ _ <| x <| preimage f X)
      have := hx <| preimage_le (f := f) g.le |>.hom
      obtain ⟨t, ht⟩ : ∃ g : G, QuotientGroup.mk g = x (preimage f X) := 
        Quot.exists_rep (x (preimage f X))
      rw [← this, ← ht]
      have := P.cone.π.naturality g
      apply_fun fun q => q (f t) at this
      exact this
  }⟩

@[reassoc (attr := simp)]
lemma lift_eta (f : G ⟶ GrpCat.of P) : eta G ≫ (forget₂ _ _).map (lift f) = f := by
  let e := isoLimittoFiniteQuotientFunctor P
  rw [← (forget₂ ProfiniteGrp GrpCat).mapIso e |>.cancel_iso_hom_right]
  dsimp
  rw [Category.assoc, ← (forget₂ ProfiniteGrp GrpCat).map_comp (lift f) e.hom]
  change eta G ≫ ((forget₂ _ _).map ((_ ≫ e.inv) ≫ e.hom)) = _
  simp only [Category.assoc, Iso.inv_hom_id]
  rfl

lemma lift_unique (f g : completion G ⟶ P)
    (h : eta G ≫ (forget₂ _ _).map f = eta G ≫ (forget₂ _ _).map g) : f = g := by
  apply ConcreteCategory.hom_ext
  intro x
  have hfg : (fun x => f x) = fun x => g x := by
    refine (denseRange (G := G)).equalizer ?_ ?_ ?_
    · exact f.hom.continuous_toFun
    · exact g.hom.continuous_toFun
    · funext y
      simpa [GrpCat.comp_apply] using (CategoryTheory.congr_hom h y)
  exact congrFun hfg x

end ProfiniteCompletion

/-- The profinite completion functor. -/
@[simps]
noncomputable def profiniteCompletion : GrpCat.{u} ⥤ ProfiniteGrp.{u} where
  obj G := ProfiniteCompletion.completion G
  map f := ProfiniteCompletion.lift <| f ≫ ProfiniteCompletion.eta _
  map_id G := by 
    apply ProfiniteCompletion.lift_unique
    aesop_cat
  map_comp f g := by 
    apply ProfiniteCompletion.lift_unique
    aesop_cat

namespace ProfiniteCompletion

/-- The hom-set equivalence exhibiting the adjunction. -/
noncomputable
def homEquiv (G : GrpCat.{u}) (P : ProfiniteGrp.{u}) :
    (completion G ⟶ P) ≃ (G ⟶ GrpCat.of P) where
  toFun f := eta G ≫ (forget₂ _ _).map f
  invFun f := lift f
  left_inv f := by apply lift_unique ; simp
  right_inv f := by simp

/-- The profinite completion is left adjoint to the forgetful functor. -/
noncomputable
def adjunction : profiniteCompletion ⊣ forget₂ _ _ :=
  Adjunction.mkOfHomEquiv {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm f g := by 
      apply lift_unique
      simp [homEquiv]
    homEquiv_naturality_right f g := rfl
  }

end ProfiniteCompletion

end ProfiniteGrp
