/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Orientation
import Mathlib.Data.Complex.FiniteDimensional
import Mathlib.Data.Complex.Orientation
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Tactic.LinearCombination

/-!
# Oriented two-dimensional real inner product spaces

This file defines constructions specific to the geometry of an oriented two-dimensional real inner
product space `E`.

## Main declarations

* `Orientation.areaForm`: an antisymmetric bilinear form `E →ₗ[ℝ] E →ₗ[ℝ] ℝ` (usual notation `ω`).
  Morally, when `ω` is evaluated on two vectors, it gives the oriented area of the parallelogram
  they span. (But mathlib does not yet have a construction of oriented area, and in fact the
  construction of oriented area should pass through `ω`.)

* `Orientation.rightAngleRotation`: an isometric automorphism `E ≃ₗᵢ[ℝ] E` (usual notation `J`).
  This automorphism squares to -1. In a later file, rotations (`Orientation.rotation`) are defined,
  in such a way that this automorphism is equal to rotation by 90 degrees.

* `Orientation.basisRightAngleRotation`: for a nonzero vector `x` in `E`, the basis `![x, J x]`
  for `E`.

* `Orientation.kahler`: a complex-valued real-bilinear map `E →ₗ[ℝ] E →ₗ[ℝ] ℂ`. Its real part is the
  inner product and its imaginary part is `Orientation.areaForm`. For vectors `x` and `y` in `E`,
  the complex number `o.kahler x y` has modulus `‖x‖ * ‖y‖`. In a later file, oriented angles
  (`Orientation.oangle`) are defined, in such a way that the argument of `o.kahler x y` is the
  oriented angle from `x` to `y`.

## Main results

* `Orientation.rightAngleRotation_rightAngleRotation`: the identity `J (J x) = - x`

* `Orientation.nonneg_inner_and_areaForm_eq_zero_iff_sameRay`: `x`, `y` are in the same ray, if
  and only if `0 ≤ ⟪x, y⟫` and `ω x y = 0`

* `Orientation.kahler_mul`: the identity `o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y`

* `Complex.areaForm`, `Complex.rightAngleRotation`, `Complex.kahler`: the concrete
  interpretations of `areaForm`, `rightAngleRotation`, `kahler` for the oriented real inner
  product space `ℂ`

* `Orientation.areaForm_map_complex`, `Orientation.rightAngleRotation_map_complex`,
  `Orientation.kahler_map_complex`: given an orientation-preserving isometry from `E` to `ℂ`,
  expressions for `areaForm`, `rightAngleRotation`, `kahler` as the pullback of their concrete
  interpretations on `ℂ`

## Implementation notes

Notation `ω` for `Orientation.areaForm` and `J` for `Orientation.rightAngleRotation` should be
defined locally in each file which uses them, since otherwise one would need a more cumbersome
notation which mentions the orientation explicitly (something like `ω[o]`). Write

```
local notation "ω" => o.areaForm
local notation "J" => o.rightAngleRotation
```

-/


noncomputable section

open scoped RealInnerProductSpace ComplexConjugate

open Module

lemma FiniteDimensional.of_fact_finrank_eq_two {K V : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] [Fact (finrank K V = 2)] : FiniteDimensional K V :=
  .of_fact_finrank_eq_succ 1

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2))

namespace Orientation

/-- An antisymmetric bilinear form on an oriented real inner product space of dimension 2 (usual
notation `ω`). When evaluated on two vectors, it gives the oriented area of the parallelogram they
span. -/
irreducible_def areaForm : E →ₗ[ℝ] E →ₗ[ℝ] ℝ := by
  let z : E [⋀^Fin 0]→ₗ[ℝ] ℝ ≃ₗ[ℝ] ℝ :=
    AlternatingMap.constLinearEquivOfIsEmpty.symm
  let y : E [⋀^Fin 1]→ₗ[ℝ] ℝ →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.llcomp ℝ E (E [⋀^Fin 0]→ₗ[ℝ] ℝ) ℝ z ∘ₗ AlternatingMap.curryLeftLinearMap
  exact y ∘ₗ AlternatingMap.curryLeftLinearMap o.volumeForm

local notation "ω" => o.areaForm

theorem areaForm_to_volumeForm (x y : E) : ω x y = o.volumeForm ![x, y] := by simp [areaForm]

@[simp]
theorem areaForm_apply_self (x : E) : ω x x = 0 := by
  rw [areaForm_to_volumeForm]
  refine o.volumeForm.map_eq_zero_of_eq ![x, x] ?_ (?_ : (0 : Fin 2) ≠ 1)
  · simp
  · norm_num

theorem areaForm_swap (x y : E) : ω x y = -ω y x := by
  simp only [areaForm_to_volumeForm]
  convert o.volumeForm.map_swap ![y, x] (_ : (0 : Fin 2) ≠ 1)
  · ext i
    fin_cases i <;> rfl
  · norm_num

@[simp]
theorem areaForm_neg_orientation : (-o).areaForm = -o.areaForm := by
  ext x y
  simp [areaForm_to_volumeForm]

/-- Continuous linear map version of `Orientation.areaForm`, useful for calculus. -/
def areaForm' : E →L[ℝ] E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    (↑(LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ) ∘ₗ o.areaForm)

@[simp]
theorem areaForm'_apply (x : E) :
    o.areaForm' x = LinearMap.toContinuousLinearMap (o.areaForm x) :=
  rfl

theorem abs_areaForm_le (x y : E) : |ω x y| ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.abs_volumeForm_apply_le ![x, y]

theorem areaForm_le (x y : E) : ω x y ≤ ‖x‖ * ‖y‖ := by
  simpa [areaForm_to_volumeForm, Fin.prod_univ_succ] using o.volumeForm_apply_le ![x, y]

theorem abs_areaForm_of_orthogonal {x y : E} (h : ⟪x, y⟫ = 0) : |ω x y| = ‖x‖ * ‖y‖ := by
  rw [o.areaForm_to_volumeForm, o.abs_volumeForm_apply_of_pairwise_orthogonal]
  · simp [Fin.prod_univ_succ]
  intro i j hij
  fin_cases i <;> fin_cases j
  · simp_all
  · simpa using h
  · simpa [real_inner_comm] using h
  · simp_all

theorem areaForm_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).areaForm x y =
    o.areaForm (φ.symm x) (φ.symm y) := by
  have : φ.symm ∘ ![x, y] = ![φ.symm x, φ.symm y] := by
    ext i
    fin_cases i <;> rfl
  simp [areaForm_to_volumeForm, volumeForm_map, this]

/-- The area form is invariant under pullback by a positively-oriented isometric automorphism. -/
theorem areaForm_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.areaForm (φ x) (φ y) = o.areaForm x y := by
  convert o.areaForm_map φ (φ x) (φ y)
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]
  · simp
  · simp

/-- Auxiliary construction for `Orientation.rightAngleRotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
irreducible_def rightAngleRotationAux₁ : E →ₗ[ℝ] E :=
  let to_dual : E ≃ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    (InnerProductSpace.toDual ℝ E).toLinearEquiv ≪≫ₗ LinearMap.toContinuousLinearMap.symm
  ↑to_dual.symm ∘ₗ ω

@[simp]
theorem inner_rightAngleRotationAux₁_left (x y : E) : ⟪o.rightAngleRotationAux₁ x, y⟫ = ω x y := by
  simp only [rightAngleRotationAux₁, LinearEquiv.trans_symm, LinearEquiv.symm_symm,
    LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_symm_toLinearEquiv]
  rw [InnerProductSpace.toDual_symm_apply]
  norm_cast

@[simp]
theorem inner_rightAngleRotationAux₁_right (x y : E) :
    ⟪x, o.rightAngleRotationAux₁ y⟫ = -ω x y := by
  rw [real_inner_comm]
  simp [o.areaForm_swap y x]

/-- Auxiliary construction for `Orientation.rightAngleRotation`, rotation by 90 degrees in an
oriented real inner product space of dimension 2. -/
def rightAngleRotationAux₂ : E →ₗᵢ[ℝ] E :=
  { o.rightAngleRotationAux₁ with
    norm_map' := fun x => by
      refine le_antisymm ?_ ?_
      · rcases eq_or_lt_of_le (norm_nonneg (o.rightAngleRotationAux₁ x)) with h | h
        · rw [← h]
          positivity
        refine le_of_mul_le_mul_right ?_ h
        rw [← real_inner_self_eq_norm_mul_norm, o.inner_rightAngleRotationAux₁_left]
        exact o.areaForm_le x (o.rightAngleRotationAux₁ x)
      · let K : Submodule ℝ E := ℝ ∙ x
        have : Nontrivial Kᗮ := by
          apply nontrivial_of_finrank_pos (R := ℝ)
          have : finrank ℝ K ≤ Finset.card {x} := by
            rw [← Set.toFinset_singleton]
            exact finrank_span_le_card ({x} : Set E)
          have : Finset.card {x} = 1 := Finset.card_singleton x
          have : finrank ℝ K + finrank ℝ Kᗮ = finrank ℝ E := K.finrank_add_finrank_orthogonal
          have : finrank ℝ E = 2 := Fact.out
          omega
        obtain ⟨w, hw₀⟩ : ∃ w : Kᗮ, w ≠ 0 := exists_ne 0
        have hw' : ⟪x, (w : E)⟫ = 0 := Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
        have hw : (w : E) ≠ 0 := fun h => hw₀ (Submodule.coe_eq_zero.mp h)
        refine le_of_mul_le_mul_right ?_ (by rwa [norm_pos_iff] : 0 < ‖(w : E)‖)
        rw [← o.abs_areaForm_of_orthogonal hw']
        rw [← o.inner_rightAngleRotationAux₁_left x w]
        exact abs_real_inner_le_norm (o.rightAngleRotationAux₁ x) w }

@[simp]
theorem rightAngleRotationAux₁_rightAngleRotationAux₁ (x : E) :
    o.rightAngleRotationAux₁ (o.rightAngleRotationAux₁ x) = -x := by
  apply ext_inner_left ℝ
  intro y
  have : ⟪o.rightAngleRotationAux₁ y, o.rightAngleRotationAux₁ x⟫ = ⟪y, x⟫ :=
    LinearIsometry.inner_map_map o.rightAngleRotationAux₂ y x
  rw [o.inner_rightAngleRotationAux₁_right, ← o.inner_rightAngleRotationAux₁_left, this,
    inner_neg_right]

/-- An isometric automorphism of an oriented real inner product space of dimension 2 (usual notation
`J`). This automorphism squares to -1. We will define rotations in such a way that this
automorphism is equal to rotation by 90 degrees. -/
irreducible_def rightAngleRotation : E ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofLinearIsometry o.rightAngleRotationAux₂ (-o.rightAngleRotationAux₁)
    (by ext; simp [rightAngleRotationAux₂]) (by ext; simp [rightAngleRotationAux₂])

local notation "J" => o.rightAngleRotation

@[simp]
theorem inner_rightAngleRotation_left (x y : E) : ⟪J x, y⟫ = ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_left x y

@[simp]
theorem inner_rightAngleRotation_right (x y : E) : ⟪x, J y⟫ = -ω x y := by
  rw [rightAngleRotation]
  exact o.inner_rightAngleRotationAux₁_right x y

@[simp]
theorem rightAngleRotation_rightAngleRotation (x : E) : J (J x) = -x := by
  rw [rightAngleRotation]
  exact o.rightAngleRotationAux₁_rightAngleRotationAux₁ x

@[simp]
theorem rightAngleRotation_symm :
    LinearIsometryEquiv.symm J = LinearIsometryEquiv.trans J (LinearIsometryEquiv.neg ℝ) := by
  rw [rightAngleRotation]
  exact LinearIsometryEquiv.toLinearIsometry_injective rfl

theorem inner_rightAngleRotation_self (x : E) : ⟪J x, x⟫ = 0 := by simp

theorem inner_rightAngleRotation_swap (x y : E) : ⟪x, J y⟫ = -⟪J x, y⟫ := by simp

theorem inner_rightAngleRotation_swap' (x y : E) : ⟪J x, y⟫ = -⟪x, J y⟫ := by
  simp [o.inner_rightAngleRotation_swap x y]

theorem inner_comp_rightAngleRotation (x y : E) : ⟪J x, J y⟫ = ⟪x, y⟫ :=
  LinearIsometryEquiv.inner_map_map J x y

@[simp]
theorem areaForm_rightAngleRotation_left (x y : E) : ω (J x) y = -⟪x, y⟫ := by
  rw [← o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_right, neg_neg]

@[simp]
theorem areaForm_rightAngleRotation_right (x y : E) : ω x (J y) = ⟪x, y⟫ := by
  rw [← o.inner_rightAngleRotation_left, o.inner_comp_rightAngleRotation]

theorem areaForm_comp_rightAngleRotation (x y : E) : ω (J x) (J y) = ω x y := by simp

@[simp]
theorem rightAngleRotation_trans_rightAngleRotation :
    LinearIsometryEquiv.trans J J = LinearIsometryEquiv.neg ℝ := by ext; simp

theorem rightAngleRotation_neg_orientation (x : E) :
    (-o).rightAngleRotation x = -o.rightAngleRotation x := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_rightAngleRotation_left]
  simp

@[simp]
theorem rightAngleRotation_trans_neg_orientation :
    (-o).rightAngleRotation = o.rightAngleRotation.trans (LinearIsometryEquiv.neg ℝ) :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_neg_orientation

theorem rightAngleRotation_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation x =
      φ (o.rightAngleRotation (φ.symm x)) := by
  apply ext_inner_right ℝ
  intro y
  rw [inner_rightAngleRotation_left]
  trans ⟪J (φ.symm x), φ.symm y⟫
  · simp [o.areaForm_map]
  trans ⟪φ (J (φ.symm x)), φ (φ.symm y)⟫
  · rw [φ.inner_map_map]
  · simp

/-- `J` commutes with any positively-oriented isometric automorphism. -/
theorem linearIsometryEquiv_comp_rightAngleRotation (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x : E) : φ (J x) = J (φ x) := by
  convert (o.rightAngleRotation_map φ (φ x)).symm
  · simp
  · symm
    rwa [← o.map_eq_iff_det_pos φ.toLinearEquiv] at hφ
    rw [@Fact.out (finrank ℝ E = 2), Fintype.card_fin]

theorem rightAngleRotation_map' {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).rightAngleRotation =
      (φ.symm.trans o.rightAngleRotation).trans φ :=
  LinearIsometryEquiv.ext <| o.rightAngleRotation_map φ

/-- `J` commutes with any positively-oriented isometric automorphism. -/
theorem linearIsometryEquiv_comp_rightAngleRotation' (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) :
    LinearIsometryEquiv.trans J φ = φ.trans J :=
  LinearIsometryEquiv.ext <| o.linearIsometryEquiv_comp_rightAngleRotation φ hφ

/-- For a nonzero vector `x` in an oriented two-dimensional real inner product space `E`,
`![x, J x]` forms an (orthogonal) basis for `E`. -/
def basisRightAngleRotation (x : E) (hx : x ≠ 0) : Basis (Fin 2) ℝ E :=
  @basisOfLinearIndependentOfCardEqFinrank ℝ _ _ _ _ _ _ _ ![x, J x]
    (linearIndependent_of_ne_zero_of_inner_eq_zero (fun i => by fin_cases i <;> simp [hx])
      (by
        intro i j hij
        fin_cases i <;> fin_cases j <;> simp_all))
    (@Fact.out (finrank ℝ E = 2)).symm

@[simp]
theorem coe_basisRightAngleRotation (x : E) (hx : x ≠ 0) :
    ⇑(o.basisRightAngleRotation x hx) = ![x, J x] :=
  coe_basisOfLinearIndependentOfCardEqFinrank _ _

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. (See
`Orientation.inner_mul_inner_add_areaForm_mul_areaForm` for the "applied" form.) -/
theorem inner_mul_inner_add_areaForm_mul_areaForm' (a x : E) :
    ⟪a, x⟫ • innerₛₗ ℝ a + ω a x • ω a = ‖a‖ ^ 2 • innerₛₗ ℝ x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [real_inner_self_eq_norm_sq, mul_comm, real_inner_comm]
  · simp [real_inner_self_eq_norm_sq, mul_comm, o.areaForm_swap a x]

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫`. -/
theorem inner_mul_inner_add_areaForm_mul_areaForm (a x y : E) :
    ⟪a, x⟫ * ⟪a, y⟫ + ω a x * ω a y = ‖a‖ ^ 2 * ⟪x, y⟫ :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_inner_add_areaForm_mul_areaForm' a x)

theorem inner_sq_add_areaForm_sq (a b : E) : ⟪a, b⟫ ^ 2 + ω a b ^ 2 = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  simpa [sq, real_inner_self_eq_norm_sq] using o.inner_mul_inner_add_areaForm_mul_areaForm a b b

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. (See
`Orientation.inner_mul_areaForm_sub` for the "applied" form.) -/
theorem inner_mul_areaForm_sub' (a x : E) : ⟪a, x⟫ • ω a - ω a x • innerₛₗ ℝ a = ‖a‖ ^ 2 • ω x := by
  by_cases ha : a = 0
  · simp [ha]
  apply (o.basisRightAngleRotation a ha).ext
  intro i
  fin_cases i
  · simp [real_inner_self_eq_norm_sq, mul_comm, o.areaForm_swap a x]
  · simp [real_inner_self_eq_norm_sq, mul_comm, real_inner_comm]

/-- For vectors `a x y : E`, the identity `⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y`. -/
theorem inner_mul_areaForm_sub (a x y : E) : ⟪a, x⟫ * ω a y - ω a x * ⟪a, y⟫ = ‖a‖ ^ 2 * ω x y :=
  congr_arg (fun f : E →ₗ[ℝ] ℝ => f y) (o.inner_mul_areaForm_sub' a x)

theorem nonneg_inner_and_areaForm_eq_zero_iff_sameRay (x y : E) :
    0 ≤ ⟪x, y⟫ ∧ ω x y = 0 ↔ SameRay ℝ x y := by
  by_cases hx : x = 0
  · simp [hx]
  constructor
  · let a : ℝ := (o.basisRightAngleRotation x hx).repr y 0
    let b : ℝ := (o.basisRightAngleRotation x hx).repr y 1
    suffices ↑0 ≤ a * ‖x‖ ^ 2 ∧ b * ‖x‖ ^ 2 = 0 → SameRay ℝ x (a • x + b • J x) by
      rw [← (o.basisRightAngleRotation x hx).sum_repr y]
      simp only [Fin.sum_univ_succ, coe_basisRightAngleRotation, Matrix.cons_val_zero,
        Fin.succ_zero_eq_one', Finset.univ_eq_empty, Finset.sum_empty, areaForm_apply_self,
        map_smul, map_add, real_inner_smul_right, inner_add_right, Matrix.cons_val_one,
        Algebra.id.smul_eq_mul, areaForm_rightAngleRotation_right,
        mul_zero, add_zero, zero_add, neg_zero, inner_rightAngleRotation_right,
        real_inner_self_eq_norm_sq]
      exact this
    rintro ⟨ha, hb⟩
    have hx' : 0 < ‖x‖ := by simpa using hx
    have ha' : 0 ≤ a := nonneg_of_mul_nonneg_left ha (by positivity)
    have hb' : b = 0 := eq_zero_of_ne_zero_of_mul_right_eq_zero (pow_ne_zero 2 hx'.ne') hb
    exact (SameRay.sameRay_nonneg_smul_right x ha').add_right <| by simp [hb']
  · intro h
    obtain ⟨r, hr, rfl⟩ := h.exists_nonneg_left hx
    simp only [inner_smul_right, real_inner_self_eq_norm_sq, LinearMap.map_smulₛₗ,
      areaForm_apply_self, Algebra.id.smul_eq_mul, mul_zero, and_true]
    positivity

/-- A complex-valued real-bilinear map on an oriented real inner product space of dimension 2. Its
real part is the inner product and its imaginary part is `Orientation.areaForm`.

On `ℂ` with the standard orientation, `kahler w z = conj w * z`; see `Complex.kahler`. -/
def kahler : E →ₗ[ℝ] E →ₗ[ℝ] ℂ :=
  LinearMap.llcomp ℝ E ℝ ℂ Complex.ofRealCLM ∘ₗ innerₛₗ ℝ +
    LinearMap.llcomp ℝ E ℝ ℂ ((LinearMap.lsmul ℝ ℂ).flip Complex.I) ∘ₗ ω

theorem kahler_apply_apply (x y : E) : o.kahler x y = ⟪x, y⟫ + ω x y • Complex.I :=
  rfl

theorem kahler_swap (x y : E) : o.kahler x y = conj (o.kahler y x) := by
  simp only [kahler_apply_apply]
  rw [real_inner_comm, areaForm_swap]
  simp [Complex.conj_ofReal]

@[simp]
theorem kahler_apply_self (x : E) : o.kahler x x = ‖x‖ ^ 2 := by
  simp [kahler_apply_apply, real_inner_self_eq_norm_sq]

@[simp]
theorem kahler_rightAngleRotation_left (x y : E) :
    o.kahler (J x) y = -Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_left, o.inner_rightAngleRotation_left,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination ω x y * Complex.I_sq

@[simp]
theorem kahler_rightAngleRotation_right (x y : E) :
    o.kahler x (J y) = Complex.I * o.kahler x y := by
  simp only [o.areaForm_rightAngleRotation_right, o.inner_rightAngleRotation_right,
    o.kahler_apply_apply, Complex.ofReal_neg, Complex.real_smul]
  linear_combination -ω x y * Complex.I_sq

-- @[simp] -- Porting note: simp normal form is `kahler_comp_rightAngleRotation'`
theorem kahler_comp_rightAngleRotation (x y : E) : o.kahler (J x) (J y) = o.kahler x y := by
  simp only [kahler_rightAngleRotation_left, kahler_rightAngleRotation_right]
  linear_combination -o.kahler x y * Complex.I_sq

theorem kahler_comp_rightAngleRotation' (x y : E) :
    -(Complex.I * (Complex.I * o.kahler x y)) = o.kahler x y := by
  linear_combination -o.kahler x y * Complex.I_sq

@[simp]
theorem kahler_neg_orientation (x y : E) : (-o).kahler x y = conj (o.kahler x y) := by
  simp [kahler_apply_apply, Complex.conj_ofReal]

theorem kahler_mul (a x y : E) : o.kahler x a * o.kahler a y = ‖a‖ ^ 2 * o.kahler x y := by
  trans ((‖a‖ ^ 2 :) : ℂ) * o.kahler x y
  · apply Complex.ext
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      linear_combination o.inner_mul_inner_add_areaForm_mul_areaForm a x y
    · simp only [o.kahler_apply_apply, Complex.add_im, Complex.add_re, Complex.I_im, Complex.I_re,
        Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re, Complex.real_smul]
      rw [real_inner_comm a x, o.areaForm_swap x a]
      linear_combination o.inner_mul_areaForm_sub a x y
  · norm_cast

theorem normSq_kahler (x y : E) : Complex.normSq (o.kahler x y) = ‖x‖ ^ 2 * ‖y‖ ^ 2 := by
  simpa [kahler_apply_apply, Complex.normSq, sq] using o.inner_sq_add_areaForm_sq x y

theorem norm_kahler (x y : E) : ‖o.kahler x y‖ = ‖x‖ * ‖y‖ := by
  rw [← sq_eq_sq₀, Complex.sq_norm]
  · linear_combination o.normSq_kahler x y
  · positivity
  · positivity

@[deprecated (since := "2025-02-17")] alias abs_kahler := norm_kahler

theorem eq_zero_or_eq_zero_of_kahler_eq_zero {x y : E} (hx : o.kahler x y = 0) : x = 0 ∨ y = 0 := by
  have : ‖x‖ * ‖y‖ = 0 := by simpa [hx] using (o.norm_kahler x y).symm
  rcases eq_zero_or_eq_zero_of_mul_eq_zero this with h | h
  · left
    simpa using h
  · right
    simpa using h

theorem kahler_eq_zero_iff (x y : E) : o.kahler x y = 0 ↔ x = 0 ∨ y = 0 := by
  refine ⟨o.eq_zero_or_eq_zero_of_kahler_eq_zero, ?_⟩
  rintro (rfl | rfl) <;> simp

theorem kahler_ne_zero {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) : o.kahler x y ≠ 0 := by
  apply mt o.eq_zero_or_eq_zero_of_kahler_eq_zero
  tauto

theorem kahler_ne_zero_iff (x y : E) : o.kahler x y ≠ 0 ↔ x ≠ 0 ∧ y ≠ 0 := by
  refine ⟨?_, fun h => o.kahler_ne_zero h.1 h.2⟩
  contrapose
  simp only [not_and_or, Classical.not_not, kahler_apply_apply, Complex.real_smul]
  rintro (rfl | rfl) <;> simp

theorem kahler_map {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [hF : Fact (finrank ℝ F = 2)] (φ : E ≃ₗᵢ[ℝ] F) (x y : F) :
    (Orientation.map (Fin 2) φ.toLinearEquiv o).kahler x y = o.kahler (φ.symm x) (φ.symm y) := by
  simp [kahler_apply_apply, areaForm_map]

/-- The bilinear map `kahler` is invariant under pullback by a positively-oriented isometric
automorphism. -/
theorem kahler_comp_linearIsometryEquiv (φ : E ≃ₗᵢ[ℝ] E)
    (hφ : 0 < LinearMap.det (φ.toLinearEquiv : E →ₗ[ℝ] E)) (x y : E) :
    o.kahler (φ x) (φ y) = o.kahler x y := by
  simp [kahler_apply_apply, o.areaForm_comp_linearIsometryEquiv φ hφ]

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

@[simp]
protected theorem areaForm (w z : ℂ) : Complex.orientation.areaForm w z = (conj w * z).im := by
  let o := Complex.orientation
  simp only [o, o.areaForm_to_volumeForm,
    o.volumeForm_robust Complex.orthonormalBasisOneI rfl, Basis.det_apply, Matrix.det_fin_two,
    Basis.toMatrix_apply, toBasis_orthonormalBasisOneI, Matrix.cons_val_zero, coe_basisOneI_repr,
    Matrix.cons_val_one, mul_im, conj_re, conj_im]
  ring

@[simp]
protected theorem rightAngleRotation (z : ℂ) :
    Complex.orientation.rightAngleRotation z = I * z := by
  apply ext_inner_right ℝ
  intro w
  rw [Orientation.inner_rightAngleRotation_left]
  simp only [Complex.areaForm, Complex.inner, mul_re, mul_im, conj_re, conj_im, map_mul, conj_I,
    neg_re, neg_im, I_re, I_im]
  ring

@[simp]
protected theorem kahler (w z : ℂ) : Complex.orientation.kahler w z = z * conj w := by
  rw [Orientation.kahler_apply_apply]
  apply Complex.ext <;> simp [mul_comm]

end Complex

namespace Orientation

local notation "ω" => o.areaForm

local notation "J" => o.rightAngleRotation

open Complex

-- Porting note: The instance `finrank_real_complex_fact` cannot be found by synthesis for
-- `areaForm_map`, `rightAngleRotation_map` and `kahler_map` in the three theorems below,
-- so it has to be provided by unification (i.e. by naming the instance-implicit argument where
-- it belongs and using `(hF := _)`).

/-- The area form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem areaForm_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    ω x y = (conj (f x) * f y).im := by
  rw [← Complex.areaForm, ← hf, areaForm_map (hF := _)]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

/-- The rotation by 90 degrees on an oriented real inner product space of dimension 2 can be
evaluated in terms of a complex-number representation of the space. -/
theorem rightAngleRotation_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x : E) :
    f (J x) = I * f x := by
  rw [← Complex.rightAngleRotation, ← hf, rightAngleRotation_map (hF := _),
    LinearIsometryEquiv.symm_apply_apply]

/-- The Kahler form on an oriented real inner product space of dimension 2 can be evaluated in terms
of a complex-number representation of the space. -/
theorem kahler_map_complex (f : E ≃ₗᵢ[ℝ] ℂ)
    (hf : Orientation.map (Fin 2) f.toLinearEquiv o = Complex.orientation) (x y : E) :
    o.kahler x y = f y * conj (f x) := by
  rw [← Complex.kahler, ← hf, kahler_map (hF := _)]
  iterate 2 rw [LinearIsometryEquiv.symm_apply_apply]

end Orientation
