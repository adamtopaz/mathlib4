/-
Copyright (c) 2025 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Topology.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.Bases

/-!

# Valuative Relations

In this file we introduce a class called `ValuativeRel R` for a ring `R`.
This bundles a relation `rel : R → R → Prop` on `R` which mimics a
preorder on `R` arising from a valuation.
We introduce the notation `x ∣ᵥ y` for this relation.

Recall that the equivalence class of a valuation is *completely* characterized by
such a preorder. Thus, we can think of `ValuativeRel R` as a way of
saying that `R` is endowed with an equivalence class of a valuation.
-/

noncomputable section

/-- The class `[ValuativeRel R]` class introduces an operator `x ∣ᵥ y : Prop` for `x y : R`
which is the natural relation arising from an equivalence class of a valuation on `R`.
More precisely, if v is a valuation on R then the associated relation is `x ∣ᵥ y ↔ v x ≤ v y`.
Use this class to talk about the case where `R` is equipped with an equivalence class
of valuations. -/
class ValuativeRel (R : Type*) [CommRing R] where
  /-- The relation operator arising from `ValuativeRel`. -/
  rel : R → R → Prop
  rel_total (x y) : rel x y ∨ rel y x
  rel_trans {z y x} : rel x y → rel y z → rel x z
  rel_add {x y z} : rel x z → rel y z → rel (x + y) z
  rel_mul_right {x y} (z) : rel x y → rel (x * z) (y * z)
  rel_mul_cancel {x y z} : ¬ rel z 0 → rel (x * z) (y * z) → rel x y
  not_rel_one_zero : ¬ rel 1 0

@[inherit_doc] infix:50  " ≤ᵥ " => ValuativeRel.rel

namespace Valuation

variable {R Γ : Type*} [CommRing R] [LinearOrderedCommMonoidWithZero Γ]
  (v : Valuation R Γ)

/-- We say that a valuation `v` is `Compatible` if the relation `x ∣ᵥ y`
is equivalent to `v x ≤ x y`. -/
class Compatible [ValuativeRel R] where
  rel_iff_le (x y : R) : x ≤ᵥ y ↔ v x ≤ v y

end Valuation

/-- A preorder on a ring is said to be "valuative" if it agrees with the
valuative relation. -/
class ValuativePreorder (R : Type*) [CommRing R] [ValuativeRel R] [Preorder R] where
  dvd_iff_le (x y : R) : x ≤ᵥ y ↔ x ≤ y

namespace ValuativeRel

variable {R : Type*} [CommRing R] [ValuativeRel R]

@[simp]
lemma rel_refl (x : R) : x ≤ᵥ x := by
  cases rel_total x x <;> assumption

lemma rel_rfl {x : R} : x ≤ᵥ x :=
  rel_refl x

protected alias rel.refl := rel_refl

protected alias rel.rfl := rel_rfl

@[simp]
theorem zero_rel (x : R) : 0 ≤ᵥ x := by
  simpa using rel_mul_right x ((rel_total 0 1).resolve_right not_rel_one_zero)

lemma rel_mul_left {x y : R} (z) : x ≤ᵥ y → (z * x) ≤ᵥ (z * y) := by
  rw [mul_comm z x, mul_comm z y]
  apply rel_mul_right

instance : Trans (rel (R := R)) (rel (R := R)) (rel (R := R)) where
  trans h1 h2 := rel_trans h1 h2

lemma rel_mul {x x' y y' : R} : x ≤ᵥ y → x' ≤ᵥ y' → x * x' ≤ᵥ y * y' := by
  intro h1 h2
  calc x * x' ≤ᵥ x * y' := rel_mul_left _ h2
    _ ≤ᵥ y * y' := rel_mul_right _ h1

theorem rel_add_cases (x y : R) : x + y ≤ᵥ x ∨ x + y ≤ᵥ y :=
  (rel_total y x).imp (fun h => rel_add .rfl h) (fun h => rel_add h .rfl)

variable (R) in
def unitSubmonoid : Submonoid R where
  carrier := { x | ¬ x ≤ᵥ 0}
  mul_mem' := by
    intro x y hx hy
    by_contra c
    apply hy
    simp only [Set.mem_setOf_eq, not_not] at c
    rw [show (0 : R) = x * 0 by simp, mul_comm x y, mul_comm x 0] at c
    exact rel_mul_cancel hx c
  one_mem' := not_rel_one_zero

@[simp]
lemma right_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    x * u ≤ᵥ y * u ↔ x ≤ᵥ y := by
  refine ⟨fun h => rel_mul_cancel u.prop h, fun h => ?_⟩
  exact rel_mul_right _ h

@[simp]
lemma left_cancel_unitSubmonoid (x y : R) (u : unitSubmonoid R) :
    u * x ≤ᵥ u * y ↔ x ≤ᵥ y := by
  rw [← right_cancel_unitSubmonoid x y u]
  simp only [mul_comm _ x, mul_comm _ y]

variable (R) in
/-- The setoid used to construct `ValueMonoid R`. -/
def valueSetoid : Setoid (R × unitSubmonoid R) where
  r := fun (x,s) (y,t) => x * t ≤ᵥ y * s ∧ y * s ≤ᵥ x * t
  iseqv := {
    refl ru := ⟨rel_refl _, rel_refl _⟩
    symm h := ⟨h.2, h.1⟩
    trans := by
      rintro ⟨r, u⟩ ⟨s, v⟩ ⟨t, w⟩ ⟨h1, h2⟩ ⟨h3, h4⟩
      constructor
      · have := rel_mul h1 (rel_refl ↑w)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h3 (rel_refl _))
        rw [mul_right_comm r, mul_right_comm t] at this
        simpa using this
      · have := rel_mul h4 (rel_refl ↑u)
        rw [mul_right_comm s] at this
        have := rel_trans this (rel_mul h2 (rel_refl _))
        rw [mul_right_comm t, mul_right_comm r] at this
        simpa using this
  }

variable (R) in
/-- The "canonical" value monoid of a ring with a valuative relation. -/
def ValueGroup := Quotient (valueSetoid R)

protected
def ValueGroup.mk (x : R) (y : unitSubmonoid R) : ValueGroup R :=
  Quotient.mk _ (x, y)

protected
theorem ValueGroup.sound {x y : R} {t s : unitSubmonoid R}
    (h₁ : x * s ≤ᵥ y * t) (h₂ : y * t ≤ᵥ x * s) :
    ValueGroup.mk x t = ValueGroup.mk y s :=
  Quotient.sound ⟨h₁, h₂⟩

protected
theorem ValueGroup.ind {motive : ValueGroup R → Prop} (mk : ∀ x y, motive (.mk x y))
    (t : ValueGroup R) : motive t :=
  Quotient.ind (fun (x, y) => mk x y) t

protected
def ValueGroup.lift {α : Sort*} (f : R → unitSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : unitSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (t : ValueGroup R) : α :=
  Quotient.lift (fun (x, y) => f x y) (fun (x, t) (y, s) ⟨h₁, h₂⟩ => hf x y s t h₁ h₂) t

@[simp] protected
theorem ValueGroup.lift_mk {α : Sort*} (f : R → unitSubmonoid R → α)
    (hf : ∀ (x y : R) (t s : unitSubmonoid R), x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → f x s = f y t)
    (x : R) (y : unitSubmonoid R) : ValueGroup.lift f hf (.mk x y) = f x y := rfl

protected
def ValueGroup.lift₂ {α : Sort*} (f : R → unitSubmonoid R → R → unitSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : unitSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (t₁ : ValueGroup R) (t₂ : ValueGroup R) : α :=
  Quotient.lift₂ (fun (x, t) (y, s) => f x t y s)
    (fun (x, t) (z, v) (y, s) (w, u) ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ => hf x y z w s t u v h₁ h₂ h₃ h₄) t₁ t₂

@[simp] protected
def ValueGroup.lift₂_mk {α : Sort*} (f : R → unitSubmonoid R → R → unitSubmonoid R → α)
    (hf : ∀ (x y z w : R) (t s u v : unitSubmonoid R),
      x * t ≤ᵥ y * s → y * s ≤ᵥ x * t → z * u ≤ᵥ w * v → w * v ≤ᵥ z * u →
      f x s z v = f y t w u)
    (x y : R) (z w : unitSubmonoid R) :
    ValueGroup.lift₂ f hf (.mk x z) (.mk y w) = f x z y w := rfl

theorem ValueGroup.mk_eq_mk {x y : R} {t s : unitSubmonoid R} :
    ValueGroup.mk x t = ValueGroup.mk y s ↔ x * s ≤ᵥ y * t ∧ y * t ≤ᵥ x * s :=
  Quotient.eq

instance : Zero (ValueGroup R) where
  zero := .mk 0 1

@[simp]
theorem ValueGroup.mk_eq_zero (x : R) (y : unitSubmonoid R) :
    ValueGroup.mk x y = 0 ↔ x ≤ᵥ 0 :=
  ⟨fun h => by simpa using ValueGroup.mk_eq_mk.mp h,
    fun h => ValueGroup.sound (by simpa using h) (by simp)⟩

@[simp]
theorem ValueGroup.mk_zero (x : unitSubmonoid R) : ValueGroup.mk 0 x = 0 :=
  (ValueGroup.mk_eq_zero 0 x).mpr .rfl

instance : One (ValueGroup R) where
  one := .mk 1 1

@[simp]
theorem ValueGroup.mk_self (x : unitSubmonoid R) : ValueGroup.mk (x : R) x = 1 :=
  ValueGroup.sound (by simp) (by simp)

@[simp]
theorem ValueGroup.mk_one_one : ValueGroup.mk (1 : R) 1 = 1 :=
  ValueGroup.sound (by simp) (by simp)

instance : Mul (ValueGroup R) where
  mul := ValueGroup.lift₂ (fun a b c d => .mk (a * c) (b * d)) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    apply ValueGroup.sound
    · rw [Submonoid.coe_mul, Submonoid.coe_mul,
        mul_mul_mul_comm x, mul_mul_mul_comm y]
      exact rel_mul h₁ h₃
    · rw [Submonoid.coe_mul, Submonoid.coe_mul,
        mul_mul_mul_comm x, mul_mul_mul_comm y]
      exact rel_mul h₂ h₄

@[simp]
theorem ValueGroup.mk_mul_mk (a b : R) (c d : unitSubmonoid R) :
    ValueGroup.mk a c * ValueGroup.mk b d = ValueGroup.mk (a * b) (c * d) := rfl

instance : CommMonoidWithZero (ValueGroup R) where
  mul_assoc a b c := by
    induction a using ValueGroup.ind
    induction b using ValueGroup.ind
    induction c using ValueGroup.ind
    simp [mul_assoc]
  one_mul := ValueGroup.ind <| by simp [← ValueGroup.mk_one_one]
  mul_one := ValueGroup.ind <| by simp [← ValueGroup.mk_one_one]
  zero_mul := ValueGroup.ind <| fun _ _ => by
    rw [← ValueGroup.mk_zero 1, ValueGroup.mk_mul_mk]
    simp
  mul_zero := ValueGroup.ind <| fun _ _ => by
    rw [← ValueGroup.mk_zero 1, ValueGroup.mk_mul_mk]
    simp
  mul_comm a b := by
    induction a using ValueGroup.ind
    induction b using ValueGroup.ind
    simp [mul_comm]
  npow n := ValueGroup.lift (fun a b => ValueGroup.mk (a ^ n) (b ^ n)) <| by
    intro x y t s h₁ h₂
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [pow_succ, ← ValueGroup.mk_mul_mk, ih]
      apply congrArg (_ * ·)
      exact ValueGroup.sound h₁ h₂
  npow_zero := ValueGroup.ind (by simp)
  npow_succ n := ValueGroup.ind (by simp [pow_succ])

instance : LE (ValueGroup R) where
  le := ValueGroup.lift₂ (fun a s b t => a * t ≤ᵥ b * s) <| by
    intro x y z w t s u v h₁ h₂ h₃ h₄
    by_cases hw : w ≤ᵥ 0 <;> by_cases hz : z ≤ᵥ 0
    · refine propext ⟨fun h => rel_trans ?_ (zero_rel _), fun h => rel_trans ?_ (zero_rel _)⟩
      · apply rel_mul_cancel (s * v).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (v : R) h₂))
        rw [mul_right_comm x]
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (t : R) h))
        apply rel_trans (rel_mul_right (u : R) (rel_mul_right (t : R) (rel_mul_right (s : R) hz)))
        simp
      · apply rel_mul_cancel (t * u).prop
        rw [mul_right_comm, Submonoid.coe_mul, ← mul_assoc]
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (u : R) h₁))
        rw [mul_right_comm y]
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (s : R) h))
        apply rel_trans (rel_mul_right (v : R) (rel_mul_right (s : R) (rel_mul_right (t : R) hw)))
        simp
    · absurd hz
      apply rel_mul_cancel u.prop
      simpa using rel_trans h₃ (rel_mul_right (v : R) hw)
    · absurd hw
      apply rel_mul_cancel v.prop
      simpa using rel_trans h₄ (rel_mul_right (u : R) hz)
    · refine propext ⟨fun h => ?_, fun h => ?_⟩
      · apply rel_mul_cancel s.prop
        apply rel_mul_cancel hz
        calc y * u * s * z
          _ = y * s * (z * u) := by ring
          _ ≤ᵥ x * t * (w * v) := rel_mul h₂ h₃
          _ = x * v * (t * w) := by ring
          _ ≤ᵥ z * s * (t * w) := rel_mul_right (t * w) h
          _ = w * t * s * z := by ring
      · apply rel_mul_cancel t.prop
        apply rel_mul_cancel hw
        calc x * v * t * w
          _ = x * t * (w * v) := by ring
          _ ≤ᵥ y * s * (z * u) := rel_mul h₁ h₄
          _ = y * u * (s * z) := by ring
          _ ≤ᵥ w * t * (s * z) := rel_mul_right (s * z) h
          _ = z * s * t * w := by ring

@[simp]
theorem ValueGroup.mk_le_mk (x y : R) (t s : unitSubmonoid R) :
    ValueGroup.mk x t ≤ ValueGroup.mk y s ↔ x * s ≤ᵥ y * t := Iff.rfl

instance : LinearOrder (ValueGroup R) where
  le_refl := ValueGroup.ind fun _ _ => .rfl
  le_trans a b c hab hbc := by
    induction a using ValueGroup.ind with | mk a₁ a₂
    induction b using ValueGroup.ind with | mk b₁ b₂
    induction c using ValueGroup.ind with | mk c₁ c₂
    rw [ValueGroup.mk_le_mk] at hab hbc ⊢
    apply rel_mul_cancel b₂.prop
    calc a₁ * c₂ * b₂
      _ = a₁ * b₂ * c₂ := by rw [mul_right_comm]
      _ ≤ᵥ b₁ * a₂ * c₂ := rel_mul_right (c₂ : R) hab
      _ = b₁ * c₂ * a₂ := by rw [mul_right_comm]
      _ ≤ᵥ c₁ * b₂ * a₂ := rel_mul_right (a₂ : R) hbc
      _ = c₁ * a₂ * b₂ := by rw [mul_right_comm]
  le_antisymm a b hab hba := by
    induction a using ValueGroup.ind
    induction b using ValueGroup.ind
    exact ValueGroup.sound hab hba
  le_total a b := by
    induction a using ValueGroup.ind
    induction b using ValueGroup.ind
    rw [ValueGroup.mk_le_mk, ValueGroup.mk_le_mk]
    apply rel_total
  toDecidableLE := Classical.decRel LE.le

instance : Bot (ValueGroup R) where
  bot := 0

theorem ValueGroup.bot_eq_zero : (⊥ : ValueGroup R) = 0 := rfl

instance : OrderBot (ValueGroup R) where
  bot_le := ValueGroup.ind fun x y => by
    rw [ValueGroup.bot_eq_zero, ← ValueGroup.mk_zero 1, ValueGroup.mk_le_mk]
    simp

instance : IsOrderedMonoid (ValueGroup R) where
  mul_le_mul_left a b hab c := by
    induction a using ValueGroup.ind
    induction b using ValueGroup.ind
    induction c using ValueGroup.ind
    simp only [ValueGroup.mk_mul_mk, ValueGroup.mk_le_mk, Submonoid.coe_mul]
    conv_lhs => apply mul_mul_mul_comm
    conv_rhs => apply mul_mul_mul_comm
    apply rel_mul_left
    exact hab

instance : Inv (ValueGroup R) where
  inv := ValueGroup.lift (fun x s => by
    classical exact if h : x ≤ᵥ 0 then 0 else .mk s ⟨x, h⟩) <| by
    intro x y t s h₁ h₂
    by_cases hx : x ≤ᵥ 0 <;> by_cases hy : y ≤ᵥ 0
    · simp [hx, hy]
    · absurd hy
      apply rel_mul_cancel s.prop
      simpa using rel_trans h₂ (rel_mul_right (t : R) hx)
    · absurd hx
      apply rel_mul_cancel t.prop
      simpa using rel_trans h₁ (rel_mul_right (s : R) hy)
    · simp only [dif_neg hx, dif_neg hy]
      apply ValueGroup.sound
      · simpa [mul_comm] using h₂
      · simpa [mul_comm] using h₁

@[simp]
theorem ValueGroup.inv_mk (x : R) (y : unitSubmonoid R) (hx : ¬x ≤ᵥ 0) :
    (ValueGroup.mk x y)⁻¹ = ValueGroup.mk (y : R) ⟨x, hx⟩ := dif_neg hx

/-- The value monoid is a linearly ordered commutative monoid with zero. -/
instance : LinearOrderedCommGroupWithZero (ValueGroup R) where
  zero_le_one := bot_le
  exists_pair_ne := by
    refine ⟨0, 1, fun h => ?_⟩
    apply ge_of_eq at h
    rw [← ValueGroup.mk_zero 1, ← ValueGroup.mk_one_one, ValueGroup.mk_le_mk] at h
    simp [not_rel_one_zero] at h
  inv_zero := dif_pos .rfl
  mul_inv_cancel := ValueGroup.ind fun x y h => by
    rw [ne_eq, ← ValueGroup.mk_zero 1, ValueGroup.mk_eq_mk] at h
    simp only [Submonoid.coe_one, mul_one, zero_mul, zero_rel, and_true] at h
    rw [ValueGroup.inv_mk x y h, ← ValueGroup.mk_one_one, ValueGroup.mk_mul_mk, ValueGroup.mk_eq_mk]
    simp [mul_comm]

variable (R) in
/-- The "canonical" valuation associated to a valuative relation. -/
def valuation : Valuation R (ValueGroup R) where
  toFun r := ValueGroup.mk r 1
  map_zero' := rfl
  map_one' := rfl
  map_mul' _ _ := by simp
  map_add_le_max' := by simp [rel_add_cases]

instance : (valuation R).Compatible where
  rel_iff_le _ _ := by simp [valuation]

/-- Construct a valuative relation on a ring using a valuation. -/
def ofValuation
    {S Γ : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation S Γ) : ValuativeRel S where
  rel x y := v x ≤ v y
  rel_total x y := le_total (v x) (v y)
  rel_trans := le_trans
  rel_add hab hbc := (map_add_le_max v _ _).trans (sup_le hab hbc)
  rel_mul_right _ h := by simp only [map_mul, mul_le_mul_right' h]
  rel_mul_cancel h0 h := by
    rw [map_zero, le_zero_iff] at h0
    simp only [map_mul] at h
    exact le_of_mul_le_mul_right h (lt_of_le_of_ne' zero_le' h0)
  not_rel_one_zero := by simp

lemma isEquiv {Γ₁ Γ₂ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₁]
    [LinearOrderedCommMonoidWithZero Γ₂]
    (v₁ : Valuation R Γ₁)
    (v₂ : Valuation R Γ₂)
    [v₁.Compatible] [v₂.Compatible] :
    v₁.IsEquiv v₂ := by
  intro x y
  simp_rw [← Valuation.Compatible.rel_iff_le]

variable (R) in
/-- An alias for endowing a ring with a preorder defined as the valuative relation. -/
def WithPreorder := R

/-- The ring instance on `WithPreorder R` arising from the ring structure on `R`. -/
instance : CommRing (WithPreorder R) := inferInstanceAs (CommRing R)

/-- The preorder on `WithPreorder R` arising from the valuative relation on `R`. -/
instance : Preorder (WithPreorder R) where
  le (x y : R) := x ≤ᵥ y
  le_refl _ := rel_refl _
  le_trans _ _ _ := rel_trans

/-- The valutaive relation on `WithPreorder R` arising from the valuative relation on `R`.
This is defined as the preorder itself. -/
instance : ValuativeRel (WithPreorder R) where
  rel := (· ≤ ·)
  rel_total := rel_total (R := R)
  rel_trans := rel_trans (R := R)
  rel_add := rel_add (R := R)
  rel_mul_right := rel_mul_right (R := R)
  rel_mul_cancel := rel_mul_cancel (R := R)
  not_rel_one_zero := not_rel_one_zero (R := R)


instance : ValuativePreorder (WithPreorder R) where
  dvd_iff_le _ _ := Iff.rfl

open NNReal in variable (R) in
/-- An auxiliary structure used to define `IsRankOne`. -/
structure RankOneStruct where
  /-- The embedding of the value monoid into the nonnegative reals. -/
  emb : ValueGroup R →*₀ ℝ≥0
  strictMono : StrictMono emb
  nontrivial : ∃ γ : ValueGroup R, emb γ ≠ 0 ∧ emb γ ≠ 1

variable (R) in
/-- We say that a ring with a valuative relation is of rank one if
there exists a strictly monotone embedding of the "canonical" value monoid into
the nonnegative reals, and the image of this embedding contains some element different
from `0` and `1`. -/
class IsRankOne where
  nonempty : Nonempty (RankOneStruct R)

variable (R) in
/-- A ring with a valuative relation is discrete if its value monoid
has a maximal element `< 1`. -/
class IsDiscrete where
  has_maximal_element :
    ∃ γ : ValueGroup R, γ < 1 ∧ (∀ δ : ValueGroup R, δ < 1 → δ ≤ γ)

lemma valuation_surjective (γ : ValueGroup R) :
    ∃ (a : R) (b : unitSubmonoid R), valuation _ a / valuation _ (b : R) = γ := by
  induction γ using ValueGroup.ind with | mk a b
  use a, b
  simp [valuation, div_eq_mul_inv, ValueGroup.inv_mk (b : R) 1 b.prop]

end ValuativeRel

open Topology ValuativeRel in
/-- We say that a topology on `R` is valuative if the neighborhoods of `0` in `R`
are determined by the relation `· ∣ᵥ ·`. -/
class ValuativeTopology (R : Type*) [CommRing R] [ValuativeRel R] [TopologicalSpace R] where
  mem_nhds_iff : ∀ s : Set R, s ∈ 𝓝 (0 : R) ↔ ∃ γ : (ValueGroup R)ˣ, { x | valuation _ x < γ } ⊆ s

namespace ValuativeRel

variable
  {R Γ : Type*} [CommRing R] [ValuativeRel R] [TopologicalSpace R]
  [LinearOrderedCommGroupWithZero Γ]
  (v : Valuation R Γ) [v.Compatible]

end ValuativeRel

/-- If `B` is an `A` algebra and both `A` and `B` have valuative relations,
we say that `B|A` is a valuative extension if the valuative relation on `A` is
induced by the one on `B`. -/
class ValuativeExtension
    (A B : Type*)
    [CommRing A] [CommRing B]
    [ValuativeRel A] [ValuativeRel B]
    [Algebra A B] where
  dvd_iff_dvd (a b : A) : a ≤ᵥ b ↔ algebraMap A B a ≤ᵥ algebraMap A B b
