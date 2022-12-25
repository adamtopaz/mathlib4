/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Johan Commelin, Patrick Massot

! This file was ported from Lean 3 source module algebra.order.with_zero
! leanprover-community/mathlib commit 655994e298904d7e5bbd1e18c95defd7b543eb94
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.Hom.Equiv.Units.GroupWithZero
import Mathlib.Algebra.GroupWithZero.InjSurj
import Mathlib.Algebra.Order.Group.Units
import Mathlib.Algebra.Order.Monoid.Basic
import Mathlib.Algebra.Order.Monoid.WithZero.Defs
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Monoid.TypeTags

/-!
# Linearly ordered commutative groups and monoids with a zero element adjoined

This file sets up a special class of linearly ordered commutative monoids
that show up as the target of so-called “valuations” in algebraic number theory.

Usually, in the informal literature, these objects are constructed
by taking a linearly ordered commutative group Γ and formally adjoining a zero element: Γ ∪ {0}.

The disadvantage is that a type such as `nnreal` is not of that form,
whereas it is a very common target for valuations.
The solutions is to use a typeclass, and that is exactly what we do in this file.

Note that to avoid issues with import cycles, `LinearOrderedCommMonoidWithZero` is defined
in another file. However, the lemmas about it are stated here.
-/


/-- A linearly ordered commutative group with a zero element. -/
class LinearOrderedCommGroupWithZero (α : Type _) extends LinearOrderedCommMonoidWithZero α,
  CommGroupWithZero α
#align linear_ordered_comm_group_with_zero LinearOrderedCommGroupWithZero

variable {α : Type _}

variable {a b c d x y z : α}

instance [LinearOrderedAddCommMonoidWithTop α] :
    LinearOrderedCommMonoidWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.orderedCommMonoid, Multiplicative.linearOrder with
    zero := Multiplicative.ofAdd ⊥
    zero_mul := fun _ ↦ toAdd_injective <| OrderDual.ofDual.injective <| top_add _
    -- Porting note:  Here and elsewhere in the file, just `zero_mul` worked in Lean 3.  See
    -- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Type.20synonyms
    mul_zero := fun _ ↦ toAdd_injective <| OrderDual.ofDual.injective <| add_top _
    zero_le_one := (le_top : (0 : α) ≤ ⊤) }
#align multiplicative.linear_ordered_comm_monoid_with_zero
  instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual

instance [LinearOrderedAddCommGroupWithTop α] :
    LinearOrderedCommGroupWithZero (Multiplicative αᵒᵈ) :=
  { Multiplicative.divInvMonoid, instLinearOrderedCommMonoidWithZeroMultiplicativeOrderDual,
    instNontrivialMultiplicative with
    inv_zero := toAdd_injective <| OrderDual.ofDual.injective
      LinearOrderedAddCommGroupWithTop.neg_top
    mul_inv_cancel := fun _ ha ↦ toAdd_injective <| OrderDual.ofDual.injective <|
      LinearOrderedAddCommGroupWithTop.add_neg_cancel _ <| toAdd_injective.ne ha }

instance [LinearOrderedCommMonoid α] : LinearOrderedCommMonoidWithZero (WithZero α) :=
  { WithZero.linearOrder, WithZero.commMonoidWithZero with
    mul_le_mul_left := fun _ _ ↦ mul_le_mul_left', zero_le_one := WithZero.zero_le _ }
#align with_zero.linear_ordered_comm_monoid_with_zero instLinearOrderedCommMonoidWithZeroWithZero

instance [LinearOrderedCommGroup α] : LinearOrderedCommGroupWithZero (WithZero α) :=
  { instLinearOrderedCommMonoidWithZeroWithZero, WithZero.commGroupWithZero with }

section LinearOrderedCommMonoid

variable [LinearOrderedCommMonoidWithZero α]

/-
The following facts are true more generally in a (linearly) ordered commutative monoid.
-/
/-- Pullback a `LinearOrderedCommMonoidWithZero` under an injective map.
See note [reducible non-instances]. -/
@[reducible]
def Function.Injective.linearOrderedCommMonoidWithZero {β : Type _} [Zero β] [One β] [Mul β]
    [Pow β ℕ] [HasSup β] [HasInf β] (f : β → α) (hf : Function.Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (hsup : ∀ x y, f (x ⊔ y) = max (f x) (f y)) (hinf : ∀ x y, f (x ⊓ y) = min (f x) (f y)) :
    LinearOrderedCommMonoidWithZero β :=
  { LinearOrder.lift f hf hsup hinf, hf.orderedCommMonoid f one mul npow,
    hf.commMonoidWithZero f zero one mul npow with
    zero_le_one :=
      show f 0 ≤ f 1 by simp only [zero, one, LinearOrderedCommMonoidWithZero.zero_le_one] }
#align function.injective.linear_ordered_comm_monoid_with_zero
  Function.Injective.linearOrderedCommMonoidWithZero

@[simp]
theorem zero_le' : 0 ≤ a := by simpa only [mul_zero, mul_one] using mul_le_mul_left' zero_le_one a
#align zero_le' zero_le'

@[simp]
theorem not_lt_zero' : ¬a < 0 :=
  not_lt_of_le zero_le'
#align not_lt_zero' not_lt_zero'

@[simp]
theorem le_zero_iff : a ≤ 0 ↔ a = 0 :=
  ⟨fun h ↦ le_antisymm h zero_le', fun h ↦ h ▸ le_rfl⟩
#align le_zero_iff le_zero_iff

theorem zero_lt_iff : 0 < a ↔ a ≠ 0 :=
  ⟨ne_of_gt, fun h ↦ lt_of_le_of_ne zero_le' h.symm⟩
#align zero_lt_iff zero_lt_iff

theorem ne_zero_of_lt (h : b < a) : a ≠ 0 := fun h1 ↦ not_lt_zero' <| show b < 0 from h1 ▸ h
#align ne_zero_of_lt ne_zero_of_lt

instance : LinearOrderedAddCommMonoidWithTop (Additive αᵒᵈ) :=
  { Additive.orderedAddCommMonoid, Additive.linearOrder with
    top := ⟨OrderDual.toDual 0⟩
    top_add' := fun _ ↦ toMul_injective <| OrderDual.ofDual.injective <| zero_mul _
    le_top := fun _ ↦ zero_le' }
#align additive.linear_ordered_add_comm_monoid_with_top
  instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual

end LinearOrderedCommMonoid

variable [LinearOrderedCommGroupWithZero α]

-- TODO: Do we really need the following two?
/-- Alias of `mul_le_one'` for unification. -/
theorem mul_le_one₀ (ha : a ≤ 1) (hb : b ≤ 1) : a * b ≤ 1 :=
  mul_le_one' ha hb
#align mul_le_one₀ mul_le_one₀

/-- Alias of `one_le_mul'` for unification. -/
theorem one_le_mul₀ (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b :=
  one_le_mul ha hb
#align one_le_mul₀ one_le_mul₀

theorem le_of_le_mul_right (h : c ≠ 0) (hab : a * c ≤ b * c) : a ≤ b := by
  simpa only [mul_inv_cancel_right₀ h] using mul_le_mul_right' hab c⁻¹
#align le_of_le_mul_right le_of_le_mul_right

theorem le_mul_inv_of_mul_le (h : c ≠ 0) (hab : a * c ≤ b) : a ≤ b * c⁻¹ :=
  le_of_le_mul_right h (by simpa [h] using hab)
#align le_mul_inv_of_mul_le le_mul_inv_of_mul_le

theorem mul_inv_le_of_le_mul (hab : a ≤ b * c) : a * c⁻¹ ≤ b := by
  by_cases h : c = 0
  · simp [h]
  · exact le_of_le_mul_right h (by simpa [h] using hab)
#align mul_inv_le_of_le_mul mul_inv_le_of_le_mul

theorem inv_le_one₀ (ha : a ≠ 0) : a⁻¹ ≤ 1 ↔ 1 ≤ a :=
  @inv_le_one' _ _ _ _ <| Units.mk0 a ha
#align inv_le_one₀ inv_le_one₀

theorem one_le_inv₀ (ha : a ≠ 0) : 1 ≤ a⁻¹ ↔ a ≤ 1 :=
  @one_le_inv' _ _ _ _ <| Units.mk0 a ha
#align one_le_inv₀ one_le_inv₀

theorem le_mul_inv_iff₀ (hc : c ≠ 0) : a ≤ b * c⁻¹ ↔ a * c ≤ b :=
  ⟨fun h ↦ inv_inv c ▸ mul_inv_le_of_le_mul h, le_mul_inv_of_mul_le hc⟩
#align le_mul_inv_iff₀ le_mul_inv_iff₀

theorem mul_inv_le_iff₀ (hc : c ≠ 0) : a * c⁻¹ ≤ b ↔ a ≤ b * c :=
  ⟨fun h ↦ inv_inv c ▸ le_mul_inv_of_mul_le (inv_ne_zero hc) h, mul_inv_le_of_le_mul⟩
#align mul_inv_le_iff₀ mul_inv_le_iff₀

theorem div_le_div₀ (a b c d : α) (hb : b ≠ 0) (hd : d ≠ 0) : a * b⁻¹ ≤ c * d⁻¹ ↔ a * d ≤ c * b :=
  by rw [mul_inv_le_iff₀ hb, mul_right_comm, le_mul_inv_iff₀ hd]
#align div_le_div₀ div_le_div₀

@[simp]
theorem Units.zero_lt (u : αˣ) : (0 : α) < u :=
  zero_lt_iff.2 <| u.ne_zero
#align units.zero_lt Units.zero_lt

theorem mul_lt_mul_of_lt_of_le₀ (hab : a ≤ b) (hb : b ≠ 0) (hcd : c < d) : a * c < b * d :=
  have hd : d ≠ 0 := ne_zero_of_lt hcd
  if ha : a = 0 then by
    rw [ha, zero_mul, zero_lt_iff]
    exact mul_ne_zero hb hd
  else
    if hc : c = 0 then by
      rw [hc, mul_zero, zero_lt_iff]
      exact mul_ne_zero hb hd
    else
      show Units.mk0 a ha * Units.mk0 c hc < Units.mk0 b hb * Units.mk0 d hd from
        mul_lt_mul_of_le_of_lt hab hcd
#align mul_lt_mul_of_lt_of_le₀ mul_lt_mul_of_lt_of_le₀

theorem mul_lt_mul₀ (hab : a < b) (hcd : c < d) : a * c < b * d :=
  mul_lt_mul_of_lt_of_le₀ hab.le (ne_zero_of_lt hab) hcd
#align mul_lt_mul₀ mul_lt_mul₀

theorem mul_inv_lt_of_lt_mul₀ (h : x < y * z) : x * z⁻¹ < y := by
  contrapose! h
  simpa only [inv_inv] using mul_inv_le_of_le_mul h
#align mul_inv_lt_of_lt_mul₀ mul_inv_lt_of_lt_mul₀

theorem inv_mul_lt_of_lt_mul₀ (h : x < y * z) : y⁻¹ * x < z := by
  rw [mul_comm] at *
  exact mul_inv_lt_of_lt_mul₀ h
#align inv_mul_lt_of_lt_mul₀ inv_mul_lt_of_lt_mul₀

theorem mul_lt_right₀ (c : α) (h : a < b) (hc : c ≠ 0) : a * c < b * c := by
  contrapose! h
  exact le_of_le_mul_right hc h
#align mul_lt_right₀ mul_lt_right₀

theorem inv_lt_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ < b⁻¹ ↔ b < a :=
  show (Units.mk0 a ha)⁻¹ < (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb < Units.mk0 a ha from inv_lt_inv_iff
#align inv_lt_inv₀ inv_lt_inv₀

theorem inv_le_inv₀ (ha : a ≠ 0) (hb : b ≠ 0) : a⁻¹ ≤ b⁻¹ ↔ b ≤ a :=
  show (Units.mk0 a ha)⁻¹ ≤ (Units.mk0 b hb)⁻¹ ↔ Units.mk0 b hb ≤ Units.mk0 a ha from inv_le_inv_iff
#align inv_le_inv₀ inv_le_inv₀

theorem lt_of_mul_lt_mul_of_le₀ (h : a * b < c * d) (hc : 0 < c) (hh : c ≤ a) : b < d := by
  have ha : a ≠ 0 := ne_of_gt (lt_of_lt_of_le hc hh)
  simp_rw [← inv_le_inv₀ ha (ne_of_gt hc)] at hh
  have := mul_lt_mul_of_lt_of_le₀ hh (inv_ne_zero (ne_of_gt hc)) h
  simpa [inv_mul_cancel_left₀ ha, inv_mul_cancel_left₀ (ne_of_gt hc)] using this
#align lt_of_mul_lt_mul_of_le₀ lt_of_mul_lt_mul_of_le₀

theorem mul_le_mul_right₀ (hc : c ≠ 0) : a * c ≤ b * c ↔ a ≤ b :=
  ⟨le_of_le_mul_right hc, fun hab ↦ mul_le_mul_right' hab _⟩
#align mul_le_mul_right₀ mul_le_mul_right₀

theorem mul_le_mul_left₀ (ha : a ≠ 0) : a * b ≤ a * c ↔ b ≤ c := by
  simp only [mul_comm a]
  exact mul_le_mul_right₀ ha
#align mul_le_mul_left₀ mul_le_mul_left₀

theorem div_le_div_right₀ (hc : c ≠ 0) : a / c ≤ b / c ↔ a ≤ b := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_le_mul_right₀ (inv_ne_zero hc)]
#align div_le_div_right₀ div_le_div_right₀

theorem div_le_div_left₀ (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) : a / b ≤ a / c ↔ c ≤ b := by
  simp only [div_eq_mul_inv, mul_le_mul_left₀ ha, inv_le_inv₀ hb hc, iff_self]
-- Porting note: the simplifier in Lean 3 functioned in such a way that, effectively, `iff_self` was
-- silently added to a `simp only`.  It had to be manually added here.
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/.60simp.60.20.28or.20.60refl.60.3F.29.20difference.20Lean.203.2F4
-- would be resolved by https://github.com/leanprover/lean4/issues/1933
#align div_le_div_left₀ div_le_div_left₀

theorem le_div_iff₀ (hc : c ≠ 0) : a ≤ b / c ↔ a * c ≤ b := by
  rw [div_eq_mul_inv, le_mul_inv_iff₀ hc]
#align le_div_iff₀ le_div_iff₀

theorem div_le_iff₀ (hc : c ≠ 0) : a / c ≤ b ↔ a ≤ b * c := by
  rw [div_eq_mul_inv, mul_inv_le_iff₀ hc]
#align div_le_iff₀ div_le_iff₀

/-- `Equiv.mulLeft₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`.

Note that `OrderIso.mulLeft₀` refers to the `LinearOrderedField` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulLeft₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulLeft₀ a ha with map_rel_iff' := mul_le_mul_left₀ ha }
#align order_iso.mul_left₀' OrderIso.mulLeft₀'

theorem OrderIso.mulLeft₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulLeft₀' ha).symm = OrderIso.mulLeft₀' (inv_ne_zero ha) := by
  ext
  rfl
#align order_iso.mul_left₀'_symm OrderIso.mulLeft₀'_symm

/-- `Equiv.mulRight₀` as an `OrderIso` on a `LinearOrderedCommGroupWithZero.`.

Note that `OrderIso.mulRight₀` refers to the `LinearOrderedField` version. -/
@[simps (config := { simpRhs := true }) apply toEquiv]
def OrderIso.mulRight₀' {a : α} (ha : a ≠ 0) : α ≃o α :=
  { Equiv.mulRight₀ a ha with map_rel_iff' := mul_le_mul_right₀ ha }
#align order_iso.mul_right₀' OrderIso.mulRight₀'

theorem OrderIso.mulRight₀'_symm {a : α} (ha : a ≠ 0) :
    (OrderIso.mulRight₀' ha).symm = OrderIso.mulRight₀' (inv_ne_zero ha) := by
  ext
  rfl
#align order_iso.mul_right₀'_symm OrderIso.mulRight₀'_symm

instance : LinearOrderedAddCommGroupWithTop (Additive αᵒᵈ) :=
  { instLinearOrderedAddCommMonoidWithTopAdditiveOrderDual, Additive.subNegMonoid with
    neg_top := toMul_injective <| OrderDual.ofDual.injective inv_zero
    add_neg_cancel := fun _ ha ↦ toMul_injective <| OrderDual.ofDual.injective <|
      mul_inv_cancel <| toMul_injective.ne ha }
