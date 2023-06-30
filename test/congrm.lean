import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Congrm

namespace Tests.Congrm

section docs

-- These are the examples from the documentation of the tactic

example {a b c d : ℕ} :
    Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ ?h1) * (?h2 + ?h3)
  case h1 =>
    guard_target = a = b
    sorry
  case h2 =>
    guard_target = d = b
    sorry
  case h3 =>
    guard_target = c + a.pred = c + d.pred
    sorry

example {a b : ℕ} (h : a = b) : (λ y : ℕ => ∀ z, a + a = z) = (λ x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, ?_ + a = w
  guard_hyp x : ℕ
  guard_hyp w : ℕ
  exact h

end docs

example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  fail_if_success congrm f ?_
  congrm ∀ x, ?_
  guard_hyp x : α
  exact h x

example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm ∀ x, c(h _)

example (f : α → α → Prop) (h : ∀ a b, f a b = True) :
    (∀ a b, f a b) ↔ (∀ _ _ : α, True) := by
  congrm ∀ x y, ?_
  exact h x y

example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm λ x => ?_
  guard_target = x + a = x + b
  rw [h]

example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm λ (x : ℕ) => x + ?_
  exact h

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm f ?_
  exact h

example (a b c d : ℕ) (h : a = b) (h' : c = d) (f : ℕ → ℕ → ℕ) : f a c = f b d := by
  congrm f ?_ ?_ <;> assumption

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f (f a) = f (f b) := by
  congrm f (f ?_)
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm _ = ?_
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  fail_if_success congrm b = ?_
  congrm a = ?_
  exact h


example {a b : ℕ} (h : a = b) : (fun _ : ℕ => ∀ z, a + a = z) = (fun _ => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, ?_ + a = w
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  fail_if_success congrm Eq ?_ ?_ ?_
  congrm _ = ?_
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm _ = c(h)

example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  fail_if_success congrm f ?_
  congrm ∀ _, ?_
  exact h _

def foo (n : Nat) : Nat := 1 + n

-- Unfolding
example (n m : Nat) (h : n = m) : foo (2 + n) = foo (2 + m) := by
  congrm 1 + (2 + ?_)
  exact h

-- Reflexive relations
example (a b : Nat) (h : a = b) : 1 + a ≤ 1 + b := by
  congrm 1 + ?_
  exact h

/-
-- Fails for now; simp can't synthesize arguments for `Fintype.card_congr'` with so
-- little information

set_option trace.Tactic.congrm true
set_option trace.Tactic.congr true
set_option trace.Meta.Tactic.simp.congr true
set_option trace.Debug.Meta.Tactic.simp.congr true
#check Fintype.card_congr'
example [Fintype α] [Fintype β] (h : α = β) : Fintype.card α = Fintype.card β := by
  --congrm Fintype.card ?_
  --congrm Fintype.card c((?_ : α = β))
-/
