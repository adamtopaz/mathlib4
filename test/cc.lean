import Mathlib.Tactic.CC
import Mathlib.Tactic.RunCmd
import Mathlib.Data.Vector
import Mathlib.Data.Set.Basic
import Mathlib.Algebra.Ring.Defs

section cc1

open Mathlib.Tactic.CC

open Lean Meta Elab Tactic

set_option pp.explicit true

example (a b c d : Nat) (f : Nat → Nat → Nat) :
    a = b → b = c → d + (if b > 0 then a else b) = 0 → f (b + b) b ≠ f (a + c) c → False := by
  intros
  run_tac do
    let s ← CCState.mkUsingHs
    logInfo (toMessageData s)
    let some (_, t₁, t₂) ← liftM <| getFVarFromUserName `h >>= inferType >>= matchNe? | failure
    let b ← getFVarFromUserName `b
    let d ← getFVarFromUserName `d
    guard s.inconsistent
    guard (s.eqcSize b = 4)
    guard !(s.inSingletonEqc b)
    guard (s.inSingletonEqc d)
    logInfo (m!">>> Equivalence roots" ++ .ofFormat .line ++ toMessageData s.roots)
    logInfo (m!">>> b's equivalence class" ++ .ofFormat .line ++ toMessageData (s.eqcOf b))
    let pr ← s.eqvProof t₁ t₂
    let spr ← Term.exprToSyntax pr
    evalTactic <| ← `(tactic| have h := $spr; contradiction)

example (a b : Nat) (f : Nat → Nat) : a = b → f a = f b := by
  cc

example (a b : Nat) (f : Nat → Nat) : a = b → f a ≠ f b → False := by
  cc

example (a b : Nat) (f : Nat → Nat) : a = b → f (f a) ≠ f (f b) → False := by
  cc

example (a b c : Nat) (f : Nat → Nat) : a = b → c = b → f (f a) ≠ f (f c) → False := by
  cc

example (a b c : Nat) (f : Nat → Nat → Nat) :
    a = b → c = b → f (f a b) a ≠ f (f c c) c → False := by
  cc

example (a b c : Nat) (f : Nat → Nat → Nat) : a = b → c = b → f (f a b) a = f (f c c) c := by
  cc

example (a b c d : Nat) : HEq a b → b = c → HEq c d → HEq a d := by
  cc

example (a b c d : Nat) : a = b → b = c → HEq c d → HEq a d := by
  cc

example (a b c d : Nat) : a = b → HEq b c → HEq c d → HEq a d := by
  cc

example (a b c d : Nat) : HEq a b → HEq b c → c = d → HEq a d := by
  cc

example (a b c d : Nat) : HEq a b → b = c → c = d → HEq a d := by
  cc

example (a b c d : Nat) : a = b → b = c → c = d → HEq a d := by
  cc

example (a b c d : Nat) : a = b → HEq b c → c = d → HEq a d := by
  cc

axiom f₁ : {α : Type} → α → α → α
axiom g₁ : Nat → Nat

example (a b c : Nat) : a = b → HEq (g₁ a) (g₁ b) := by
  cc

example (a b c : Nat) : a = b → c = b → f₁ (f₁ a b) (g₁ c) = f₁ (f₁ c a) (g₁ b) := by
  cc

example (a b c d e x y : Nat) : a = b → a = x → b = y → c = d → c = e → c = b → a = e := by
  cc

end cc1

section cc2

axiom f₂ (a b : Nat) : a > b → Nat
axiom g₂ : Nat → Nat

example (a₁ a₂ b₁ b₂ c d : Nat)
        (H₁ : a₁ > b₁)
        (H₂ : a₂ > b₂) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        g₂ (g₂ (f₂ a₁ b₁ H₁)) = g₂ (g₂ (f₂ a₂ b₂ H₂)) := by
  cc

example (a₁ a₂ b₁ b₂ c d : Nat) :
        a₁ = c → a₂ = c →
        b₁ = d → d  = b₂ →
        a₁ + b₁ + a₁ = a₂ + b₂ + c := by
  cc

example (a b c : Prop) : (a ↔ b) → ((a ∧ (c ∨ b)) ↔ (b ∧ (c ∨ a))) := by
  cc

example (a b c d : Prop)
    [d₁ : Decidable a] [d₂ : Decidable b] [d₃ : Decidable c] [d₄ : Decidable d] :
    (a ↔ b) → (c ↔ d) →
      ((if (a ∧ c) then True else False) ↔ (if (b ∧ d) then True else False)) := by
  cc

example (a b c d : Prop) (x y z : Nat)
    [d₁ : Decidable a] [d₂ : Decidable b] [d₃ : Decidable c] [d₄ : Decidable d] :
    (a ↔ b) → (c ↔ d) → x = y →
      ((if (a ∧ c ∧ a) then x else y) = (if (b ∧ d ∧ b) then y else x)) := by
  cc

end cc2

section cc3

example (a b : Nat) : (a = b ↔ a = b) := by
  cc

example (a b : Nat) : (a = b) = (b = a) := by
  cc

example (a b : Nat) : HEq (a = b) (b = a) := by
  cc

example (p : Nat → Nat → Prop) (f : Nat → Nat) (a b c d : Nat) :
    p (f a) (f b) → a = c → b = d → b = c → p (f c) (f c) := by
  cc

example (p : Nat → Nat → Prop) (a b c d : Nat) :
    p a b → a = c → b = d → p c d := by
  cc

example (p : Nat → Nat → Prop) (f : Nat → Nat) (a b c d : Nat) :
    p (f (f (f (f (f (f a))))))
      (f (f (f (f (f (f b)))))) →
    a = c → b = d → b = c →
    p (f (f (f (f (f (f c))))))
      (f (f (f (f (f (f c)))))) := by
  cc

axiom R : Nat → Nat → Prop

example (a b c : Nat) : a = b → R a b → R a a := by
  cc

example (a b c : Prop) : a = b → b = c → (a ↔ c) := by
  cc

example (a b c : Prop) : a = b → HEq b c → (a ↔ c) := by
  cc

example (a b c : Nat) : HEq a b → b = c → HEq a c := by
  cc

example (a b c : Nat) : HEq a b → b = c → a = c := by
  cc

example (a b c d : Nat) : HEq a b → HEq b c → HEq c d → a = d := by
  cc

example (a b c d : Nat) : HEq a b → b = c → HEq c d → a = d := by
  cc

example (a b c : Prop) : a = b → b = c → (a ↔ c) := by
  cc

example (a b c : Prop) : HEq a b → b = c → (a ↔ c) := by
  cc

example (a b c d : Prop) : HEq a b → HEq b c → HEq c d → (a ↔ d) := by
  cc

def foo (a b c d : Prop) : HEq a b → b = c → HEq c d → (a ↔ d) := by
  cc

example (a b c : Nat) (f : Nat → Nat) : HEq a b → b = c → HEq (f a) (f c) := by
  cc

example (a b c : Nat) (f : Nat → Nat) : HEq a b → b = c → f a = f c := by
  cc

example (a b c d : Nat) (f : Nat → Nat) : HEq a b → b = c → HEq c (f d) → f a = f (f d) := by
  cc

end cc3

section cc4

universe u

axiom app : {α : Type u} → {n m : Nat} → Vector α m → Vector α n → Vector α (m + n)

example (n1 n2 n3 : Nat) (v1 w1 : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 : Vector Nat n2) :
    n1 = n3 → v1 = w1 → HEq w1 w1' → v2 = w2 → HEq (app v1 v2) (app w1' w2) := by
  cc

example (n1 n2 n3 : Nat) (v1 w1 : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 : Vector Nat n2) :
    HEq n1 n3 → v1 = w1 → HEq w1 w1' → HEq v2 w2 → HEq (app v1 v2) (app w1' w2) := by
  cc

example (n1 n2 n3 : Nat) (v1 w1 v : Vector Nat n1) (w1' : Vector Nat n3) (v2 w2 w : Vector Nat n2) :
    HEq n1 n3 → v1 = w1 → HEq w1 w1' → HEq v2 w2 → HEq (app w1' w2) (app v w) →
      app v1 v2 = app v w := by
  cc

end cc4

section cc5
namespace LocalAxioms

axiom A : Type
axiom B : A → Type
axiom C : (a : A) → B a → Type
axiom D : (a : A) → (ba : B a) → C a ba → Type
axiom E : (a : A) → (ba : B a) → (cba : C a ba) → D a ba cba → Type
axiom F : (a : A) → (ba : B a) → (cba : C a ba) → (dcba : D a ba cba) → E a ba cba dcba → Type
axiom C_ss : ∀ a ba, Subsingleton (C a ba)
axiom a1 : A
axiom a2 : A
axiom a3 : A
axiom mk_B1 : (a : _) → B a
axiom mk_B2 : (a : _) → B a
axiom mk_C1 : {a : _} → (ba : _) → C a ba
axiom mk_C2 : {a : _} → (ba : _) → C a ba
axiom tr_B : {a : _} → B a → B a
axiom x : A → A
axiom y : A → A
axiom z : A → A
axiom f : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom f' : {a : A} → {ba : B a} → (cba : C a ba) → D a ba cba
axiom g : {a : A} → {ba : B a} → {cba : C a ba} → (dcba : D a ba cba) → E a ba cba dcba
axiom h : {a : A} → {ba : B a} → {cba : C a ba} → {dcba : D a ba cba} →
    (edcba : E a ba cba dcba) → F a ba cba dcba edcba

attribute [instance] C_ss

example : ∀ (a a' : A), HEq a a' → HEq (mk_B1 a) (mk_B1 a') := by
  cc

example : ∀ (a a' : A), HEq a a' → HEq (mk_B2 a) (mk_B2 a') := by
  cc

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B1 (y a2)) := by
  cc

example : HEq a1 (x a2) → HEq a2 (y a1) → HEq (mk_B1 (x (y a1))) (mk_B1 (x (y (x a2)))) := by
  cc

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (mk_B1 (y a2)))) := by
  cc

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (f (mk_C1 (mk_B2 a1))) (f (mk_C2 (tr_B (mk_B1 (y a2))))) := by
  cc

example : HEq a1 (y a2) → HEq (mk_B1 a1) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (mk_B1 (y a2))))) := by
  cc

example : HEq a1 (y a2) → HEq (tr_B (mk_B1 a1)) (mk_B2 (y a2)) →
    HEq (g (f (mk_C1 (mk_B2 a1)))) (g (f (mk_C2 (tr_B (mk_B1 (y a2)))))) := by
  cc

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (g (f (mk_C1 (mk_B2 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B1 a1)))) := by
  cc

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) → HEq (mk_B1 a1) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (mk_B1 a1))) →
          HEq (f' (mk_C1 (mk_B1 a1))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (mk_B1 (y (z (x a1))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  cc

example : HEq a1 (y a2) → HEq a2 (z a3) → HEq a3 (x a1) →
          HEq (tr_B (mk_B1 a1)) (mk_B2 (y (z (x a1)))) →
          HEq (f (mk_C1 (mk_B2 (y (z (x a1)))))) (f' (mk_C2 (tr_B (mk_B1 a1)))) →
          HEq (f' (mk_C1 (tr_B (mk_B1 a1)))) (f (mk_C2 (mk_B2 (y (z (x a1)))))) →
          HEq (g (f (mk_C1 (tr_B (mk_B1 (y (z (x a1)))))))) (g (f' (mk_C2 (mk_B2 a1)))) := by
  cc

end LocalAxioms
end cc5

section cc6

example (a b c a' b' c' : Nat) : a = a' → b = b' → c = c' → a + b + c + a = a' + b' + c' + a' := by
  cc

example (a b : Unit) : a = b := by
  cc

example (a b : Nat) (h₁ : a = 0) (h₂ : b = 0) : a = b → HEq h₁ h₂ := by
  cc

axiom inv' : (a : Nat) → a ≠ 0 → Nat

example (a b : Nat) (h₁ : a ≠ 0) (h₂ : b ≠ 0) : a = b → inv' a h₁ = inv' b h₂ := by
  cc

example (C : Nat → Type) (f : (n : _) → C n → C n) (n m : Nat) (c : C n) (d : C m) :
    HEq (f n) (f m) → HEq c d → HEq n m → HEq (f n c) (f m d) := by
  cc

end cc6

section cc7

example (f g : {α : Type} → α → α → α) (h : Nat → Nat) (a b : Nat) :
    h = f a → h b = f a b := by
  cc

example (f g : {α : Type} → (a b : α) → {x : α // x ≠ b})
    (h : (b : Nat) → {x : Nat // x ≠ b}) (a b₁ b₂ : Nat) :
    h = f a → b₁ = b₂ → HEq (h b₁) (f a b₂) := by
  cc

example (f : Nat → Nat → Nat) (a b c d : Nat) :
    c = d → f a = f b → f a c = f b d := by
  cc

example (f : Nat → Nat → Nat) (a b c d : Nat) :
        HEq c d → HEq (f a) (f b) → HEq (f a c) (f b d) := by
  cc

end cc7

instance naa : IsAssociative ℕ (· + ·) := ⟨Nat.add_assoc⟩
instance nac : IsCommutative ℕ (· + ·) := ⟨Nat.add_comm⟩
instance nma : IsAssociative ℕ (· * ·) := ⟨Nat.mul_assoc⟩
instance nmc : IsCommutative ℕ (· * ·) := ⟨Nat.mul_comm⟩

section cc_ac1

example (a b c : Nat) (f : Nat → Nat) : f (a + b + c) = f (c + b + a) := by
  cc

example (a b c : Nat) (f : Nat → Nat) : a + b = c → f (c + c) = f (a + b + c) := by
  cc

end cc_ac1

section cc_ac2

example (a b c d : Nat) (f : Nat → Nat → Nat) : b + a = d → f (a + b + c) a = f (c + d) a := by
  cc

end cc_ac2

section cc_ac3

example (a b c d e : Nat) (f : Nat → Nat → Nat) :
    b + a = d → b + c = e → f (a + b + c) (a + b + c) = f (c + d) (a + e) := by
  cc

example (a b c d e : Nat) (f : Nat → Nat → Nat) :
    b + a = d + d → b + c = e + e → f (a + b + c) (a + b + c) = f (c + d + d) (e + a + e) := by
  cc

section
universe u
variable {α : Type u}
variable (op : α → α → α)
variable [IsAssociative α op]
variable [IsCommutative α op]

lemma ex₁ (a b c d e : α) (f : α → α → α) :
    op b a = op d d → op b c = op e e →
    f (op a (op b c)) (op (op a b) c) = f (op (op c d) d) (op e (op a e)) := by
  cc
end

end cc_ac3

section cc_ac4

section
universe u
variable {α : Type u}

example (a b c d₁ d₂ e₁ e₂ : Set α) (f : Set α → Set α → Set α) :
    b ∪ a = d₁ ∪ d₂ → b ∪ c = e₂ ∪ e₁ →
      f (a ∪ b ∪ c) (a ∪ b ∪ c) = f (c ∪ d₂ ∪ d₁) (e₂ ∪ a ∪ e₁) := by
  cc
end

end cc_ac4

section cc_ac5

universe u

variable {α : Type u}
variable [CommRing α]

example (x1 x2 x3 x4 x5 x6 : α) :
    x1*x4 = x1 → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → x1 = x1*(x6*x3) := by
  cc

example (y1 y2 x2 x3 x4 x5 x6 : α) :
    (y1 + y2)*x4 = (y2 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 →
      (y2 + y1) = (y1 + y2)*(x6*x3) := by
  cc

example (y1 y2 y3 x2 x3 x4 x5 x6 : α) :
    (y1 + y2)*x4 = (y3 + y1) → x3*x6 = x5*x5 → x5 = x4 → x6 = x2 → y2 = y3 →
      (y2 + y1) = (y1 + y3)*(x6*x3) := by
  cc

end cc_ac5

section cc_constructors

example (a b : Nat) (s t : List Nat) : a :: s = b :: t → a ≠ b → False := by
  cc

example (a b : Nat) (s t : List Nat) : a :: s = b :: t → t ≠ s → False := by
  cc

example (a c b : Nat) (s t : List Nat) : a :: s = b :: t → a ≠ c → c = b → False := by
  cc

example (a c b : Nat) (s t : List Nat) : a :: a :: s = a :: b :: t → a ≠ c → c = b → False := by
  cc

example (a b : Nat) (s t r : List Nat) : a :: s = r → r = b :: t → a ≠ b → False := by
  cc

example (a b : Nat) (s t r : List Nat) : a :: s = r → r = b :: t → a = b := by
  cc

example (a b : Nat) (s t r : List Nat) : List.cons a = List.cons b → a = b := by
  intro h1
  /- In the current implementation, cc does not "complete" partially applied
     constructor applications. So, the following one should fail. -/
  try cc
  /- Complete it manually. TODO(Leo): we can automate it for inhabited types. -/
  have h := congr_fun h1 []
  cc

inductive Foo
| mk1 : Nat → Nat → Foo
| mk2 : Nat → Nat → Foo

example (a b : Nat) : Foo.mk1 a = Foo.mk2 b → False := by
  intro h1
  /- In the current implementation, cc does not "complete" partially applied
     constructor applications. So, the following one should fail. -/
  try cc
  have h := congr_fun h1 0
  cc

universe u
inductive Vec (α : Type u) : Nat → Type (max 1 u)
| nil  : Vec α 0
| cons : ∀ {n}, α → Vec α n → Vec α (Nat.succ n)

example (α : Type u) (a b c d : α) (n : Nat) (s t : Vec α n) :
    Vec.cons a s = Vec.cons b t → a ≠ b → False := by
  cc

example (α : Type u) (a b c d : α) (n : Nat) (s t : Vec α n) :
    Vec.cons a s = Vec.cons b t → t ≠ s → False := by
  cc

example (α : Type u) (a b c d : α) (n : Nat) (s t : Vec α n) :
    Vec.cons a (Vec.cons a s) = Vec.cons a (Vec.cons b t) → b ≠ c → c = a → False := by
  cc

end cc_constructors

section cc_proj

example (a b c d : Nat) (f : Nat → Nat × Nat) : (f d).1 ≠ a → f d = (b, c) → b = a → False := by
  cc

def ex₂ (a b c d : Nat) (f : Nat → Nat × Nat) : (f d).2 ≠ a → f d = (b, c) → c = a → False := by
  cc

example (a b c : Nat) (f : Nat → Nat) : (f b, c).1 ≠ f a → f b = f c → a = c → False := by
  cc

end cc_proj

section cc_value

example (a b : Nat) : a = 1 → b = 2 → a = b → False := by
  cc

example (a b c : Int) : a = 1 → c = -2 → a = b → c = b → False := by
  cc

example (a b : Char) : a = 'h' → b = 'w' → a = b → False := by
  cc

example (a b : String) : a = "hello" → b = "world" → a = b → False := by
  cc

example (a b c : String) : a = c → a = "hello" → c = "world" → c = b → False := by
  cc

end cc_value