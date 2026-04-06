import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem inductionOn' {p : FreeMonoid α → Prop} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (FreeMonoid.of b * a)) : p a := by
  induction a using FreeMonoid.recOn with
  | h0 =>
      simpa using one
  | ih b a ha =>
      simpa using mul_of b a ha
