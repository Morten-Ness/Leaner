import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem inductionOn' {p : FreeMonoid α → Prop} (a : FreeMonoid α)
    (one : p (1 : FreeMonoid α)) (mul_of : ∀ b a, p a → p (FreeMonoid.of b * a)) : p a := List.rec one (fun _ _ tail_ih => mul_of _ _ tail_ih) a

