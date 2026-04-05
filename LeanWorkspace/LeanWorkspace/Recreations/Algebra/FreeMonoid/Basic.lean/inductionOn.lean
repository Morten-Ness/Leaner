import Mathlib

variable {α : Type*} {β : Type*} {γ : Type*} {M : Type*} [Monoid M] {N : Type*} [Monoid N]

theorem inductionOn {C : FreeMonoid α → Prop} (z : FreeMonoid α) (one : C 1)
    (FreeMonoid.of : ∀ (x : α), C (FreeMonoid.of x)) (mul : ∀ (x y : FreeMonoid α), C x → C y → C (x * y)) :
    C z := List.rec one (fun _ _ ih => mul [_] _ (FreeMonoid.of _) ih) z

