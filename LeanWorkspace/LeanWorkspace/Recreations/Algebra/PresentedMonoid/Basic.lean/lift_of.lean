import Mathlib

variable {α : Type*}

variable {α : Type*} {rels : FreeMonoid α → FreeMonoid α → Prop} {x y : FreeMonoid α}

variable {α M : Type*} [Monoid M] (f : α → M)

variable {rels : FreeMonoid α → FreeMonoid α → Prop}

variable (h : ∀ a b : FreeMonoid α, rels a b → FreeMonoid.lift f a = FreeMonoid.lift f b)

theorem lift_of {x : α} : PresentedMonoid.lift f h (PresentedMonoid.of rels x) = f x := rfl

