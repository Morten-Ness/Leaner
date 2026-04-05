import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_erase [DecidableEq M] (ha : a ∈ l) : a * (l.erase a).prod = l.prod := List.prod_erase_of_comm ha fun x _ y _ ↦ mul_comm x y

