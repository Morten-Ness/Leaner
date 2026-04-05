import Mathlib

variable {F α β γ : Type*}

variable [Monoid α] {s t : Set α} {a : α} {m n : ℕ}

theorem _root_.IsUnit.set : IsUnit a → IsUnit ({a} : Set α) := IsUnit.map (Set.singletonMonoidHom : α →* Set α)

