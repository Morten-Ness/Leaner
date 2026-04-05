import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem _root_.IsUnit.finset : IsUnit a → IsUnit ({a} : Finset α) := IsUnit.map (Finset.singletonMonoidHom : α →* Finset α)

