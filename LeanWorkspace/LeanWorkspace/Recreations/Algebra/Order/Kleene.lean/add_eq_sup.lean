import Mathlib

variable {α β ι : Type*} {π : ι → Type*}

variable [IdemSemiring α] {a b c : α}

theorem add_eq_sup (a b : α) : a + b = a ⊔ b := IdemSemiring.add_eq_sup _ _

scoped[Computability] attribute [simp] add_eq_sup

