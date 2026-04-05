import Mathlib

variable {α : Type u} {β : Type v}

variable [Monoid α] [Monoid β]

theorem IsConj.pow {a b : α} (n : ℕ) : IsConj a b → IsConj (a ^ n) (b ^ n)
  | ⟨c, hc⟩ => ⟨c, hc.pow_right n⟩
