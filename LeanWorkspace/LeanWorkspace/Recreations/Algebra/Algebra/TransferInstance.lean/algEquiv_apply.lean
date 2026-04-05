import Mathlib

variable {R α β : Type*} [CommSemiring R]

variable (e : α ≃ β)

theorem algEquiv_apply (e : α ≃ β) [Semiring β] [Algebra R β] (a : α) : (Equiv.algEquiv R e) a = e a := rfl

