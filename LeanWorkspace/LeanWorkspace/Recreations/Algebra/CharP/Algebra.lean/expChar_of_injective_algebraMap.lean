import Mathlib

variable {R A : Type*}

theorem expChar_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (q : ℕ) [ExpChar R q] : ExpChar A q := expChar_of_injective_ringHom h q

