import Mathlib

variable {R A : Type*}

theorem charP_of_injective_algebraMap [CommSemiring R] [Semiring A] [Algebra R A]
    (h : Function.Injective (algebraMap R A)) (p : ℕ) [CharP R p] : CharP A p := charP_of_injective_ringHom h p

