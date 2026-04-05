import Mathlib

variable {R A : Type*}

theorem charP_of_injective_algebraMap' (R : Type*) [CommRing R] [Semiring A]
    [Algebra R A] [FaithfulSMul R A] (p : ℕ) [CharP R p] : CharP A p := charP_of_injective_ringHom (FaithfulSMul.algebraMap_injective R A) p

