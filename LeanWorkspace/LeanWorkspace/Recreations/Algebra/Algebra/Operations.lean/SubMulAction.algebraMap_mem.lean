import Mathlib

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

theorem algebraMap_mem (r : R) : algebraMap R A r ∈ (1 : SubMulAction R A) := ⟨r, (algebraMap_eq_smul_one r).symm⟩

