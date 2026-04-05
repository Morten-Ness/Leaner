import Mathlib

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]

theorem mem_one' {x : A} : x ∈ (1 : SubMulAction R A) ↔ ∃ y, algebraMap R A y = x := exists_congr fun r => by rw [algebraMap_eq_smul_one]

