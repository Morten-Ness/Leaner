import Mathlib

open scoped Pointwise Ring

variable {R : Type u} {A : Type v}

variable [CommSemiring R] [Ring A] [Algebra R A]

theorem preimage_units_mul_comm (a b : A) :
    ((↑) : Rˣ → R) ⁻¹' σ (a * b) = (↑) ⁻¹' σ (b * a) := Set.ext fun _ => spectrum.unit_mem_mul_comm

