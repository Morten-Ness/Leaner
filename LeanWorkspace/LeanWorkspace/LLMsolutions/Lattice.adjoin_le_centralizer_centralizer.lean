FAIL
import Mathlib

universe uR uS uA uB

variable {R : Type uR} {S : Type uS} {A : Type uA} {B : Type uB}

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]

variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

variable {s t : Set A}

theorem adjoin_le_centralizer_centralizer (s : Set A) :
    Algebra.adjoin R s ≤ Subalgebra.centralizer R (Subalgebra.centralizer R s) := by
  rw [Algebra.adjoin_le_iff]
  intro x hx
  change x ∈ Subalgebra.centralizer R (↑(Subalgebra.centralizer R s) : Set A)
  rw [Subalgebra.mem_centralizer_iff]
  intro y hy
  exact (Subalgebra.mem_centralizer_iff.mp hy) x hx
