import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem algebraMapSubmonoid_powers {S : Type*} [Semiring S] [Algebra R S] (r : R) :
    Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r) := by
  ext x
  simp [Submonoid.mem_powers_iff]
