import Mathlib

variable {R A M : Type*}

variable [CommSemiring R]

variable [Semiring A] [Algebra R A]

theorem algebraMapSubmonoid_self (M : Submonoid R) : Algebra.algebraMapSubmonoid R M = M := Submonoid.map_id M

