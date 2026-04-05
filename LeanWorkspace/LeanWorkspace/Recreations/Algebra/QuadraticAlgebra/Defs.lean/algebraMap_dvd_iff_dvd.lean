import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem algebraMap_dvd_iff_dvd {z w : R} :
    algebraMap R (QuadraticAlgebra R a b) z ∣ algebraMap R (QuadraticAlgebra R a b) w ↔ z ∣ w := by
  rw [QuadraticAlgebra.algebraMap_dvd_iff]
  simp

