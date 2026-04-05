import Mathlib

variable {R : Type*}

variable {S T : Type*} {a b} (r : R) (x y : QuadraticAlgebra R a b)

variable [CommSemiring R]

theorem algebraMap_dvd_iff {r : R} {z : QuadraticAlgebra R a b} :
    (algebraMap R (QuadraticAlgebra R a b) r) ∣ z ↔ r ∣ z.re ∧ r ∣ z.im := by
  constructor
  · rintro ⟨x, rfl⟩
    simp
  · rintro ⟨⟨r, hr⟩, ⟨i, hi⟩⟩
    use ⟨r, i⟩
    simp [QuadraticAlgebra.ext_iff, hr, hi, ← QuadraticAlgebra.C_eq_algebraMap]

