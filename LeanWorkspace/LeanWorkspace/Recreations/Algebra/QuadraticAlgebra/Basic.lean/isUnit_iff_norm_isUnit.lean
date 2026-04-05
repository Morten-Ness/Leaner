import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem isUnit_iff_norm_isUnit {x : QuadraticAlgebra R a b} :
    IsUnit x ↔ IsUnit (x.norm) := by
  constructor
  · exact IsUnit.map QuadraticAlgebra.norm
  · simp only [isUnit_iff_exists]
    rintro ⟨r, hr, hr'⟩
    rw [← C_inj (R := R) (a := a) (b := b), C_mul, C_eq_algebraMap, QuadraticAlgebra.algebraMap_norm_eq_mul_star,
      mul_assoc, map_one] at hr
    refine ⟨_, hr, ?_⟩
    rw [mul_comm, hr]

