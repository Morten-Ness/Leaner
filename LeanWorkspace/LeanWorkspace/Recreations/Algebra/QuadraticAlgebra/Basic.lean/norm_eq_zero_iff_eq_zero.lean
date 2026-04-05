import Mathlib

variable {R : Type*} {a b : R}

variable [Field R] [Hab : Fact (∀ r, r ^ 2 ≠ a + b * r)]

theorem norm_eq_zero_iff_eq_zero {z : QuadraticAlgebra R a b} :
    QuadraticAlgebra.norm z = 0 ↔ z = 0 := by
  constructor
  · intro hz
    rw [QuadraticAlgebra.norm_def] at hz
    by_cases h : z.im = 0
    · simp [h] at hz
      aesop
    · exfalso
      rw [← pow_two, sub_eq_zero, ← eq_sub_iff_add_eq] at hz
      apply Hab.out (-z.re / z.im)
      grind
  · intro hz
    simp [hz]

