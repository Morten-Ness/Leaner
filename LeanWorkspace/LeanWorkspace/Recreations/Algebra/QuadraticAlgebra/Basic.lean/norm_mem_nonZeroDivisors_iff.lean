import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem norm_mem_nonZeroDivisors_iff {z : QuadraticAlgebra R a b} :
    z.norm ∈ R⁰ ↔ z ∈ (QuadraticAlgebra R a b)⁰ := by
  constructor
  · simp only [mem_nonZeroDivisors_iff_right]
    intro h w hw
    have : QuadraticAlgebra.norm z • w = 0 := by
      rw [← C_mul_eq_smul, C_eq_algebraMap, QuadraticAlgebra.algebraMap_norm_eq_mul_star, mul_comm, ← mul_assoc, hw,
        zero_mul]
    simp only [QuadraticAlgebra.ext_iff, re_smul, smul_eq_mul, mul_comm, re_zero, im_smul,
      im_zero] at this
    ext <;> simp [h _ this.left, h _ this.right]
  · intro hz
    rw [← QuadraticAlgebra.algebraMap_mem_nonZeroDivisors_iff, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    exact Submonoid.mul_mem _ hz (QuadraticAlgebra.star_mem_nonZeroDivisors hz)

