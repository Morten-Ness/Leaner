import Mathlib

variable {R : Type*} {a b : R}

variable [CommRing R]

theorem algebraMap_mem_nonZeroDivisors_iff {r : R} :
    algebraMap R (QuadraticAlgebra R a b) r ∈ (QuadraticAlgebra R a b)⁰ ↔ r ∈ R⁰ := by
  simp only [mem_nonZeroDivisors_iff_right]
  constructor
  · intro H x hxr
    rw [← algebraMap_inj, map_zero]
    apply H
    rw [← map_mul, hxr, map_zero]
  · intro h z hz
    rw [QuadraticAlgebra.ext_iff, re_zero, im_zero] at hz
    simp only [re_mul, algebraMap_re, algebraMap_im, mul_zero, add_zero, im_mul, zero_add] at hz
    simp [QuadraticAlgebra.ext_iff, re_zero, im_zero, h _ hz.left, h _ hz.right]

