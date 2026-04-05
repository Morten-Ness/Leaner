import Mathlib

open scoped Pointwise Ring

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

theorem spectrum.units_conjugate {a : A} {u : Aˣ} :
    spectrum R (u * a * u⁻¹) = spectrum R a := by
  suffices ∀ (b : A) (v : Aˣ), spectrum R (v * b * v⁻¹) ⊆ spectrum R b by
    refine le_antisymm (this a u) ?_
    apply le_of_eq_of_le ?_ <| this (u * a * u⁻¹) u⁻¹
    simp [mul_assoc]
  intro a u μ hμ
  rw [spectrum.mem_iff spectrum] at hμ ⊢
  contrapose! hμ
  simpa [mul_sub, sub_mul, Algebra.right_comm] using u.isUnit.mul hμ |>.mul u⁻¹.isUnit

