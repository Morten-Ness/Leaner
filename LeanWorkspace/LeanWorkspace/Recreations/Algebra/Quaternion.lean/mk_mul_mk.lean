import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Ring R]

theorem mk_mul_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (QuaternionAlgebra.mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) * QuaternionAlgebra.mk b₁ b₂ b₃ b₄ =
    QuaternionAlgebra.mk
      (a₁ * b₁ + c₁ * a₂ * b₂ + c₃ * a₃ * b₃ + c₂ * c₃ * a₃ * b₄ - c₁ * c₃ * a₄ * b₄)
      (a₁ * b₂ + a₂ * b₁ + c₂ * a₂ * b₂ - c₃ * a₃ * b₄ + c₃ * a₄ * b₃)
      (a₁ * b₃ + c₁ * a₂ * b₄ + a₃ * b₁ + c₂ * a₃ * b₂ - c₁ * a₄ * b₂)
      (a₁ * b₄ + a₂ * b₃ + c₂ * a₂ * b₄ - a₃ * b₂ + a₄ * b₁) := rfl

