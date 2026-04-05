import Mathlib

variable {S T R : Type*} {c₁ c₂ c₃ : R} (r x y : R) (a b : ℍ[R,c₁,c₂,c₃])

variable [Add R]

theorem mk_add_mk (a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄ : R) :
    (QuaternionAlgebra.mk a₁ a₂ a₃ a₄ : ℍ[R,c₁,c₂,c₃]) + QuaternionAlgebra.mk b₁ b₂ b₃ b₄ =
    QuaternionAlgebra.mk (a₁ + b₁) (a₂ + b₂) (a₃ + b₃) (a₄ + b₄) := rfl

