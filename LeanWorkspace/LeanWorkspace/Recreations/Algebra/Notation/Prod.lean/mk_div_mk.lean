import Mathlib

variable {G H M N P R S : Type*}

variable {G H : Type*} [Div G] [Div H]

theorem mk_div_mk (x₁ x₂ : G) (y₁ y₂ : H) : (x₁, y₁) / (x₂, y₂) = (x₁ / x₂, y₁ / y₂) := rfl

