import Mathlib

variable {α : Type u} {o n m : ℕ} {m' : Type uₘ} {n' : Type uₙ} {o' : Type uₒ}

variable (a b : ℕ)

variable [AddCommMonoid α] [Mul α]

theorem vec3_dotProduct' {a₀ a₁ a₂ b₀ b₁ b₂ : α} :
    ![a₀, a₁, a₂] ⬝ᵥ ![b₀, b₁, b₂] = a₀ * b₀ + a₁ * b₁ + a₂ * b₂ := by
  simp [add_assoc]

-- This is not tagged `@[simp]` because it does not mesh well with simp lemmas for
-- dot and cross products in dimension 3.

