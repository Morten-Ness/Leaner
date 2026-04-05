import Mathlib

variable {C : Type*} [Category* C] [Abelian C]

variable {K L : CochainComplex C ℤ} (f : K ⟶ L)

variable [EnoughInjectives C]

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁)

theorem ι_π : ι f n₁ ≫ π K L n₁ = f := by simp

