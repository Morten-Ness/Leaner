import Mathlib

variable {R : Type u} [Ring R]

variable (S : ShortComplex (ModuleCat.{v} R))

theorem moduleCat_exact_iff :
    S.Exact ↔ ∀ (x₂ : S.X₂) (_ : S.g x₂ = 0), ∃ (x₁ : S.X₁), S.f x₁ = x₂ := S.exact_iff_of_hasForget

