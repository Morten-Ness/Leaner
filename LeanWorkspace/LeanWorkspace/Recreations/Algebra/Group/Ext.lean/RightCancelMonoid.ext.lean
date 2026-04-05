import Mathlib

theorem RightCancelMonoid.ext {M : Type u} ⦃m₁ m₂ : RightCancelMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  RightCancelMonoid.toMonoid_injective <| Monoid.ext h_mul

