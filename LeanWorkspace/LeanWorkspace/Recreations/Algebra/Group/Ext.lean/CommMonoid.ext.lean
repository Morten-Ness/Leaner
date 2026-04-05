import Mathlib

theorem CommMonoid.ext {M : Type*} ⦃m₁ m₂ : CommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) : m₁ = m₂ :=
  CommMonoid.toMonoid_injective <| Monoid.ext h_mul

