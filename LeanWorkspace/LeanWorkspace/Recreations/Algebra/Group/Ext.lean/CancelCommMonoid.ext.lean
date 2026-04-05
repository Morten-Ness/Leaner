import Mathlib

theorem CancelCommMonoid.ext {M : Type*} ⦃m₁ m₂ : CancelCommMonoid M⦄
    (h_mul : (letI := m₁; HMul.hMul : M → M → M) = (letI := m₂; HMul.hMul : M → M → M)) :
    m₁ = m₂ :=
  CancelCommMonoid.toCommMonoid_injective <| CommMonoid.ext h_mul

