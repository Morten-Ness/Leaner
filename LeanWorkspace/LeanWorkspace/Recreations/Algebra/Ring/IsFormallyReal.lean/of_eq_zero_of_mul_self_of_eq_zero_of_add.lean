import Mathlib

variable {R : Type*}

theorem of_eq_zero_of_mul_self_of_eq_zero_of_add [AddCommMonoid R] [Mul R]
    (hz : ∀ {a : R}, a * a = 0 → a = 0)
    (ha : ∀ {s₁ s₂ : R}, IsSumSq s₁ → IsSumSq s₂ → s₁ + s₂ = 0 → s₁ = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => grind
    | @sq_add b s hb hs ih => grind [ha (IsSumSq.mul_self b) hs.isSumSq]

