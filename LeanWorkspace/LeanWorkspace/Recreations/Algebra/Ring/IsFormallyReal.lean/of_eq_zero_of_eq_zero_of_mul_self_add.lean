import Mathlib

variable {R : Type*}

theorem of_eq_zero_of_eq_zero_of_mul_self_add [NonUnitalNonAssocSemiring R]
    (h : ∀ {s a : R}, IsSumSq s → a * a + s = 0 → a = 0) : IsFormallyReal R where
  not_isSumNonzeroSq_zero := by
    suffices ∀ (x : R), IsSumNonzeroSq x → x ≠ 0 by grind
    intro x hx
    induction hx with
    | sq ha => exact fun hc ↦ ha (h IsSumSq.zero (by simpa using hc))
    | sq_add ha hs ih => grind [hs.isSumSq]

