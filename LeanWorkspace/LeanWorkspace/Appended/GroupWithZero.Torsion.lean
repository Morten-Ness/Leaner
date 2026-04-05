import Mathlib

section

variable {M : Type*} [CommMonoidWithZero M]

theorem IsMulTorsionFree.mk' [NoZeroDivisors M]
    (ih : ∀ x ≠ 0, ∀ y ≠ 0, ∀ n ≠ 0, (x ^ n : M) = y ^ n → x = y) :
    IsMulTorsionFree M := by
  refine ⟨fun n hn x y hxy ↦ ?_⟩
  by_cases h : x ≠ 0 ∧ y ≠ 0
  · exact ih x h.1 y h.2 n hn hxy
  have : IsReduced M := inferInstance
  grind [eq_zero_of_pow_eq_zero, zero_pow]

end
