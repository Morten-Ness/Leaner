import Mathlib

variable {R : Type u}

theorem IsStrictOrderedRing.of_mul_pos [Ring R] [PartialOrder R] [IsOrderedAddMonoid R]
    [ZeroLEOneClass R] [Nontrivial R] (mul_pos : ∀ a b : R, 0 < a → 0 < b → 0 < a * b) :
    IsStrictOrderedRing R where
  mul_lt_mul_of_pos_left a ha b c hbc := by
    simpa only [mul_sub, sub_pos] using mul_pos _ _ ha (sub_pos.2 hbc)
  mul_lt_mul_of_pos_right a ha b c hbc := by
    simpa only [sub_mul, sub_pos] using mul_pos _ _ (sub_pos.2 hbc) ha

-- see Note [lower instance priority]

