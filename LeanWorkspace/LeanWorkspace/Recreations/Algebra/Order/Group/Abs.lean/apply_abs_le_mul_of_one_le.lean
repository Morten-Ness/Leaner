import Mathlib

variable {G : Type*}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {a b c : G}

theorem apply_abs_le_mul_of_one_le {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    (h : ∀ x, 1 ≤ f x) (a : G) : f |a| ≤ f a * f (-a) := apply_abs_le_mul_of_one_le' (h _) (h _)

