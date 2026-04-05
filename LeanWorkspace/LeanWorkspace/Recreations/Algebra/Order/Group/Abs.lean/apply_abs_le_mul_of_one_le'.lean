import Mathlib

variable {G : Type*}

variable [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G] {a b c : G}

theorem apply_abs_le_mul_of_one_le' {H : Type*} [MulOneClass H] [LE H]
    [MulLeftMono H] [MulRightMono H] {f : G → H}
    {a : G} (h₁ : 1 ≤ f a) (h₂ : 1 ≤ f (-a)) : f |a| ≤ f a * f (-a) := (le_total a 0).rec (fun ha => (abs_of_nonpos ha).symm ▸ le_mul_of_one_le_left' h₁) fun ha =>
    (abs_of_nonneg ha).symm ▸ le_mul_of_one_le_right' h₂

