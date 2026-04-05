import Mathlib

theorem negOnePow_add (n₁ n₂ : ℤ) :
    (n₁ + n₂).negOnePow = n₁.negOnePow * n₂.negOnePow := zpow_add _ _ _

