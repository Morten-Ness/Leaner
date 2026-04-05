import Mathlib

variable {ι α β M N P G : Type*}

variable [CommGroup G]

theorem alternatingProd_append :
    ∀ l₁ l₂ : List G,
      alternatingProd (l₁ ++ l₂) = alternatingProd l₁ * alternatingProd l₂ ^ (-1 : ℤ) ^ length l₁
  | [], l₂ => by simp
  | a :: l₁, l₂ => by
    simp_rw [cons_append, alternatingProd_cons, alternatingProd_append, length_cons, pow_succ',
      Int.neg_mul, one_mul, zpow_neg, ← div_eq_mul_inv, div_div]
