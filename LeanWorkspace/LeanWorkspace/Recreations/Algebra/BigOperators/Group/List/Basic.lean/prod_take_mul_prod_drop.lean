import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_take_mul_prod_drop (L : List M) (i : ℕ) :
    (L.take i).prod * (L.drop i).prod = L.prod := by
  simp [← prod_append]

