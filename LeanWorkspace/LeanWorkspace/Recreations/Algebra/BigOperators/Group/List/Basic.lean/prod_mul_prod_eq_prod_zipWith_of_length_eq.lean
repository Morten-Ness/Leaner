import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem prod_mul_prod_eq_prod_zipWith_of_length_eq (l l' : List M) (h : l.length = l'.length) :
    l.prod * l'.prod = (zipWith (· * ·) l l').prod := by
  apply (List.prod_mul_prod_eq_prod_zipWith_mul_prod_drop l l').trans
  rw [← h, drop_length, h, drop_length, prod_nil, mul_one, mul_one]

