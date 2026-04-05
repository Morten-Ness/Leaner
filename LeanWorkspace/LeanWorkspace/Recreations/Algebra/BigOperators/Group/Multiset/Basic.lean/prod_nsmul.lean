import Mathlib

variable {F ι κ G M N O : Type*}

variable [CommMonoid M] [CommMonoid N] {s t : Multiset M} {a : M} {m : Multiset ι} {f g : ι → M}

theorem prod_nsmul (m : Multiset M) : ∀ n : ℕ, (n • m).prod = m.prod ^ n
  | 0 => by
    rw [zero_nsmul, pow_zero]
    rfl
  | n + 1 => by rw [add_nsmul, one_nsmul, pow_add, pow_one, Multiset.prod_add, prod_nsmul m n]
