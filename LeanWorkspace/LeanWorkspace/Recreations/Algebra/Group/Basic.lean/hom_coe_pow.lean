import Mathlib

variable {α β G M : Type*}

theorem hom_coe_pow {F : Type*} [Monoid F] (c : F → M → M) (h1 : c 1 = id)
    (hmul : ∀ f g, c (f * g) = c f ∘ c g) (f : F) : ∀ n, c (f ^ n) = (c f)^[n]
  | 0 => by
    rw [pow_zero, h1]
    rfl
  | n + 1 => by rw [pow_succ, iterate_succ, hmul, hom_coe_pow c h1 hmul f n]
