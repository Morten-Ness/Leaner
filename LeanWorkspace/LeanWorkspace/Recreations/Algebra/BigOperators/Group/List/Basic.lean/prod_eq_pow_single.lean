import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_eq_pow_single [DecidableEq M] (a : M) (h : ∀ a', a' ≠ a → a' ∈ l → a' = 1) :
    l.prod = a ^ l.count a := _root_.trans (by rw [map_id]) (List.prod_map_eq_pow_single a id h)

