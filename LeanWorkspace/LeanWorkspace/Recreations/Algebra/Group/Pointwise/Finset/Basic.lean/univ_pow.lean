import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [DecidableEq α] [DecidableEq β]

variable [Monoid α] {s t : Finset α} {a : α} {m n : ℕ}

theorem univ_pow [Fintype α] (hn : n ≠ 0) : (univ : Finset α) ^ n = univ := coe_injective <| by rw [Finset.coe_pow, coe_univ, Set.univ_pow hn]

