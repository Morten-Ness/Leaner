import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem degree_list_prod_le (l : List S[X]) : degree l.prod ≤ (l.map degree).sum := l.apply_prod_le_sum_map _ degree_one_le degree_mul_le

