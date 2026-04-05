import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable {S : Type*} [Semiring S]

theorem natDegree_list_prod_le (l : List S[X]) : natDegree l.prod ≤ (l.map natDegree).sum := l.apply_prod_le_sum_map _ natDegree_one.le fun _ _ => natDegree_mul_le

