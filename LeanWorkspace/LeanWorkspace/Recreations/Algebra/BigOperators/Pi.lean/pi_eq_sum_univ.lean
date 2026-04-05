import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem pi_eq_sum_univ {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • fun j => if i = j then (1 : R) else 0 := by
  ext
  simp

