import Mathlib

open scoped Finset

variable {ι κ M N R α : Type*}

theorem pi_eq_sum_univ' {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*} [NonAssocSemiring R]
    (x : ι → R) : x = ∑ i, (x i) • Pi.single (M := fun _ ↦ R) i 1 := by
  convert pi_eq_sum_univ x
  aesop

