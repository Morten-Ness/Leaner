import Mathlib

variable {ι α β M N P G : Type*}

theorem sum_const_nat (m n : ℕ) : sum (replicate m n) = m * n := sum_replicate m n

