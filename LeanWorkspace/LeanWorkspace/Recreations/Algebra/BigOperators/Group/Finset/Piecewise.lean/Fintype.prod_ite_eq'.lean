import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

variable [DecidableEq ι]

theorem prod_ite_eq' (i : ι) (f : ι → M) : ∏ j, (if j = i then f j else 1) = f i := by
  rw [Finset.prod_ite_eq', if_pos (Finset.mem_univ _)]

