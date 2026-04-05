import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M] [Fintype ι]

variable [DecidableEq ι]

theorem prod_dite_eq (i : ι) (f : ∀ j, i = j → M) :
    ∏ j, (if h : i = j then f j h else 1) = f i rfl := by
  rw [Finset.prod_dite_eq, if_pos (Finset.mem_univ _)]

