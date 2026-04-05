import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem sup'_one [SemilatticeSup β] (f : α → β) : sup' 1 Finset.one_nonempty f = f 1 := rfl

