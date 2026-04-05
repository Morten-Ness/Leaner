import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

variable [One α] {s : Finset α} {a : α}

theorem map_one {f : α ↪ β} : map f 1 = {f 1} := map_singleton f 1

