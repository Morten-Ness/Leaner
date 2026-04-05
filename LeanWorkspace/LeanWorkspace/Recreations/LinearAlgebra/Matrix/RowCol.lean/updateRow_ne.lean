import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_ne [DecidableEq m] {i' : m} (i_ne : i' ≠ i) : Matrix.updateRow M i b i' = M i' := Function.update_of_ne (β := fun _ => (n → α)) i_ne b M

