import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_self [DecidableEq n] : Matrix.updateCol M j c i j = c i := Function.update_self (β := fun _ => α) j (c i) (M i)

