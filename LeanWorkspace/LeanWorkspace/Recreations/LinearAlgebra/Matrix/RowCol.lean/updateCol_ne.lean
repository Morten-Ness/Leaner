import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_ne [DecidableEq n] {j' : n} (j_ne : j' ≠ j) :
    Matrix.updateCol M j c i j' = M i j' := Function.update_of_ne (β := fun _ => α) j_ne (c i) (M i)

