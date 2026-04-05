import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_self [DecidableEq m] : Matrix.updateRow M i b i = b := Function.update_self (β := fun _ => (n → α)) i b M

