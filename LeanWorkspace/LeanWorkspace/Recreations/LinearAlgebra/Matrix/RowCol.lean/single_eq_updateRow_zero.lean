import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem single_eq_updateRow_zero [DecidableEq m] [DecidableEq n] [Zero α] (i : m) (j : n) (r : α) :
    single i j r = Matrix.updateRow 0 i (Pi.single j r) := single_eq_of_single_single _ _ _

