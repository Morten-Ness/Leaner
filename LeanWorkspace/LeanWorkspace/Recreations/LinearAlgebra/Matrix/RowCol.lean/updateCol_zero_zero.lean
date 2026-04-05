import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateCol_zero_zero [DecidableEq n] [Zero α] (i : n) :
    (0 : Matrix m n α).updateCol i 0 = 0 := Matrix.updateCol_eq_self _ i

