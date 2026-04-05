import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_zero_zero [DecidableEq m] [Zero α] (i : m) :
    (0 : Matrix m n α).updateRow i 0 = 0 := Matrix.updateRow_eq_self _ i

