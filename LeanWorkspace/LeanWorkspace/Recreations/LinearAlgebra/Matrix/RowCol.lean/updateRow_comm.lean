import Mathlib

variable {l m n o : Type*}

variable {R : Type*} {α : Type v} {β : Type w}

variable {ι : Type*}

variable {M : Matrix m n α} {i : m} {j : n} {b : n → α} {c : m → α}

theorem updateRow_comm [DecidableEq m] (A : Matrix m n α) {i i' : m} (h : i ≠ i') (x y : n → α) :
    (A.updateRow i x).updateRow i' y = (A.updateRow i' y).updateRow i x := Function.update_comm h _ _ _

