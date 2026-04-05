import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem le_log_of_exp_le (hax : exp a ≤ x) : a ≤ log x := (WithZero.le_log_iff_exp_le (exp_pos.trans_le hax).ne').2 hax

