import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem lt_log_of_exp_lt (hax : exp a < x) : a < log x := (WithZero.lt_log_iff_exp_lt (exp_pos.trans hax).ne').2 hax

