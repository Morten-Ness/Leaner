import Mathlib

variable {α β : Type*}

variable {G : Type*} [Preorder G] {a b : G}

variable [AddGroup G] {x y : Gᵐ⁰}

theorem le_exp_log {x : Gᵐ⁰} :
    x ≤ exp (log x) := by
  cases x
  · simp
  · rfl

