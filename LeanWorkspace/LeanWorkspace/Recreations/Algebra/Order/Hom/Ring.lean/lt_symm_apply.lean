import Mathlib

variable {F α β γ δ : Type*}

variable {R S : Type*} [Mul R] [Add R] [Mul S] [Add S] [Preorder R] [Preorder S]

theorem lt_symm_apply (e : R ≃+*o S) {x : R} {y : S} : x < e.symm y ↔ e x < y := by
  simpa using e.toOrderIso.lt_symm_apply

