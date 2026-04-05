import Mathlib

variable {F α β γ δ : Type*}

variable {R S : Type*} [Mul R] [Add R] [Mul S] [Add S] [Preorder R] [Preorder S]

theorem symm_apply_lt (e : R ≃+*o S) {x : R} {y : S} : e.symm y < x ↔ y < e x := by
  simpa using e.toOrderIso.symm_apply_lt

