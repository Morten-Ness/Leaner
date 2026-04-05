import Mathlib

variable {G : Type*}

variable [Mul G]

variable {R : Type*}

theorem IsRegular.all [Mul R] [IsCancelMul R] (g : R) : IsRegular g := ⟨.all g, .all g⟩

