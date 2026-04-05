import Mathlib

variable {α M N P : Type*}

variable {G : Type*} {H : Type*}

variable {F : Type*}

variable [DivisionCommMonoid α]

theorem invMonoidHom_comp_invMonoidHom : (invMonoidHom (α := α)).comp invMonoidHom = .id _ := by
  ext; simp

