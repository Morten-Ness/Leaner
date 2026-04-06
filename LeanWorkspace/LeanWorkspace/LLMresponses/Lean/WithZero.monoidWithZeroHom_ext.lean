import Mathlib

variable {α β γ : Type*}

variable [MulOneClass α]

variable [MulZeroOneClass β]

theorem monoidWithZeroHom_ext ⦃f g : WithZero α →*₀ β⦄
    (h : f.toMonoidHom.comp WithZero.coeMonoidHom = g.toMonoidHom.comp WithZero.coeMonoidHom) :
    f = g := by
  ext x <;> simp
  exact congrArg (fun k : α →* β => k x) h
