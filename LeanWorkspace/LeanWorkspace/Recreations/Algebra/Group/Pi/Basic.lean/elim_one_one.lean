import Mathlib

variable {I : Type u}

variable {α β γ : Type*}

variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

variable (a a' : α → γ) (b b' : β → γ)

theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 := Sum.elim_const_const 1

