import Mathlib

variable {ι : Type*} {α : ι → Type*}

variable [∀ i, MulZeroClass (α i)] [DecidableEq ι] {i : ι} {f : ∀ i, α i}

theorem single_mul (i : ι) (x y : α i) : single i (x * y) = single i x * single i y := (MulHom.single _).map_mul _ _

