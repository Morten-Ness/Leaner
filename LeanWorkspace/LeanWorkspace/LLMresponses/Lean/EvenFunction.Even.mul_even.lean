import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro x
  simp [Pi.mul_apply, hf x, hg x]
