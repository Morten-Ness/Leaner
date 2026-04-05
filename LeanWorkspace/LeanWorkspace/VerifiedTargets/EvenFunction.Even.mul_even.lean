import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Even.mul_even (hf : f.Even) (hg : g.Even) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a]

