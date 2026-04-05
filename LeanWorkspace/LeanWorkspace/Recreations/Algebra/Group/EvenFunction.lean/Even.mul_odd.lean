import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Even.mul_odd [HasDistribNeg R] (hf : f.Even) (hg : g.Odd) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg]

