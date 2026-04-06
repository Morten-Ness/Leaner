import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro x
  rw [Pi.mul_apply, Pi.mul_apply, hf x, hg x, neg_mul_neg]
