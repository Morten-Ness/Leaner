import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Odd.mul_odd [HasDistribNeg R] (hf : f.Odd) (hg : g.Odd) : (f * g).Even := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, mul_neg, neg_mul, neg_neg]

