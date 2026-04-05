import Mathlib

variable {α β : Type*} [Neg α]

variable {R : Type*} [Mul R] {f g : α → R}

theorem Odd.mul_even [HasDistribNeg R] (hf : f.Odd) (hg : g.Even) : (f * g).Odd := by
  intro a
  simp only [Pi.mul_apply, hf a, hg a, neg_mul]

