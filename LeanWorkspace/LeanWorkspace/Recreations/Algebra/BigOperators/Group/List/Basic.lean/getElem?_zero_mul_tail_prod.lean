import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem getElem?_zero_mul_tail_prod (l : List M) : l[0]?.getD 1 * l.tail.prod = l.prod := by
  cases l <;> simp

