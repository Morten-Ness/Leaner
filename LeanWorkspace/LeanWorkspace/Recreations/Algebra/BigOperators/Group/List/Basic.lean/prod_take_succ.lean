import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_take_succ (L : List M) (i : ℕ) (p : i < L.length) :
    (L.take (i + 1)).prod = (L.take i).prod * L[i] := by
  rw [← take_concat_get' _ _ p, prod_append]
  simp

