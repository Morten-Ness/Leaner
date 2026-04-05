import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [ConditionallyCompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

theorem csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sSup (s / t) = sSup s / sInf t := by
  rw [div_eq_mul_inv, csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, csSup_inv ht₀ ht₁, div_eq_mul_inv]

