import Mathlib

open scoped Pointwise

variable {M : Type*}

variable [ConditionallyCompleteLattice M]

variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

theorem csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sInf (s / t) = sInf s / sSup t := by
  rw [div_eq_mul_inv, csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, csInf_inv ht₀ ht₁, div_eq_mul_inv]

