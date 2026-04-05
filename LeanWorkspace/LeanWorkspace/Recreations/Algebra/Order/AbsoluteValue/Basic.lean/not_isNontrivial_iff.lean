import Mathlib

variable {ι α R S : Type*}

variable {R : Type*} [Semiring R] {S : Type*} [Semiring S] [PartialOrder S] [IsOrderedRing S]

omit [IsOrderedRing S] in
theorem not_isNontrivial_iff (v : AbsoluteValue R S) :
    ¬ v.IsNontrivial ↔ ∀ x ≠ 0, v x = 1 := by
  simp only [AbsoluteValue.IsNontrivial]
  push Not
  rfl

