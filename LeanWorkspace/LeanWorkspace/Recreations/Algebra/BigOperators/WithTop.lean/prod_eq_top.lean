import Mathlib

variable {ι M M₀ : Type*}

variable [CommMonoidWithZero M₀] [NoZeroDivisors M₀] [Nontrivial M₀] [DecidableEq M₀]
  {s : Finset ι} {f : ι → WithTop M₀} {i : ι}

theorem prod_eq_top (hi : i ∈ s) (hi' : f i = ⊤) (h : ∀ j ∈ s, f j ≠ 0) :
    ∏ j ∈ s, f j = ⊤ := by
  classical rw [← prod_erase_mul _ _ hi]
  refine WithTop.mul_eq_top_iff.mpr (Or.inl ⟨?_, hi'⟩)
  refine prod_ne_zero_iff.mpr ?_
  intros
  simp_all only [ne_eq, mem_erase, not_false_eq_true]

