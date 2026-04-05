import Mathlib

variable {ι κ M β γ : Type*} {s : Finset ι}

variable [CommMonoid M]

theorem prod_update_of_notMem [DecidableEq ι] {s : Finset ι} {i : ι} (h : i ∉ s) (f : ι → M)
    (b : M) : ∏ x ∈ s, Function.update f i b x = ∏ x ∈ s, f x := by
  apply prod_congr rfl
  intro j hj
  have : j ≠ i := by
    rintro rfl
    exact h hj
  simp [this]

