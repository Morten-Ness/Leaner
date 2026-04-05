import Mathlib

variable (ι : Type v) (β : ι → Type w)

variable [∀ i, AddCommMonoid (β i)]

variable [DecidableEq ι]

theorem sum_univ_of [Fintype ι] (x : ⨁ i, β i) :
    ∑ i ∈ Finset.univ, DirectSum.of β i (x i) = x := by
  ext i
  simp [DirectSum.of_apply]

