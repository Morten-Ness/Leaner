import Mathlib

open scoped Pointwise

variable {F α β γ : Type*}

theorem smul_set_pi_of_isUnit {M ι : Type*} {α : ι → Type*} [Monoid M] [∀ i, MulAction M (α i)]
    {c : M} (hc : IsUnit c) (I : Set ι) (s : ∀ i, Set (α i)) : c • I.pi s = I.pi (c • s) := by
  lift c to Mˣ using hc
  exact Set.smul_set_pi c I s

