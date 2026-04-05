import Mathlib

variable {M N γ : Type*}

variable [Monoid M] [CommMonoid N] [MulDistribMulAction M N]

theorem smul_finprod' {ι : Sort*} [Finite ι] {f : ι → N} (r : M) :
    r • ∏ᶠ x : ι, f x = ∏ᶠ x : ι, r • (f x) := by
  cases nonempty_fintype (PLift ι)
  simp only [finprod_eq_prod_plift_of_mulSupport_subset (s := Finset.univ) (by simp),
    Finset.smul_prod']

