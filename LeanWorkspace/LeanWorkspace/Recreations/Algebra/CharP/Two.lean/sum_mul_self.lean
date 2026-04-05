import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by simp_rw [← pow_two, CharTwo.sum_sq]

