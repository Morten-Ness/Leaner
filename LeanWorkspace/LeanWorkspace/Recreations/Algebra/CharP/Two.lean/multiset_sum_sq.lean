import Mathlib

variable {R ι : Type*}

variable [CommSemiring R] [CharP R 2]

private def sqAddMonoidHom : R →+ R where
  toFun := (· ^ 2)
  map_zero' := zero_pow two_ne_zero
  map_add' := CharTwo.add_sq


theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum := map_multiset_sum sqAddMonoidHom _

