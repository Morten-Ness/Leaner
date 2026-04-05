import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

theorem degree_multiset_prod [Nontrivial R] : t.prod.degree = (t.map fun f => degree f).sum := map_multiset_prod (@degreeMonoidHom R _ _ _) _

