import Mathlib

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [CommSemiring R] [NoZeroDivisors R] (f : ι → R[X]) (t : Multiset R[X])

theorem degree_prod [Nontrivial R] : (∏ i ∈ s, f i).degree = ∑ i ∈ s, (f i).degree := map_prod (@degreeMonoidHom R _ _ _) _ _

