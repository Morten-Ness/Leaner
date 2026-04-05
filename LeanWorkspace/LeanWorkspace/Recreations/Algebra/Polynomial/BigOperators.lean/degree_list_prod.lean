import Mathlib

open scoped Polynomial

variable {R : Type u} {ι : Type w}

variable (s : Finset ι)

variable [Semiring R] [NoZeroDivisors R]

theorem degree_list_prod [Nontrivial R] (l : List R[X]) : l.prod.degree = (l.map degree).sum := map_list_prod (@degreeMonoidHom R _ _ _) l

