import Mathlib

variable {ι M N : Type*}

variable [MulOneClass M] {l : List M} {a : M}

theorem prod_map_one {l : List ι} :
    (l.map fun _ => (1 : M)).prod = 1 := by
  induction l with simp [*]

