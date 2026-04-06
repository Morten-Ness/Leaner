import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι → M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := by
  simpa using List.prod_hMul_prod_comm (L := l.map f) (L' := l.map g)
