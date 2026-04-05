import Mathlib

variable {ι α β M N P G : Type*}

variable [Monoid M] [Monoid N] [Monoid P] {l l₁ l₂ : List M} {a : M}

theorem prod_map_mul {M : Type*} [CommMonoid M] {l : List ι} {f g : ι → M} :
    (l.map fun i => f i * g i).prod = (l.map f).prod * (l.map g).prod := List.prod_hom₂ l (· * ·) mul_mul_mul_comm (mul_one _) _ _

