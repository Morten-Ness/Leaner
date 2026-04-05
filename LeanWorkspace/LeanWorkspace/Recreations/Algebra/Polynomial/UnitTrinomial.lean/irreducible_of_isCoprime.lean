import Mathlib

open scoped Polynomial

variable (p q : ℤ[X])

theorem irreducible_of_isCoprime (hp : p.IsUnitTrinomial) (h : IsCoprime p p.mirror) :
    Irreducible p := Polynomial.IsUnitTrinomial.irreducible_of_coprime hp fun _ => h.isUnit_of_dvd'

