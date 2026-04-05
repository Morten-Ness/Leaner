import Mathlib

variable {M : Type*}

theorem map {M N : Type*} [Monoid M] [Monoid N] {F : Type*} [FunLike F M N] [MonoidHomClass F M N]
    (f : F) {x y : M} (ha : Associated x y) : Associated (f x) (f y) :=
  ha.map f
