import Mathlib

variable {M A B : Type*}

variable [Monoid M] {a : M}

theorem map_powers {N : Type*} {F : Type*} [Monoid N] [FunLike F M N] [MonoidHomClass F M N]
    (f : F) (m : M) :
    (Submonoid.powers m).map f = Submonoid.powers (f m) := by
  simp only [Submonoid.powers_eq_closure, map_mclosure f, Set.image_singleton]

