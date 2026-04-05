import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem unit_map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) :
    (IsUnit.map h f).unit = f h.unit := rfl

