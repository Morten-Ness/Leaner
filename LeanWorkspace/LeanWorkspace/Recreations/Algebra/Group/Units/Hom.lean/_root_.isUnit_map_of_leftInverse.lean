import Mathlib

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

variable [Monoid M] [Monoid N]

theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨IsUnit.of_leftInverse g hfg, IsUnit.map _⟩

