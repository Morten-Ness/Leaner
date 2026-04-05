import Mathlib

variable {M : Type u} {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

theorem map_mk (f : M →* N) (val inv : M) (val_inv inv_val) :
    Units.map f (Units.mk val inv val_inv inv_val) =
      Units.mk (f val) (f inv) (by simp [← map_mul, val_inv]) (by simp [← map_mul, inv_val]) := rfl

