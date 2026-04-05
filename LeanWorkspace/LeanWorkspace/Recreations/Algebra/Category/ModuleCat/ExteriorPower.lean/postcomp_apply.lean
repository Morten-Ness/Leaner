import Mathlib

variable {R : Type u} [CommRing R]

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

variable (φ : M.AlternatingMap N n) {N' : ModuleCat.{max u v} R} (g : N ⟶ N')

theorem postcomp_apply (x : Fin n → M) :
    φ.postcomp g x = g (φ x) := rfl

