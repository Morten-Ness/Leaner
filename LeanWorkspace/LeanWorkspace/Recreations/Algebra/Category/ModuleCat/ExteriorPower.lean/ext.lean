import Mathlib

variable {R : Type u} [CommRing R]

variable {M : ModuleCat.{v} R} {N : ModuleCat.{max u v} R} {n : ℕ}

theorem ext {φ φ' : M.AlternatingMap N n} (h : ∀ (x : Fin n → M), φ x = φ' x) :
    φ = φ' := _root_.AlternatingMap.ext h

