import Mathlib

variable {R : Type*} [CommSemiring R] {S : Type*} [CommSemiring S]

variable (f : R →* S) (g : R →+* S) (p m n : ℕ) [ExpChar R p] [ExpChar S p] (x y : R)

theorem RingHom.frobenius_comm : g.comp (frobenius R p) = (frobenius S p).comp g := ext <| map_frobenius g p

