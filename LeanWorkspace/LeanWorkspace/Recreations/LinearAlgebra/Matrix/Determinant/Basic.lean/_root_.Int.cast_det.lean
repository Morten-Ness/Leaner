import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {S : Type w} [CommRing S]

theorem _root_.Int.cast_det (M : Matrix n n ℤ) :
    (M.det : R) = (M.map fun x ↦ (x : R)).det := Int.castRingHom R |>.map_det M

