import Mathlib

variable {m n : Type*} [DecidableEq n] [Fintype n] [DecidableEq m] [Fintype m]

variable {R : Type v} [CommRing R]

variable {S : Type w} [CommRing S]

theorem _root_.Rat.cast_det {F : Type*} [Field F] [CharZero F] (M : Matrix n n ℚ) :
    (M.det : F) = (M.map fun x ↦ (x : F)).det := Rat.castHom F |>.map_det M

