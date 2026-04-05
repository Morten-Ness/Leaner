import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

theorem prod_mono_right (s : Subsemiring R) : Monotone fun t : Subsemiring S => s.prod t := Subsemiring.prod_mono (le_refl s)

