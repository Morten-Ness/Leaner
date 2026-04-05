import Mathlib

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

variable (s : Subsemiring R)

theorem toSubmonoid_mono : Monotone (toSubmonoid : Subsemiring R → Submonoid R) := Subsemiring.toSubmonoid_strictMono.monotone

