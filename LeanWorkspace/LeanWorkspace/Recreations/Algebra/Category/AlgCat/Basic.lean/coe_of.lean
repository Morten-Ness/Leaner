import Mathlib

variable (R : Type u) [CommRing R]

set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem coe_of (X : Type v) [Ring X] [Algebra R X] : (of R X : Type v) = X := rfl

