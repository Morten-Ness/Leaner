import Mathlib

variable (R : Type u) [Ring R]

set_option backward.privateInPublic true in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem coe_of (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := rfl

-- Ensure the roundtrips are reducibly defeq (so tactics like `rw` can see through them).
example (X : Type v) [Ring X] [Module R X] : (of R X : Type v) = X := by with_reducible rfl
example (M : ModuleCat.{v} R) : of R M = M := by with_reducible rfl

