import Mathlib

variable {G M : Type*} [Group G]

variable [Monoid M]

theorem coe_toHomUnits (f : G →* M) (g : G) : (f.toHomUnits g : M) = f g := rfl

