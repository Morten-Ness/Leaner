import Mathlib

theorem envelAction_prop {R : Type*} [Rack R] (x y : R) :
    Rack.envelAction (Rack.toEnvelGroup R x) y = x ◃ y := rfl

