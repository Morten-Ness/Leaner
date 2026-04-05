import Mathlib

theorem mulEquiv_coe_eq {X Y : Type _} [Mul X] [Mul Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e := rfl

