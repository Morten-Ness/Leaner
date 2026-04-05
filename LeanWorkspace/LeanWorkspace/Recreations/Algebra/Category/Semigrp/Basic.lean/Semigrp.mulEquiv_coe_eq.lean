import Mathlib

theorem mulEquiv_coe_eq {X Y : Type _} [Semigroup X] [Semigroup Y] (e : X ≃* Y) :
    (ofHom (e : X →ₙ* Y)).hom = ↑e := rfl

