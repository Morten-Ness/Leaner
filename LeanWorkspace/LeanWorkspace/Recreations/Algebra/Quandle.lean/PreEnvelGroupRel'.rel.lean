import Mathlib

theorem PreEnvelGroupRel'.rel {R : Type u} [Rack R] {a b : PreEnvelGroup R} :
    PreEnvelGroupRel' R a b → PreEnvelGroupRel R a b := PreEnvelGroupRel.rel

