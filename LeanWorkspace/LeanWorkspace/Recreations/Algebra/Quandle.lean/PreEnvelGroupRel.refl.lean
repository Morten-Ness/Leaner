import Mathlib

theorem PreEnvelGroupRel.refl {R : Type u} [Rack R] {a : PreEnvelGroup R} :
    PreEnvelGroupRel R a a := PreEnvelGroupRel.rel PreEnvelGroupRel'.refl

