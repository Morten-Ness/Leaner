import Mathlib

theorem PreEnvelGroupRel.trans {R : Type u} [Rack R] {a b c : PreEnvelGroup R} :
    PreEnvelGroupRel R a b → PreEnvelGroupRel R b c → PreEnvelGroupRel R a c
  | ⟨rab⟩, ⟨rbc⟩ => (rab.trans rbc).rel
