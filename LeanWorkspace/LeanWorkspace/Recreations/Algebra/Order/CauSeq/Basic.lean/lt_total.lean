import Mathlib

variable {α β : Type*}

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]

theorem lt_total (f g : CauSeq α abs) : f < g ∨ f ≈ g ∨ g < f := (CauSeq.trichotomy (g - f)).imp_right fun h =>
    h.imp (fun h => Setoid.symm h) fun h => by rwa [neg_sub] at h

