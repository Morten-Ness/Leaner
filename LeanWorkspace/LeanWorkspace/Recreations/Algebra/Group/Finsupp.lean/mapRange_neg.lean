import Mathlib

variable {ι F M N O G H : Type*}

theorem mapRange_neg [NegZeroClass G] [NegZeroClass H] {f : G → H} {hf : f 0 = 0}
    (hf' : ∀ x, f (-x) = -f x) (v : ι →₀ G) : mapRange f hf (-v) = -mapRange f hf v := ext fun _ => by simp only [hf', Finsupp.neg_apply, mapRange_apply]

