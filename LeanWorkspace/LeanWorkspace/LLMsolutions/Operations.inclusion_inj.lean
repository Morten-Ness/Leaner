import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

theorem inclusion_inj {S T : Submonoid M} (h : S ≤ T) {x y : S} :
    Submonoid.inclusion h x = Submonoid.inclusion h y ↔ x = y := by
  constructor
  · intro hxy
    apply Subtype.ext
    exact congrArg (fun z : T => z.1) hxy
  · intro hxy
    cases hxy
    rfl
