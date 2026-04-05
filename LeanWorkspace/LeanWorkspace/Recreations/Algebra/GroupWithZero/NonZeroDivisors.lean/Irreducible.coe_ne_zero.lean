import Mathlib

theorem Irreducible.coe_ne_zero {M₀ S : Type*} [MonoidWithZero M₀] [SetLike S M₀]
    [SubmonoidClass S M₀] {s : S} {x : s} (hx : Irreducible x) : (x : M₀) ≠ 0 := fun h ↦ hx.1 <| by simpa using hx.2 (a := x) (b := x) (by ext; simp [h])

