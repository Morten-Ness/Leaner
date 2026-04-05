import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

theorem OrderRingIso.eq_refl [IsStrictOrderedRing α] [Archimedean α] (f : α ≃+*o α) : f = .refl _ := Subsingleton.elim ..

