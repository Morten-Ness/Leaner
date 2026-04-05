import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

theorem OrderRingHom.eq_id [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) : f = .id _ := Subsingleton.elim ..

