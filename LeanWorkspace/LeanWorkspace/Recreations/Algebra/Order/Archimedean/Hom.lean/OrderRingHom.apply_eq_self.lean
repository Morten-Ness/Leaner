import Mathlib

variable {α β : Type*} [Field α] [LinearOrder α] [Field β] [LinearOrder β]

theorem OrderRingHom.apply_eq_self [IsStrictOrderedRing α] [Archimedean α] (f : α →+*o α) (x : α) :
    f x = x := by
  rw [f.eq_id]; rfl

