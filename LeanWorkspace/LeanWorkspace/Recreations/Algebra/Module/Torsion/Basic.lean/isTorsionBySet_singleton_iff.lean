import Mathlib

variable {R M : Type*}

variable [Semiring R] [AddCommMonoid M] [Module R M] (s : Set R) (a : R)

theorem isTorsionBySet_singleton_iff : IsTorsionBySet R M {a} ↔ IsTorsionBy R M a := by
  refine ⟨fun h x => @h _ ⟨_, Set.mem_singleton _⟩, fun h x => ?_⟩
  rintro ⟨b, rfl : b = a⟩; exact @h _

