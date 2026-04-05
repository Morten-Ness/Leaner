import Mathlib

variable (R : Type u) (L : Type v) (M : Type w)

variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]

variable [LieRingModule L M] [LieModule R L M]

theorem isFaithful_iff' : IsFaithful R L M ↔ ∀ x : L, (∀ m : M, ⁅x, m⁆ = 0) → x = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m ↦ ?_
    rw [sub_lie, sub_eq_zero, ← toEnd_apply_apply R, ← toEnd_apply_apply R, hxy]

