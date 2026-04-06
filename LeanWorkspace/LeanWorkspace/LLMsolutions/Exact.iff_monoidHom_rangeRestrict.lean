FAIL
import Mathlib

variable {R M M' N N' P P' : Type*}

variable [Group M] [Group N] [Group P] {f : M →* N} {g : N →* P}

theorem iff_monoidHom_rangeRestrict :
    Function.MulExact f g ↔ Function.MulExact f.range.subtype g.rangeRestrict := by
  rw [MonoidHom.mulExact_iff, MonoidHom.mulExact_iff]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext x
      rfl
    · ext y
      constructor
      · intro hy
        change g y = 1 at hy
        rw [h.2]
        exact hy
      · rintro ⟨x, rfl⟩
        change g (f x) = 1
        rw [h.1]
        simp
  · intro h
    refine ⟨?_, ?_⟩
    · ext x
      exact congrArg Subtype.val (DFunLike.congr_fun h.1 x)
    · ext y
      constructor
      · intro hy
        have hy' : g.rangeRestrict y = 1 := by
          ext
          exact hy
        rw [h.2] at hy'
        rcases hy' with ⟨x, rfl⟩
        rfl
      · intro hy
        rw [← h.2]
        rcases hy with ⟨x, rfl⟩
        change g.rangeRestrict (f x) = 1
        ext
        simpa [h.1] using DFunLike.congr_fun h.1 x
