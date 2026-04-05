import Mathlib

variable {R A : Type*}

theorem isStarNormal {R : Type*} [Mul R] [Star R] {x : R} (hx : IsSelfAdjoint x) :
    IsStarNormal x := ⟨by simp only [Commute, SemiconjBy, IsSelfAdjoint.star_eq hx]⟩

