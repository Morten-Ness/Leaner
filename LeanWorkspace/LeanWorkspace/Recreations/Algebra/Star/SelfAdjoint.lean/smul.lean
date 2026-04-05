import Mathlib

variable {R A : Type*}

theorem smul [Star R] [Star A] [SMul R A] [StarModule R A]
    {r : R} (hr : IsSelfAdjoint r) {x : A} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (r • x) := by
  simp only [isSelfAdjoint_iff, star_smul, IsSelfAdjoint.star_eq hr, IsSelfAdjoint.star_eq hx]

