import Mathlib

variable {R A : Type*}

theorem all [Star R] [TrivialStar R] (r : R) : IsSelfAdjoint r := star_trivial _

