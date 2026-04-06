import Mathlib

variable {F R S : Type*}

theorem map_rat_algebraMap [Semiring R] [Semiring S] [Algebra ℚ R] [Algebra ℚ S] (f : R →+* S)
    (r : ℚ) : f (algebraMap ℚ R r) = algebraMap ℚ S r := by
  simpa using (Commutes.all (f.comp (algebraMap R S)) (algebraMap ℚ R) r)
