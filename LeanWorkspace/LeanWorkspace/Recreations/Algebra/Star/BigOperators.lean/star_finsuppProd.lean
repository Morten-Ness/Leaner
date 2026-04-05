import Mathlib

variable {R : Type*}

theorem star_finsuppProd {ι : Type*} {M : Type*} [Zero M] [CommMonoid R] [StarMul R]
    (s : ι →₀ M) (f : ι → M → R) : star (s.prod f) = s.prod (fun i m ↦ star f i m) := by
  simp [Finsupp.prod]

