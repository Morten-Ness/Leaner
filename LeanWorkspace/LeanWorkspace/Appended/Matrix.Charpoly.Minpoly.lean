import Mathlib

section

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

variable (M : Matrix n n R)

theorem isIntegral : IsIntegral R M := ⟨M.charpoly, ⟨charpoly_monic M, aeval_self_charpoly M⟩⟩

end

section

variable {R : Type u} [CommRing R]

variable {n : Type v} [DecidableEq n] [Fintype n]

variable {N : Type w} [AddCommGroup N] [Module R N]

variable (M : Matrix n n R)

theorem minpoly_dvd_charpoly {K : Type*} [Field K] (M : Matrix n n K) : minpoly K M ∣ M.charpoly := minpoly.dvd _ _ (aeval_self_charpoly M)

end
