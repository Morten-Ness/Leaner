import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

theorem cast_list_sum [AddGroupWithOne R] (s : List ℤ) : (↑s.sum : R) = (s.map (↑)).sum := map_list_sum (castAddHom R) _

