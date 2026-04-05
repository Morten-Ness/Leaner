import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

theorem cast_list_prod [Ring R] (s : List ℤ) : (↑s.prod : R) = (s.map (↑)).prod := map_list_prod (castRingHom R) _

