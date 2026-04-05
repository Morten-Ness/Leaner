import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_list_prod [Semiring R] (s : List ℕ) : (↑s.prod : R) = (s.map (↑)).prod := map_list_prod (castRingHom R) _

