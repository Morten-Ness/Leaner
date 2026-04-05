import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_multiset_prod [CommSemiring R] (s : Multiset ℕ) : (↑s.prod : R) = (s.map (↑)).prod := map_multiset_prod (castRingHom R) _

