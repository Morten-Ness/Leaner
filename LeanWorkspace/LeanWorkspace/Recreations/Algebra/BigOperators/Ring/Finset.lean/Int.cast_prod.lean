import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

theorem cast_prod {R : Type*} [CommRing R] (f : ι → ℤ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) := map_prod (Int.castRingHom R) _ _

