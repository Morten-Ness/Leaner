import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℕ} {n : ℕ}

theorem cast_prod [CommSemiring R] (f : ι → ℕ) (s : Finset ι) :
    (↑(∏ i ∈ s, f i) : R) = ∏ i ∈ s, (f i : R) := map_prod (castRingHom R) _ _

