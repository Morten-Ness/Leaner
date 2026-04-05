import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

theorem cast_sum [AddCommGroupWithOne R] (s : Finset ι) (f : ι → ℤ) :
    ↑(∑ x ∈ s, f x : ℤ) = ∑ x ∈ s, (f x : R) := map_sum (castAddHom R) _ _

