import Mathlib

variable {ι κ M R : Type*} {s s₁ s₂ : Finset ι} {i : ι}

variable {ι : Type*} {s : Finset ι} {f : ι → ℤ} {n : ℤ}

theorem cast_multiset_sum [AddCommGroupWithOne R] (s : Multiset ℤ) :
    (↑s.sum : R) = (s.map (↑)).sum := map_multiset_sum (castAddHom R) _

