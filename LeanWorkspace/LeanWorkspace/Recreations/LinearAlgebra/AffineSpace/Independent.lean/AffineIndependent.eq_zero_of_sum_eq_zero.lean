import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

theorem AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent k p)
    (hw₀ : ∑ i ∈ s, w i = 0) (hw₁ : ∑ i ∈ s, w i • p i = 0) : ∀ i ∈ s, w i = 0 := affineIndependent_iff.1 hp _ _ hw₀ hw₁

