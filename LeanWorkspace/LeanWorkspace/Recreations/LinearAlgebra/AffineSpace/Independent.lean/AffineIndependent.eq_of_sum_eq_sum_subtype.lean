import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

theorem AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w₁ w₂ : V → k} (hw : ∑ i ∈ s, w₁ i = ∑ i ∈ s, w₂ i)
    (hwp : ∑ i ∈ s, w₁ i • i = ∑ i ∈ s, w₂ i • i) : ∀ i ∈ s, w₁ i = w₂ i := by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

