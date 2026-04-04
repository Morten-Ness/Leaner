import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P] {ι : Type*}

variable {k}

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

theorem AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w : V → k} (hw₀ : ∑ x ∈ s, w x = 0)
    (hw₁ : ∑ x ∈ s, w x • x = 0) : ∀ x ∈ s, w x = 0 := by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx ↦ hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

