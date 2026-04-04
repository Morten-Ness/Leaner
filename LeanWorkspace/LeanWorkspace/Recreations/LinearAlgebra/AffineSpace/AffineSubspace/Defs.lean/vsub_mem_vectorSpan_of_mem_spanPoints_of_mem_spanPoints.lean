import Mathlib

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]

variable [AddTorsor V P]

variable (P) in

theorem vsub_mem_vectorSpan_of_mem_spanPoints_of_mem_spanPoints {s : Set P} {p₁ p₂ : P}
    (hp₁ : p₁ ∈ spanPoints k s) (hp₂ : p₂ ∈ spanPoints k s) : p₁ -ᵥ p₂ ∈ vectorSpan k s := by
  rcases hp₁ with ⟨p₁a, ⟨hp₁a, ⟨v₁, ⟨hv₁, hv₁p⟩⟩⟩⟩
  rcases hp₂ with ⟨p₂a, ⟨hp₂a, ⟨v₂, ⟨hv₂, hv₂p⟩⟩⟩⟩
  rw [hv₁p, hv₂p, vsub_vadd_eq_vsub_sub (v₁ +ᵥ p₁a), vadd_vsub_assoc, add_comm, add_sub_assoc]
  have hv₁v₂ : v₁ - v₂ ∈ vectorSpan k s := (vectorSpan k s).sub_mem hv₁ hv₂
  refine (vectorSpan k s).add_mem ?_ hv₁v₂
  exact vsub_mem_vectorSpan k hp₁a hp₂a

