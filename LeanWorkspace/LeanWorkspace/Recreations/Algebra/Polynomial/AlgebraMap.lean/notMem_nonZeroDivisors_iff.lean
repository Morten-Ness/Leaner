import Mathlib

open scoped Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {A : Type z} {A' B : Type*} {a b : R} {n : ℕ}

variable [CommSemiring R] {a p : R[X]}

theorem notMem_nonZeroDivisors_iff {P : R[X]} : P ∉ R[X]⁰ ↔ ∃ a : R, a ≠ 0 ∧ a • P = 0 := by
  refine ⟨fun hP ↦ ?_, fun ⟨a, ha, h⟩ h1 ↦ ha <| C_eq_zero.1 <| (h1.2 _) <| smul_eq_C_mul a ▸ h⟩
  by_contra! h
  obtain ⟨Q, hQ⟩ := notMem_nonZeroDivisors_iff_right.1 hP
  refine hQ.2 (Polynomial.eq_zero_of_mul_eq_zero_of_smul P (fun a ha ↦ ?_) Q (mul_comm P _ ▸ hQ.1))
  contrapose! ha
  exact h a ha

protected lemma mem_nonZeroDivisors_iff {P : R[X]} : P ∈ R[X]⁰ ↔ ∀ a : R, a • P = 0 → a = 0 := by
  simpa [not_imp_not] using (notMem_nonZeroDivisors_iff (P := P)).not

