FAIL
import Mathlib

variable {M A B : Type*}

theorem mem_closure_pair {A : Type*} [CommMonoid A] (a b c : A) :
    c ∈ Submonoid.closure ({a, b} : Set A) ↔ ∃ m n : ℕ, a ^ m * b ^ n = c := by
  constructor
  · intro hc
    let P : A → Prop := fun x => ∃ m n : ℕ, a ^ m * b ^ n = x
    have ha : P a := ⟨1, 0, by simp [P]⟩
    have hb : P b := ⟨0, 1, by simp [P]⟩
    have h1 : P 1 := ⟨0, 0, by simp [P]⟩
    have hmul : ∀ x y, P x → P y → P (x * y) := by
      intro x y hx hy
      rcases hx with ⟨m₁, n₁, rfl⟩
      rcases hy with ⟨m₂, n₂, rfl⟩
      refine ⟨m₁ + m₂, n₁ + n₂, ?_⟩
      simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
    have hP : P c := by
      refine Submonoid.closure_induction hc ?_ h1 hmul
      intro x hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    simpa [P] using hP
  · rintro ⟨m, n, rfl⟩
    exact Submonoid.mul_mem (Submonoid.closure ({a, b} : Set A))
      (Submonoid.pow_mem _ (Submonoid.subset_closure (by simp)) m)
      (Submonoid.pow_mem _ (Submonoid.subset_closure (by simp)) n)
