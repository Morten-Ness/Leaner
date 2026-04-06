FAIL
import Mathlib

variable {ι κ G M : Type*} {s s₁ s₂ : Finset ι} {a : ι}

variable [CommMonoid M] {f g : ι → M}

theorem prod_eq_mul_of_mem {s : Finset ι} {f : ι → M} (a b : ι) (ha : a ∈ s) (hb : b ∈ s)
    (hn : a ≠ b) (h₀ : ∀ c ∈ s, c ≠ a ∧ c ≠ b → f c = 1) : ∏ x ∈ s, f x = f a * f b := by
  classical
  rw [Finset.mul_prod_erase _ _ ha]
  rw [Finset.mul_assoc]
  congr 1
  rw [Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hn, hb⟩)]
  rw [Finset.prod_eq_one]
  · simp [mul_comm, mul_left_comm, mul_assoc]
  · intro c hc
    exact h₀ c (Finset.mem_of_mem_erase <| Finset.mem_of_mem_erase hc) ⟨by
      intro hca
      apply Finset.mem_erase.mp (Finset.mem_of_mem_erase hc) |>.1
      simpa [hca] using hn
    , by
      exact (Finset.mem_erase.mp hc).1
    ⟩
