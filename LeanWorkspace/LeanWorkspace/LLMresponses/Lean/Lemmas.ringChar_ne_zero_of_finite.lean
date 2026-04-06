FAIL
import Mathlib

variable {R S : Type*}

variable (R) [NonAssocRing R]

theorem ringChar_ne_zero_of_finite [Finite R] : ringChar R ≠ 0 := by
  intro h
  have h' : (1 : R) = 0 := by
    rw [← Nat.cast_one, ← h]
    exact ringChar.cast_eq_zero R 1
  have hR : Subsingleton R := by
    refine ⟨?_⟩
    intro a b
    calc
      a = a + 0 := by rw [add_zero]
      _ = a + 1 := by rw [h']
      _ = b + 1 := by simp
      _ = b + 0 := by rw [h']
      _ = b := by rw [add_zero]
  haveI := hR
  have : ¬ Finite R := by
    intro _
    exact not_nonempty_empty (Finite.of_injective (fun x : R => (False.elim x)) (by intro a; cases a))
  exact this ‹Finite R›
