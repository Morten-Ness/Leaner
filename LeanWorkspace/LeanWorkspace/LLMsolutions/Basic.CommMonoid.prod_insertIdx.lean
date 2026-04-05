FAIL
import Mathlib

variable {ι α β M N P G : Type*}

variable [CommMonoid M] {a : M} {l l₁ l₂ : List M}

theorem CommMonoid.prod_insertIdx {i} (h : i ≤ l.length) : (l.insertIdx i a).prod = a * l.prod := by
  induction l generalizing i with
  | nil =>
      simp at h
      subst i
      simp
  | cons b l ih =>
      cases i with
      | zero =>
          simp [List.insertIdx, mul_left_comm, mul_assoc]
      | succ i =>
          simp at h
          simp only [List.insertIdx, List.prod_cons]
          rw [ih h]
          ac_rfl
