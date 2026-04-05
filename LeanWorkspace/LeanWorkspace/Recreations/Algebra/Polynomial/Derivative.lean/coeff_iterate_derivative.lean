import Mathlib

open scoped Nat Polynomial

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {A : Type z} {a b : R} {n : ℕ}

variable [Semiring R]

theorem coeff_iterate_derivative {k} (p : R[X]) (m : ℕ) :
    (Polynomial.derivative^[k] p).coeff m = (m + k).descFactorial k • p.coeff (m + k) := by
  induction k generalizing m with
  | zero => simp
  | succ k ih =>
      calc
        (Polynomial.derivative^[k + 1] p).coeff m
        _ = Nat.descFactorial (Nat.succ (m + k)) k • p.coeff (m + k.succ) * (m + 1) := by
          rw [Function.iterate_succ_apply', Polynomial.coeff_derivative, ih m.succ, Nat.succ_add, Nat.add_succ]
        _ = ((m + 1) * Nat.descFactorial (Nat.succ (m + k)) k) • p.coeff (m + k.succ) := by
          rw [← Nat.cast_add_one, ← nsmul_eq_mul', smul_smul]
        _ = Nat.descFactorial (m.succ + k) k.succ • p.coeff (m + k.succ) := by
          rw [← Nat.succ_add, Nat.descFactorial_succ, add_tsub_cancel_right]
        _ = Nat.descFactorial (m + k.succ) k.succ • p.coeff (m + k.succ) := by
          rw [Nat.succ_add_eq_add_succ]

