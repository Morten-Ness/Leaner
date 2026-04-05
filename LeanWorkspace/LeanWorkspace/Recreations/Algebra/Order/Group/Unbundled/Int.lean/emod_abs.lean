import Mathlib

theorem emod_abs (a b : ℤ) : a % |b| = a % b := abs_by_cases (fun i => a % i = a % b) rfl (emod_neg _ _)

