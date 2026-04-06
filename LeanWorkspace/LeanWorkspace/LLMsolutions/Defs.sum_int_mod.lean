import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem sum_int_mod (s : Finset ι) (n : ℤ) (f : ι → ℤ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, Int.add_emod, ih]
