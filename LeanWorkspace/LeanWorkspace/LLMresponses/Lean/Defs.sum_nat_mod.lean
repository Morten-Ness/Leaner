import Mathlib

variable {ι κ M N G α : Type*}

variable {s s₁ s₂ : Finset ι} {a : ι} {f g : ι → M}

theorem sum_nat_mod [DecidableEq ι] (s : Finset ι) (n : ℕ) (f : ι → ℕ) :
    (∑ i ∈ s, f i) % n = (∑ i ∈ s, f i % n) % n := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      simp [ha, Nat.add_mod, ih]
