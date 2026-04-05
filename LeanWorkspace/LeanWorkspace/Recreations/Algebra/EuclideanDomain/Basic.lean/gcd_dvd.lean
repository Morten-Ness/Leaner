import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem gcd_dvd (a b : R) : gcd a b ∣ a ∧ gcd a b ∣ b := GCD.induction a b
    (fun b => by
      rw [gcd_zero_left]
      exact ⟨dvd_zero _, dvd_rfl⟩)
    fun a b _ ⟨IH₁, IH₂⟩ => by
    rw [EuclideanDomain.gcd_val]
    exact ⟨IH₂, (EuclideanDomain.dvd_mod_iff IH₂).1 IH₁⟩

