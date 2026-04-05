import Mathlib

variable {α : Type*}

variable [CommMonoidWithZero α]

theorem pow_dvd_of_mul_eq_pow [GCDMonoid α] {a b c d₁ d₂ : α} (ha : a ≠ 0) (hab : IsUnit (gcd a b))
    {k : ℕ} (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a := by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply isUnit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply isUnit_of_dvd_one
      grw [hd₁, hab.dvd]
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h, hc]
    exact mul_pow d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [h1.mul_left_dvd]
  have h4 : d₁ ^ k ≠ 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

