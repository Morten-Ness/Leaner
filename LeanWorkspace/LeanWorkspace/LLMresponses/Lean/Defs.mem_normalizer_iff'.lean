FAIL
import Mathlib

open scoped Int

variable {G : Type*} [Group G] {A : Type*} [AddGroup A]

variable (H : Subgroup G)

theorem mem_normalizer_iff' {g : G} : g ∈ Subgroup.normalizer H ↔ ∀ n, n * g ∈ H ↔ g * n ∈ H := by
  constructor
  · intro hg
    intro n
    constructor
    · intro hng
      have hconj : g⁻¹ * (n * g) ∈ H := by
        rw [← Subgroup.mem_carrier]
        exact hg (by
          change n * g * g⁻¹ ∈ H
          simpa [mul_assoc] using hng)
      simpa [mul_assoc] using hconj
    · intro hgn
      have hnorm : g⁻¹ ∈ Subgroup.normalizer H := by
        rw [Subgroup.mem_normalizer_iff] at hg ⊢
        intro x
        constructor
        · intro hx
          have hx' : g * x * g⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hg x).mp hx
          simpa [mul_assoc] using hx'
        · intro hx
          have hx' : g⁻¹ * (g * x * g⁻¹) * g ∈ H := (Subgroup.mem_normalizer_iff.mp hg (g * x * g⁻¹)).mpr hx
          simpa [mul_assoc] using hx'
      have hconj : g * (n * g⁻¹) ∈ H := by
        simpa [mul_assoc] using hgn
      have hmem : n * g⁻¹ ∈ H := by
        rw [Subgroup.mem_normalizer_iff] at hnorm
        exact (hnorm (n * g⁻¹)).mp hconj
      have hfinal : (n * g⁻¹) * g ∈ H := H.mul_mem hmem (by
        have : g ∈ H ↔ (g⁻¹ * g) * g ∈ H := by
          simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hnorm g)
        have hone : (1 : G) ∈ H := H.one_mem
        have hgmem : g ∈ H := by
          simpa using this.mp (by simpa using hone)
        exact hgmem)
      simpa [mul_assoc] using hfinal
  · intro h
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      have h1 : g * n ∈ H := (h n).mp (by simpa using H.mul_mem hn H.one_mem)
      have h2 : (g * n) * g⁻¹ ∈ H := H.mul_mem h1 (by
        have h3 : g * 1 ∈ H := (h 1).mp (by simpa using H.one_mem)
        simpa using H.inv_mem h3)
      simpa [mul_assoc] using h2
    · intro hgn
      have h1 : g * (g⁻¹ * n * g) ∈ H := by
        simpa [mul_assoc] using hgn
      have h2 : (g⁻¹ * n * g) * g ∈ H := (h (g⁻¹ * n * g)).mp h1
      simpa [mul_assoc] using h2
