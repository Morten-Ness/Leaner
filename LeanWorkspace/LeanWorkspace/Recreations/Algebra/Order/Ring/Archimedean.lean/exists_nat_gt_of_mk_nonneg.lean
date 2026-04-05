import Mathlib

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

variable [CommRing R]

variable [IsStrictOrderedRing R]

variable {S : Type*} [LinearOrder S] [CommRing S] [IsStrictOrderedRing S]

private theorem mk_mul_le_of_le {x₁ y₁ x₂ y₂ : R} (hx : ArchimedeanClass.mk x₁ ≤ ArchimedeanClass.mk x₂) (hy : ArchimedeanClass.mk y₁ ≤ ArchimedeanClass.mk y₂) :
    ArchimedeanClass.mk (x₁ * y₁) ≤ ArchimedeanClass.mk (x₂ * y₂) := by
  obtain ⟨m, hm⟩ := hx
  obtain ⟨n, hn⟩ := hy
  use m * n
  convert mul_le_mul hm hn (abs_nonneg _) (nsmul_nonneg (abs_nonneg _) _) using 1 <;>
    simp_rw [ArchimedeanOrder.val_of, abs_mul]
  ring


private theorem zero_add' (x : ArchimedeanClass R) : 0 + x = x := by
  induction x with | ArchimedeanClass.mk x
  rw [← mk_one, ← mk_mul, one_mul]


private theorem add_assoc' (x y z : ArchimedeanClass R) : x + y + z = x + (y + z) := by
  induction x with | ArchimedeanClass.mk x
  induction y with | ArchimedeanClass.mk y
  induction z with | ArchimedeanClass.mk z
  simp_rw [← mk_mul, mul_assoc]


theorem exists_nat_gt_of_mk_nonneg {x : R} (hx : 0 ≤ ArchimedeanClass.mk x) : ∃ n : ℕ, x < n := by
  obtain ⟨n, hn⟩ := ArchimedeanClass.exists_nat_ge_of_mk_nonneg hx
  refine ⟨n + 1, hn.trans_lt ?_⟩
  simp

