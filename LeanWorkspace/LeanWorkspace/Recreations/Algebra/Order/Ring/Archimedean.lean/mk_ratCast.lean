import Mathlib

variable {R S : Type*} [LinearOrder R] [LinearOrder S]

variable [Field R] [IsOrderedRing R]

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


private theorem zsmul_succ' (n : ℕ) (x : ArchimedeanClass R) :
    (n.succ : ℤ) • x = (n : ℤ) • x + x := by
  induction x with | ArchimedeanClass.mk x
  rw [← mk_zpow, Nat.cast_succ]
  obtain rfl | hx := eq_or_ne x 0
  · simp [zero_zpow _ n.cast_add_one_ne_zero]
  · rw [zpow_add_one₀ hx, mk_mul, mk_zpow]

noncomputable instance : LinearOrderedAddCommGroupWithTop (ArchimedeanClass R) where
  neg_top := by simp [← mk_zero, ← mk_inv]
  top_add' := by simp
  add_neg_cancel_of_ne_top x h := by
    induction x with | ArchimedeanClass.mk x
    simp [← mk_inv, ← mk_mul, mul_inv_cancel₀ (mk_eq_top_iff.not.1 h)]
  zsmul n x := n • x
  zsmul_zero' x := by induction x with | ArchimedeanClass.mk x => rw [← mk_zpow, zpow_zero, mk_one]
  zsmul_succ' := by exact zsmul_succ'
  zsmul_neg' n x := by
    induction x with | ArchimedeanClass.mk x
    rw [← mk_zpow, zpow_negSucc, pow_succ, zsmul_succ', mk_inv, mk_mul, ← zpow_natCast, mk_zpow]


theorem mk_ratCast {q : ℚ} (h : q ≠ 0) : ArchimedeanClass.mk (q : R) = 0 := by
  simpa using ArchimedeanClass.mk_map_of_archimedean ⟨(Rat.castHom R).toAddMonoidHom, fun _ ↦ by simp⟩ h

