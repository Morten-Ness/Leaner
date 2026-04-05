import Mathlib

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem commute_inl_inr (m : G₀) (n : H₀) : Commute (MonoidWithZeroHom.inl G₀ H₀ m) (MonoidWithZeroHom.inr G₀ H₀ n) := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit m <;>
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit n <;>
  simp [MonoidWithZeroHom.inl, MonoidWithZeroHom.inr, WithZero.withZeroUnitsEquiv, commute_iff_eq, ← WithZero.coe_mul]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inl G₀ H₀) = .id _ := MonoidWithZeroHom.ext fun _ ↦ MonoidWithZeroHom.fst_inl _

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (MonoidWithZeroHom.fst ..).comp (MonoidWithZeroHom.inr G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.fst, MonoidWithZeroHom.inr]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_inl [DecidablePred fun x : G₀ ↦ x = 0] (x : G₀) :
    MonoidWithZeroHom.fst _ H₀ (MonoidWithZeroHom.inl _ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.fst, MonoidWithZeroHom.inl]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem fst_surjective : Function.Surjective (MonoidWithZeroHom.fst G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨MonoidWithZeroHom.inl .., fun _ ↦ by simp⟩

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inl_injective [DecidablePred fun x : G₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inl G₀ H₀) := Function.HasLeftInverse.injective ⟨MonoidWithZeroHom.fst .., fun _ ↦ by simp⟩

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

variable [DecidablePred fun x : G₀ ↦ x = 0] [DecidablePred fun x : H₀ ↦ x = 0]

theorem inl_mul_inr_eq_mk_of_unit (m : G₀ˣ) (n : H₀ˣ) :
    (MonoidWithZeroHom.inl G₀ H₀ m * MonoidWithZeroHom.inr G₀ H₀ n) = (m, n) := by
  simp [MonoidWithZeroHom.inl, WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.inr, ← WithZero.coe_mul]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem inr_injective [DecidablePred fun x : H₀ ↦ x = 0] :
    Function.Injective (MonoidWithZeroHom.inr G₀ H₀) := Function.HasLeftInverse.injective ⟨MonoidWithZeroHom.snd .., fun _ ↦ by simp⟩

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_comp_inl [DecidablePred fun x : G₀ ↦ x = 0] :
    (MonoidWithZeroHom.snd ..).comp (MonoidWithZeroHom.inl G₀ H₀) = 1 := by
  ext x
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp_all [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.snd, MonoidWithZeroHom.inl]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_comp_inr [DecidablePred fun x : H₀ ↦ x = 0] :
    (MonoidWithZeroHom.snd ..).comp (MonoidWithZeroHom.inr G₀ H₀) = .id _ := MonoidWithZeroHom.ext fun _ ↦ MonoidWithZeroHom.snd_inr _

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_inr [DecidablePred fun x : H₀ ↦ x = 0] (x : H₀) :
    MonoidWithZeroHom.snd _ _ (MonoidWithZeroHom.inr G₀ _ x) = x := by
  obtain rfl | ⟨_, rfl⟩ := GroupWithZero.eq_zero_or_unit x <;>
  simp [WithZero.withZeroUnitsEquiv, MonoidWithZeroHom.snd, MonoidWithZeroHom.inr]

end

section

variable (G₀ H₀ : Type*) [GroupWithZero G₀] [GroupWithZero H₀]

theorem snd_surjective : Function.Surjective (MonoidWithZeroHom.snd G₀ H₀) := by
  classical
  exact Function.HasRightInverse.surjective ⟨MonoidWithZeroHom.inr .., fun _ ↦ by simp⟩

end
