import Mathlib

variable {C D : Type*} [Category.{v} C] [Category.{v'} D] [Preadditive C] [Preadditive D]

variable {F G : CochainComplex C ℤ} (φ : F ⟶ G)

variable [HasHomotopyCofiber φ]

variable {K : CochainComplex C ℤ} (α : Cocycle K F 1) (β : Cochain K G 0)
    (eq : δ 0 1 β + α.1.comp (Cochain.ofHom φ) (add_zero 1) = 0)

theorem lift_f_snd_v (p q : ℤ) (hpq : p + 0 = q) :
    (CochainComplex.mappingCone.lift φ α β eq).f p ≫ (CochainComplex.mappingCone.snd φ).v p q hpq = β.v p q hpq := by
  obtain rfl : q = p := by lia
  simp [CochainComplex.mappingCone.lift]

