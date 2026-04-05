import Mathlib

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiring R] {p q r : R[X]}

theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g := by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C' : g = g'.comp (toFinsuppIso R) := by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B, C', A]

