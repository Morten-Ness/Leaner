import Mathlib

variable {k : Type*} {V1 : Type*} {P1 : Type*} {V2 : Type*} {P2 : Type*} {V3 : Type*}
  {P3 : Type*} {V4 : Type*} {P4 : Type*} [Ring k] [AddCommGroup V1] [Module k V1]
  [AddTorsor V1 P1] [AddCommGroup V2] [Module k V2] [AddTorsor V2 P2] [AddCommGroup V3]
  [Module k V3] [AddTorsor V3 P3] [AddCommGroup V4] [Module k V4] [AddTorsor V4 P4]

variable (k P1)

variable {k P1}

variable {P1}

variable {k}

theorem linear_injective_iff (f : P1 →ᵃ[k] P2) :
    Function.Injective f.linear ↔ Function.Injective f := by
  obtain ⟨p⟩ := (inferInstance : Nonempty P1)
  have h : ⇑f.linear = (Equiv.vaddConst (f p)).symm ∘ f ∘ Equiv.vaddConst p := by
    ext v
    simp [f.map_vadd]
  rw [h, Equiv.comp_injective, Equiv.injective_comp]

