import Mathlib

section

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp_apply
    {φ : M →* N} {ψ : N →* P} {χ : M →* P} (h : MonoidHom.CompTriple φ ψ χ) (x : M) :
    ψ (φ x) = χ x := by
  rw [← h.comp_eq, MonoidHom.comp_apply]

end

section

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M →* N} {φ₂ : N →* P} {φ₁₂ : M →* P}
    (κ : MonoidHom.CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P →* Q} {φ₂₃ : N →* Q} (κ' : MonoidHom.CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M →* Q} :
    MonoidHom.CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ MonoidHom.CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  constructor <;>
  · rintro ⟨h⟩
    exact ⟨by simp only [← κ.comp_eq, ← h, ← κ'.comp_eq, MonoidHom.comp_assoc]⟩

end
