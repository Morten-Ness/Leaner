FAIL
import Mathlib

variable {M N P : Type*} [Monoid M] [Monoid N] [Monoid P]

theorem comp_assoc {Q : Type*} [Monoid Q]
    {φ₁ : M →* N} {φ₂ : N →* P} {φ₁₂ : M →* P}
    (κ : MonoidHom.CompTriple φ₁ φ₂ φ₁₂)
    {φ₃ : P →* Q} {φ₂₃ : N →* Q} (κ' : MonoidHom.CompTriple φ₂ φ₃ φ₂₃)
    {φ₁₂₃ : M →* Q} :
    MonoidHom.CompTriple φ₁ φ₂₃ φ₁₂₃ ↔ MonoidHom.CompTriple φ₁₂ φ₃ φ₁₂₃ := by
  simpa [MonoidHom.CompTriple, κ, κ'] using
    (show φ₂₃.comp φ₁ = φ₁₂₃ ↔ φ₃.comp φ₁₂ = φ₁₂₃ from Iff.rfl)
