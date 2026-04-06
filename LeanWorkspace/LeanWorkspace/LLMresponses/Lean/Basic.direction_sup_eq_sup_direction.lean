FAIL
import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_sup_eq_sup_direction {s₁ s₂ : AffineSubspace k P} {p : P} (hp₁ : p ∈ s₁)
    (hp₂ : p ∈ s₂) : (s₁ ⊔ s₂).direction = s₁.direction ⊔ s₂.direction := by
  let e : AffineSubspace k P ≃o Submodule k V := AffineSubspace.comap p
  have hs1 : e s₁ = s₁.direction := by
    ext v
    simp [e, hp₁, AffineSubspace.mem_comap]
  have hs2 : e s₂ = s₂.direction := by
    ext v
    simp [e, hp₂, AffineSubspace.mem_comap]
  have hsup : e (s₁ ⊔ s₂) = s₁.direction ⊔ s₂.direction := by
    rw [OrderIso.map_sup, hs1, hs2]
  have hp : p ∈ s₁ ⊔ s₂ := by exact Or.inl hp₁
  have hsdir : e (s₁ ⊔ s₂) = (s₁ ⊔ s₂).direction := by
    ext v
    simp [e, hp, AffineSubspace.mem_comap]
  rw [← hsdir, hsup]
