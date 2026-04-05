import Mathlib

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]

variable (K L : CochainComplex C ℤ) (n m p : ℤ)

theorem mem_coboundaries_iff (α : Cocycle K L n) (m : ℤ) (hm : m + 1 = n) :
    α ∈ CochainComplex.HomComplex.coboundaries K L n ↔ ∃ (β : Cochain K L m), δ m n β = α := by
  simp only [CochainComplex.HomComplex.coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk]
  grind

