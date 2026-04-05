import Mathlib

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [AddTorsor V P]

theorem direction_affineSpan_insert {s : AffineSubspace k P} {p₁ p₂ : P} (hp₁ : p₁ ∈ s) :
    (affineSpan k (insert p₂ (s : Set P))).direction =
    Submodule.span k {p₂ -ᵥ p₁} ⊔ s.direction := by
  rw [sup_comm, ← Set.union_singleton, ← AffineSubspace.coe_affineSpan_singleton k V p₂]
  change (s ⊔ affineSpan k {p₂}).direction = _
  rw [AffineSubspace.direction_sup hp₁ (mem_affineSpan k (Set.mem_singleton _)), direction_affineSpan]
  simp

