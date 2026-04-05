import Mathlib

variable (C : Type u) [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

theorem isIso_Qh_map_iff {X Y : HomotopyCategory C (ComplexShape.up ℤ)} (f : X ⟶ Y) :
    IsIso (Qh.map f) ↔ HomotopyCategory.quasiIso C _ f := by
  constructor
  · intro hf
    rw [HomotopyCategory.mem_quasiIso_iff]
    intro n
    rw [← NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactorsh C n) f]
    dsimp
    infer_instance
  · exact Localization.inverts Qh (HomotopyCategory.quasiIso _ _) _

