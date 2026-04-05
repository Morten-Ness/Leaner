import Mathlib

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [MulOneClass P] (S : Submonoid M)

variable {A : Type*} [AddZeroClass A]

theorem Submonoid.toAddSubmonoid'_closure (S : Set (Multiplicative A)) :
    Submonoid.toAddSubmonoid' (Submonoid.closure S)
      = AddSubmonoid.closure (Multiplicative.ofAdd ⁻¹' S) := le_antisymm
    (Submonoid.toAddSubmonoid'.to_galoisConnection.l_le <|
      Submonoid.closure_le.2 <| AddSubmonoid.subset_closure (M := A))
    (AddSubmonoid.closure_le.2 <| Submonoid.subset_closure (M := Multiplicative A))

