import Mathlib

open scoped Pointwise

variable {R : Type*} [CommRing R]

variable (A : Type*) [CommRing A] [Algebra R A]

variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]

variable (M : Submodule R V)

theorem of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M ≤ N) [Submodule.IsLattice A M]
    (hfg : N.FG) : Submodule.IsLattice A N := ⟨hfg, eq_top_iff.mpr <|
    le_trans (by rw [Submodule.IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

