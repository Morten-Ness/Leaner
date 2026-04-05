import Mathlib

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H] [Nontrivial H] (f : G →*₀ H)

theorem range_nontrivial :
    (Set.range f).Nontrivial := Set.nontrivial_coe_sort.mp MonoidWithZeroHom.mrange_nontrivial f

