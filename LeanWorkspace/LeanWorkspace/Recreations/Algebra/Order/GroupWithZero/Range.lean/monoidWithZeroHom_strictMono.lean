import Mathlib

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

theorem monoidWithZeroHom_strictMono :
    StrictMono (MonoidWithZeroHom.ValueGroup₀.orderMonoidWithZeroHom f) := map'_strictMono (Subtype.strictMono_coe _)

