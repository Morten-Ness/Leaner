import Mathlib

variable {A B : Type*} [MonoidWithZero A] [LinearOrderedCommGroupWithZero B] {f : A →*₀ B}

theorem embedding_strictMono : StrictMono (embedding (f := f)) := by
  intro x y hxy
  rw [← MonoidWithZeroHom.ValueGroup₀.monoidWithZeroHom_strictMono.lt_iff_lt] at hxy
  simpa using (OrderEmbedding.lt_iff_lt (OrderIso.withZeroUnits.toOrderEmbedding)).mpr hxy

