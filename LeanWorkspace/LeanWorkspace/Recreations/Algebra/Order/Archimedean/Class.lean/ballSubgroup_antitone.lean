import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {s : UpperSet (MulArchimedeanClass M)}

theorem ballSubgroup_antitone : Antitone (ballSubgroup (M := M)) := by
  intro _ _ h
  exact MulArchimedeanClass.subgroup_antitone <| (UpperSet.Ioi_strictMono _).monotone h

