import Mathlib

variable {M : Type*}

variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M] {a b : M}

variable {N : Type*} [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

variable {s : UpperSet (FiniteMulArchimedeanClass M)}

theorem ballSubgroup_strictAnti : StrictAnti (ballSubgroup (M := M)) :=
  fun _ _ h ↦ subgroup_strictAnti <| UpperSet.Ioi_strictMono _ h

attribute [deprecated FiniteMulArchimedeanClass.subgroup (since := "2025-12-14")] MulArchimedeanClass.subgroup
attribute [deprecated FiniteMulArchimedeanClass.subsemigroup_eq_subgroup (since := "2025-12-14")]
  MulArchimedeanClass.subsemigroup_eq_subgroup_of_ne_top
attribute [deprecated FiniteMulArchimedeanClass.subgroup_eq_bot (since := "2025-12-14")] MulArchimedeanClass.subgroup_eq_bot
attribute [deprecated FiniteMulArchimedeanClass.mem_subgroup_iff (since := "2025-12-14")] MulArchimedeanClass.mem_subgroup_iff
attribute [deprecated subgroup_strictAnti (since := "2025-12-14")]
  MulArchimedeanClass.subgroup_strictAntiOn
attribute [deprecated subgroup_strictAnti (since := "2025-12-14")]
  MulArchimedeanClass.subgroup_antitone
attribute [deprecated ballSubgroup (since := "2025-12-14")] MulArchimedeanClass.ballSubgroup
attribute [deprecated closedBallSubgroup (since := "2025-12-14")]
  MulArchimedeanClass.closedBallSubgroup
attribute [deprecated FiniteMulArchimedeanClass.mem_ballSubgroup_iff (since := "2025-12-14")]
  MulArchimedeanClass.mem_ballSubgroup_iff
attribute [deprecated FiniteMulArchimedeanClass.mem_closedBallSubgroup_iff (since := "2025-12-14")]
  MulArchimedeanClass.mem_closedBallSubgroup_iff
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")]
  MulArchimedeanClass.ballSubgroup_top
attribute [deprecated "Lemma for junk value." (since := "2025-12-14")]
  MulArchimedeanClass.closedBallSubgroup_top
attribute [deprecated ballSubgroup_strictAnti (since := "2025-12-14")]
  MulArchimedeanClass.ballSubgroup_antitone

