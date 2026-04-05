import Mathlib

variable {G M R K : Type*}

theorem MulArchimedean.comap [CommMonoid G] [LinearOrder G] [CommMonoid M] [PartialOrder M]
    [MulArchimedean M] (f : G →* M) (hf : StrictMono f) :
    MulArchimedean G where
  arch x _ h := by
    refine (MulArchimedean.arch (f x) (by simpa using hf h)).imp ?_
    simp [← map_pow, hf.le_iff_le]

