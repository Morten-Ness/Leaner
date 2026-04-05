import Mathlib

variable {R : Type*}

variable [AddCommGroupWithOne R] [PartialOrder R] [AddLeftMono R]

variable [ZeroLEOneClass R]

variable [NeZero (1 : R)] {m n : ℤ}

theorem cast_strictMono : StrictMono (fun x : ℤ => (x : R)) := strictMono_of_le_iff_le fun _ _ => cast_le.symm

