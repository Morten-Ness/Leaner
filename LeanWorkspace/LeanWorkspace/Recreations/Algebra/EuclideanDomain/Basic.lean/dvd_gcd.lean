import Mathlib

variable {R : Type u}

variable [EuclideanDomain R]

variable [DecidableEq R]

theorem dvd_gcd {a b c : R} : c ∣ a → c ∣ b → c ∣ gcd a b := GCD.induction a b (fun _ _ H => by simpa only [gcd_zero_left] using H) fun a b _ IH ca cb => by
    rw [EuclideanDomain.gcd_val]
    exact IH ((EuclideanDomain.dvd_mod_iff ca).2 cb) ca

