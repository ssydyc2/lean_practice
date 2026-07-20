import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace LeanPractice.NumberTheory

/-- For every natural-number bound, there is a prime larger than it.

This is Euclid's factorial-plus-one proof. Given `n`, construct
`p = minFac ((n + 1)! + 1)`. If `p ≤ n`, then `p` divides both `(n + 1)!`
and `(n + 1)! + 1`, so it divides `1`, contradicting that `p` is prime.
-/
theorem infinitely_many_primes (n : ℕ) : ∃ p : ℕ, n < p ∧ Nat.Prime p := by
  let p := Nat.minFac ((n + 1).factorial + 1)
  have h_ne_one : (n + 1).factorial + 1 ≠ 1 :=
    Nat.ne_of_gt (Nat.succ_lt_succ (Nat.factorial_pos _))
  have hp : Nat.Prime p := Nat.minFac_prime h_ne_one
  have hn_lt_p : n < p := by
    apply Nat.lt_of_not_ge
    intro hp_le_n
    have hp_dvd_factorial : p ∣ (n + 1).factorial :=
      Nat.dvd_factorial (Nat.minFac_pos _) (hp_le_n.trans (Nat.le_succ n))
    have hp_dvd_one : p ∣ 1 :=
      (Nat.dvd_add_iff_right hp_dvd_factorial).2 (Nat.minFac_dvd _)
    exact hp.not_dvd_one hp_dvd_one
  exact ⟨p, hn_lt_p, hp⟩

end LeanPractice.NumberTheory
