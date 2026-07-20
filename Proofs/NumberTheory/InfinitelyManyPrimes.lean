import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs

namespace LeanPractice.NumberTheory

/-- For every natural-number bound, there is a prime larger than it.

This is Euclid's factorial-plus-one proof. Given `n`, construct
`p = minFac ((n + 1)! + 1)`. If `p ≤ n`, then `p` divides both `(n + 1)!`
and `(n + 1)! + 1`, so it divides `1`, contradicting that `p` is prime.
-/
theorem infinitely_many_primes (n : ℕ) : ∃ p : ℕ, n < p ∧ Nat.Prime p := by
  -- Let `p` be the smallest prime factor of `(n + 1)! + 1`.
  let p := Nat.minFac ((n + 1).factorial + 1)

  -- A factorial is always positive, so `1 < (n + 1)! + 1`; in particular,
  -- `(n + 1)! + 1` is not `1`.
  have h_ne_one : (n + 1).factorial + 1 ≠ 1 :=
    Nat.ne_of_gt (Nat.succ_lt_succ (Nat.factorial_pos _))

  -- `Nat.minFac_prime` says that if `m ≠ 1`, then `Nat.minFac m` is prime.
  -- Supplying `h_ne_one` as its proof argument therefore proves that `p` is prime.
  have hp : Nat.Prime p := Nat.minFac_prime h_ne_one

  have hn_lt_p : n < p := by
    -- Argue by contradiction. `by_contra!` automatically simplifies
    -- `¬ n < p` to `p ≤ n`.
    by_contra! hp_le_n

    -- `Nat.dvd_factorial` needs two facts: `0 < p` and `p ≤ n + 1`.
    -- `Nat.minFac_pos _` gives the first. Transitivity applied to
    -- `p ≤ n ≤ n + 1` gives the second.
    have hp_dvd_factorial : p ∣ (n + 1).factorial :=
      Nat.dvd_factorial (Nat.minFac_pos _) (hp_le_n.trans (Nat.le_succ n))

    -- `Nat.minFac_dvd _` proves that `p ∣ (n + 1)! + 1`.
    -- Given `p ∣ (n + 1)!`, `Nat.dvd_add_iff_right` gives
    -- `p ∣ 1 ↔ p ∣ (n + 1)! + 1`; `.2` selects the right-to-left direction.
    have hp_dvd_one : p ∣ 1 :=
      (Nat.dvd_add_iff_right hp_dvd_factorial).2 (Nat.minFac_dvd _)

    -- A prime cannot divide `1`, contradicting `hp_dvd_one`.
    exact hp.not_dvd_one hp_dvd_one

  -- Use `p` as the witness and provide proofs of both required properties.
  exact ⟨p, hn_lt_p, hp⟩

end LeanPractice.NumberTheory
