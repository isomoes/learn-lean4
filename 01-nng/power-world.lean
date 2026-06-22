import Mathlib.Data.Nat.Notation

-- Power World: exponentiation, defined by recursion on the exponent:
--   `pow_zero a : a ^ 0 = 1`   and   `pow_succ a b : a ^ succ b = a ^ b * a`.
-- Multiplication/addition lemmas (`Nat.mul_*`, `Nat.add_*`) are carried over from
-- the earlier worlds. `pow_zero`/`pow_succ` below name the two `Nat.pow` equations
-- in NNG's `succ` form so the level proofs read like the game.

theorem pow_zero (a : ℕ) : a ^ 0 = 1 := Nat.pow_zero a
theorem pow_succ (a b : ℕ) : a ^ Nat.succ b = a ^ b * a := Nat.pow_succ a b

theorem one_eq_succ_zero : (1 : ℕ) = Nat.succ 0 := rfl
theorem two_eq_succ_one : (2 : ℕ) = Nat.succ 1 := rfl

-- Level 1 — zero_pow_zero: in this game the convention is `0 ^ 0 = 1`.
theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  rw [pow_zero]

-- Level 2 — zero_pow_succ: a positive power of zero is zero.
theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ Nat.succ m = 0 := by
  rw [pow_succ, Nat.mul_zero]

-- Level 3 — pow_one: `a ^ 1 = a`; not quite definitional, since `a ^ 1 = 1 * a`.
theorem pow_one (a : ℕ) : a ^ 1 = a := by
  rw [one_eq_succ_zero, pow_succ, pow_zero, Nat.one_mul]

-- Level 4 — one_pow: `1 ^ m = 1`, by induction on `m`.
theorem one_pow (m : ℕ) : (1 : ℕ) ^ m = 1 := by
  induction m with
  | zero      => rw [pow_zero]
  | succ d hd => rw [pow_succ, hd, Nat.mul_one]

-- Level 5 — pow_two: `a ^ 2 = a * a` (this one is needed for the final boss).
theorem pow_two (a : ℕ) : a ^ 2 = a * a := by
  rw [two_eq_succ_one, pow_succ, pow_one]

-- Level 6 — pow_add: `a ^ (m + n) = a ^ m * a ^ n`, by induction on `n`.
theorem pow_add (a m n : ℕ) : a ^ (m + n) = a ^ m * a ^ n := by
  induction n with
  | zero      => rw [Nat.add_zero, pow_zero, Nat.mul_one]
  | succ d hd => rw [Nat.add_succ, pow_succ, pow_succ, hd, Nat.mul_assoc]

-- Level 7 — mul_pow: `(a * b) ^ n = a ^ n * b ^ n`, by induction on `n`.
-- The successor step reassociates the product and commutes the middle factors.
theorem mul_pow (a b n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero      => rw [pow_zero, pow_zero, pow_zero, Nat.mul_one]
  | succ d hd =>
    rw [pow_succ, pow_succ, pow_succ, hd]
    repeat rw [Nat.mul_assoc]
    rw [Nat.mul_comm a (_ * b), Nat.mul_assoc, Nat.mul_comm b a]

-- Level 8 — pow_pow: `(a ^ m) ^ n = a ^ (m * n)`, by induction on `n`.
theorem pow_pow (a m n : ℕ) : (a ^ m) ^ n = a ^ (m * n) := by
  induction n with
  | zero      => rw [Nat.mul_zero, pow_zero, pow_zero]
  | succ d hd => rw [pow_succ, hd, Nat.mul_succ, pow_add]

-- Level 9 — add_sq (the final boss): `(a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b`,
-- a.k.a. why the "freshman's dream" `(a + b) ^ 2 = a ^ 2 + b ^ 2` is wrong.
theorem add_sq (a b : ℕ) : (a + b) ^ 2 = a ^ 2 + b ^ 2 + 2 * a * b := by
  rw [pow_two, pow_two, pow_two]
  rw [Nat.add_right_comm]
  rw [Nat.mul_add, Nat.add_mul, Nat.add_mul]
  rw [Nat.two_mul, Nat.add_mul]
  rw [Nat.mul_comm b a]
  rw [← Nat.add_assoc, ← Nat.add_assoc]

-- Level 10 — Fermat's Last Theorem. NNG states it with `n + 3` standing in for an
-- exponent ≥ 3 and `a + 1` for "positive", then lets you cheat with `xyzzy`, a
-- `sorry` in disguise:
--   (a + 1) ^ (n + 3) + (b + 1) ^ (n + 3) ≠ (c + 1) ^ (n + 3)
-- A genuine proof is the Wiles–Taylor theorem (millions of lines of Lean), so we
-- stop at the honest boundary rather than write `sorry`.
