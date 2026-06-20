import Mathlib.Data.Nat.Notation

-- Multiplication is defined by recursion on the right argument:
--   `Nat.mul_zero : n * 0 = 0`   and   `Nat.mul_succ : n * succ m = n * m + n`.
-- Addition lemmas (`Nat.add_*`) are the results carried over from Addition World.

theorem mul_one (m : ℕ) : m * 1 = m := by
  rw [Nat.mul_succ, Nat.mul_zero, Nat.zero_add]

theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero      => rw [Nat.mul_zero]
  | succ d hd => rw [Nat.mul_succ, hd, Nat.add_zero]

theorem succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero      => rw [Nat.mul_zero, Nat.mul_zero, Nat.add_zero]
  | succ d hd => rw [Nat.mul_succ, Nat.mul_succ, hd, Nat.add_succ, Nat.add_succ,
                     Nat.add_right_comm]

theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with
  | zero      => rw [Nat.mul_zero, zero_mul]
  | succ d hd => rw [Nat.mul_succ, succ_mul, hd]

theorem one_mul (m : ℕ) : 1 * m = m := by
  rw [succ_mul, zero_mul, Nat.zero_add]

theorem two_mul (m : ℕ) : 2 * m = m + m := by
  rw [succ_mul, one_mul]

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with
  | zero      => rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, Nat.mul_succ, hd, Nat.mul_succ, Nat.add_assoc]

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, mul_add, mul_comm c a, mul_comm c b]

theorem mul_assoc (a b c : ℕ) : a * b * c = a * (b * c) := by
  induction c with
  | zero      => rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | succ d hd => rw [Nat.mul_succ, hd, Nat.mul_succ, mul_add]
