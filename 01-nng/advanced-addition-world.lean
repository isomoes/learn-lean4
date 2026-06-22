import Mathlib.Data.Nat.Notation
import Mathlib.Tactic.ApplyAt          -- `apply t at h` (forwards reasoning)

-- Advanced Addition World: the cancellation laws (`a + n = b + n → a = b`) and the
-- "a sum is zero" lemmas (`a + b = 0 → a = 0` and `→ b = 0`). These follow from the
-- Peano facts `succ_inj` / `zero_ne_succ` together with the addition lemmas carried
-- over from Addition World (`add_comm`, `zero_add`, and the core `Nat.add_*`).
--
-- We restate `succ_inj` and `zero_ne_succ` at the top exactly as Implication World
-- does, so the level proofs read like the game.

theorem succ_inj {a b : ℕ} (hab : Nat.succ a = Nat.succ b) : a = b := Nat.succ.inj hab

theorem zero_ne_succ (n : ℕ) : (0 : ℕ) ≠ Nat.succ n := (Nat.succ_ne_zero n).symm

-- Level 1 — succ_inj: `succ a = succ b → a = b`, the injectivity of `succ`.
-- (Restated above; here we record it as a level proof for completeness.)
theorem succ_inj' {a b : ℕ} (h : Nat.succ a = Nat.succ b) : a = b := by
  apply succ_inj at h
  exact h

-- Level 2 — add_right_cancel: cancel a common right summand, by induction on `n`.
-- Base case `n = 0` strips the `+ 0`; the step peels a `succ` off each side with
-- `add_succ` and then `succ_inj`, leaving the inductive hypothesis to finish.
theorem add_right_cancel (a b n : ℕ) (h : a + n = b + n) : a = b := by
  induction n with
  | zero      =>
    rw [Nat.add_zero, Nat.add_zero] at h   -- h : a = b
    exact h
  | succ d hd =>
    rw [Nat.add_succ, Nat.add_succ] at h   -- h : succ (a + d) = succ (b + d)
    apply succ_inj at h                    -- h : a + d = b + d
    apply hd at h                          -- h : a = b
    exact h

-- Level 3 — add_left_cancel: cancel a common *left* summand, via `add_comm` to put
-- the `n` on the right, then reuse `add_right_cancel`.
theorem add_left_cancel (a b n : ℕ) (h : n + a = n + b) : a = b := by
  rw [Nat.add_comm n a, Nat.add_comm n b] at h   -- h : a + n = b + n
  apply add_right_cancel a b n h

-- Level 4 — add_left_eq_self: `a + b = b → a = 0`. To cancel `b`, make the RHS look
-- like `0 + b` so both sides are `_ + b`, then apply `add_right_cancel`. We argue the
-- goal `a = 0` backwards into `a + b = 0 + b`.
theorem add_left_eq_self (a b : ℕ) (h : a + b = b) : a = 0 := by
  apply add_right_cancel a 0 b   -- goal : a + b = 0 + b
  rw [Nat.zero_add]              -- goal : a + b = b
  exact h

-- Level 5 — add_right_eq_self: `a + b = a → b = 0`, the mirror image. Cancel `a` on
-- the left with `add_left_cancel`, arguing the goal backwards into `a + b = a + 0`.
theorem add_right_eq_self (a b : ℕ) (h : a + b = a) : b = 0 := by
  apply add_left_cancel b 0 a    -- goal : a + b = a + 0
  rw [Nat.add_zero]             -- goal : a + b = a
  exact h

-- Level 6 — add_right_eq_zero: `a + b = 0 → b = 0`. Case-split on `b`: if `b` is a
-- successor, `a + succ d = succ (a + d)` is a successor, contradicting `... = 0` via
-- `zero_ne_succ`; the `b = 0` case is immediate.
theorem add_right_eq_zero (a b : ℕ) (h : a + b = 0) : b = 0 := by
  cases b with
  | zero   => rfl
  | succ d =>
    rw [Nat.add_succ] at h            -- h : succ (a + d) = 0
    -- `succ _ = 0` is impossible: feed it to `zero_ne_succ` (flipped) to get `False`.
    exact absurd h.symm (zero_ne_succ (a + d))

-- Level 7 — add_left_eq_zero: `a + b = 0 → a = 0`, via `add_comm` and Level 6.
theorem add_left_eq_zero (a b : ℕ) (h : a + b = 0) : a = 0 := by
  rw [Nat.add_comm] at h            -- h : b + a = 0
  apply add_right_eq_zero b a h
