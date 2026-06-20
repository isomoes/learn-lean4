/-
# Addition World 🚧 (in progress)

Part of Phase 1 — Natural Number Game (see `README.md`).

Unlike Tutorial World (which used a hand-rolled `MyNat` to mimic NNG's *locked*
environment), this file uses Lean's **real** natural numbers. The new tactic this
world teaches is **`induction`**.

Check it standalone with:  `lake env lean 01-nng/addition-world.lean`

Three honest notes about using the real naturals instead of a `MyNat` sandbox:
* Real `rfl` actually *computes*, so Tutorial World's lesson "rfl is syntactic,
  you must rewrite" does NOT apply here — e.g. `example : (2 : Nat) + 2 = 4 := rfl`
  just works. We still prove `zero_add` the NNG way (induction + `add_succ`) to
  mirror the game's moves, but nothing here is "locked": `simp`, `omega`, or
  `Nat.zero_add n` would each close it in one line.
* We write `Nat`, not the `ℕ` glyph: `ℕ` is notation from Mathlib/Batteries, and
  in plain core Lean an undefined `ℕ` silently becomes a stray type variable
  (you'd get a confusing `HAdd Nat ℕ ℕ` / "not an inductive type" error).
* The lemmas are `Nat.add_zero` / `Nat.add_succ`; the bare `add_zero` / `add_succ`
  names NNG shows you only exist once Mathlib is imported.

--------------------------------------------------------------------------------
## New tactic: `induction`

`induction n with ...` splits a goal about a natural number `n` into the two
shapes a `Nat` can take:

* `| zero =>`        — prove the goal for `n = 0` (the **base case**).
* `| succ d hd =>`   — prove it for `n = d + 1`, where you are *given* the
                       **induction hypothesis** `hd` : the statement already
                       holds for `d`. The job is to rewrite the `d + 1` goal
                       (with `Nat.add_succ`) until you can `rw [hd]`.

The NNG game writes this as the linear `induction n with d hd` followed by one
tactic per goal; the labelled `| zero => … | succ d hd => …` form used here is
plain-Lean 4 syntax and is sturdier — each tactic is welded to its own case, so a
step tactic can never spill onto the base goal.
-/

/-
## Level 1: `zero_add`  —  `0 + n = n`

Why this needs induction: `Nat.add` recurses on its **right** argument, so
`Nat.add_zero` (`a + 0 = a`) is the base equation. But `zero_add` has the `0` on
the **left**, where the definition can't take a step — so a single rewrite won't
do; you peel the right argument down with `Nat.add_succ`, one `succ` at a time,
which is exactly induction.

Goal-state trace (captured from the InfoView; note `Nat.succ d` prints as `d + 1`):

  case        command              goal
  zero        (start)              0 + 0 = 0
  zero        rw [Nat.add_zero]    0 = 0                  → closed (rw's trailing rfl)
  succ d hd   (start)              0 + (d + 1) = d + 1    (hd : 0 + d = d)
  succ d hd   rw [Nat.add_succ]    (0 + d).succ = d + 1
  succ d hd   rw [hd]              d.succ = d + 1         → closed (rw's trailing rfl)
-/
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero      => rw [Nat.add_zero]
  | succ d hd => rw [Nat.add_succ, hd]
