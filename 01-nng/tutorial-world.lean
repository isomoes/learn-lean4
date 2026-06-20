/-
# Tutorial World ✅

Status: **completed** — through the final level `2 + 2 = 4`.
Part of Phase 1 — Natural Number Game (see `README.md`).

This world is where NNG teaches `rfl` and `rw`. Big caveat now that this note uses
Lean's **real** `Nat` (not a `MyNat` sandbox): in real Lean, `rfl` actually
*computes*, so the entire final level is honestly just one line —

    example : (2 : Nat) + 2 = 4 := rfl

Everything below the lemmas reconstructs what the **game** makes you do, because
NNG deliberately cripples `rfl` to be purely *syntactic*: there you can't compute,
so you must drive the proof with `rw`. Keeping that record is the point of the
note — just remember the busywork is the game's, not Lean's.

We write `Nat`, not the `ℕ` glyph (`ℕ` is Mathlib/Batteries notation; a bare `ℕ`
in core Lean silently becomes a stray type variable).

Check it standalone with:  `lake env lean 01-nng/tutorial-world.lean`

--------------------------------------------------------------------------------
## Tactics introduced

* `rfl` — in **NNG**, closes only a goal that is *syntactically* equal on both
  sides (you must first `rw` with `add_succ`/`add_zero` to compute the sums). In
  **real Lean**, `rfl` is the full definitional check and will reduce `2 + 2` to
  `4` all by itself — which is why this world collapses to a one-liner here.
* `rw [h]` — rewrites left→right with equation `h`; `rw [← h]` reverses. Rewrites
  **all** matching occurrences, then auto-tries `rfl`.
* `nth_rewrite n [h]` / `nth_rw n [h]` — rewrites only the **n-th** occurrence
  (1-indexed). `nth_rw` also auto-`rfl`s. These are Mathlib tactics and may be
  **locked** at this level — useful to know for later. (Shown as a comment below;
  using them for real would need `import Mathlib.Tactic`.)

## Key lemmas

Real core lemmas (already in Lean — `Nat.add` recurses on its right argument):
* `Nat.add_zero a : a + 0 = a`
* `Nat.add_succ a b : a + succ b = succ (a + b)`   ← the engine that *computes* a sum
* `Nat.succ_eq_add_one n : succ n = n + 1`          ← turns a successor into `+ 1`
                                                      (rarely what you want)

Numeral expansions NNG hands you — not in core, but each is true by `rfl` on `Nat`,
so we just declare them:
-/

theorem one_eq_succ_zero   : (1 : Nat) = Nat.succ 0 := rfl
theorem two_eq_succ_one    : (2 : Nat) = Nat.succ 1 := rfl
theorem three_eq_succ_two  : (3 : Nat) = Nat.succ 2 := rfl
theorem four_eq_succ_three : (4 : Nat) = Nat.succ 3 := rfl

/-
## The real-Lean proof: just compute
-/
example : (2 : Nat) + 2 = 4 := rfl

/-
## The NNG way: drive it with `rw` (what the game forces)

**The trap (in the game):** expanding `4` into `1 + 1 + 1 + 1` (via
`succ_eq_add_one`) leaves `1 + 1 + (1 + 1) = 1 + 1 + 1 + 1`, which differs only by
**associativity**. NNG's `rfl` is syntactic and `Nat.add_assoc` isn't unlocked yet
→ dead end.

**The fix:** compute the left side down to `succ` form with `add_succ`/`add_zero`,
and expand `4` into `succ` form too — never use `succ_eq_add_one` to evaluate a sum.

Goal-state trace *as the game shows it* (its `rfl` is syntactic, so the steps are
visible one at a time):

  #  command                        resulting goal
  0  (start)                        2 + 2 = 4
  1  rw [two_eq_succ_one]           succ 1 + succ 1 = 4
  2  rw [one_eq_succ_zero]          succ (succ 0) + succ (succ 0) = 4
  3  rw [add_succ]                  succ (succ (succ 0) + succ 0) = 4
  4  rw [add_succ]                  succ (succ (succ (succ 0) + 0)) = 4
  5  rw [add_zero]                  succ (succ (succ (succ 0))) = 4
  6  rw [four_eq_succ_three]        … = succ 3
  7  rw [three_eq_succ_two]         … = succ (succ 2)
  8  rw [two_eq_succ_one]           … = succ (succ (succ 1))
  9  rw [one_eq_succ_zero]          both sides succ⁴ 0 → closed

Heads-up on **real Nat**: this chain type-checks only as a *single* `rw [...]`
list, because `rw`'s closing `rfl` fires once at the very end. Split it into
separate `rw` lines and real `Nat`'s `rfl` pounces right after step 1 with
"no goals to be solved" — a vivid reminder that none of this is needed off-game.
-/
example : (2 : Nat) + 2 = 4 := by
  rw [two_eq_succ_one, one_eq_succ_zero, Nat.add_succ, Nat.add_succ, Nat.add_zero,
      four_eq_succ_three, three_eq_succ_two, two_eq_succ_one, one_eq_succ_zero]

/-
**Alternative with `nth_rewrite`** (if unlocked — it's a Mathlib tactic, needs
`import Mathlib.Tactic`). Expand only the *right* summand:

    example : (2 : Nat) + 2 = 4 := by
      nth_rewrite 2 [two_eq_succ_one]   -- 2 + succ 1 = 4
      rw [Nat.add_succ, one_eq_succ_zero, Nat.add_succ, Nat.add_zero,
          four_eq_succ_three, three_eq_succ_two]

## Takeaways

* In the **NNG game**, `rfl` only closes syntactically-equal goals — *compute*
  with `add_succ`/`add_zero`. In **real Lean**, `rfl` computes, so this whole
  world is one `rfl`.
* `rw` hits **all** occurrences; use `nth_rewrite n` to target one (once unlocked).
* The associativity "trap" is a property of the game's *locked* lemma set, not of
  `Nat` — `Nat.add_assoc` is right there in core.
-/
