# Phase 1 — Natural Number Game (NNG4)

> Game: <https://adam.math.hhu.de/> · browser-based, no install.
> NNG runs in the browser, so notes live here (per the repo plan). **One `.lean` file per world** — prose in comments, the world's key proof reproduced so it type-checks.

## Progress

| World | Status | Notes |
| --- | --- | --- |
| Tutorial | ✅ done | [tutorial-world.lean](tutorial-world.lean) |
| Addition | ⬜ todo | — |
| Multiplication | ⬜ todo | — |
| Power | ⬜ todo | — |
| Implication (`intro`/`exact`/`apply`) | ⬜ todo | — |
| Advanced Addition | ⬜ optional | — |
| Less-Or-Equal | ⬜ optional | — |
| Advanced Multiplication | ⬜ optional | — |
| Algorithm | ⬜ optional | — |

**Phase 1 milestone:** prove `add_comm`, `add_assoc`, `mul_comm`, and basic inequalities by induction, on my own.

## How I take notes here

One `.lean` file per world, created when I finish (or while working through) it. Prose goes in `/- ... -/` comments; the world's key proof is reproduced over a minimal NNG environment so the file actually type-checks (`lake env lean 01-nng/<world>.lean`). Each file records: status, tactics/lemmas the world introduced, and any proof that taught me something — with the goal-state trace, not just the final answer.
