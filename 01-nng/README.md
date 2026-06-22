# Phase 1 — Natural Number Game (NNG4)

> Game: <https://adam.math.hhu.de/> · browser-based, no install.
> Source: <https://github.com/leanprover-community/NNG4> · upstream Lean levels (`Game/Levels/`).
> NNG runs in the browser, so notes live here (per the repo plan). **One `.lean` file per world** — prose in comments, the world's key proof reproduced so it type-checks.

## Progress

| World | Status | Notes |
| --- | --- | --- |
| Tutorial | ✅ done | [tutorial-world.lean](tutorial-world.lean) |
| Addition | 🚧 wip | [addition-world.lean](addition-world.lean) — `zero_add` ✅ |
| Multiplication | ✅ done | [multiplication-world.lean](multiplication-world.lean) — `mul_comm`, `mul_assoc`, distributivity ✅ |
| Implication (`intro`/`exact`/`apply`/`symm`) | ✅ done | [implication-world.lean](implication-world.lean) — `succ_inj`, `zero_ne_succ`, `2+2≠5` ✅ |
| Power | ✅ done | [power-world.lean](power-world.lean) — `pow_add`, `mul_pow`, `pow_pow`, `add_sq` ✅ |
| Advanced Addition | ✅ done | [advanced-addition-world.lean](advanced-addition-world.lean) — `add_right_cancel`, `add_left_cancel`, `add_*_eq_zero` ✅ |
| Less-Or-Equal | ✅ done | [le-world.lean](le-world.lean) — `le_refl`, `le_trans`, `le_antisymm`, `le_total`, `add_le_add_right` ✅ |
| Advanced Multiplication | ⬜ optional | — |
| Algorithm | ✅ done | [algorithm-world.lean](algorithm-world.lean) — `add_left_comm`, `simp_add` tactic, `pred`→`succ_inj`, `is_zero`→`succ_ne_zero`, `succ_ne_succ`, `decide` (`20+20=40`, `2+2≠5`) ✅ |

**Phase 1 milestone:** prove `add_comm`, `add_assoc`, `mul_comm`, and basic inequalities by induction, on my own.

