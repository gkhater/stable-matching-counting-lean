# Validation records

The original development passed normal Lean 4.35.0 Lake builds before publication:

| Check | Result | Native output |
| --- | --- | --- |
| Full matching library and pure marriage entry | Passed, 4,895 jobs | [Build log](original-matching-build.log) |
| Matching freshness and standalone public theorem | Passed, all 4,895 jobs current, both exit codes 0 | [Freshness log](original-matching-freshness.log) |
| Actual Anthropic `Solution` freshness and `MainResults.mainTheorem` | Passed, all 4,753 jobs current, both exit codes 0 | [Solution validation](original-solution-validation.log) |

The printed transitive axiom dependencies of the public counting theorem and actual Anthropic theorem are exactly `propext`, `Classical.choice`, and `Quot.sound`. These are records from the original checkout, not a claim that the public checkout has been independently rebuilt.

All 153 published Lean and Lake configuration/toolchain files were compared byte for byte with the exported source bundle used for the fresh reproduction. The complete MathEconLib patch also matches that bundle. Their SHA-256 values are in [source-sha256.json](source-sha256.json).

A separate clean source-bundle reproduction started on Windows on 4 November 2026. It clones both pinned vendors, applies the patch, obtains the official Mathlib dependency cache, and builds `Solution`, the extended marriage entry, and `StableMatching`. No matching or Anthropic proof build artifacts were supplied to that checkout. This reproduction is **still running**; no clean-reproduction success is claimed here.

Reusable pure mathematics is being contributed separately: [upstream MathEconLib PR #283](https://github.com/matheconlib/matheconlib/pull/283) and the three dependent fork-side draft PRs [#2](https://github.com/gkhater/matheconlib/pull/2), [#3](https://github.com/gkhater/matheconlib/pull/3), and [#4](https://github.com/gkhater/matheconlib/pull/4). All four branch heads passed the standard MathEconLib CI on the contributor fork. The latter three are staged on the fork pending parent merges; they are not upstream submissions. Upstream first-time-contributor CI for #283 awaits maintainer approval.
