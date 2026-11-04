# Stable matching counting in Lean

This repository contains a Lean 4.35.0 formalization of exact counting for finite stable marriage markets, together with the compatibility bridge to Anthropic's formal proof. The main library theorem is `MathEconLib.Matching.MarriageMarket.subexponential_exact_counting` in [`MathEconLibCounting.lean`](stable_matching/StableMatching/MathEconLibCounting.lean).

The result gives one fixed finite-alphabet multi-stack Turing machine that counts stable matchings. For every `epsilon > 0` there is a constant `c_epsilon` such that its running time is at most `c_epsilon * 2^(epsilon * n)` for `n >= 1`, where `n` is the size of each side. Balance refers to equal side sizes. The stronger proved bound has the form `poly(input size) * 2^(O(n / (log(n))^(1/4)))`. The machine includes input reading, market and reduction construction, SAT simulation, and accumulation of the count; all computation costs are charged. See [`UniformRuntime.lean`](stable_matching/StableMatching/UniformRuntime.lean) for the machine statements and explicit bound.

The input is the explicit normalized preference-rank bit string, and the output is exactly `Nat.bits (Nat.card mkt.StableMatching)`. Preferences are strict orders over partners and the outside option. Complete strict preference lists are included. This development does not claim the partner-constraint, rank-histogram, rank-balanced optimization, or sampling extensions.

The development imports the actual `MainResults.mainTheorem` through the `Solution` proof. The original full builds passed, and the final theorem's printed axiom dependencies are exactly Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`. Native logs and source hashes are in [`validation/`](validation/). The bridge check is [`axiom_audit.lean`](anthropic_bridge/axiom_audit.lean). A separate clean reproduction of the identical proof sources is **running**; no clean-reproduction success is claimed yet.

## Contents

- [`stable_matching/`](stable_matching/) contains the matching counting development and Lake project.
- [`anthropic_bridge/`](anthropic_bridge/) contains the bridge, compatibility overrides and its Lake project. Its original license is in that directory.
- [`patches/matheconlib.patch`](patches/matheconlib.patch) adds the pure matching extensions to the pinned MathEconLib checkout.
- `external/` holds ignored vendor checkouts created by setup. MathEconLib is pinned to `58f602847d7f131994d32ca7a8cc1af35b7e2dbe` and [Anthropic formal-math](https://github.com/anthropics/formal-math) to `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.

The Lean files and Lake configuration were copied byte for byte from the source bundle. Existing source attribution and headers are retained. The root [LICENSE](LICENSE) is from MathEconLib; the bridge has its own [LICENSE](anthropic_bridge/LICENSE), and the downloaded dependencies retain their respective licenses.

## Reproduction

Install Git, Python 3 and Lean 4.35.0 via Elan. Run from the repository root, using a shell in which `lake` is available:

```sh
python scripts/setup.py
cd stable_matching
lake exe cache get
cd ../anthropic_bridge
lake --fail-fast build +Solution:olean
cd ../stable_matching
lake --fail-fast build +StableMatching:olean
```

Set `LEAN_NUM_THREADS=1` in the environment for a serial build. The builds are substantial and need time and disk space. To build the extended pure marriage entry point as well, run `lake --fail-fast build +MathEconLib.Matching.Classical.Marriage:olean` from `stable_matching`.

[`ci/lean.yml`](ci/lean.yml) is an inactive GitHub Actions template for a clean Ubuntu build. Automatic CI is not configured: the publishing credential cannot create workflow files. The template can be installed as `.github/workflows/lean.yml` by an account with the required workflow permission.

Setup clones the two pinned vendors if absent, verifies their origins and exact HEADs, then checks and applies the patch. Rerunning setup recognizes the applied patch. It stops if a checkout or patch is incompatible; inspect any local changes before resolving the issue. Setup does not change global Git configuration.
