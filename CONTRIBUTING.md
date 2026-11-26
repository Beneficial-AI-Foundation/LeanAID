# Contributing to LeanAID

Thanks for your interest in contributing. LeanAID is a function-by-function
translation of the oref0 insulin-dosing algorithm into Lean 4, with machine-checked
proofs and a native executable, `aid-lean`, that reproduces `oref0-determine-basal`.
This guide covers how to build it, the standards we hold code to, and how to send a
change. It follows the shared contribution standard used across the
[Beneficial AI Foundation](https://github.com/Beneficial-AI-Foundation) Lean projects.

> **Research artifact. Not a medical device. Nothing here may be used to dose insulin.**

## Prerequisites

Install [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager.
It reads `lean-toolchain` and fetches the exact Lean/Lake version this project uses,
so you don't install Lean by hand:

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

No other dependencies are required to build the library, the proofs or the binary.
The optional differential comparison against oref0 additionally needs Node.js and an
oref0 checkout (see below); it is not part of the build.

## Building

```sh
lake build                         # the translation, all proofs, the conformance checks
lake build aid-lean                # the aid-lean binary at .lake/build/bin/aid-lean
```

LeanAID builds on Linux and macOS.

## Testing

```sh
lake test                          # build + `aid-lean selftest` + scripts/check.sh
.lake/build/bin/aid-lean selftest  # replays oref0's own test cases (cheap)
```

Continuous integration (`.github/workflows/ci.yml`) builds the project and runs the
sorry audit on every push and pull request; please make sure `lake build` and
`lake test` pass locally before opening a PR.

The full differential suite — 100,000s of random dose decisions and pump histories
run through both `aid-lean` and the original oref0 — needs Node.js and oref0 at the
pinned commit, and takes **hours** of CPU time, so it is run deliberately rather than
on every change (see the README, "Compare with oref0"):

```sh
git clone https://github.com/openaps/oref0 vendor/oref0
git -C vendor/oref0 checkout 88cf032aa74ff25f69464a7d9cd601ee3940c0b3
(cd vendor/oref0 && npm install --no-save)
bash scripts/check.sh                          # forbidden constructs, axioms, findings
TZ=UTC node scripts/difftest/run.js 100000 7   # random dose decisions
```

## Proof discipline

Correctness here comes from machine-checked proofs, so the hand-written libraries
(`LeanAID`, `App`) must stay honest:

- **No `sorry`.** CI runs a sorry audit over `LeanAID` and `App`
  (`Beneficial-AI-Foundation/veritooling/actions/sorry-audit`) and flags any new
  `sorry` on a pull request. The 314 theorems are proved without it.
- The safety theorems are checked by the **kernel** with standard axioms only
  (`propext`, `Classical.choice`, `Quot.sound`).
- The **conformance** checks (`LeanAID/Conformance/`) use `native_decide` by design —
  replaying oref0's recorded cases trusts Lean's compiler, which is called out in the
  README's "Limits". Keep `native_decide` to those replay checks; do not introduce it
  into the safety proofs.

## Submitting a change

1. **Branch** off `main` (or fork the repository).
2. Keep each pull request focused, and add or update a spec/test for behaviour you
   change — tests are theorems here.
3. Make sure `lake build` and `lake test` pass, and that CI is green.
4. Write a clear PR description: what changed, why, and how you verified it.
5. By contributing, you agree your contribution is licensed under this repository's
   license (MIT, see `LICENSE`), and you certify the
   [Developer Certificate of Origin](https://developercertificate.org/) — add a
   `Signed-off-by: Your Name <you@example.com>` line to your commits (`git commit -s`).

## Reporting issues

Open a GitHub issue with a clear title, what you expected, what happened, and the
smallest inputs that reproduce it. Security-sensitive reports can be sent privately to
**support@beneficialaifoundation.org** instead of a public issue.

## Code of conduct

Be respectful and constructive. Harassment or abuse is not tolerated. Maintainers may
remove comments, commits or contributions that don't meet this standard.
