# LeanAID review prompt

You are an independent reviewer. Another agent is building LeanAID: a Lean 4
transcription of the OpenAPS oref0 insulin dosing algorithm, with proofs of safety
properties. Its task is in `prompts/kickoff.md` and its rules are in `AGENTS.md`.
Your job is to check its work so far, critically, before anything is published.
**Do not fix anything. Report.**

## Setup: work on a separate copy

The other agent is still working in `~/Code/LeanAID`. Do not read from, write to, build
in, or run git commands in that folder. Instead:

```bash
git clone ~/Code/LeanAID ~/Code/LeanAID-review
cd ~/Code/LeanAID-review
git clone https://github.com/openaps/oref0.git vendor/oref0
git -C vendor/oref0 checkout 88cf032aa74ff25f69464a7d9cd601ee3940c0b3
```

Work only in `~/Code/LeanAID-review`. Do not commit, do not push, do not run `gh`.
Record the commit you reviewed (`git log -1 --oneline`).

## What to check

1. **Does it build, and honestly?**
   Run `lake build` and `lake test`. Record pass or fail and any warnings. Search the
   Lean sources for `sorry`, `admit`, `axiom`, `partial`, `unsafe`, `@[extern]`,
   `implemented_by` and `native_decide`; list every hit with file and line, and say
   whether `AGENTS.md` and `prompts/kickoff.md` allow it there. Run `#print axioms` on
   every theorem named in `docs/TRACEABILITY.md` and list any non-standard axiom.

2. **Do the theorems say what the requirements say?** This is the most important check.
   For every requirement in `docs/REQUIREMENTS.md` marked as proved, read the Lean
   statement (not the proof) and report whether it is:
   - **faithful**: it says what the requirement says;
   - **weaker**: extra hypotheses, narrower scope, or a different quantity;
   - **vacuous**: its hypotheses can never all hold (try to construct an input that
     satisfies them; if you cannot, say why);
   - **circular**: it restates the implementation instead of an independent property.

3. **Is "valid input" reasonable?**
   Find the definition of valid input used by the safety theorems. Check that oref0's
   own test inputs satisfy it (if most do not, the theorems may not apply to realistic
   cases). List any condition that would exclude inputs a real user could produce.

4. **Is the transcription faithful?**
   Pick at least five functions, including `determine_basal`, basal rounding and the
   insulin-on-board calculation. Compare each Lean function with the JavaScript at the
   cited file and lines in `vendor/oref0`. Report any missing branch, changed constant,
   changed comparison (`<` vs `<=`), or different rounding.

5. **Are the conformance claims true?**
   Check that the number of oref0 test cases claimed as reproduced matches the code,
   and that tests marked as excluded or disabled are justified.

6. **Do the documents match the code?**
   Compare `docs/LOG.md`, `docs/TESTS.md`, `docs/TRACEABILITY.md` and
   `site/index.html` with what you found. Flag any claim that overstates the evidence.

## Output

Write `~/Code/LeanAID-review/REVIEW.md` with:
- the commit reviewed and the build and test result;
- findings ranked by severity: **blocker** (must fix before publishing),
  **major**, **minor**, each with file and line and a concrete example where possible;
- a table: requirement → theorem → verdict (faithful, weaker, vacuous or circular);
- a one-paragraph verdict: is this safe to publish as it stands, and what must change first.

Be specific and sceptical. Praise is not needed. Then stop.
