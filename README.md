# LeanAID

A Lean 4 version of the OpenAPS **oref0** dosing algorithm (the algorithm behind
Trio and AndroidAPS), with machine-checked proofs of its safety properties.

Planned:

- A function-by-function transcription of oref0 into Lean, using exact arithmetic.
- oref0's unit tests lifted to theorems that hold for every input.
- Safety requirements traced to FDA hazard analyses and regulations.
- A native binary, `aid-lean`, that matches oref0's command-line interface.
- Evaluation against virtual patients (simglucose).

**Research artifact. Not for dosing insulin.**

Work in progress by the Beneficial AI Foundation.
