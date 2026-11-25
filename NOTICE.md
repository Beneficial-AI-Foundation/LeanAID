# Notices

LeanAID is Copyright (c) 2026 Beneficial AI Foundation, under the MIT licence in `LICENSE`.

**Research artifact. Not a medical device. Nothing here may be used to dose insulin.**

## oref0

`LeanAID/Core/` translates parts of oref0 0.7.1 (commit `88cf032`) function by function,
and `LeanAID/Conformance/Data/` and `scripts/capture/out/` hold the inputs and outputs of
oref0's own tests, captured by running them. These parts are derived from oref0, which is
under the following licence:

```
The MIT License (MIT)

Copyright (c) 2015-2019 OpenAPS Contributors

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
```

oref0 itself is not included: the scripts that compare with it expect a checkout in
`vendor/oref0` (see `README.md`).

## Other sources

- `refs/21CFR-862.1356.txt` and `refs/21CFR-880.5730.txt` are texts of the US Code of
  Federal Regulations, a work of the US government.
- The papers cited in `refs/README.md` are not included.
- The virtual patients come from simglucose (`sim/requirements.txt`), installed from PyPI,
  not included.
