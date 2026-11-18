// Loaded as an extra spec file before the oref0 test file: root-level hooks apply to every test.
beforeEach(function () { global.__capture.begin(this.currentTest); });
afterEach(function () { global.__capture.end(this.currentTest); });
