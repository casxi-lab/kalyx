# Porting record

kalyx is built from its foundations. Some of its foundation code is to be
taken over from an earlier implementation of the casξ computer algebra system,
which is not public. This record lists every module taken over, one row per
module, added in the same change as the code. No module has been taken over
yet.

- **Module**: the module in this repository.
- **Source**: the files it came from, written as
  `cas-project@<full commit SHA>:<path>`, where `cas-project` names the
  earlier implementation.
- **Change**: one of *ported* (taken over with only the changes that the
  rules of this repository require), *adapted* (interfaces or structure
  changed) or *fixed deviation* (a known deviation of the source from its
  contract was corrected, with a test that rejects it); a short note follows
  and names any known deviation that is kept as a limitation.
- **Tests not carried over**: tests of the source that were not taken over,
  one per line, each with the reason.

Ported code is tested again in this repository. Tests, proofs and results of
the earlier implementation are not evidence for kalyx.

| Module | Source | Change | Tests not carried over |
| --- | --- | --- | --- |
