# Logic utils

This repo contains a variety of small utility programs that help me test,
synthesize, or manipulate logical propositions.

I originally made the first util file (`test_logic.py`) to help me with
a specific homework assignment for a particular class, but found I kept
needing to resurrect it for random one-off stuff every few months or so.
I eventually gave up, promoted it to a full-fledged repo, and am now
slowing adding to it.

- `test_logic.py`: For testing/manipulating logical equivalences
- `synthesize.py`: For synthesizing logical propositions given a 
  user-specified set of opcodes.

Pending todos: 

- Refactor; rewrite the brute-force segments of the 
synthesizer to use a SAT/SMT solver.

