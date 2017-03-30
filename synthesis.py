#!/usr/bin/env python
'''
Synthesizes a logic proposition using a user-specified set of 
opcodes.

TODO: Integrate a SAT/SMT solver to perform synthesis, rather
then using brute-force. 
'''

from typing import List, Callable, Dict, Optional, Tuple
from itertools import product

class Opcode:
    def __init__(self, num_args):
        self.num_args = num_args

    def eval(self, args: List[bool]) -> bool:
        raise NotImplementedError()

class Nor(Opcode):
    def __init__(self):
        super().__init__(2)

    def eval(self, args: List[bool]) -> bool:
        assert len(args) == 2
        return not args[0] and not args[1]

    def __str__(self):
        return 'Nor'

class Or(Opcode):
    def __init__(self):
        super().__init__(2)

    def eval(self, args: List[bool]) -> bool:
        assert len(args) == 2
        return args[0] or args[1]

    def __str__(self):
        return 'Or'

class Not(Opcode):
    def __init__(self):
        super().__init__(1)

    def eval(self, args: List[bool]) -> bool:
        assert len(args) == 1
        return not args[0] 

    def __str__(self):
        return 'Not'

class And(Opcode):
    def __init__(self):
        super().__init__(2)

    def eval(self, args: List[bool]) -> bool:
        assert len(args) == 2
        return args[0] and args[1]

    def __str__(self):
        return 'And'

class Variable(Opcode):
    def __init__(self, name):
        super().__init__(0)
        self.name = name

    def __str__(self):
        return 'Var({})'.format(self.name)

class Command:
    def __init__(self, op: Opcode, args: List[int]) -> None:
        self.op = op
        self.args = args

    def __str__(self):
        return '{}: {}'.format(str(self.op), self.args)

def synthesize(evaluator: Callable[[List[Command]], bool], 
               initial: List[Command],
               opcodes: List[Opcode],
               size: int) -> Optional[List[Command]]:
    '''
    Synthesizes a series of commands of exactly the given size
    using the provided set of opcodes and the initial set of commands.

    Either returns a list of commands that passes the given evaluator,
    or returns None otherwise.
    '''

    def helper(current: List[Command]) -> Tuple[bool, Optional[List[Command]]]:
        if len(current) == size:
            return evaluator(current), current
        else:
            prev_args = list(range(len(current)))
            for op in opcodes:
                for args in product(prev_args, repeat=op.num_args):
                    current.append(Command(op, list(args)))
                    res, possible = helper(current)
                    if res:
                        return res, possible
                    current.pop()
            return False, None

    copy = list(initial)
    res, out = helper(copy)
    return out

def trace(var_assigns: Dict[str, bool], commands: List[Command]) -> bool:
    '''Evaluates the given commands using the provided variable assignments.'''
    results = []
    for cmd in commands:
        if isinstance(cmd.op, Variable):
            results.append(var_assigns[cmd.op.name])
        else:
            arg_vals = [results[i] for i in cmd.args]
            results.append(cmd.op.eval(arg_vals))

    return results[-1]

def get_vars(commands: List[Command]) -> List[str]:
    '''Extracts free variables from a command list.'''
    out = []
    for cmd in commands:
        if isinstance(cmd.op, Variable):
            out.append(cmd.op.name)
    return out

def truth_table(commands: List[Command]) -> List[Tuple[Dict[str, bool], bool]]:
    '''Constructs a truth table of sorts, for debugging.'''
    out = []
    variables = get_vars(commands)
    for assignments in product([True, False], repeat=len(variables)):
        asgns = {a: b for (a, b) in zip(variables, assignments)}
        out.append((asgns, trace(asgns, commands)))
    return out

def make_evaluator(var_names: List[str], func: Callable[..., bool]) -> Callable[[List[Command]], bool]:
    '''Takes a list of variable names, a regular function, and constructs
    the corresponding evaluator.'''
    def eval(commands: List[Command]) -> bool:
        for assignments in product([True, False], repeat=len(var_names)):
            asgns = {a: b for (a, b) in zip(var_names, assignments)}
            given = trace(asgns, commands)
            expected = func(*assignments)
            if given != expected:
                return False
        return True
    return eval

def full_synthesize(variables: List[str], 
                    func: Callable[..., bool], 
                    opcodes: List[Opcode], 
                    limit: int) -> Optional[List[Command]]:
    '''Attempts to synthesize a set of commands that match the given function
    using only the provided opcodes. Will give up if the number of commands
    exceeds the provided limit.'''
    cmds = [Command(Variable(v), []) for v in variables]
    evaluator = make_evaluator(variables, func)
    for i in range(len(cmds) + 1, limit):
        res = synthesize(evaluator, cmds, opcodes, i)
        if res is not None:
            return res 
    return None

def display(cmds: Optional[List[Command]]) -> None:
    '''Nicely displays a command list.'''
    if cmds is None:
        print('N\A')
    else:
        for idx, cmd in enumerate(cmds):
            print(idx, cmd)
    print()


def main():
    display(full_synthesize(['p'], lambda p: not p, [Nor()], 10))
    display(full_synthesize(['p', 'q'], lambda p, q: p or q, [Nor()], 10))
    display(full_synthesize(['p', 'q'], lambda p, q: p and q, [Nor()], 10))
    display(full_synthesize(['p', 'q'], lambda p, q: p == q, [Nor()], 10))
    display(full_synthesize(
        ['p', 'q', 'r'], 
        lambda p, q, r: q if p else r,
        [And(), Or(), Not()],
        10))

if __name__ == '__main__':
    main()


