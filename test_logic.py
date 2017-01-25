#!/usr/bin/env python
'''
A program to test logical expressions for equivalence and generate truth tables.

Usage: 

    python test_logic.py
    
Edit the "main" function located at the bottom of the file to change what 
expressions you want to test.
'''
from __future__ import print_function

import itertools
import operator
import functools

DEBUG = False

# Maps the following symbols to the logical operator.
# Any of the aliases are equivalent to the operator on the 
# right. For example, the following two expressions are equivalent:
#
#   (-p ^ q) v (p -> r)
#   LPAREN NEG p AND q RPAREN OR LPAREN p IMPLIES r RPAREN
#   
ALIASES = {
    '-': 'NEG',
    '~': 'NEG',
    '~': 'NEG',
    'V': 'OR',
    'v': 'OR',
    'or': 'OR',
    '+': 'OR',
    '|': 'OR',
    '||': 'OR',
    '^': 'AND',
    '&': 'AND',
    '&&': 'AND',
    '*': 'AND',
    'and': 'AND',
    'xor': 'XOR',
    'nor': 'NOR',
    '$': 'NOR',
    '->': 'IMPLIES',
    '<->': 'BICOND',
    '(': 'LPAREN',
    ')': 'RPAREN',
    'True': 'TRUE',
    'true': 'TRUE',
    'T': 'TRUE',
    '1': 'TRUE',
    'False': 'FALSE',
    'false': 'FALSE',
    'F': 'FALSE',
    '0': 'FALSE'
}

# Which operators take precedence, sort of. The left parens
# and right parens are handled a little unusually.
PRECEDENCE = [
    'LPAREN',
    'AND',
    'OR',
    'XOR',
    'NOR',
    'IMPLIES',
    'BICOND',
    'NEG',
    'RPAREN'
]

# Maps each operator to an equivalent Python function
OP_MAP = {
    'AND': operator.and_,
    'OR': operator.or_,
    'XOR': operator.ne,
    'NOR': lambda a, b: not (a or b),
    'IMPLIES': lambda a, b: not a or b,
    'BICOND': operator.eq
}

def indent(lines):
    '''
    Indents the given lines by four additional spaces. Can be applied
    to the same string multiple times to add multiple indents.
    '''
    return '\n'.join('    ' + line for line in lines.split('\n'))

class Atom(object):
    '''Represents a single variable, such as p or q.'''
    def __init__(self, name):
        self.name = name
        
    def is_simple(self):
        return True
        
    def is_bool(self):
        return self.name in ('TRUE', 'FALSE')
        
    def eval(self, env):
        if self.name == 'TRUE':
            return True
        elif self.name == 'FALSE':
            return False
        else:
            return self.name if isinstance(self.name, bool) else env[self.name]
        
    def __str__(self):
        return self.name

class Expression(object):
    '''Represents an expression -- a collection of compound expressions or 
    atoms. Each expression is made up of one operator (such as AND, NEG, OR), 
    and any number of children expressions.
    
    The primary exception is with NEG -- this program implicitly assumes that
    a NEG expression has only one child.'''
    def __init__(self, op, children):
        self.op = op
        self.children = list(children)
        
    def is_simple(self):
        return self.op == 'NEG' and self.children[0].is_simple()
        
    def children_are_simple(self):
        return all(child.is_simple() for child in self.children)
        
    def eval(self, env):
        if self.op == 'NEG':
            return not self.children[0].eval(env)
        else:
            op_func = OP_MAP[self.op]
            components = [child.eval(env) for child in self.children]
            return functools.reduce(op_func, components)
            
    def __str__(self):
        if self.op == 'NEG':
            return '-' + str(self.children[0])
        elif self.children_are_simple():
            return '(' + self.op + ' ' + ' '.join(map(str, self.children)) + ')'
        else:
            child_strings = '\n'.join(str(child) for child in self.children)
            return '(' + self.op + '\n' + indent(child_strings) + '\n)'

def flatmap(func, iter):
    return list(itertools.chain.from_iterable(map(func, iter)))

def tokenize(text):
    '''Takes a string and breaks it down into a series of separate tokens.'''
    replacements = [(alias, ' {0} '.format(new)) for alias, new in ALIASES.items()]
    replacements = sorted(replacements, key=lambda x: -len(x[0]))
    
    for original, new in replacements:
        text = text.replace(original, new)
        
    tokens = [word for word in text.split(' ') if word.strip() != '']
    return [ALIASES.get(token, token) for token in tokens]
    
def level(token):
    '''Returns what precedence a given operator has.'''
    return -PRECEDENCE.index(token)
    
def transfer_while(func, src, dest):
    '''Transfers objects between stacks.'''
    while func(src):
        dest.append(src.pop())
    
def parse(tokens):
    '''Takes a flat list of tokens, and rearranges them into reverse-polish notation
    (postfix notation) using the Shunting-yard algorithm. For example, the expression 
    
        (-p ^ q) v (r -> q) v -(p ^ q)
        
    ...would be rearranged to:
    
        p NEG q AND r q IMPLIES OR p q AND NEG OR
    '''
    output = []
    operators = []
    transfer = lambda func: transfer_while(func, operators, output)
    level = lambda token: -PRECEDENCE.index(token)
    for tok in tokens:
        if tok == 'LPAREN':
            operators.append(tok)
        elif tok == 'RPAREN':
            transfer(lambda ops: ops[-1] != 'LPAREN')
            operators.pop()
        elif tok in PRECEDENCE:
            transfer(lambda ops: len(ops) > 0 and level(tok) >= level(ops[-1]))
            operators.append(tok)
        else:
            output.append(tok)
    transfer(lambda ops: len(ops) > 0)
    return output
    
def build_ast(tokens):
    '''Converts a series of tokens in RPN to a basic abstract syntax tree. For example,
    the token stream 
    
        p NEG q AND r q IMPLIES OR p q AND NEG OR
        
    ...would be parsed to
    
        (OR
            (NEG (AND q p))
            (OR
                (IMPLIES q r)
                (AND q (NEG p))
            )
        )
        
    Notice that this stage, the children are all in reverse order compared to the 
    original.
    '''
    stack = []
    for tok in tokens:
        if tok in OP_MAP:
            stack.append(Expression(tok, [stack.pop(), stack.pop()]))
        elif tok == 'NEG':
            stack.append(Expression('NEG', [stack.pop()]))
        else:
            stack.append(Atom(tok))
    return stack.pop()
    
def shake(tree):
    '''Takes an AST and cleans it up/fixes the reversed children. Combines 
    operations together when able. For example, the following:
    
        (OR
            (NEG (AND q p))
            (OR
                (IMPLIES q r)
                (AND q (NEG p))
            )
        )
        
    ...would be converted into:
    
        (OR
            (AND (NEG p) q)
            (IMPLIES r q)
            (NEG (AND p q))
        )
    '''
    if isinstance(tree, Atom):
        return tree
    elif len(tree.children) == 2:
        last = tree.children.pop()
        while isinstance(last, Expression) and last.op == tree.op:
            tree.children += last.children
            last = tree.children.pop()
        tree.children = list(map(shake, tree.children + [last]))
        tree.children.reverse() # Converting the tree to rpn flips the items
        return tree
    else:
        tree.children[0] = shake(tree.children[0])
        return tree
    
def build_tree(expr, debug=DEBUG):
    '''Builds a complete tree given a string expression.'''
    def w(message, item):
        if debug:
            print(message)
            print(indent(str(item)))
        return item
    tokens = w('tokenize', tokenize(expr))
    rpn = w('parse', parse(tokens))
    ast = w('build_ast', build_ast(rpn))
    clean = w('shake', shake(ast))
    return clean
    
def find_atom_names(tree):
    '''Finds all unique atom names in a tree.'''
    if isinstance(tree, Atom):
        return [] if tree.is_bool() else [tree.name]
    else:
        return tuple(sorted(set(flatmap(find_atom_names, tree.children))))
    
def generate_envs(atom_names):
    '''Generates all possible truth table values given a list of atom names'''
    def build_combos(atom_names):
        if len(atom_names) == 1:
            return [[True], [False]]
        else:
            prev = build_combos(atom_names[1:])
            output = [[True] + combo for combo in prev]
            output = output + [[False] + combo for combo in prev]
            return output
    return [dict(zip(atom_names, combo)) for combo in build_combos(atom_names)]
    
def display_info(atom_names, exprs, trees):
    print('Initial Input:')
    for expr in exprs:
        print(indent(expr))
    print()
    
    print('All variable names:')
    print(indent(' '.join(atom_names)))
    print()
    
    for index, (expr, tree) in enumerate(zip(exprs, trees)):
        print('Expression {0}: {1}'.format(index + 1, expr))
        print(indent(str(tree)))
        print()
    
def truth_table(*exprs):
    '''Generates and prints a truth table for all provided expressions.'''
    to_str = lambda boolean: 'T' if boolean else 'F'
        
    trees = list(map(build_tree, exprs))
    atom_names = list(find_atom_names(trees[0]))
    combos = generate_envs(atom_names)
    

    display_info(atom_names, exprs, trees)
    
    symbols = atom_names + [str(i + 1) for i in range(len(exprs))]
    header = '  '.join(symbols)
    underline = '-' * len(header)
    
    print('Truth table')    
    print(indent(header))
    print(indent(underline))
    
    for env in combos:
        init = [env[name] for name in atom_names]
        answers = [tree.eval(env) for tree in trees]
        values = list(map(to_str, init + answers))
        print(indent('  '.join(v + ' ' * (len(s) - 1) for v, s in zip(values, symbols))))
        
    print()
        
def is_same(iterator):
    '''Returns true if all elements in the iterator are the same.'''
    try:
        iterator = iter(iterator)
        first = next(iterator)
        return all(first == rest for rest in iterator)
    except StopIteration:
        return True
        
def is_equiv(*exprs):
    '''Attempts to determine if all of the given expressions are logically 
    equivalent.'''
    trees = list(map(build_tree, exprs))
    atom_names = list(flatmap(find_atom_names, trees))

    atom_names = sorted(list(set(atom_names)))
    
    combos = generate_envs(atom_names)
    success = all(is_same(tree.eval(env) for tree in trees) for env in combos)
    
    if not success:
        truth_table(*exprs)
        print('Failure: mismatch')
    else:
        display_info(atom_names, exprs, trees)
        print('Success: complete match')
    print()
    
def s(bool):
    return '1' if bool else '0'
    
def xor(a, b):
    return ''.join(s(i != j) for i, j in zip(a, b))
    
def xnor(a, b):
    return ''.join(s(i == j) for i, j in zip(a, b))

def demo():
    # Tests to see if the following expressions are equivalent.
    # Can accept an arbitrary number of expressions.
    # Place each expression inside of a string. 
    is_equiv(
        "-p v (-q v (-r v s))",
        "s v (-p v (-q v -r))",
        "-s -> (p -> (q -> -r))")
        
    print('-----')
    print()
        
    # Generates truth tables for the given expressions.
    truth_table(
        '-(a XOR b)',
        'a <-> b')
        
    is_equiv(
        '((p -> q) ^ (p -> -r)) -> (-(p ^ r))',
        '((p -> q) ^ (q -> -r)) -> (-p v -r)',
        '((-p v q) ^ (-q v -r)) -> (-p v -r)',
        '-((-p V q) ^ (-q v -r)) v (-p V -r)',
        '(-(-p V q) V -(-q V -r)) v (-q V -r)',
        '((-(-p) ^ -q) V (-(-q) v -(-r))) v (-p v -r)',
        '((p ^ -q) V (q ^ r)) v (-p V -r)',
        '(p ^ -q) v (q ^ r) v -p v -r',
        '((p v -p) ^ (-q v -p)) v (q ^ r) v -p v -r',
        '(true ^ (-q v -p)) v (q ^ r) v -p v -r',
        '(-q v -p) v (q ^ r) v -p v -r',
        '-q v -p v (q ^ r) v -p v -r',
        '-q v (q ^ r) v -p v -r',
        '-q v ((q v -r) ^ (r v -r)) v -p v -r',
        '-q v ((q v -r) ^ true) v -p v -r',
        '-q v (q v -r) v -p v -r',
        '-q v q v -r v -p v -r',
        'true v -r v -p v -r',
        'true')
        
    truth_table(
        '((p -> q) -> (q -> -r)) -> (-p -> -r)')
        
    truth_table('a xor b')
    
    truth_table('a -> b')
    
    truth_table(
        'a xor b',
        '(a v b)  ^ -(a ^ b)',
        '(a ^ -b) v (-a ^ b)')
    
def main():
    is_equiv(
            '(x + y) * (-x + z)',
            '((x + y) * -x) + ((x + y) * z)',
            '(-x * (x + y)) + (z * (x + y))',
            '((-x * x) + (-x * y)) + ((z * x) + (z * y))',
            '(F + (-x * y)) + ((z * x) + (z * y))',
            '(-x * y) + (x * z) + (y * z)',
            '(x * z) + (y * z)  + (-x * y)',
            '(x * z) + (z * y)  + (-x * y)',
            '(x * z) + (-x * y)',
            '(x * z) + (-x * y)')
        
        
if __name__ == '__main__':
    main()
            
