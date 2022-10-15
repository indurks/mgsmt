#!/usr/bin/env python3

from z3 import *

def same_node(x, y):
    return x in (y,)

def distinct(xs):
    xs = [x for x in xs] # in-case xs is a generator
    assert all(isinstance(x, tuple) for x in xs)
    return (x for x in xs if len(set(x)) == len(x))

def ordered(xs):
    xs = [x for x in xs] # in-case xs is a generator
    assert all(isinstance(x, tuple) for x in xs)
    return (x for x in distinct(xs) if list(sorted(x)) == x)
