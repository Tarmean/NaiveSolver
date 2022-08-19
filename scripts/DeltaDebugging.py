
import math as m
from typing import Callable,Sequence,Any

PASS = 'PASS'
FAIL = 'FAIL'
UNRESOLVED = 'UNRESOLVED'

def ddmin(test: Callable, inp: Sequence, *test_args: Any) -> Sequence:
    """Reduce the input inp, using the outcome of test(fun, inp)."""
    # assert test(inp, *test_args) != PASS

    n = 2     # Initial granularity
    offset = 0
    while len(inp) >= 2:
        start = 0
        subset_length = int(len(inp) / n)

        for idx_base in range(0, n):
            idx = (idx_base + offset) % n
            base = subset_length * idx
            complement = inp[:base] + inp[base + subset_length:]
            if test(complement, *test_args) == FAIL:
                inp = complement
                n = max(n-1, 2)
                offset = idx
                break
        else:
            if n == len(inp):
                break
            new_n = min(n * 2, len(inp))
            offset = round(offset * (new_n / n))
            # offset = m.floor(offset * n / new_n)
            # offset = offset+(n-new_n) // 2
            n = new_n
    return inp



stack = []
seen = {}
repeats = []
def predicate(x):
    l = frozenset(x)
    global repeats
    if l in seen:
        repeats.append(len(l))
        return seen[l]
    out = {100,200,300,400,500,600,700,800,900}.issubset(set(x))
    seen[l] = out
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate2(x):
    l = frozenset(x)
    global repeats
    if l in seen:
        repeats.append(len(l))
        return seen[l]
    out = set(range(100,200)).issubset(set(x))
    out = out and set(range(700,800)).issubset(set(x))
    seen[l] = out
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate3(x):
    l = frozenset(x)
    global repeats
    if l in seen:
        repeats.append(len(l))
        return seen[l]
    out = set(range(100,110)).issubset(set(x))
    seen[l] = out
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate4(x):
    l = frozenset(x)
    global repeats
    if l in seen:
        repeats.append(len(l))
        return seen[l]
    out = set(range(20)) == set(x)
    seen[l] = out
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate5(x):
    l = frozenset(x)
    global repeats
    if l in seen:
        repeats.append(len(l))
        return seen[l]
    out = set(range(0,10000,1000)).issubset(set(x))
    seen[l] = out
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'

def distribution_for(pos,size, total, tag, step=1):
    global stack
    stack = []
    print(list(range(pos, size, step)))
    def predicate(s):
        global stack
        out = set(range(pos, size, step)).issubset(set(s))
        stack.append((out, len(s)))
        return out and 'FAIL' or 'PASS'
    ddmin(predicate, list(range(total)))
    length = len(stack)
    total = sum(x[1] for x in stack)
    return tag,total,length

out = []
for i in range(10,200, 10):
    step = 1000 // i
    out.append(distribution_for(step,1000, 1000, step=step, tag=i))

print(out)
# print(ddmin(predicate4, list(range(20))))
# ddmin(predicate3, list(range(1000)))
# ddmin(predicate5, list(range(10000)))
# print(len(repeats))
# print("invocations", len(stack))
# # print(stack)
# print("repeats", sum(repeats))
# print("total", sum(x[1] for x in stack))

