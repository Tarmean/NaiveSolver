
from typing import Callable,Sequence,Any

PASS = 'PASS'
FAIL = 'FAIL'
UNRESOLVED = 'UNRESOLVED'

def ddmin(test: Callable, inp: Sequence, *test_args: Any) -> Sequence:
    """Reduce the input inp, using the outcome of test(fun, inp)."""
    assert test(inp, *test_args) != PASS

    n = 2     # Initial granularity
    while len(inp) >= 2:
        start = 0
        subset_length = int(len(inp) / n)
        some_complement_is_failing = False

        while start < len(inp):
            complement = (inp[:int(start)] + inp[int(start + subset_length):])

            if test(complement, *test_args) == FAIL:
                inp = complement
                n = max(n - 1, 2)
                some_complement_is_failing = True
                break

            start += subset_length

        if not some_complement_is_failing:
            if n == len(inp):
                break
            n = min(n * 2, len(inp))

    return inp



stack = []
def predicate(x):
    out = {100,200,300,400,500,600,700,800,900}.issubset(set(x))
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate2(x):
    out = set(range(100,200)).issubset(set(x))
    out = out and set(range(700,800)).issubset(set(x))
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate3(x):
    out = set(range(100,110)).issubset(set(x))
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'
def predicate4(x):
    out = set(range(20)) == set(x)
    stack.append((out, len(x)))
    return out and 'FAIL' or 'PASS'

print(ddmin(predicate4, list(range(20))))
# print(ddmin(predicate3, list(range(1000))))
print(stack)

