import random
from typing import Callable
import math as m
import traceback



def binary_search(lo: int, hi: int, f: Callable[[int], bool]) -> int:
    """Binary searches in [lo , hi) to find
    n such that f(n) == f(lo) but f(n + 1) != f(lo).
    It is implicitly assumed and will not be checked
    that f(hi) != f(lo).
    """

    reference = f(lo)

    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if f(mid) == reference:
            lo = mid
        else:
            hi = mid
    return lo
def find_integer(f: Callable[[int], bool], start=1) -> int:
    """Finds a (hopefully large) integer such that f(n) is True and f(n + 1) is
    False.
    f(0) is assumed to be True and will not be checked.
    """
    # We first do a linear scan over the small numbers and only start to do
    # anything intelligent if f(4) is true. This is because it's very hard to
    # win big when the result is small. If the result is 0 and we try 2 first
    # then we've done twice as much work as we needed to!
    for i in range(start, 5):
        if not f(i):
            return i - 1

    # We now know that f(4) is true. We want to find some number for which
    # f(n) is *not* true.
    # lo is the largest number for which we know that f(lo) is true.
    lo = max(start-1, 4)

    # Exponential probe upwards until we find some value hi such that f(hi)
    # is not true. Subsequently we maintain the invariant that hi is the
    # smallest number for which we know that f(hi) is not true.
    hi = max(start, 5)
    while f(hi):
        lo = hi
        hi *= 2

    # Now binary search until lo + 1 = hi. At that point we have f(lo) and not
    # f(lo + 1), as desired..
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if f(mid):
            lo = mid
        else:
            hi = mid
    return lo

class Shrink:
    def __init__(self, items, p):
        self.items = list(items)
        self.state = items
        self.oracle = p
        self.history = []
        self._epoch = 0
        self.hidden = set()
        self.pending = []
        self.critical = set()
    def try_shrink_in_place(self, new):
        inp = new.union(self.hidden)
        if self.oracle(inp):
            self.history.append((True, len(inp)))
            self._epoch += 1
            return True
        else:
            self.history.append((False, len(inp)))
            return False
    def try_shrink(self, new):
        inp = new.union(self.hidden)
        if self.oracle(inp):
            affected = self.state.difference(new)
            # print("true", affected, new)
            self.history.append((True, len(inp)))
            self.state = new
            self._epoch += 1
            return True
        else:
            affected = self.state.difference(new)
            # print("false", affected, new.union(self.hidden))
            self.block(affected)
            self.history.append((False, len(inp)))
        return False
    def epoch(self):
        return self._epoch
    def try_drop(self, i,left):
        if i < 0 or i + left > len(self.state) or left == 0:
            return False
        out = self.state.copy()
        while left > 0:
            if i > len(self.items):
                return False
            if self.items[i] in out:
                left = left - 1
                out.remove(self.items[i])
            i += 1
        return self.try_shrink(out)
    def shrink_set_jump(self, k):
        k = max(k, 1)
        left = len(self.state) - k
        if left < 0:
            print("shrink set jump fail 1", k, self.state)
            return False
        i = random.randint(0, left)
        def offset_left(j):
            return i - j * k
        l = offset_left(find_integer(lambda n: 
            self.try_drop(offset_left(n), k*n)
        ))
        r = find_integer(lambda n:
            self.try_drop(l, k * n)
        )
    def fix_point(self, f, tries=1):
        epoch = self.epoch()
        while tries > 0:
            f()
            if self.epoch() == epoch:
                tries -= 1
            epoch = self.epoch()
    def best_blocked(self):
        return len(self.pending) and len(self.pending[0]) or -1
    def step(self, f):
        blocked = self.best_blocked()
        local = len(self.state)
        if blocked > local:
            self.unblock_some()
        else:
            f()
    def is_done(self):
        return len(self.pending) == 0 and len(self.state) == 0

    def pop_blocked(self):
        out = self.pending[0]
        assert(type(out) == type(set()))
        self.pending = self.pending[1:]
        self.hidden.difference_update(out)
        return out

    def stop_implicit(self, s):
        self.hidden.difference_update(s)
    def unhide(self, s):
        assert(type(s) == type(set()))
        print("unhide", s)
        self.hidden.difference_update(s)
        self.state.update(s)
    def hide(self, s):
        assert(type(s) == type(set()))
        caller = traceback.format_stack()
        print("hide", s, caller)
        self.hidden.update(s)
        self.state.difference_update(s)
    def hide_all(self):
        s = self.state
        self.state = set()
        self.hide(s)
        return s
    def unblock_some(self):
        temp = self.hide_all()

        self.bin_search_crit(list(self.pop_blocked()))

        self.unhide(temp)
    def block(self, s):
        print("block", s)
        self.hide(s)
        self.pending.append(s)
    def mark_critical(self, s):
        assert(type(s) == type(set()))
        self.critical.update(s)
        self.hide(s)
    def bin_search_crit(self, s):
        assert(len(set(s).intersection(self.hidden)) == 0)
        s0 = s.copy()
        self.stop_implicit(set(s))
        while True:
            if len(s) <= 1:
                print("critical", s, s0)
                self.mark_critical(set(s))
                return
            half = len(s)//2
            l = s[:half]
            r = s[half:]
            if self.try_shrink_in_place(set(l)):
                print(s0, "=>l ", l)
                self.block(set(l))
                return
            else:
                s = r
    def solve(self):
        while not self.is_done():
            self.step(lambda: self.shrink_set_jump(round(m.log(len(self.state), 2))))

        
# hide {0, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999} [
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 201, in <module>\n    shrinker.solve()\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 196, in solve\n    self.step(lambda: self.shrink_set_jump(round(m.log(len(self.state), 2))))\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 134, in step\n    self.unblock_some()\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 162, in unblock_some\n    self.hide(temp)\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 156, in hide\n    caller = traceback.format_stack()\n'
# ]       

shrinker = Shrink(set(range(1000)), lambda x: {100,200,300,400,500,600,700,800,900}.issubset(x))
shrinker.solve()
print("state", shrinker.state)
print("hidden", shrinker.hidden)
print("critical", shrinker.critical)
print("pending", shrinker.pending)
# shrinker.fix_point(lambda:
#     shrinker.shrink_set_jump(3)
# )
# shrinker.fix_point(lambda:
#     shrinker.shrink_set_jump(1)
# )
print(shrinker.history)

