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
    for i in range(start, 2):
        if not f(i):
            return

    # We now know that f(4) is true. We want to find some number for which
    # f(n) is *not* true.
    # lo is the largest number for which we know that f(lo) is true.
    # lo = max(start-1, 0)

    # Exponential probe upwards until we find some value hi such that f(hi)
    # is not true. Subsequently we maintain the invariant that hi is the
    # smallest number for which we know that f(hi) is not true.
    # hi = max(start, 3)
    # if not f(0):
    #     return 0
    i = 3
    while f(i):
        # lo = hi
        i = i * 2

    # Now binary search until lo + 1 = hi. At that point we have f(lo) and not
    # f(lo + 1), as desired..
    # while lo + 1 < hi:
    #     mid = (lo + hi) // 2
    #     if f(mid):
    #         lo = mid
    #     else:
    #         hi = mid
    # return lo

class Shrink:
    def __init__(self, items, p):
        self.items = list(items)
        self.backmap = {k: idx for idx,k in enumerate(self.items)}
        self.state = items
        self.oracle = p
        self.history = []
        self._epoch = 0
        self.hidden = set()
        self.pending = []
        self.critical = set()
        self.avg_shrink = 0
    def try_shrink_in_place(self, new):
        inp = new.union(self.hidden)
        # print("inplace", len(inp))
        if self.oracle(inp):
            self.history.append((True, len(inp)))
            self._epoch += 1
            return True
        else:
            self.history.append((False, len(inp)))
            return False
    def try_drop(self, affected):
        assert(len(affected) > 0)
        inp = self.state.union(self.hidden).difference(affected)
        if self.oracle(inp):
            # print("mut1", len(inp), affected)
            self.history.append((True, len(inp)))
            self.state.difference_update(affected)
            self._epoch += 1
            return True
        else:
            self.block(affected)
            self.history.append((False, len(inp)))
        return False
    def try_shrink(self, new):
        inp = new.union(self.hidden)
        if self.oracle(inp):
            affected = self.state.difference(new)
            assert(len(affected) > 0)
            # print("mut1", len(inp), affected)
            self.history.append((True, len(inp)))
            self.state = new
            self._epoch += 1
            return True
        else:
            affected = self.state.difference(new)
            self.block(affected)
            self.history.append((False, len(inp)))
        return False
    def epoch(self):
        return self._epoch
    def try_drop_range(self, idx_map,i,left, orig):
        if i < 0 or i + left > len(idx_map) or left == 0:
            return False

        out = orig.copy()
        for x in range(i, i + left):
            out.remove(self.items[idx_map[x]])
        return self.try_shrink(out)
    def best_blocked(self):
        return len(self.pending) and len(self.pending[-1]) or -1
    def step(self):
        if self.prefer_blocked(self.state):
            self.unblock_some()
        else:
            self.handle_unblocked()
    def prefer_blocked(self, S):
        raise NotImplementedError()
    def handle_unblocked(self):
        raise NotImplementedError()

    def is_done(self):
        return len(self.pending) == 0 and len(self.state) == 0

    def pop_blocked(self):
        out = self.pending.pop()
        assert(type(out) == type(set()))
        self.stop_implicit(out)
        return out

    def stop_implicit(self, s):
        self.hidden.difference_update(s)
    def unhide(self, s):
        assert(type(s) == type(set()))
        self.hidden.difference_update(s)
        self.state.update(s)
    def hide(self, s):
        assert(type(s) == type(set()))
        self.hidden.update(s)
        self.state.difference_update(s)
    def hide_all(self):
        s = self.state
        self.state = set()
        self.hide(s)
        return s
    def unblock_some(self):
        temp = self.hide_all()
        self.bin_search_crit(self.pop_blocked())

        self.unhide(temp)
    def block(self, s):
        if len(s) == 1:
            self.mark_critical(s)
        else:
            self.hide(s)
            self.pending.append(s)
            self.mk_queue_order()
    def mk_queue_order(self):
        below_avg_shrink = [x for x in self.pending if len(x) < self.avg_shrink]
        above_avg_shrink = [x for x in self.pending if len(x) >= self.avg_shrink]
        below_avg_shrink.sort(key = lambda x: len(x))
        above_avg_shrink.sort(key = lambda x: -len(x))
        self.pending = below_avg_shrink + above_avg_shrink
        # self.pending.sort(key= lambda x: len(x))
    def mark_critical(self, s):
        assert(type(s) == type(set()))
        self.critical.update(s)
        self.hide(s)
    def tell_shrink(self, size):
        self.avg_shrink = max(size, self.avg_shrink)
    def bin_search_crit(self, s):
        assert(len(set(s).intersection(self.hidden)) == 0)
        self.stop_implicit(s)
        while True:
            if len(s) <= 1:
                self.mark_critical(s)
                return
            # if len(s) == 3 or len(s) == 5:
            #     self.linear_scan(s)
            #     return
            ls = list(s)
            half = len(ls)//2
            l = set(ls[:half])
            r = set(ls[half:])
            print(compact(s), "=>", compact(l), compact(r))
            if self.try_shrink_in_place(l):
                self.tell_shrink(half)
                s = l
            elif self.try_shrink_in_place(r):
                self.tell_shrink(half)
                s = r
            elif half > self.avg_shrink:
                self.block(l)
                s = r
            else:
                self.block(l)
                self.block(r)
                return
            if self.best_blocked() > 32 and  len(s) <= self.avg_shrink and self.best_blocked() >= (len(s)-1)*2:
                # print(len(s), "->", self.best_blocked())
                self.block(s)
                return
    def solve(self):
        while not self.is_done():
            self.step()
    def linear_scan(self, s):
        self.state.update(s)
        for x in s:
            self.try_drop(set([x]))
        return

class Crits:
    def __init__(self, shrinker):
        self.backmap = shrinker.backmap
        self.crits = []
        known = [shrinker.backmap[c] for c in shrinker.critical]
        guessed = [self.region_center(reg) for reg in shrinker.pending if len(reg) <= 32]
        # print("crits", known, guessed)

        self.crits.extend(known) 
        self.crits.extend(guessed)

        if len(self.crits) > 0:
            noncrits = set(shrinker.items)
            noncrits.difference_update(shrinker.hidden)
            noncrits.difference_update(shrinker.state)

            self.danger_distance = len(noncrits) and sum(self.crit_distance(n) for n in noncrits) / len(noncrits) or 0
        else:
            self.danger_distance = 0
    def region_center(self, reg):
        positions = [self.backmap[c] for c in reg]
        return sum(positions)/len(positions)
    def crit_distance(self, idx):
        if len(self.crits) == 0:
            return 0
        total = min(abs(idx-x) for x in self.crits)
        return total
    def total_crit_distance(self, S):
        return min(self.crit_distance(self.backmap[c]) for c in S)

    def partition_crit_distances(self, S):
        ls = [(self.crit_distance(self.backmap[i]), i) for i in S]
        half = len(ls)//2
        splitter = self.danger_distance + 2
        l = [i[1] for i in ls if i[0] < splitter]
        r = [i[1] for i in ls if i[0] >= splitter]
        if len(S) <= 3 or (len(r) == 0 and len(l) < 8):
            return []
        if len(l) == 0 or len(r) == 0:
            ls = list(S)
            r = ls[:half]
            l = ls[half:]
        return [l,r]
def compact(s):
    s = list(s)
    if len(s) == 0:
        return "[]"
    s.sort()
    l = s[0]
    r = s[0]
    out = []
    for i in s[1:]:
        if i == r + 1:
            r = i
        else:
            if l == r:
                out.append(str(l))
            else:
                out.append("{}-{}".format(l, r))
            l = i
            r=i

    if l == r:
        out.append(str(l))
    else:
        out.append("{}-{}".format(l, r))
    return "[" + ",".join(out) + "]"
class CritShrink(Shrink):
    def handle_unblocked(self):
        self.block(set(self.state))
        self.state = set()
        # crits = Crits(self)
    def prefer_blocked(self, S):
        return self.best_blocked() > len(S)
    def bin_search_crit(self, s):
        assert(len(set(s).intersection(self.hidden)) == 0)
        crits = Crits(self)
        avg_len = len(self.pending) and (sum(len(x) for x in self.pending) / len(self.pending)) or 0
        while True:
            assert(len(set(s).intersection(self.hidden)) == 0)
            if len(s) <= 1:
                self.mark_critical(s)
                return
            partition = crits.partition_crit_distances(s)
            if len(partition) == 0:
                self.linear_scan(s)
                return
            for x in partition:
                x = set(x)
                if self.try_shrink_in_place(set(x)):
                    s = x
                    break
            else:
                for x in partition:
                    self.block(set(x))
                return
    def pop_blocked(self):
        crits = Crits(self)
        boring = (all(len(v) > 32 for v in self.pending) and len(self.critical) == 0 )
        self.pending.sort(key = lambda x:  boring and -len(x) or crits.total_crit_distance(x)+len(x))
        out = self.pending.pop()
        assert(type(out) == type(set()))
        self.stop_implicit(out)
        return out

        
class BlockShrink(Shrink):
    def handle_unblocked(self):
        self.block(set(self.state))
        self.state = set()
    def prefer_blocked(self, S):
        return self.best_blocked() > len(S)

class AdaptiveShrink(Shrink):
    def prefer_blocked(self, S):
        return self.best_blocked() >= self.mk_step(S)
    def handle_unblocked(self):
        k = max(1, self.mk_step(self.state))
        idx_map = []
        for idx,v in enumerate(self.items):
            if v in self.state:
                idx_map.append(idx)
        k = max(k, 1)
        left = len(idx_map) - k
        if left < 0:
            return False
        i = random.randint(0, left)

        orig = self.state.copy()
        def offset_left(j):
            return i - (j//2) * k
        def app_shrink(n):
            l = offset_left(n)
            r = k * n
            lt = max(0, l)
            fromL = len(idx_map) - l
            rt = min(fromL, r)
            if lt != l and rt != r:
                return False
            return self.try_drop_range(idx_map, lt, rt, orig=orig)


        find_integer(app_shrink)
    def mk_step(self, S):
        crits_found = len(self.critical) + len(self.pending)
        removed = len(self.items) - len(S)
        percent_crit = ((1+crits_found) / (removed+40))
        expected_crit = percent_crit * len(S)
        step = round(len(S) / max(1, expected_crit))
        return step

        
# hide {0, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999} [
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 201, in <module>\n    shrinker.solve()\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 196, in solve\n    self.step(lambda: self.shrink_set_jump(round(m.log(len(self.state), 2))))\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 134, in step\n    self.unblock_some()\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 162, in unblock_some\n    self.hide(temp)\n',
#     '  File "C:\\Users\\Cyril\\Projects\\NaiveSolver\\shrink_list.py", line 156, in hide\n    caller = traceback.format_stack()\n'
# ]       

def oracle1(x):
    out = {100,200,300,400,500,600,700,800,900}.issubset(set(x))
    return out
def oracle2(x):
    out = set(range(100,200)).issubset(set(x))
    out = out and set(range(700,800)).issubset(set(x))
    return out
def oracle3(x):
    out = set(range(100,110)).issubset(set(x))
    # out = out and set(range(700,800)).issubset(set(x))
    return out
def oracle4(x):
    out = set(range(20)) == set(x)
    return out
def oracle5(x):
    out = set(range(0,10000, 1000)).issubset(set(x))
    return out


def distribution_for(pos,size, tag, step=1):
    def predicate(s):
        out = set(range(pos, size, step)).issubset(set(s))
        return out
    shrinker = BlockShrink(set(range(1000)), predicate)
    shrinker.solve()
    stack = shrinker.history
    length = len(stack)
    total = sum(x[1] for x in stack)
    return tag,total,length

# out = []
# for i in range(10,200, 10):
#     step = 1000 // i
#     out.append(distribution_for(step,1000, step=step, tag=i))
# print(out)
# shrinker = BlockShrink(set(range(20)), oracle4)
shrinker = BlockShrink(set(range(1000)), oracle1)
# shrinker = BlockShrink(set(range(10000)), oracle5)
shrinker.solve()
print("state", compact(shrinker.state))
print("hidden", compact(shrinker.hidden))
print("critical", compact(shrinker.critical))
print("pending", list(map(compact, shrinker.pending)))
print("oracles", len(shrinker.history))
print("total", sum(v[1] for v in shrinker.history))

print(shrinker.history)
