

def quickxplain(p, s, r):
    if p(r):
        return set()
    else:
        # return has_fault2(p,len(r) > 0, s,r)
        return has_fault(p, s,r)
def has_fault2(p, has_delta, s, c):
    if has_delta and p(c):
        return set()
    if len(s) == 1:
        return set(s)
    ls = list(s)
    half = len(ls)//2
    l = set(ls[:half])
    r = set(ls[half:])

    # if p(l.union(c)):
    #     return has_fault(p,l,c)
    # elif p(r.union(c)):
    #     return has_fault(p,r,c)
    # else:
    x = has_fault2(p,True, r,c.union(l))
    return x.union(has_fault2(p, True, l, c.union(x)))


def has_fault(p, s, c):
    if len(s) == 1:
        return set(s)
    ls = list(s)
    half = len(ls)//2
    l = set(ls[:half])
    r = set(ls[half:])
    if p(l.union(c)):
        return has_fault(p,l,c)
    elif p(r.union(c)):
        return has_fault(p,r,c)
    else:
        x = has_fault(p,r,c.union(l))
        assert(len(x) > 0)
        return x.union(has_fault(p, l, c.union(x)))


stack = []
def oracle(s):
    out = {100,200,300,400,500,600,700,800,900}.issubset(set(s))
    global stack
    stack.append((out, len(s)))
    return out
def oracle2(x):
    out = set(range(100,200)).issubset(set(x))
    out = out and set(range(700,800)).issubset(set(x))
    stack.append((out, len(x)))
    return out
def oracle3(x):
    out = set(range(100,110)).issubset(set(x))
    stack.append((out, len(x)))
    return out
def oracle4(x):
    out = set(range(20)) == set(x)
    stack.append((out, len(x)))
    return out

print(quickxplain(oracle4, set(range(20)), set()))
# print(quickxplain(oracle, set(range(1000)), set()))
print(stack)
    # elif p(l.union(c)):
    #     has_fault(p,l,c)

