

def quickxplain(p, s, r):
    if p(r):
        return set()
    else:
        return has_fault(p,s,r)


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
    # print("oracle", s)
    global stack
    stack.append((out, len(s)))
    return out

print(quickxplain(oracle, set(range(1000)), set()))
print(stack)
    # elif p(l.union(c)):
    #     has_fault(p,l,c)

