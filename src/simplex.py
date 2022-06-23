import numpy as np
import itertools as itertools


# we are doing minimizing simplex over normalized constraints,
# minimize c^T x
# subject to A x = b, x >= 0, b >= 0

# If c is |b| (the number of constraints)  and k = |c| (the
# number of variables), then the problem has k-c degrees of freedom.
# Intuitively, every equation determines one variable and the leftovers have to be optimized.
# The big idea is that the solution must be at a vertex where multiple
# constraints meet. This is because our objective is linear, i.e. we can visualize plane which is slowly pushed in one direction until it is about to leave our feasible polygon.
# Because our only inequality constraints have the form x_i >= 0 we can pick
# k-c constraints to "max out" (set x_i=0), and the remaining k-c constraints
# follow from the equation system.
# The zeroed variables (which touch their minimum) are called non-basic variables, the indirectly determined ones are called basic variables.

# We must find the right set of k-c to use as non-basic variables

def simplex_for_basis(A, b, c, basis):
    B = A[:, basis]
    inv_B = np.linalg.inv(B)
    amounts = np.dot(inv_B, b)
    cost = np.dot(c[basis], amounts)[0]
    basis_set = { b:i for i,b in enumerate(basis) }
    bindings = [amounts[basis_set[i]] if i in basis_set else 0 for i in range(len(c))]
    return cost, bindings

def stupid_simplex(A, b, c):
    for s in itertools.combinations(range(len(c)), len(c)-len(b)):
        print(simplex_for_basis(A, b, c, s))
# stupid_simplex(np.array([[2, 1]]), np.array([3]), np.array([1, 2]))


def pivot(M, b, c, r,base):
    pivot_in = np.argmin(c)
    if c[pivot_in] >= 0:
        return "min reached", M, b, c, r,base
    piv_dir = M[:, pivot_in]
    if np.all(piv_dir < 0):
        return "unlimited", M, b, c, r,base
    pivot_out = np.argmin(b / piv_dir)
    piv_amount = b[pivot_out]/piv_dir[pivot_out]

    pivot = pivot_matrix(M, pivot_in, pivot_out)
    r = r - c[pivot_in] * b[pivot_out] / M[pivot_out, pivot_in]
    M = pivot @ M
    b = pivot @ b
    print(np.shape(c), np.shape(pivot))
    base[pivot_out] = pivot_in
    c = c - c[pivot_in] * M[pivot_out] / M[pivot_out, pivot_in]
    return True,M, b,c,r,base
def pivot_matrix(m, p_col, q_row):
    piv = np.identity(len(m))
    piv[:, q_row] = -m[:, p_col] / m[q_row, p_col]
    piv[q_row, q_row] = 1 / m[q_row, p_col]
    return piv



eA = np.array([[3,2,1,1,0], [2,5,3,0,1]])
eb = np.array([10, 15])
ec = np.array([-2, -3, -4, 0, 0])

def initialize(eA, eb, ec):
    base_len = len(ec)-len(eb)
    inv = np.linalg.inv(eA[:, base_len:])
    M = inv @ eA
    b = inv @ eb
    ecb = ec[base_len:]
    c = ec - (ecb @ M)
    return M, b, c, list(range(len(eb)+1, len(ec)))

M,b,c,base = initialize(eA, eb, ec)
r = - (c[base] @ b)
print(M, b, c, base, -r)
while True:
   k,M,b,c,r,base = pivot(M, b, c, r, base)
   print(k, M, b, c, -r, base)
   if k is not True: break
print(ec[base] @ b)
