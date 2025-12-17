from math import gcd, log, floor, sqrt, exp, ceil
from random import randint
from copy import deepcopy

# Import prime numbers lower n
def getFirstPrimesLower(n):
    with open("primes.txt", "r") as fd:
        primes = list(map(int, fd.read().split()))
        ind = 0
        while (ind == 0):
            try:
                ind = primes.index(n)
            except:
                n-=1
    return(primes[:ind+1])

# Import prime at position
def getCurPrime(n):
    with open("primes.txt", "r") as fd:
        prime = list(map(int, fd.read().split()))[n - 1]
    return(prime)

# Import prime number at next position
def getNextPrime(n):
    with open("primes.txt", "r") as fd:
        primes = list(map(int, fd.read().split()))
        ind = 0
        n+=1
        while (ind == 0):
            try:
                ind = primes.index(n)
            except:
                n+=1
    return(primes[ind])

### ++POLLARD'S P-1 METHOD++ ###

def pm1Pollard(n, B):
    a = randint(2, n-2)
    d = gcd(a, n)
    if d > 1:
        return d
    for _ in B:
        l = floor(log(n)/log(_))
        a = pow(a, _**l, n)
    d = gcd(a-1, n)
    if d < n and d > 1:
        return d
    return -1

### ++POLLARD'S RHO METHOD++ ###

# Functions for random mapping
def F1(x, n):
    return pow(x*x + 1, 1, n)
def F2(x, n):
    return pow(x*x + 2, 1, n)
def F3(x, n):
    return pow(x*x + 3, 1, n)
def F4(x, n):
    return pow(x*x + 4, 1, n)
def F5(x, n):
    return pow(x*x + 5, 1, n)

# Rho method
def RhoPollard(n):
    x = 1
    y = x
    while True:
        x = F5(x, n)
        y = F5(F5(x, n), n)
        d = gcd(abs(x - y), n)
        if d != 1:
            if d == n:
                return -1
            else:
                return d

### ++QUADRATIC SIEVE METHOD++ ###

# Transpose Matrix
def TM(A):
    TA = [[0 for x in range(len(A))] for x in range(len(A[0]))]
    for i in range(len(A)):
        for j in range(len(A[0])):
            TA[j][i] = A[i][j]
    return TA

# Gauss Transformation
def GaussTransform(A):
    A.sort(reverse=True)
    i = 0
    while i < len(A):
        for j in range(len(A[0])):
            if j < i and A[i][j] == 1:
                for k in range(len(A[0])):
                    if A[j][k] == 1:
                        A[i][k] = 0 if A[i][k] == 1 else 1
                A.sort(reverse=True)
                i = -1
                break
        i+=1
    return A

# Gauss Solution
def GaussSolve(A):
    K = [[0 for i in range(len(A))]]
    for i in range(len(A) - 1, 0, -1):
        if A[i][i] == 0:
            KK = []
            for j in range(len(K)):
                K[j][i] = 0
                KK.append(K[j].copy())
                KK[j][i] = 1
            K = K + KK
        if A[i][i] == 1:
            for _ in K:
                s = 0
                for j in range(i+1, len(_)):
                    s+=_[j]*A[i][j]
                if s%2 == 0:
                    for j in range(len(K)):
                        K[j][i] = 0
                else:
                    for j in range(len(K)):
                        K[j][i] = 1
    return K

# Legandre Symbol
def LS(a, n):
    g = 1
    while (True):
        if (a == 0):
            return 0
        if (a == 1):
            return g
        a1 = a
        k = 0
        while (a1 % 2 == 0):
            k+=1
            a1>>=1
        if (k % 2 == 0):
            s = 1
        else:
            if (n % 8 == 1 or n % 8 == 7):
                s = 1
            else:
                s = -1
        if (a1 == 1):
            return (g * s)
        if (n % 4 == 3 and a1 % 4 == 3):
            s*=-1
        a = n % a1
        n = a1
        g*=s

# Quadratic Nonresidue modulo p
def NR(p):
    i = 1
    while (True):
        if LS(i, p) == -1:
            return p
        i+=1

# Multiplicatively inverse
def MultInverse(a, p):
    #ax = 1(mod p)
    y1 = 1
    y0 = 0
    n1 = p
    n2 = a
    while(n2 != 0):
        k = n1//n2
        n1, n2 = n2, n1%n2
        y0, y1 = y1, y0 - y1*k
    return y0

# Second Degree Comparision
def SDC(n, p):
    k = 0
    h = p - 1
    while (h%2 == 0):
        k+=1
        h>>=1
    a1 = pow(n, (h+1)//2, p)
    a2 = MultInverse(n, p)
    n1 = NR(p) % p
    n2 = 1
    j = 0
    for i in range(k-1):
        b = (a1 * n2) % p
        c = (a2 * b**2) % p
        d = pow(c, 2**(k-2-i), p)
        if (d == 1):
            j = 0
        if (d == p-1):
            j = 1
        n2*=n1**(2**i*j)
        n2%=p

    return [(a1*n2 - floor(sqrt(n)))%p, (-a1*n2 - floor(sqrt(n)))%p]

# Check B-smoothing
def CheckB(x, n, B):
    s = x + floor(sqrt(n))
    f = s**2 - n
    E = []
    ExpE = []
    for p in B[1:]:
        e = 0
        while (f % p == 0):
            e+=1
            f//=p
        ExpE.append(e)
        E.append(e % 2)
    if (f < 0):
        f//=-1
        E = [1] + E
        ExpE = [1] + ExpE
    else:
        E = [0] + E
        ExpE = [0] + ExpE
    if (f == 1):
        return [True, E, s, ExpE]
    else:
        return [False, E, s, ExpE]
    
# Quadratic Sieve Method
# B = {-1, 2, 3, ...}
def QS(n, P): # <n> - number, <P> - optimal h, <Gs> - "grid size"
    # Get B list with prime numbers under P
    B = [-1, 2]
    B_ = getFirstPrimesLower(P)[1:]
    for _ in B_:
        if (LS(n, _) == 1):
            B.append(_)
    h = len(B) - 1
    # Need to get h + 2 "s" values ("S" list) -> need to get not less than h + 2 possible values of "x" ("X" list)
    X = []
    S = []
    # For any possible value "x" need to check f(x) = (x + [sqrt(n)])^2 - n for B-smoothing
    # For optimization, all values f(x) cant be checked, so need to "sieve" them
    # "Sieving" performed based on quadratic comparison modulo p from B (p - prime number)
    # CompSolved - list with solutions of comparisons x^2 = a (mod p)
    CompSolved = [] # [0] = a, [1] = p
    CompSolved.append([n%2, 2]) # (mod 2) have only 1 solution
    for p in B[2:]:
        sdcSol = SDC(n, p) # 2 solutions for (mod p), p > 2
        CompSolved.append([sdcSol[0], p])
        CompSolved.append([sdcSol[1], p])
    # For factorization n need "E" list of vectors "e", needed for calculating "s" and "t"
    E = []
    ExpE = []
    # Check "sieving" with "grid size" = 3 ("x" must satisfy not less than 3 solved comparisions)
    # A (in our designation - M) must satisfy P < A < P^2
    M = (P+1) ** 3
    flNsqrt = floor(sqrt(n))
    logsTable = [[log(abs((x+flNsqrt)**2-n)), x] for x in range(-M, M+1)]
    for comp in CompSolved:
            for i in range(len(logsTable)):
                if logsTable[i][1] % comp[1] == comp[0]:
                    while i < len(logsTable):
                        if logsTable[i][0] > 0:
                            logsTable[i][0] -= log(comp[1])
                        i+=comp[1]
    logsTable.sort(key=lambda x: abs(x[0]))
    for x in logsTable:
        IsBSmooth = CheckB(x[1], n, B)
        if (IsBSmooth[0]):
            X.append(x[1])
            S.append(IsBSmooth[2])
            E.append(IsBSmooth[1])
            ExpE.append(IsBSmooth[3])
        if (len(X) > h+2):
            break
    # Find possible combinations of "e" vectors in "E" list with Gauss method for potential "s" and "t" values calculating
    TE = deepcopy(TM(E))
    GTE = deepcopy(GaussTransform(TE))
    Vectors = deepcopy(GaussSolve(GTE))
    for K in Vectors:
        s = 1
        t = 1
        tVector = [0 for x in range(len(B))]
        for i in range(len(K)):
            if (K[i] == 1):
                s *= S[i]
                for j in range(len(B)):
                    tVector[j] += ExpE[i][j]
        for i in range(len(tVector)):
            t *= B[i] ** (tVector[i]//2)
        s %= n
        t %= n
        if ((s**2)%n == (t**2)%n):
            if (s%n != t%n and s%n != n-t%n):
                return gcd(s-t, n)

### ++CONTINUED FRACTIONS METHOD++ ###

# Continued fraction calculation
def CFRACC(n):
    A = []
    a0 = floor(sqrt(n))
    A.append(a0)
    
    return

nums_from_book = [5338771, 1557697, 1728239, 1373503, 1359331, 84257901, 8931721, 21299881]
nums_from_var = [22079925932281979779]

n = nums_from_var[0]
# n = nums_from_book[-1]

print(ceil(pow(exp(sqrt(log(n) * log(log(n)))), sqrt(2)/4)))
k = ceil(pow(exp(sqrt(log(n) * log(log(n)))), sqrt(2)/4))
p = QS(n, k)
while p == None:
    print(k)
    k = getNextPrime(k)
    p = QS(n, k)

print(p, n/p)