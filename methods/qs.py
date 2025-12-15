from math import gcd, log, floor, sqrt, exp, ceil

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
    with open("../primes.txt", "r") as fd:
        prime = list(map(int, fd.read().split()))[n - 1]
    return(prime)

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
