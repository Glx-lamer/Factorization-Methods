from math import sqrt, log, exp, ceil, floor, gcd

# Legendre (Jacobi) symbol, O(log^2(n))
def LegendreSymbol(a, n):
    g = 1
    while (True):
        if (a == 0):
            return 0
        if (a == 1):
            return g
        a_ = a
        k = 0
        while (a_ % 2 == 0):
            a_ >>= 1
            k+=1
        if (k % 2 == 0):
            s = 1
        else:
            if (n % 8 == 1 or n % 8 == 7):
                s = 1
            else:
                s = -1
        if (a_ == 1):
            return g*s
        if (n % 4 == 3 and a_ % 4 == 3):
            s*=-1
        a = n % a_
        n = a_
        g = g*s

# Generate Factorization base for Quadratic Sieve method
def getFactBase(n):
    P = ceil(sqrt(exp(sqrt(log(n)*log(log(n))))))
    # Get first prime numbers lower than P
    with open("primes.txt", "r") as fd:
        primes = list(map(int, fd.read().split()))
        ind = 0
        while (ind == 0):
            try:
                ind = primes.index(P)
            except:
                P-=1
        B_ = primes[:(ind + 1)]
    B = [-1, 2]
    # Check if n is quadratic residue modulo p
    for p in B_[1:]:
        if (LegendreSymbol(n, p) == 1):
            B.append(p)
    return B

# Solve comparisons of type: f(x) = (x+[sqrt(n)])^2 == n (mod p), O(log^4(p) for any p in B)
def getSolvComp(n, B):
    # x^2 == a (mod p)
    a = n
    SolvComp = []
    SolvComp.append([a%2, 2])
    for p in B[2:]:
        # Get num N, which is quadratic non-residue modulo p
        N = 2
        while (LegendreSymbol(N, p) != -1):
            N+=1
        h = p - 1
        k = 0
        while (h % 2 == 0):
            h >>= 1
            k+=1
        a1 = pow(a, (h+1)//2, p)
        # Get multiplicatively inverse of a
        y1 = 1
        y0 = 0
        n1 = p
        n2 = a
        while(n2 != 0):
            k = n1//n2
            n1, n2 = n2, n1%n2
            y0, y1 = y1, y0 - y1 * k
        a2 = y0
        N1 = pow(N, h, p)
        N2 = 1
        j = 0
        for i in range(k-2):
            b = (a1 * N2) % p
            c = (a2 * b**2) % p
            d = pow(c, 2**(k-2-i), p)
            if (d > p//2):
                d = p - d
            if (d == 1):
                j = 0
            if (d == -1):
                j = 1
            N2 = (N2 * N1**(2**i * j)) % p
        SolvComp.append([(a1*N2 - floor(sqrt(n))) % p, p])
        SolvComp.append([(-a1*N2 - floor(sqrt(n))) % p, p])
    return SolvComp

# Quadratic Sieve method
def QuadraticSieve(n):
    # Generate table with ln(f(x)) for any x in [-M, M]
    M = (ceil(exp(sqrt(log(n)*log(log(n))))**(sqrt(2)/4)))**3
    sqrtN = floor(sqrt(n))
    logsTable = [[log(abs((x+sqrtN)**2-n)), x] for x in range(-M, M+1)]
    B = getFactBase(n)
    h = len(B) - 1
    # Sort table by probability of B-smoothness for x
    Comps = getSolvComp(n, B)
    for comp in Comps:
        for x in range(1, M+1):
            if (x % comp[1] == comp[0]):
                x_ = x
                while x <= M:
                    logsTable[M + x][0] -= log(comp[1])
                    x+=comp[1]
                while x_ <= M:
                    logsTable[M - x_][0] -= log(comp[1])
                    x_+=comp[1]
                break
    logsTable.sort(key=lambda x: abs(x[0]))
    # Get first h+2 B-smooth x
    X = []
    A = []
    E = []
    for i in range(len(logsTable)):
        x = logsTable[i][1]
        e = []
        for p in B[1:]:
            a = 0
            while (x % p == 0):
                a+=1
                x//=p
            e.append(a)
        if (x == 1):
            e = [0] + e
            X.append(logsTable[i][1])
            A.append(e)
            E.append([elem % 2 for elem in e])
        if (x == -1):
            e = [0] + e
            X.append(logsTable[i][1])
            A.append(e)
            E.append([elem % 2 for elem in e])
        if (len(X) >= (h + 2)):
            break
    # Transpose matrix with binary vectors
    TranspE = [[0 for x in range(len(E))] for x in range(len(E[0]))]
    for i in range(len(E)):
        for j in range(len(E[0])):
            TranspE[j][i] = E[i][j]
    # Transform matrix with binary vectors to triangular
    TranspE.sort(reverse=True)
    i = 0
    while i < len(TranspE):
        for j in range(len(TranspE[0])):
            if j < i and TranspE[i][j] == 1:
                for k in range(len(TranspE[0])):
                    if TranspE[j][k] == 1:
                        TranspE[i][k] = 0 if TranspE[i][k] == 1 else 1
                TranspE.sort(reverse=True)
                i = -1
                break
        i+=1
    TriangE = TranspE
    # Find combinations of binary vectors that guarantee sum(e) % 2 == 0
    K = [[0 for i in range(len(TriangE))]]
    for i in range(len(TriangE) - 1, 0, -1):
        if TriangE[i][i] == 0:
            KK = []
            for j in range(len(K)):
                K[j][i] = 0
                KK.append(K[j].copy())
                KK[j][i] = 1
            K = K + KK
        if TriangE[i][i] == 1:
            for _ in K:
                s = 0
                for j in range(i+1, len(_)):
                    s+=_[j]*TriangE[i][j]
                if s%2 == 0:
                    for j in range(len(K)):
                        K[j][i] = 0
                else:
                    for j in range(len(K)):
                        K[j][i] = 1
    for k in K:
        s = 1
        t = 1
        tVector = [0 for x in range(len(B))]
        for i in range(len(k)):
            if (k[i] == 1):
                s *= X[i] + floor(sqrt(n))
                for j in range(len(B)):
                    tVector[j] += A[i][j]
        for i in range(len(tVector)):
            t *= B[i] ** (tVector[i]//2)
        s %= n
        t %= n
        print(s, t)
        if ((s**2)%n == (t**2)%n):
            if (s%n != t%n and s%n != n-t%n):
                return gcd(s-t, n)

n = 8931721

print(QuadraticSieve(n))