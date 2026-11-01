#!/usr/bin/env python3
"""Checks for v4.3: (1) worked-example matrices of Section 4; (2) det Phi for the
Fermat-type case (n,p,d,r)=(9,17,16,3), block k=2. Pure Python, no dependencies."""
from math import comb
def polypow(f,N,p):
    r=[1]
    for _ in range(N):
        t=[0]*(len(r)+len(f)-1)
        for i,a in enumerate(r):
            for j,b in enumerate(f): t[i+j]=(t[i+j]+a*b)%p
        r=t
    return r
def block(d,r,sig,p,n,k):
    kout=(k*pow(p,-1,n))%n; N=(kout*p-k)//n; gk=k*d//n; go=kout*d//n
    f=[0]*(d+1); f[0]=1; f[r]=(f[r]+sig)%p; f[d]=(f[d]+1)%p
    P=polypow(f,N,p); c=lambda e:P[e] if 0<=e<len(P) else 0
    return [[c(p*b-i) for i in range(1,gk+1)] for b in range(1,go+1)]
def mul(A,B,p): return [[sum(A[i][k]*B[k][j] for k in range(len(B)))%p for j in range(len(B[0]))] for i in range(len(A))]
def rank(A,p):
    A=[r[:] for r in A]; rk=0
    for c in range(len(A[0])):
        piv=next((i for i in range(rk,len(A)) if A[i][c]%p),None)
        if piv is None: continue
        A[rk],A[piv]=A[piv],A[rk]; inv=pow(A[rk][c],-1,p)
        A[rk]=[x*inv%p for x in A[rk]]
        for i in range(len(A)):
            if i!=rk and A[i][c]%p:
                m=A[i][c]; A[i]=[(x-m*y)%p for x,y in zip(A[i],A[rk])]
        rk+=1
    return rk
print("Section 4 example, p=7, n=3, d=4, r=1")
for sig in (1,3):
    M=block(4,1,sig,7,3,2); ranks=[rank(M,7)]; Q=M
    for _ in range(3): Q=mul(Q,M,7); ranks.append(rank(Q,7))
    print(" sigma=%d M(k=2)=%s ranks of powers=%s ; M(k=1)=%s"%(sig,M,ranks,block(4,1,sig,7,3,1)))
print("Fermat-type case (n,p,d,r)=(9,17,16,3), block k=2: det Phi vs 8(s^16-1) mod 17")
p=17; ok=True
for s in range(1,p):
    M0=block(16,3,s,p,9,2); k1=2*pow(p,-1,9)%9
    M1=block(16,3,s,p,9,k1); Phi=mul(M1,M0,p)
    # det of 3x3
    a=Phi; d=(a[0][0]*(a[1][1]*a[2][2]-a[1][2]*a[2][1])-a[0][1]*(a[1][0]*a[2][2]-a[1][2]*a[2][0])+a[0][2]*(a[1][0]*a[2][1]-a[1][1]*a[2][0]))%p
    ok&= d==8*(pow(s,16,p)-1)%p==0
print(" det Phi = 0 for every sigma in F_17^* :",ok)

# Symbolic determinant in sigma (polynomials mod p as coefficient lists, pure Python)
def padd(a,b,p):
    n=max(len(a),len(b)); return [((a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0))%p for i in range(n)]
def pmul(a,b,p):
    t=[0]*(len(a)+len(b)-1) if a and b else [0]
    for i,x in enumerate(a):
        for j,y in enumerate(b): t[i+j]=(t[i+j]+x*y)%p
    return t
def sblock(d,r,p,n,k):
    kout=(k*pow(p,-1,n))%n; N=(kout*p-k)//n; gk=k*d//n; go=kout*d//n
    def coef(e):  # coefficient of x^e in (1+s x^r+x^d)^N as polynomial in s
        out=[0]*(N+1)
        for al in range(N+1):
            for be in range(N-al+1):
                if d*al+r*be==e:
                    out[be]=(out[be]+comb(N,al)*comb(N-al,be))%p
        return out
    return [[coef(p*b-i) for i in range(1,gk+1)] for b in range(1,go+1)]
def smatmul(A,B,p):
    R=[]
    for i in range(len(A)):
        row=[]
        for j in range(len(B[0])):
            acc=[0]
            for k in range(len(B)): acc=padd(acc,pmul(A[i][k],B[k][j],p),p)
            row.append(acc)
        R.append(row)
    return R
p=17
Phi=smatmul(sblock(16,3,p,9,7),sblock(16,3,p,9,2),p)
def neg(a): return [(-x)%p for x in a]
def det3(a):
    t=lambda i,j,k:pmul(pmul(a[0][i],a[1][j],p),a[2][k],p)
    pos=padd(padd(t(0,1,2),t(1,2,0),p),t(2,0,1),p)
    ng=padd(padd(t(0,2,1),t(1,0,2),p),t(2,1,0),p)
    return padd(pos,neg(ng),p)
D=det3(Phi)
while len(D)>1 and D[-1]==0: D.pop()
T=[0]*17; T[0]=(-8)%p; T[16]=8
print("det Phi(sigma) mod 17 as polynomial (coeff list, constant first):",D)
print("equals 8*(sigma^16-1):", D==T)
