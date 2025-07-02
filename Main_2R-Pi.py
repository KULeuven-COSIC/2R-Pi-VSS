
###################################################################
## Source code for implementations of Round-Optimal VSS          ##
## schemes presented in Sections 4.2 and 4.3 of the paper        ## 
## "On Round-Optimal Computational VSS", published at CiC        ##
## jopurnal (https://cic.iacr.org/). This code also includes     ## 
## implementations of the synchronous two-round hash-based and   ##
## homomorphic commitment based VSS schemes presented by Backes, ##
## Kate,and Patra at ASIACRYPT 2011 [BKP11].                     ##    
## The source code implementations for original Pi VSS scheme    ##
## is taken from https://github.com/KULeuven-COSIC/Pi-VSS        ##
################################################################### 

from hashlib import sha256,sha1
from time import time

#####################################################
###### Initializations and necessary functions  #####
#####################################################

# global parameters
N = 2^256-189
ZN = Integers(N)
LAM = Integers(2^128)
R.<x> = PolynomialRing(ZN)

def shamir_bi(n):
    N = 2^256 - 189
    ZN = Integers(N)
    t = n // 2 - 1  # Degree t-1, leading to polynomial degree up to t-1 in each variable

    # Define the polynomial ring in two variables over Z/NZ
    R = PolynomialRing(ZN, names=('x', 'y'))
    x, y = R.gens()

    # Generate random coefficients for the polynomial
    coefficients = {}
    for i in range(t):
        for j in range(t):
            if i > j:
                coefficients[(i, j)] = ZN.random_element()
                coefficients[(j, i)] = coefficients[(i, j)]  # Immediately set the symmetric counterpart
            elif i == j:
                coefficients[(i, j)] = ZN.random_element()

    # Create the polynomial
    f = sum(coefficients[(i, j)] * x^i * y^j for i in range(t) for j in range(t))
    
    return f

# global parameters

p = 2^255-19         # Curve 25519
q = 2^252 + 27742317777372353535851937790883648493 #point group size
Zq = Integers(q)     # group of multiplication map
Am = 486662          # Montgomery A-coefficient
Ar = int((Am+2)/4)   # reduced Montgomery coefficent
E = EllipticCurve(GF(p),[0,Am,0,1,0])
RP.<x> = PolynomialRing(Zq)

G = E.random_point() # generator 1
while G.order() != q:
    G = E.random_point()
s = Zq.random_element()
s_= Zq.random_element()
H = Integer(s)*G     # generator 2
G_ = Integer(s_)*H     # generator 2

s_integer = int(s)
Hx_integer = int(H[0])
Hy_integer = int(H[1])
H_x_size = Hx_integer.bit_length()
H_y_size = Hy_integer.bit_length()
Zq_size = s_integer.bit_length()

#print("================================================")
#print(f"Size of a Z_q element in bits: {Zq_size}")
#print(f"Size of a x cordinate of H in bits: {H_x_size}")
#print(f"Size of a y cordinate of H in bits: {H_y_size}")
#print("================================================")

x_coord = G[0]
y_coord = G[1]

# Convert coordinates to integers
x_int = ZZ(x_coord)
y_int = ZZ(y_coord)

# Calculating bit lengths
x_bit_length = x_int.nbits()
y_bit_length = y_int.nbits()

#print("================================================")
#print(f"Size of |G| in bits: {(x_bit_length+y_bit_length)/2}")
#print(f"Size of a x cordinate of H in bits: {H_x_size}")
#print(f"Size of a y cordinate of H in bits: {H_y_size}")
#print("================================================")

G_Len = x_bit_length/2+y_bit_length/2
# Montgomery subroutines

def xADD(P,Q,R): # points are of the form [X,Z]
    [XP,ZP] = [P[0],P[1]];
    [XQ,ZQ] = [Q[0],Q[1]];
    [XR,ZR] = [R[0],R[1]];

    V0 = XP + ZP
    V1 = XQ - ZQ
    V1 = V1 * V0
    V0 = XP - ZP
    V2 = XQ + ZQ
    V2 = V2 * V0
    V3 = V1 + V2
    V3 = V3^2
    V4 = V1 - V2
    V4 = V4^2
    Xp = ZR * V3
    Zp = XR * V4
    
    return [Xp,Zp]

def xDBL(P): # points are of the form [X,Z]
    [XP,ZP] = [P[0],P[1]]
    
    V1 = XP + ZP
    V1 = V1^2
    V2 = XP - ZP
    V2 = V2^2
    X2 = V1 * V2
    V1 = V1 - V2
    V3 = Ar * V1
    V3 = V3 + V2
    Z2 = V1 * V3
    
    return [X2,Z2]

def Montgomery_ladder(k,P): # points are of the form [X,Z]
    x0,x1 = P,xDBL(P)
    k = k.binary()
    l = len(k)
    for i in range(1,l):
        if k[i]=='0':
            x0,x1 = xDBL(x0),xADD(x0,x1,P)
        if k[i]=='1':
            x0,x1 = xADD(x0,x1,P),xDBL(x1)
    return x0,x1

def recover_y(P,Q,R):
    [XP,YP] = [P[0],P[1]] # P is an actual elliptic curve point in the form (X:Y:Z)
    [XQ,ZQ] = [Q[0],Q[1]]
    [XR,ZR] = [R[0],R[1]]
        
    V1 = XP * ZQ
    V2 = XQ + V1
    V3 = XQ - V1
    V3 = V3^2
    V3 = V3 * XR
    V1 = 2*Am*ZQ
    
    V2 = V2 + V1
    V4 = XP * XQ
    V4 = V4 + ZQ
    V2 = V2 * V4
    V1 = V1 * ZQ
    V2 = V2 - V1
    V2 = V2 * ZR
    
    Y  = V2 - V3
    V1 =  2 * YP
    V1 = V1 * ZQ
    V1 = V1 * ZR
    X  = V1 * XQ
    Z  = V1 * ZQ
    
    return E(X,Y,Z)

def fast_multiply(k,P): # use montgomery ladder and y-recovery
    PM = [P[0],P[2]] # X-Z coordinates
    x0,x1 = Montgomery_ladder(Integer(k),PM)
    return E(recover_y(P,x0,x1))

# routines
def shamir_P(n):
    t = n//2-1 # assumes n is even!
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval

###########################################################
############# Our 2-round VSS from Sec. 4.1 ###############
###########################################################

# routines
def shamir_Pi_P(n):
    t = n//2-1 # assumes n is even!
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval

def prover_Pi_P_first_round(f,feval):
    t = f.degree()
    C = [0 for _ in range(n)]
    g = RP.random_element(degree=t)#############gamma
#    fcoeff = f.coefficients(sparse=False)
#    gcoeff = g.coefficients(sparse=False)
    
    geval = [g(x=i) for i in range(1,n+1)]

    random_vector = vector(Zq, [Zq.random_element() for _ in range(n)])  # randomizer for the commitment 
    for i in range(n):
        C[i] = fast_multiply(Integer(feval[i]),G)+fast_multiply(Integer(geval[i]),G_) + fast_multiply(Integer(random_vector[i]),H)
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    
    z=d*f+g    
    return g,C, random_vector, z

def prover_Pi_P_second_round(S1,t1,u1,v1,c1,c2):
    State1 = c1 == fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    State2 = c2 == fast_multiply(Integer(u1),G)+fast_multiply(Integer(v1),H)   
   
    return State1,State2

def verifier_Pi_P_first_round(i):
    S1 = Zq.random_element()
    t1 = Zq.random_element()
    u1 = Zq.random_element()
    v1 = Zq.random_element()   
    c1 = fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    c2 = fast_multiply(Integer(u1),G)+fast_multiply(Integer(v1),H)    

    return S1,t1,u1,v1,c1,c2

def verifier_Pi_P_second_round(i,Ci,C,z,fi,ri): 
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    zi = Integer(z(x=i))    
    gi = Integer(zi - d*fi)     
    #ri here is actually gammai in the paper
    #gi is ri in the paper
    #G is g1
    #G_ is g2
    #H is g3
    return Ci == fast_multiply(gi,G_) + fast_multiply(ri,H)+ fast_multiply(fi,G)



# benchmark function
def benchmark_two_rounds_Pi_P(n):
    Ts = time()
    f,feval = shamir_Pi_P(n)
    Ts = time() - Ts
    
    #first round prover
    T_d1 = time()
    g,C, random_vector, z = prover_Pi_P_first_round(f,feval)
    T_d1 = time()-T_d1+Ts

    i = randint(1,n) # sample verifier
    #first rounds verifier
    T_v1 = time()
    S1,t1,u1,v1,c1,c2 = verifier_Pi_P_first_round(i)
    T_v1 =  time() - T_v1
    # i = 10  # hardcode verifier 10 
    #Prover second rounds####################################
    T_d2 = time()
    state1,state2 = prover_Pi_P_second_round(S1,t1,u1,v1,c1,c2)
    T_d2 = time() -T_d2
    if state1 ==False: print(state1)
    if state2 ==False: print(state2)
    #print(state1,state2)
    Ci = C[i-1]    # commit to shares of randomizer 
    # fi = Integer(f(x=i))
    fi = f(x=i)
    # fi = Integer(feval[i])  # Share of party i 
    ri = Integer(random_vector[i-1])  # randomizer of party i in commitment Ci for gammai in paper
    #verifier second rounds
    T_v2 = time()
    boo = verifier_Pi_P_second_round(i,Ci,C,z,fi,ri)
    T_v2 = time()-T_v2

    if boo == False: print(boo)    
    return T_d1,n*T_d2,T_v1,T_v2


###########################################################
############# Our 2-round VSS from Sec. 4.2 ###############
###########################################################

# routines
def shamir_LA(n):
    t = n//2 - 1 # assumes n is even!
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval


def prover_LA_first_round(f,feval):
    t = f.degree()
    n = len(feval)
    b = RP.random_element(degree=t)
    C = ""

    for i in range(1,n+1): # parties are 0..n-1
        bi = b(x=i)
        C+= sha256((str(feval[i-1]) + str(bi)).encode()).hexdigest()+str(",")
    C= C[:-1]
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    r = b-d*f
    return C,r
def verifier_LA_first_round(i):
    S = Zq.random_element()
    t = Zq.random_element()
    c = sha256((str(S+t)).encode()).hexdigest()
    return S,t,c



def verifier_LA_second_round(i,C,r,xi):
    ri = r(x=i)
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    Ci = sha256((str(xi)+str(ri+d*xi)).encode()).hexdigest()
    return Ci == C.split(',')[i-1]



def prover_LA_second_round(S1,t1,c1):
    State1 = c1 == sha256((str(S1+t1)).encode()).hexdigest()
    return State1

# benchmark function
def benchmark_LA_two_rounds(n):
    N = 2^256-189
    ZN = Integers(N)
    LAM = Integers(2^128)
    R.<x> = PolynomialRing(ZN)

    Ts = time()
    f,feval = shamir_LA(n)
    Ts = time() - Ts

    T_d1 = time()#prover first round
    C,r = prover_LA_first_round(f,feval)
    T_d1 = time() - T_d1+Ts


    i = randint(1,n-1) # pick a random verifier
    T_v1 = time() # verfier first round
    S,t,c = verifier_LA_first_round(i)
    T_v1 = time() - T_v1
    T_d2 = time()
    state1= prover_LA_second_round(S,t,c) #prover second round
    T_d2 =  time() -T_d2
    if state1 ==False: print(state1) 
    T_v2 = time()
    b = verifier_LA_second_round(i,C,r,feval[i-1])
    T_v2 = time() - T_v2

    if b == False: print(b)
    return T_d1,n*T_d2,T_v1,T_v2


###########################################################
############# Our 2-round VSS from Sec. 4.3 ###############
###########################################################

# routines
def shamir_Pi_f(n):
    t = n//2-1 # assumes n is even!
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    return f,feval

def prover_Pi_f_first_round(f,feval):
    t = f.degree()
    C = [0 for _ in range(n)]
    r = RP.random_element(degree=t)#############gamma
    fcoeff = f.coefficients(sparse=False)
    rcoeff = r.coefficients(sparse=False)
    reval = [r(x=i) for i in range(1,n+1)]

    #random_vector = vector(Zq, [Zq.random_element() for _ in range(n)])  # randomizer for the commitment 
    for i in range(n):
        C[i] = fast_multiply(Integer(feval[i]),G) + fast_multiply(Integer(reval[i]),H)
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    
    z=d*f+r   
    return C, z

def prover_Pi_f_second_round(S1,t1,c1):
    State1 = c1 == fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    return State1

def verifier_Pi_f_first_round(i):
    S1 = Zq.random_element()
    t1 = Zq.random_element()
 
    c1 = fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    return S1,t1,c1

def verifier_Pi_f_second_round(i,Ci,C,z,fi):
    d = Integer(Zq(int(sha256(str(C).encode()).hexdigest(),16)))
    zi = Integer(z(x=i))    
    ri = Integer(zi - d*fi) 
    return Ci ==  fast_multiply(ri,H)+ fast_multiply(fi,G)


# benchmark function
def benchmark_two_rounds_Pi_f(n):
    Ts = time()
    f,feval = shamir_Pi_f(n)
    Ts = time() - Ts
    
    #first round prover
    T_d1 = time()
    C ,z = prover_Pi_f_first_round(f,feval)
    T_d1 = time()-T_d1+Ts

    i = randint(1,n) # sample verifier
    #first rounds verifier
    T_v1 = time()
    S1,t1,c1 = verifier_Pi_f_first_round(i)
    T_v1 =  time() - T_v1
    # i = 10  # hardcode verifier 10 
    #Prover second rounds####################################
    T_d2= time()
    state1= prover_Pi_f_second_round(S1,t1,c1)
    T_d2 = time() -T_d2
    if state1 ==False: print(state1)
    #print(state1,state2)
    Ci = C[i-1]    # commit to shares of randomizer 
    # fi = Integer(f(x=i))
    fi = f(x=i)
    # fi = Integer(feval[i])  # Share of party i 
    #ri = Integer(random_vector[i-1])  # randomizer of party i in commitment Ci 
    #verfier second rounds
    T_v2 = time()
    boo = verifier_Pi_f_second_round(i,Ci,z,fi)
    T_v2 = time()-T_v2


    if boo == False: print(boo)    
    return T_d1,n*T_d2,T_v1,T_v2
    

##############################################################
############# 2-Round Hash-based VSS from [BKP11] ############
##############################################################

def prover_BKP_first_round(n):
    T_bi = time()
    f = shamir_bi(n)   # f_{ij}
    
    r = shamir_bi(n) # r_{i,j}
    T_bi = time() - T_bi
    C, F, R = [], [], []
    
    Dict = {}

    for i in range(1, n + 1):
        C_, F_, R_ = [], [], []
        for j in range(1, n + 1):

            
            if not i >j:
                bij = r(x=i, y=j)  # Evaluate polynomial r at (i, j)
                
                f_ij = f(x=i, y=j)                
                c_val = bij+f_ij
                c0 = sha256(str(c_val).encode()).hexdigest()
                C_.append(c0)
            
              # Evaluate polynomial f at (i, j)
                F_.append(f_ij)
            
            # Hash of concatenated c0 and f_ij, converted to string for consistency
             
                R_.append(bij)
                Dict['f'+str(i)+','+str(j)] = f_ij
                Dict['b'+str(i)+','+str(j)] = bij
                Dict['c'+str(i)+','+str(j)] = c0
            else:
                C_.append(Dict['c'+str(j)+','+str(i)])
            
              # Evaluate polynomial f at (i, j)
                F_.append(Dict['f'+str(j)+','+str(i)])
            
            # Hash of concatenated c0 and f_ij, converted to string for consistency
             
                R_.append(Dict['b'+str(j)+','+str(i)])              

        C.append(C_)
        F.append(F_)
        R.append(R_)
    #print(T_bi)
    return F, R, C,T_bi

# Example call to the function
#F, R, C = prover_BKP_first_round(4)
#print("F:", F)
#print("R:", R)
#print("C:", C)
def verifier_BKP_first_round(i,n):
    
    s,t,u,v,c1,c2 = [],[],[],[],[],[]
    for i in range(1,n+1):
        S1 = Zq.random_element()
        u1 = Zq.random_element()
        t1 = Zq.random_element()
        v1 = Zq.random_element()
        s.append(S1)
        t.append(t1)
        u.append(u1)
        v.append(v1)   
        c1.append(sha256((str(S1+t1)).encode()).hexdigest())
        c2.append(sha256((str(u1+v1)).encode()).hexdigest())   

    return s,t,u,v,c1,c2


def verifier_BKP_second_round(i,C,R, F):
    n= len(C)
    c= C[i]
    f = F[i]
    r = R[i]
    State = True
    for j in range(n):
        c_val = f[j]+r[j]
        state = c[j] == sha256(str(c_val).encode()).hexdigest()
        State = State and state
        
    return State


def prover_BKP_second_round(s,t,u,v,c1,c2):
    n= len(s)
    State1 = True
    for i in range(n):
        state1 = c1[i] == sha256((str(s[i]+t[i])).encode()).hexdigest()
        State1 = State1 and state1
    State2 = True
    for i in range(n):
        state2 = c2[i] == sha256((str(u[i]+v[i])).encode()).hexdigest()
        State2 = State2 and state2
    return State1,State2

# benchmark function
def benchmark_BKP_two_rounds(n):
    N = 2^256-189
    ZN = Integers(N)
    LAM = Integers(2^128)
    R.<x> = PolynomialRing(ZN)

    T_d1 = time()#dealer first round
    F, R, C,T_bi = prover_BKP_first_round(n)
    T_d1 = time() - T_d1

   

    i = randint(1,n-1) # pick a random verifier
    T_v1 = time() # verfier first round
    s,t,u,v,c1,c2 = verifier_BKP_first_round(i,n)
    T_v1 = time() - T_v1
    T_d2 = time()
    state1,state2 = prover_BKP_second_round(s,t,u,v,c1,c2) #prover second round
    T_d2 =  time() -T_d2
    if state1 ==False: print(state1)
    if state2 ==False: print(state2)   
    T_v2 = time()
    b = verifier_BKP_second_round(i,C,R, F)
    T_v2 = time() - T_v2

    if b == False: print(b)
    return T_d1,n*T_d2,T_v1,T_v2,T_bi


##############################################################
############# 2-Round Pedersen Based VSS from [BKP11] ########
##############################################################

def Prover_BKP_Hm_1stR(t):
    n = t*2+2
    f = RP.random_element(degree=t)
    feval = [f(x=i) for i in range(1,n+1)]
    C = [0 for _ in range(t+1)]
    g = RP.random_element(degree=t)
    fcoeff = f.coefficients(sparse=False)
    gcoeff = g.coefficients(sparse=False)
    geval = [g(x=i) for i in range(1,n+1)]
    for i in range(t+1):
        C[i] = fast_multiply(Integer(fcoeff[i]),G) + fast_multiply(Integer(gcoeff[i]),H)
    
    return feval,geval,C


def Prover_BKP_Hm_2ndR(S1,t1,u1,v1,c1,c2):
    State1 = c1 == fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    State2 = c2 == fast_multiply(Integer(u1),G)+fast_multiply(Integer(v1),H)   
   
    return State1,State2


def Verifier_BKP_Hm_1stR(i):
    S1 = Zq.random_element()
    t1 = Zq.random_element()
    u1 = Zq.random_element()
    v1 = Zq.random_element()   
    c1 = fast_multiply(Integer(S1),G)+fast_multiply(Integer(t1),H)
    c2 = fast_multiply(Integer(u1),G)+fast_multiply(Integer(v1),H)    

    return S1,t1,u1,v1,c1,c2

def Verifier_BKP_Hm_2ndR(f_i,r_i,C,i):
    S = C[0]
    for j in range(1,len(C)):
        S += fast_multiply(Integer(Zq(i)^j),C[j])
    return S == fast_multiply(f_i,G) + fast_multiply(r_i,H)


# benchmark function
def benchmark_P_BKP_Hm(n):
    t = n//2 -1
    Tp1 = time()
    feval,reval,C = Prover_BKP_Hm_1stR(t)
    Tp1 = time() - Tp1


    i = randint(1,n+1) # sample verifier
    Tv1 = time()
    S1,t1,u1,v1,c1,c2 = Verifier_BKP_Hm_1stR(i)
    Tv1 = time()-Tv1

    #for i in range(1,n):
    Tp2 = time()   
    S1,S2 = Prover_BKP_Hm_2ndR(S1,t1,u1,v1,c1,c2)
    
    Tp2 = n*(time()-Tp2)
       
    Tv2 = time()
    i = 2
    S3 = Verifier_BKP_Hm_2ndR(feval[i-1],reval[i-1],C,i)

    Tv2 = time() - Tv2
    #print(S1,S2,S3)
    if (S1 and S2 and S3):
        return Tp1,Tp2,Tv1,Tv2
    else:
        print('Not passed')


#a,b,c,d = benchmark_P_BKP_Hm(16)


#########################
##### Benchmarking ######
#########################

#f = shamir_bi(10)
#print(f)
#f_at_x1 = f.subs(y=-1) 
from hashlib import sha256

# Generate SHA-256 hash and get the hex digest
hash_hex = sha256(str(0).encode()).hexdigest()

# Calculate length of the hash in bits
# Since each hex digit represents 4 bits, just multiply the length of the hex string by 4
hash_length_in_bits = len(hash_hex) * 4

H_ =  hash_length_in_bits

#print("==================================================================================")
#print("Length of the hash in bits:", hash_length_in_bits)
#print("==================================================================================")

# Running the benchmark
N=[16, 32, 64, 128, 256]
#N=[16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384]

for i in range(len(N)):
  n = N[i]  
  iteration = 1
  if n > 513: iteration = 1

  print("**********************************************************************************")
  print("Benchmarking Round-Optimal (2-Round) VSS Schemes for (n, t) =", (n, n/2-1))
  print("**********************************************************************************")
  
  #T_Pif =  [0]*4
  T_Pip =  [0]*4  
  T_Pila = [0]*4
  T_BKP =  [0]*5
  T_BKP_Hm = [0]*4

  for i in range(iteration):
    Td1_Pip,Td2_Pip,Tv1_Pip,Tv2_Pip = benchmark_two_rounds_Pi_P(n)
    #Td1_Pif,Td2_Pif,Tv1_Pif,Tv2_Pif =benchmark_two_rounds_Pi_f(n)
    Td1_Pila,Td2_Pila,Tv1_Pila,Tv2_Pila =benchmark_LA_two_rounds(n)
    Td1_BKP,Td2_BKP,Tv1_BKP,Tv2_BKP ,Tbi_BKP=benchmark_BKP_two_rounds(n)
    Td1_BKP_Hm,Td2_BKP_Hm,Tv1_BKP_Hm,Tv2_BKP_Hm  = benchmark_P_BKP_Hm(n)
    
    T_Pip[0]+=Td1_Pip
    T_Pip[1]+=Td2_Pip
    T_Pip[2]+=Tv1_Pip
    T_Pip[3]+=Tv2_Pip
    
    T_Pila[0]+=Td1_Pila
    T_Pila[1]+=Td2_Pila
    T_Pila[2]+=Tv1_Pila
    T_Pila[3]+=Tv2_Pila    
  
    T_BKP[0]+=Td1_BKP
    T_BKP[1]+=Td2_BKP
    T_BKP[2]+=Tv1_BKP
    T_BKP[3]+=Tv2_BKP
    T_BKP[4]+=Tbi_BKP

    T_BKP_Hm[0]+=Td1_BKP_Hm
    T_BKP_Hm[1]+=Td2_BKP_Hm
    T_BKP_Hm[2]+=Tv1_BKP_Hm
    T_BKP_Hm[3]+=Tv2_BKP_Hm


  print("=======================================================================================") 

  print("============================== Dealer Time ============================================")

  print("======================= Hash Based Commitment: Sec. 4.2 and [BKP11] ===================")
  print("2R_BKP            -- 1st Round time:       ",(T_BKP[0])/iteration)
  print("2R_BKP            -- 2nd Round time:       ",(T_BKP[1])/iteration)
    
  print("2R_VSS_Sec. 4.2   -- 1st Round time:       ",(T_Pila[0])/iteration)  
  print("2R_VSS_ Sec 4.2   -- 2nd Round time:       ",(T_Pila[1])/iteration)

  print("====================== DL Based Commitment Sec. 4.1 and [BKP11] =======================") 
  
  print("2R_BKP_Hm         -- 1st Round time:       ",(T_BKP_Hm[0])/iteration)
  print("2R_BKP_Hm         -- 2nd Round time:       ",(T_BKP_Hm[1])/iteration)  
  
  print("2R_VSS_Sec. 4.1   -- 1st Round time:       ",(T_Pip[0])/iteration)  
  print("2R_VSS_Sec. 4.1   -- 2nd Round time:       ",(T_Pip[1])/iteration)  
  print("======================================================================================")   
  
  
  print("============================ Each Party Time =========================================")
 
  print("======================= Hash Based Commitment: Sec. 4.2 and [BKP11] ==================")
  print("2R_BKP            -- 1st Round time:  ",(T_BKP[2])/iteration)
  print("2R_BKP            -- 2nd Round time:  ",(T_BKP[3])/iteration)
  
  print("2R_VSS_Sec. 4.2   -- 1st Round time:  ",(T_Pila[2])/iteration)
  print("2R_VSS_Sec. 4.2   -- 2nd Round time:  ",(T_Pila[3])/iteration)
  
  print("====================== DL Based Commitment Sec. 4.1 and [BKP11] ======================") 
  print("2R_BKP_Hm         -- 1st Round time:  ",(T_BKP_Hm[2])/iteration)
  print("2R_BKP_Hm         -- 2nd Round time:  ",(T_BKP_Hm[3])/iteration)  
  
  print("2R_VSS_Sec. 4.1   -- 1st Round time:  ",(T_Pip[2])/iteration)
  print("2R_VSS_Sec. 4.1   -- 2nd Round time:  ",(T_Pip[3])/iteration)

  print("======================================================================================")